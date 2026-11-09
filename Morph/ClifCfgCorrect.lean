/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifCfgEncode

/-!
# Stage C item C4b: the phi ↔ block-argument half

The encoder (`Morph/ClifCfgEncode.lean`) turns MIR's merge — one `phi` per
predecessor, all writing the same register — into CLIF's form: one block
parameter per merged register, fed by a different argument on each edge. The
correctness theorem for that translation has two halves:

1. **Binding.** Running the join's parameter list against the taken edge's
   arguments binds exactly the registers the executed phis would have written,
   and touches nothing else. That is this file.
2. **Simulation.** The block's remaining instructions and its terminator step in
   lockstep with the CLIF model, under the value-agreement relation Stage B
   already uses (`Morph/ClifSimulate.lean`). That needs a block-level trace
   relation, not just the bindings, and lives in `Morph/ClifCfgSimulate.lean`.

Why split it: the binding half is where a *silent* error would live. If
`paramsOf` and `edgeArgs` disagreed — one parameter per phi rather than per
destination — the join would still run whenever the arity happened to match
and would bind the wrong register. Loop 160 hit exactly that shape as an
encoding failure; loop 161 hit its runtime twin (a phi whose predecessor named
the wrong block). Stated as lemmas, the merge is checked by the kernel.

`paramsOf_nodup` closes the gap between the two: the encoder's parameter list is
duplicate-free by construction, so `bindParams_nodup_mem` applies to the list the
encoder really emits.
-/

open Morph.Core
open Morph.MIR (ValId)

namespace Morph.Clif
namespace Cfg

/-- **The binding lemma.** A duplicate-free parameter list is bound exactly as
zipped: each parameter reads the argument at its own position, whatever the
recursion order. Distinctness is what makes the statement true — with a repeated
parameter the later binding shadows the earlier one and the pair is ambiguous,
which is why the encoder refuses a duplicated destination per predecessor
(`noDupPairs`). -/
theorem bindParams_nodup_mem {env env' : Env} :
    ∀ {ps : List Reg} {vs : List Value}, ps.Nodup →
      bindParams env ps vs = some env' →
      ∀ {reg : Reg} {value : Value}, (reg, value) ∈ ps.zip vs → env' reg = some value
  | [], vs, _, _, reg, value, hm => by
    simp only [List.zip_nil_left, List.not_mem_nil] at hm
  | r :: rs, vs, hnd, h, reg, value, hm => by
    rw [List.nodup_cons] at hnd
    obtain ⟨hnotin, hnd'⟩ := hnd
    cases vs with
    | nil => simp [bindParams] at h
    | cons w ws =>
      cases hb : bindParams env rs ws with
      | none => simp [bindParams, hb] at h
      | some e =>
        have henv : e.set r w = env' := by
          simpa [bindParams, hb] using h
        rw [List.zip_cons_cons] at hm
        rcases List.mem_cons.mp hm with hhead | htail
        · simp only [Prod.mk.injEq] at hhead
          rcases hhead with ⟨rfl, rfl⟩
          rw [← henv, Env.set_same]
        · have hne : reg ≠ r := by
            intro hreg
            subst hreg
            exact hnotin (List.of_mem_zip htail).1
          rw [← henv, Env.set_other _ _ hne]
          exact bindParams_nodup_mem hnd' hb htail

/-- **Preservation outside the parameter list.** Binding parameters leaves every
other register alone, so an encoded edge cannot disturb values the rest of the
function still reads. -/
theorem bindParams_not_mem {env env' : Env} :
    ∀ {ps : List Reg} {vs : List Value},
      bindParams env ps vs = some env' →
      ∀ {reg : Reg}, reg ∉ ps → env' reg = env reg
  | [], vs, h, reg, _ => by
    cases vs with
    | nil =>
      simp only [bindParams, Option.some.injEq] at h
      subst h
      rfl
    | cons _ _ => simp [bindParams] at h
  | r :: rs, vs, h, reg, hreg => by
    cases vs with
    | nil => simp [bindParams] at h
    | cons w ws =>
      cases hb : bindParams env rs ws with
      | none => simp [bindParams, hb] at h
      | some e =>
        have henv : e.set r w = env' := by
          simpa [bindParams, hb] using h
        have hreg' : reg ∉ rs := fun hm => hreg (List.mem_cons_of_mem _ hm)
        have hne : reg ≠ r := fun hpq => hreg (by rw [hpq]; simp)
        rw [← henv, Env.set_other _ _ hne, bindParams_not_mem hb hreg']

/-! ## Arity

`encodeTerm` refuses an edge that cannot supply one argument per parameter, so a
successful encoding always has matching lengths. This is what lets the
simulation file hand `bindParams` a length-correct pair and know that its only
failure mode is a missing register value. -/

/-- `argsFor` yields one argument per parameter, by construction. -/
theorem argsFor_length (ps : List Phi) (pred : Morph.MIR.BlockId) :
    ∀ (ds : List ValId) (r : List Reg), argsFor ps pred ds = some r → r.length = ds.length
  | [], r, h => by
    simp only [argsFor, Option.some.injEq] at h
    subst h
    rfl
  | d :: ds, r, h => by
    cases hf : ps.find? (fun p => p.dst == d && p.pred == pred) with
    | none => simp [argsFor, hf] at h
    | some p =>
      cases hr : argsFor ps pred ds with
      | none => simp [argsFor, hf, hr] at h
      | some rest =>
        simp only [argsFor, hf, hr, Option.some.injEq] at h
        subst h
        simp [argsFor_length ps pred ds rest hr]

/-- An encoded edge passes exactly as many arguments as its target declares
parameters. -/
theorem edgeArgs_length {f : Morph.MIR.Func} {target pred : Morph.MIR.BlockId}
    {ps : List Phi} {args : List Reg}
    (hps : targetPhis f target = some ps)
    (h : edgeArgs f target pred = some args) :
    args.length = (paramsOf ps).length := by
  unfold edgeArgs at h
  rw [hps] at h
  exact argsFor_length ps pred (paramsOf ps) args h

/-! ## The encoder's parameter list is duplicate-free

`paramsOf` appends a destination only when the accumulator does not already hold
it, so the result has no repeats. This is the hypothesis `bindParams_nodup_mem`
needs; without it the binding lemma would say nothing about the emitted list.
Both facts are proved here because the toolchain has no
`Nodup (l ++ [x])` lemma that applies directly. -/

/-- Appending one absent element preserves duplicate-freedom. -/
theorem nodup_append_singleton {l : List ValId} {x : ValId} (h : l.Nodup) (hx : x ∉ l) :
    (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at h
    obtain ⟨ha, has⟩ := h
    rw [List.cons_append, List.nodup_cons]
    constructor
    · intro hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact ha h1
      · rw [List.mem_singleton] at h2
        subst h2
        exact hx List.mem_cons_self
    · exact ih has (fun hm => hx (List.mem_cons_of_mem _ hm))

/-- **The parameter list has no repeats.** -/
theorem paramsOf_nodup (phis : List Phi) : (paramsOf phis).Nodup := by
  suffices h : ∀ (acc : List ValId), acc.Nodup →
      ∀ (l : List Phi),
        (l.foldl (fun acc p => if acc.elem p.dst then acc else acc ++ [p.dst]) acc).Nodup from
    h [] List.nodup_nil phis
  intro acc hacc l
  induction l generalizing acc with
  | nil => exact hacc
  | cons p ps ih =>
    rw [List.foldl_cons]
    apply ih
    by_cases he : acc.elem p.dst
    · have hmem : p.dst ∈ acc := List.elem_iff.mp he
      simpa [hmem] using hacc
    · have hnot : p.dst ∉ acc := by
        simpa [List.elem_iff] using he
      show (if acc.elem p.dst = true then acc else acc ++ [p.dst]).Nodup
      rw [if_neg he]
      exact nodup_append_singleton hacc hnot

/-- Distributing the existential `List.mem_cons` leaves inside `paramsOf`'s fold
guard. Proved by hand so the closing bookkeeping of `paramsOfAux_mem` does not
depend on which distribution lemmas the toolchain exports. -/
private theorem exists_or_dst (p : Phi) (ps : List Phi) (d : ValId) :
    (∃ q, (q = p ∨ q ∈ ps) ∧ q.dst = d) ↔ (p.dst = d ∨ ∃ q ∈ ps, q.dst = d) := by
  constructor
  · rintro ⟨q, hq | hq, hqd⟩
    · subst hq; exact Or.inl hqd
    · exact Or.inr ⟨q, hq, hqd⟩
  · rintro (h | ⟨q, hq, hqd⟩)
    · exact ⟨p, Or.inl rfl, h⟩
    · exact ⟨q, Or.inr hq, hqd⟩

/-- **Which destinations the merge contains.** `paramsOf` folds with a `mem`
guard, so this says the guard changes only how often a destination appears, never
whether it does: every parameter comes from a phi, and with `paramsOf_nodup` from
exactly one. -/
theorem paramsOfAux_mem (l : List Phi) :
    ∀ (acc : List ValId) (d : ValId),
      d ∈ l.foldl (fun acc p => if acc.elem p.dst then acc else acc ++ [p.dst]) acc ↔
        d ∈ acc ∨ ∃ p ∈ l, p.dst = d
  | acc, d => by
    induction l generalizing acc with
    | nil => simp
    | cons p ps ih =>
      rw [List.foldl_cons]
      by_cases he : acc.elem p.dst
      · rw [if_pos he, ih]
        constructor
        · rintro (h | ⟨q, hq, hqd⟩)
          · exact Or.inl h
          · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqd⟩
        · rintro (h | ⟨q, hq, hqd⟩)
          · exact Or.inl h
          · rcases List.mem_cons.mp hq with rfl | hq'
            · exact Or.inl (hqd ▸ List.elem_iff.mp he)
            · exact Or.inr ⟨q, hq', hqd⟩
      · rw [if_neg he, ih (acc ++ [p.dst]), List.mem_append, List.mem_singleton]
        simp only [List.mem_cons]
        rw [exists_or_dst p ps d]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h.symm)
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h.symm)
          · exact Or.inr h

/-- The merge's parameters are exactly the destinations its phis define. -/
theorem paramsOf_mem (ps : List Phi) (d : ValId) :
    d ∈ paramsOf ps ↔ ∃ p ∈ ps, p.dst = d := by
  simpa [paramsOf] using paramsOfAux_mem ps [] d

/-! ## The encoder's gates imply the fold's hypotheses

`encodeBlock` refuses a join unless both `noDupPairs` and `noPhiChain` hold, so
every list the encoder really emits satisfies the two hypotheses the fold
lemmas demand. The first says a destination names one source per edge: the
successful check puts the phi itself and any same-edge rival in one
length-one filter, hence in one singleton. The second says no phi reads what
another phi on the same edge writes: a violation would be a live witness for
the `any` the check requires to be false. -/

/-- A successful `noDupPairs` check names one source per destination and edge. -/
theorem noDupPairs_huniq (ps : List Phi) (hnd : noDupPairs ps = true)
    (pred : Morph.MIR.BlockId)
    (q : Phi) (hq : q ∈ ps) (hqp : q.pred = pred)
    (q' : Phi) (hq' : q' ∈ ps) (hqp' : q'.pred = pred)
    (hdst : q.dst = q'.dst) : q.src = q'.src := by
  simp only [noDupPairs] at hnd
  have hall := (List.all_eq_true.mp hnd) q hq
  have hself : (q.dst == q.dst && q.pred == q.pred) = true := by simp
  have hother : (q'.dst == q.dst && q'.pred == q.pred) = true := by
    simp [hdst, hqp, hqp']
  have hlen : (ps.filter fun r => r.dst == q.dst && r.pred == q.pred).length = 1 :=
    beq_iff_eq.mp hall
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  have hmq : q ∈ ps.filter (fun r => r.dst == q.dst && r.pred == q.pred) :=
    List.mem_filter.mpr ⟨hq, hself⟩
  have hmq' : q' ∈ ps.filter (fun r => r.dst == q.dst && r.pred == q.pred) :=
    List.mem_filter.mpr ⟨hq', hother⟩
  rw [ha, List.mem_singleton] at hmq hmq'
  have heq : q = q' := hmq.trans hmq'.symm
  rw [heq]

/-- A successful `noPhiChain` check keeps same-edge reads off same-edge writes. -/
theorem noPhiChain_hsep (ps : List Phi) (hnc : noPhiChain ps = true)
    (pred : Morph.MIR.BlockId)
    (q : Phi) (hq : q ∈ ps) (hqp : q.pred = pred)
    (q' : Phi) (hq' : q' ∈ ps) (hqp' : q'.pred = pred) : q.src ≠ q'.dst := by
  simp only [noPhiChain] at hnc
  have hall := (List.all_eq_true.mp hnc) q hq
  have hfalse : (ps.any fun r => q.pred == r.pred && decide (q.src = r.dst)) = false := by
    cases h : (ps.any fun r => q.pred == r.pred && decide (q.src = r.dst)) with
    | true => simp [h] at hall
    | false => rfl
  intro hcon
  have hpred : (q.pred == q'.pred) = true := by
    simp only [beq_iff_eq, hqp, hqp']
  have htrue : (ps.any fun r => q.pred == r.pred && decide (q.src = r.dst)) = true :=
    List.any_eq_true.mpr ⟨q', hq', by
      show (q.pred == q'.pred && decide (q.src = q'.dst)) = true
      simp only [Bool.and_eq_true, hpred, true_and]
      simp [hcon]⟩
  simp [hfalse] at htrue

end Cfg
end Morph.Clif
