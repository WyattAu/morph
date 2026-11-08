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
   relation, not just the bindings, and is the next file.

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

end Cfg
end Morph.Clif
