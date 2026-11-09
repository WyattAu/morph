/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifCfgCorrect
import Morph.ClifSimulate

/-!
# Stage C item C4b: the simulation half

`docs/STAGEC-SCOPE.md` §5.1. `Morph/ClifCfgCorrect.lean` proves that binding a
block's parameters reproduces the phi writes *as a binding*. This file assembles
the rest of the simulation, in the pieces a reader can check separately:

1. **The instructions after the phis.** A `Trace` (Stage B's certificate) whose
   encoding is `cs` runs in the block model, from any environment that agrees
   with the MIR one, to an agreeing environment. This is the block-level
   counterpart of `run_simulate`: that lemma says one environment runs both
   sides, this one says two agreeing environments stay in step, which is what a
   block boundary needs because the block model reads its environment from the
   edge rather than from MIR's register file.
2. **The edge's arguments are readable.** `argsFor` builds one argument per
   parameter; `argsFor_get?` says the argument at a parameter's position is the
   `src` of the phi the encoder selected for that parameter and edge. Without
   this the binding lemma has nothing to bind *from* — it is the link between
   the encoder's `find?` and the `zip` the binding lemma consumes.
3. **Binding reads positionally.** `bindParams_get?` restates the binding lemma
   in index form, so it composes with `argsFor_get?` and with
   `evalArgs_get?` (the value actually held by each argument register) without
   any list-length bookkeeping.

What is *not* here yet: the MIR-side phi fold. `execInstrsFullFrom` walks the
leading phis one at a time, reading each `src` from the environment the previous
phi left behind; the lemma that this reproduces exactly "one write per selected
phi" needs either a disjointness hypothesis (a phi's `src` is not another phi's
`dst`) or a sequential formulation, and it is the next piece. The fuel
induction that composes (1)–(3) with the phi fold and the terminator comes after
it. Nothing here assumes that piece's shape, so it will not be rewritten.
-/

open Morph.Core
open Morph.MIR (ValId)

namespace Morph.Clif
namespace Cfg

/-! ## The instructions after the phis -/

/-- **Two agreeing environments stay in step.** Given a certified straight-line
body, its encoding, and a second environment that agrees on every non-unit value,
running the encoded list in the second environment succeeds and lands in an
environment agreeing with the MIR result.

The proof is the trace induction plus `step_transport` (the same MIR step in the
agreeing environment) and `step_simulate` (that step is the encoded CLIF
instruction). No instruction is inspected: the value-shape knowledge is entirely
in `Trace`, which is why this composes with the phi phase without case analysis.
-/
theorem trace_runInstrs_agree {is : List Morph.MIR.Instr} {u w : Morph.MIR.Env}
    {cs : List Instr} (htr : Trace is u w) (henc : instrEncodes is = some cs)
    {env : Env} (hag : AgreesOnValues u env) :
    ∃ env', runInstrs env cs = some env' ∧ AgreesOnValues w env' := by
  induction htr generalizing cs env with
  | nil =>
    simp only [instrEncodes, Option.some.injEq] at henc
    subst henc
    exact ⟨env, rfl, hag⟩
  | cons hstep _htr ih =>
    rcases instrEncodes_cons.mp henc with ⟨c, cs', henc1, henc2, rfl⟩
    obtain ⟨env₁, hstep₂, hag₁⟩ := step_transport hstep hag
    have hcl : step env c = some env₁ := step_simulate hstep₂ henc1
    obtain ⟨env₂, hrun, hag₂⟩ := ih henc2 hag₁
    exact ⟨env₂, by simp [runInstrs, hcl, hrun], hag₂⟩

/-! ## Reading the edge: one argument per parameter -/

/-- The register an edge into `target` passes for the merged value `d`, coming
from `pred` — the `src` of the phi that names `pred` for `d`. `none` when the
edge has no phi for `d`, which is the case the encoder refuses. -/
def edgeArg? (ps : List Phi) (pred : Morph.MIR.BlockId) (d : ValId) : Option Reg :=
  (ps.find? (fun p => p.dst == d && p.pred == pred)).map (·.src)

/-- **`argsFor` puts the selected `src` at the parameter's position.** This is
the lemma that makes the encoder's `find?` usable by the binding lemma: given a
parameter `d` at index `i` of the parameter list, the argument at index `i` is
exactly `edgeArg?` for `d`, so `paramsOf` and `argsFor` are aligned by
construction rather than by coincidence. -/
theorem argsFor_get? (ps : List Phi) (pred : Morph.MIR.BlockId) :
    ∀ {ds : List ValId} {args : List Reg}, argsFor ps pred ds = some args →
      ∀ (i : Nat) (d : ValId), ds[i]? = some d →
        ∃ str : Reg, args[i]? = some str ∧ edgeArg? ps pred d = some str
  | [], args, h, i, d, hd => by
    simp only [List.getElem?_nil, reduceCtorEq] at hd
  | d₀ :: ds', args, h, i, d, hd => by
    -- Expose the encoder's two matches, then invert them.
    simp only [argsFor] at h
    split at h
    · exact absurd h (by simp)
    · rename_i p hp
      split at h
      · exact absurd h (by simp)
      · rename_i rest _hr
        simp only [Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hd
          subst hd
          exact ⟨p.src, by simp, by simp [edgeArg?, hp]⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hd ⊢
          exact argsFor_get? ps pred _hr j d hd

/-- Invert one step of `evalArgs`: a successful list evaluation exposes the value
of the head register and the evaluation of the tail. -/
theorem evalArgs_cons {env : Env} {r : Reg} {rs : List Reg} {vs : List Value}
    (h : evalArgs env (r :: rs) = some vs) :
    ∃ v vs', env r = some v ∧ evalArgs env rs = some vs' ∧ vs = v :: vs' := by
  simp only [evalArgs] at h
  cases hr : env r with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some v =>
    cases hrest : evalArgs env rs with
    | none => rw [hr, hrest] at h; exact absurd h (by simp)
    | some vs' =>
      rw [hr, hrest] at h
      exact ⟨v, vs', rfl, rfl, by cases h; rfl⟩

/-- **`evalArgs` reads one value per argument register, positionally.** The
value at index `i` is what the argument register holds; `evalArgs`'s `do`-chain
only looks values up, so this is exact and needs no distinctness. -/
theorem evalArgs_get? {env : Env} :
    ∀ {rs : List Reg} {vs : List Value}, evalArgs env rs = some vs →
      ∀ (i : Nat) (r : Reg) (v : Value), rs[i]? = some r → vs[i]? = some v →
        env r = some v
  | [], vs, h, i, r, _v, hr, _hv => by
    simp only [List.getElem?_nil, reduceCtorEq] at hr
  | r₀ :: rs, vs, h, i, r, v, hr, hv => by
    obtain ⟨a, vs', ha, hrest, hvs⟩ := evalArgs_cons h
    subst hvs
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hv
      subst hr
      subst hv
      exact ha
    | succ j =>
      simp only [List.getElem?_cons_succ] at hr hv
      exact evalArgs_get? hrest j r v hr hv

/-- `evalArgs` neither drops nor duplicates a value: it produces one per
argument register, so its result has the argument list's length. -/
theorem evalArgs_length {env : Env} :
    ∀ {rs : List Reg} {vs : List Value}, evalArgs env rs = some vs → vs.length = rs.length
  | [], vs, h => by
    simp only [evalArgs, Option.some.injEq] at h
    subst h
    rfl
  | r :: rs, vs, h => by
    obtain ⟨a, vs', _ha, hrest, hvs⟩ := evalArgs_cons h
    subst hvs
    simp only [List.length_cons]
    rw [evalArgs_length hrest]

/-- Every argument position within bounds has a value in the evaluated list. -/
theorem evalArgs_get?_isSome {env : Env} :
    ∀ {rs : List Reg} {vs : List Value}, evalArgs env rs = some vs →
      ∀ (i : Nat), i < rs.length → ∃ v : Value, vs[i]? = some v
  | [], vs, h, i, hi => by simp at hi
  | r :: rs, vs, h, i, hi => by
    obtain ⟨a, vs', _ha, hrest, hvs⟩ := evalArgs_cons h
    subst hvs
    cases i with
    | zero => exact ⟨a, rfl⟩
    | succ j =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
      obtain ⟨v, hv⟩ := evalArgs_get?_isSome hrest j hi
      exact ⟨v, hv⟩

/-! ## Binding, positionally -/

/-- **The binding lemma in index form.** On a duplicate-free parameter list, the
value bound to the parameter at index `i` is the argument at index `i`. This is
`bindParams_nodup_mem` restated so that it composes with `argsFor_get?` and
`evalArgs_get?`, which are also index-based: the three together say the join's
parameter `d` holds the value of `edgeArg?` for `d` in the incoming environment.

Distinctness is load-bearing here in a visible way: `bindParams` binds the tail
first and the head last, so the head's write shadows anything the tail wrote —
exactly right for distinct parameters, and wrong for a repeated one. -/
theorem bindParams_get? {env env' : Env} :
    ∀ {ps : List Reg} {vs : List Value}, ps.Nodup → bindParams env ps vs = some env' →
      ∀ (i : Nat) (r : Reg) (v : Value), ps[i]? = some r → vs[i]? = some v →
        env' r = some v
  | [], vs, _hnd, h, i, r, _v, hr, _hv => by
    simp only [List.getElem?_nil, reduceCtorEq] at hr
  | r₀ :: ps', [], hnd, h, i, r, _v, hr, _hv => by
    simp [bindParams] at h
  | r₀ :: ps', v₀ :: vs', hnd, h, i, r, v, hr, hv => by
    rw [List.nodup_cons] at hnd
    obtain ⟨hnotin, hnd'⟩ := hnd
    simp only [bindParams] at h
    split at h
    · exact absurd h (by simp)
    · rename_i e he
      have henv : e.set r₀ v₀ = env' := Option.some.inj h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hv
        subst hr
        subst hv
        rw [← henv, Env.set_same]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hr hv
        have hne : r ≠ r₀ := by
          intro hrr
          subst hrr
          exact hnotin (List.mem_of_getElem? hr)
        rw [← henv, Env.set_other _ _ hne]
        exact bindParams_get? hnd' he j r v hr hv

/-! ## The join parameter holds the phi's edge value

The three positional lemmas compose into the statement the phi phase needs: for
a parameter at index `i` of the join, the bound environment gives it the value
that the phi selected for that parameter and edge would have written — the value
of `edgeArg?` in the *incoming* environment, read before any binding happens.

That "before any binding" is not an accident of the proof: `evalArgs` runs on
the environment the block was entered with, while `bindParams` writes the
parameters afterwards. So the correspondence holds even if a parameter shadows a
register the edge reads, which is the shadowing `bindParams` is designed for.
-/

/-- **The join's parameter reads the edge's value.** For every parameter of the
join (duplicate-free by `paramsOf_nodup`), the environment the block runs in
holds the value of the phi that the encoder selected for that parameter and
incoming edge, evaluated in the *pre-binding* environment. -/
theorem params_bound_get? (ps : List Phi) (pred : Morph.MIR.BlockId)
    {args : List Reg} {vs : List Value} {env env' : Env}
    (hargs : argsFor ps pred (paramsOf ps) = some args)
    (heval : evalArgs env args = some vs)
    (hbind : bindParams env (paramsOf ps) vs = some env') :
    ∀ (i : Nat) (d : ValId), (paramsOf ps)[i]? = some d →
      ∃ str : Reg, edgeArg? ps pred d = some str ∧ env' d = env str := by
  intro i d hd
  obtain ⟨str, hstr, harg⟩ := argsFor_get? ps pred hargs i d hd
  have hi : i < args.length := (List.getElem?_eq_some_iff.mp hstr).1
  have hlen : args.length = (paramsOf ps).length := argsFor_length ps pred (paramsOf ps) args hargs
  have hvlen : vs.length = args.length := evalArgs_length heval
  obtain ⟨v, hv⟩ : ∃ v : Value, vs[i]? = some v :=
    evalArgs_get?_isSome heval i (by omega)
  have hval : env str = some v := evalArgs_get? heval i str v hstr hv
  have hbound : env' d = some v :=
    bindParams_get? (paramsOf_nodup ps) hbind i d v hd hv
  exact ⟨str, harg, by rw [hbound, hval]⟩

/-! ## The MIR side of the phi phase

`execInstrsFullFrom` walks a block's instructions and fires a `phi` when the
incoming edge matches it. The encoder instead reads the leading phis *as a list*
(`splitPhis`) and turns them into parameters. To compare the two, this section
gives the walk a canonical form over that list:

- `splitPhis_reconstruct` — the block's instructions really are its leading phis
  followed by the rest, so nothing is lost by looking at the pair;
- `phiFoldEnv` — the phi phase as a fold, which is the shape the parameter
  binding has;
- `execInstrsFullFrom_phiList` — the walk over the re-emitted phis is that fold;
- `execInstrsFullFrom_split` — the walk over any block is the fold over its
  leading phis followed by the walk over the rest, which is what lets the phi
  phase be separated from the straight-line body.

The fold keeps MIR's sequential reading: each phi's `src` is looked up in the
environment the *previous* phi produced. That is deliberate — the encoder reads
its arguments only once, from the entry environment, so the correspondence
between them needs the hypothesis that no phi reads a register another phi
writes. Stating the fold sequentially makes that hypothesis a factual
requirement rather than something baked into a definition.
-/

/-- The instruction a `Phi` was read from. -/
def toInstr (q : Phi) : Morph.MIR.Instr := .phi q.dst q.pred q.src

/-- `phiInfo` is a projection, so re-emitting its result gives the instruction
back. -/
theorem phiInfo_toInstr {i : Morph.MIR.Instr} {q : Phi} (h : phiInfo i = some q) :
    i = toInstr q := by
  cases i <;> simp only [phiInfo] at h <;> (try (cases h; rfl)) <;> simp_all

/-- **Nothing is lost by splitting.** A block is its leading phis followed by the
rest of its instructions. -/
theorem splitPhis_reconstruct (is : List Morph.MIR.Instr) :
    is = (splitPhis is).1.map toInstr ++ (splitPhis is).2 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    cases hi : phiInfo i with
    | none => simp [splitPhis, hi]
    | some q =>
      simp only [splitPhis, hi, List.map_cons, List.cons_append]
      rw [← ih, phiInfo_toInstr hi]

/-- The phi phase as a fold: a phi whose predecessor matches the incoming edge
writes its destination in the running environment; every other phi is skipped.
`none` when a matching phi reads an unbound register, which is MIR's own
condition for the step to fail. -/
def phiFoldEnv (p : Morph.MIR.BlockId) (env : Morph.MIR.Env) : List Phi → Option Morph.MIR.Env
  | [] => some env
  | q :: qs =>
    if q.pred = p then
      match env q.src with
      | none => none
      | some v => phiFoldEnv p (env.update q.dst v) qs
    else phiFoldEnv p env qs

/-- **The walk over the phis is the fold.** Arriving from `p`, executing the
re-emitted phi list leaves the store untouched and produces exactly
`phiFoldEnv`'s environment. -/
theorem execInstrsFullFrom_phiList (p : Morph.MIR.BlockId) (fenv : Morph.MIR.FullEnv) :
    ∀ phis : List Phi,
      Morph.MIR.execInstrsFullFrom (some p) fenv (phis.map toInstr) =
        (match phiFoldEnv p fenv.env phis with
         | none => none
         | some env' => some ⟨env', fenv.store⟩)
  | [] => by
    simp only [List.map_nil, phiFoldEnv, Morph.MIR.execInstrsFullFrom_nil]
  | q :: qs => by
    simp only [List.map_cons, toInstr, phiFoldEnv]
    by_cases hp : q.pred = p
    · rw [if_pos hp]
      rw [Morph.MIR.execInstrsFullFrom_phi_hit q.dst q.pred p q.src (qs.map toInstr) fenv hp]
      cases hsrc : fenv.env q.src with
      | none => simp
      | some v =>
        exact execInstrsFullFrom_phiList p ⟨fenv.env.update q.dst v, fenv.store⟩ qs
    · rw [if_neg hp]
      rw [Morph.MIR.execInstrsFullFrom_phi_miss q.dst q.pred p q.src (qs.map toInstr) fenv hp]
      exact execInstrsFullFrom_phiList p fenv qs

/-- **The walk splits at the leading phis.** Executing a block arriving from `p`
is the same as running the phi fold first and then walking the rest of the block
in the folded environment. This is the canonical form the simulation composes
with: the fold is where the parameters come from, the walk over the rest is where
`trace_runInstrs_agree` applies. -/
theorem execInstrsFullFrom_split (p : Morph.MIR.BlockId) :
    ∀ (fenv : Morph.MIR.FullEnv) (is : List Morph.MIR.Instr),
      Morph.MIR.execInstrsFullFrom (some p) fenv is =
        (match phiFoldEnv p fenv.env (splitPhis is).1 with
         | none => none
         | some env' =>
           Morph.MIR.execInstrsFullFrom (some p) ⟨env', fenv.store⟩ (splitPhis is).2)
  | fenv, is => by
    cases is with
    | nil => simp [splitPhis, phiFoldEnv, Morph.MIR.execInstrsFullFrom]
    | cons i is' =>
      cases hi : phiInfo i with
      | none =>
        simp only [splitPhis, hi, phiFoldEnv]
      | some q =>
        simp only [splitPhis, hi]
        rw [phiInfo_toInstr hi]
        simp only [toInstr]
        rw [phiFoldEnv]
        by_cases hp : q.pred = p
        · rw [if_pos hp]
          rw [Morph.MIR.execInstrsFullFrom_phi_hit q.dst q.pred p q.src is' fenv hp]
          cases hsrc : fenv.env q.src with
          | none => simp
          | some v =>
            exact execInstrsFullFrom_split p ⟨fenv.env.update q.dst v, fenv.store⟩ is'
        · rw [if_neg hp]
          rw [Morph.MIR.execInstrsFullFrom_phi_miss q.dst q.pred p q.src is' fenv hp]
          exact execInstrsFullFrom_split p fenv is'

/-! ## The fold reproduced by the edge's binding

`params_bound_get?` says what the join's parameters hold in the block model, and
`phiFoldEnv` says what MIR's phi write leaves behind. They are two different
notions of "the merge": one binds a parameter list once, from the edge's
arguments; the other fires phis one at a time in list order. This section proves
they agree, which is what makes the encoding of a merge correct rather than
merely well-typed.

Two hypotheses, and neither is decoration:

- **`hsep`**: no matching phi reads a register another matching phi writes. The
  block model reads its arguments once, from the environment the block was
  entered with; the fold reads each `src` after the previous phi already wrote.
  Without this the two would be comparing different values, which is why the
  encoder's scope keeps arm temporaries out of merge destinations.
- **`huniq`**: two matching phis that write the same destination write the same
  value. Weaker than "one phi per `(dst, pred)`", which is what `noDupPairs`
  checks, and it is all the value statement needs: a duplicate write of the same
  value is invisible.

The conclusion is one equality per destination, stated against a single shared
environment hypothesis (`hreg`) rather than an `AgreesOnValues`: at a block
boundary the model's environment *is* MIR's register file for the registers the
edge reads, and the merge only needs that on `src`s.
-/

/-- `MIR.Env.update` writes the register it names. -/
theorem update_self (m : Morph.MIR.Env) (d : ValId) (v : Value) :
    m.update d v d = some v := by
  rw [update_eq_set]
  simp [Env.set]

/-- `MIR.Env.update` leaves every other register alone. -/
theorem update_other {m : Morph.MIR.Env} {d x : ValId} {v : Value} (h : x ≠ d) :
    m.update d v x = m x := by
  rw [update_eq_set]
  simp [Env.set, h]

/-- **The fold leaves unwritten registers alone.** If no phi matching the
incoming edge has destination `r`, the fold returns `r`'s entry value: it never
writes it, and it cannot read it to fail either. -/
theorem phiFoldEnv_not_dst (pred : Morph.MIR.BlockId) :
    ∀ (ps : List Phi) (m m' : Morph.MIR.Env), phiFoldEnv pred m ps = some m' →
      ∀ r : ValId, (∀ q ∈ ps, q.pred = pred → q.dst ≠ r) → m' r = m r
  | [], m, m', h, r, _ => by
    simp only [phiFoldEnv, Option.some.injEq] at h
    subst h
    rfl
  | hd :: tl, m, m', h, r, hr => by
    simp only [phiFoldEnv] at h
    by_cases hp : hd.pred = pred
    · rw [if_pos hp] at h
      split at h
      · exact absurd h (by simp)
      · rename_i v hsrc
        rw [phiFoldEnv_not_dst pred tl (m.update hd.dst v) m' h r
          (fun q' hq' hp' => hr q' (List.mem_cons_of_mem _ hq') hp')]
        exact update_other (Ne.symm (hr hd List.mem_cons_self hp))
    · rw [if_neg hp] at h
      exact phiFoldEnv_not_dst pred tl m m' h r
        (fun q' hq' hp' => hr q' (List.mem_cons_of_mem _ hq') hp')

/-- **The fold leaves each destination holding its own `src`'s entry value.**
This is the phi phase as an equation: for every phi that fires, the destination
ends up holding the value its `src` held on entry, not the value some *other*
firing phi wrote there first. `huniq` handles a repeated destination and `hsep`
handles a destination another phi reads. -/
theorem phiFoldEnv_get (pred : Morph.MIR.BlockId) :
    ∀ (ps : List Phi) (m m' : Morph.MIR.Env),
      (∀ q ∈ ps, q.pred = pred → ∀ q' ∈ ps, q'.pred = pred →
        q.dst = q'.dst → q.src = q'.src) →
      (∀ q ∈ ps, q.pred = pred → ∀ q' ∈ ps, q'.pred = pred → q.src ≠ q'.dst) →
      phiFoldEnv pred m ps = some m' →
      ∀ q ∈ ps, q.pred = pred → m' q.dst = m q.src
  | [], m, m', _, _, h, q, hq, _ => by
    simp only [List.not_mem_nil] at hq
  | hd :: tl, m, m', huniq, hsep, h, p, hmem, hpred => by
    have huniq' : ∀ q ∈ tl, q.pred = pred → ∀ q' ∈ tl, q'.pred = pred →
        q.dst = q'.dst → q.src = q'.src :=
      fun a ha ha' b hb hb' hd' =>
        huniq a (List.mem_cons_of_mem _ ha) ha' b (List.mem_cons_of_mem _ hb) hb' hd'
    have hsep' : ∀ q ∈ tl, q.pred = pred → ∀ q' ∈ tl, q'.pred = pred → q.src ≠ q'.dst :=
      fun a ha ha' b hb hb' =>
        hsep a (List.mem_cons_of_mem _ ha) ha' b (List.mem_cons_of_mem _ hb) hb'
    simp only [phiFoldEnv] at h
    by_cases hp₀ : hd.pred = pred
    · rw [if_pos hp₀] at h
      split at h
      · exact absurd h (by simp)
      · rename_i v hsrc
        rcases List.mem_cons.mp hmem with hpeq | hlt
        · -- The head fires: its destination is either rewritten by a later phi
          -- holding the same value, or never written again.
          subst hpeq
          by_cases hex : ∃ q' ∈ tl, q'.pred = pred ∧ q'.dst = p.dst
          · obtain ⟨q', hq'mem, hq'pred, hq'dst⟩ := hex
            have ihq' := phiFoldEnv_get pred tl (m.update p.dst v) m'
              huniq' hsep' h q' hq'mem hq'pred
            have hsame : q'.src = p.src :=
              huniq q' (List.mem_cons_of_mem _ hq'mem) hq'pred p List.mem_cons_self hp₀
                (by rw [hq'dst])
            have hne : q'.src ≠ p.dst :=
              hsep q' (List.mem_cons_of_mem _ hq'mem) hq'pred p List.mem_cons_self hp₀
            rw [← hq'dst, ihq', hsame]
            exact update_other (hsame ▸ hne)
          · have hnot : ∀ q' ∈ tl, q'.pred = pred → q'.dst ≠ p.dst :=
              fun q' hm hp hd' => hex ⟨q', hm, hp, hd'⟩
            rw [phiFoldEnv_not_dst pred tl (m.update p.dst v) m' h p.dst hnot,
              update_self, hsrc]
        · -- Any other phi: the head's write is not at its destination.
          rw [phiFoldEnv_get pred tl (m.update hd.dst v) m' huniq' hsep' h p hlt hpred,
            update_other (hsep p (List.mem_cons_of_mem _ hlt) hpred hd List.mem_cons_self hp₀)]
    · rw [if_neg hp₀] at h
      rcases List.mem_cons.mp hmem with hpeq | hlt
      · subst hpeq
        exact absurd hpred hp₀
      · exact phiFoldEnv_get pred tl m m' huniq' hsep' h p hlt hpred

/-- **The phi the encoder selected.** `edgeArg?` is a `find?` on `(dst, pred)`, so
a successful lookup names a phi in the list with that destination, that
predecessor, and that `src`. This is the link between the encoder's choice and
the fold's behaviour. -/
theorem edgeArg?_find (ps : List Phi) {pred : Morph.MIR.BlockId} {d : ValId} {str : Reg}
    (h : edgeArg? ps pred d = some str) :
    ∃ q ∈ ps, q.dst = d ∧ q.pred = pred ∧ q.src = str := by
  unfold edgeArg? at h
  cases hf : ps.find? (fun p => p.dst == d && p.pred == pred) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some q =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have htrue : (q.dst == d && q.pred == pred) = true := by
      have := List.find?_some hf
      simpa using this
    simp only [Bool.and_eq_true, beq_iff_eq] at htrue
    exact ⟨q, List.mem_of_find?_eq_some hf, htrue.1, htrue.2, h⟩

/-- **The join's parameter holds exactly what the fold writes.** The two sides of
the merge meet here: the block model's parameter `d` carries the value of the
argument the encoder chose for `d` on this edge, and MIR's fold leaves `d`
holding that same `src`'s entry value. Since `hreg` identifies the two entry
environments on `src`s, the values are equal — one equality per merged register,
which is what the block simulation consumes. -/
theorem params_hold_fold (ps : List Phi) (pred : Morph.MIR.BlockId)
    {args : List Reg} {vs : List Value} {env env' : Env} {m m' : Morph.MIR.Env}
    (hargs : argsFor ps pred (paramsOf ps) = some args)
    (heval : evalArgs env args = some vs)
    (hbind : bindParams env (paramsOf ps) vs = some env')
    (huniq : ∀ q ∈ ps, q.pred = pred → ∀ q' ∈ ps, q'.pred = pred →
      q.dst = q'.dst → q.src = q'.src)
    (hsep : ∀ q ∈ ps, q.pred = pred → ∀ q' ∈ ps, q'.pred = pred → q.src ≠ q'.dst)
    (hfold : phiFoldEnv pred m ps = some m')
    (hreg : ∀ q ∈ ps, q.pred = pred → env q.src = m q.src) :
    ∀ d, d ∈ paramsOf ps → env' d = m' d := by
  intro d hd
  obtain ⟨i, hdi⟩ := List.mem_iff_getElem?.mp hd
  obtain ⟨str, hstr, harg⟩ := params_bound_get? ps pred hargs heval hbind i d hdi
  obtain ⟨q, hq, hdst, hqpred, hsrc⟩ := edgeArg?_find ps hstr
  calc env' d = env str := harg
    _ = m str := hsrc ▸ hreg q hq hqpred
    _ = m' q.dst := hsrc ▸ (phiFoldEnv_get pred ps m m' huniq hsep hfold q hq hqpred).symm
    _ = m' d := by rw [hdst]

/-- **The merge holds on every list the encoder emits.** `encodeBlock` refuses a
join unless both `noDupPairs` and `noPhiChain` succeed, and those two checks
are exactly the fold's hypotheses — so the parameter/agreement conclusion needs
no extra assumptions on encoder output. This is the form the block simulation
consumes. -/
theorem params_hold_fold_of_checks (ps : List Phi) (pred : Morph.MIR.BlockId)
    (hnd : noDupPairs ps = true) (hnc : noPhiChain ps = true)
    {args : List Reg} {vs : List Value} {env env' : Env} {m m' : Morph.MIR.Env}
    (hargs : argsFor ps pred (paramsOf ps) = some args)
    (heval : evalArgs env args = some vs)
    (hbind : bindParams env (paramsOf ps) vs = some env')
    (hfold : phiFoldEnv pred m ps = some m')
    (hreg : ∀ q ∈ ps, q.pred = pred → env q.src = m q.src) :
    ∀ d, d ∈ paramsOf ps → env' d = m' d :=
  params_hold_fold ps pred hargs heval hbind
    (noDupPairs_huniq ps hnd pred) (noPhiChain_hsep ps hnc pred) hfold hreg

/-! ## The terminator and the agreement across an edge

The phi phase ends with two environments — MIR's folded `m'` and the block
model's bound `env'` — that agree on the join's parameters (`params_hold_fold`)
and are untouched elsewhere (`phiFoldEnv_not_dst`, `bindParams_not_mem`). This
section turns that into the full agreement the next block's body needs, and
pins what each encoded terminator shape is:

- `encodeTerm_return/goto/branch` invert `encodeTerm`, so the fuel induction
  can case on the MIR terminator and know the CLIF terminator's shape.
- `runTerm_return_agree` says a `return` reads the same value on both sides,
  and `boolOf_asBool_agree` says a `branch` takes the same edge — both through
  the value agreement the body phase maintains.
- `agrees_after_edge` propagates the agreement across the join: on parameters
  by equality with the fold, off parameters by both sides being untouched.
  This is the lemma the fuel induction consumes at every `goto`/`branch`.
- `hreg_of_agree` discharges the pointwise-equality hypothesis from agreement
  for non-unit sources, which is what lowered code carries (arm values are
  integers, never the unit prologue register).
-/

/-- `encodeTerm` on a `return` block. -/
theorem encodeTerm_return {f : Morph.MIR.Func} {b : Morph.MIR.Block} {src : ValId}
    (h : b.terminator = .return_ src) : encodeTerm f b = some (.ret src) := by
  simp [encodeTerm, h]

/-- `encodeTerm` on a `goto` block, with the edge's arguments. -/
theorem encodeTerm_goto {f : Morph.MIR.Func} {b : Morph.MIR.Block}
    {t : Morph.MIR.BlockId} {args : List Reg}
    (h : b.terminator = .goto t)
    (he : edgeArgs f t b.id = some args) :
    encodeTerm f b = some (.jump t args) := by
  simp [encodeTerm, h, he]

/-- `encodeTerm` on a `branch` block, with both edges' arguments. -/
theorem encodeTerm_branch {f : Morph.MIR.Func} {b : Morph.MIR.Block}
    {c : ValId} {tt ff : Morph.MIR.BlockId} {argsT argsF : List Reg}
    (h : b.terminator = .branch c tt ff)
    (heT : edgeArgs f tt b.id = some argsT)
    (heF : edgeArgs f ff b.id = some argsF) :
    encodeTerm f b = some (.brif c tt argsT ff argsF) := by
  simp [encodeTerm, h, heT, heF]

/-- A `return` reads the same value on both sides. -/
theorem runTerm_return_agree {m : Morph.MIR.Env} {env : Env}
    (hag : AgreesOnValues m env)
    {v : ValId} {w : Value} (h : m v = some w) (hne : w ≠ .unit) :
    runTerm env (.ret v) = some (.ret w) := by
  have he : env v = some w := hag v w h hne
  simp only [runTerm, he, Option.map_some]

/-- A boolean the MIR block branched on reads the same in an agreeing
environment, so both sides take the same edge. -/
theorem boolOf_asBool_agree {m : Morph.MIR.Env} {env : Env}
    (hag : AgreesOnValues m env)
    {c : ValId} {b : Bool} (h : m c = some (.bool b)) :
    (env c >>= asBool) = some b := by
  rw [hag c (.bool b) h (by simp)]
  rfl

/-- A non-unit `src` read is an equality: agreement reproduces the exact option,
which discharges the pointwise hypothesis the merge lemmas take. -/
theorem hreg_of_agree {m : Morph.MIR.Env} {env : Env}
    (hag : AgreesOnValues m env)
    {r : ValId} {v : Value} (h : m r = some v) (hne : v ≠ .unit) :
    env r = m r := by
  rw [hag r v h hne, h]

/-- **Agreement propagates across a join.** On parameters the two sides are
equal (`params_hold_fold`); off parameters neither side moved
(`phiFoldEnv_not_dst`, `bindParams_not_mem`), so the entry agreement carries.
The fuel induction applies this at every `goto`/`branch` edge. -/
theorem agrees_after_edge (ps : List Phi) (pred : Morph.MIR.BlockId)
    {args : List Reg} {vs : List Value} {env env' : Env} {m m' : Morph.MIR.Env}
    (hargs : argsFor ps pred (paramsOf ps) = some args)
    (heval : evalArgs env args = some vs)
    (hbind : bindParams env (paramsOf ps) vs = some env')
    (huniq : ∀ q ∈ ps, q.pred = pred → ∀ q' ∈ ps, q'.pred = pred →
      q.dst = q'.dst → q.src = q'.src)
    (hsep : ∀ q ∈ ps, q.pred = pred → ∀ q' ∈ ps, q'.pred = pred → q.src ≠ q'.dst)
    (hfold : phiFoldEnv pred m ps = some m')
    (hreg : ∀ q ∈ ps, q.pred = pred → env q.src = m q.src)
    (hag : AgreesOnValues m env) :
    AgreesOnValues m' env' := by
  intro x v hxv hne
  by_cases hx : x ∈ paramsOf ps
  · have heq := params_hold_fold ps pred hargs heval hbind huniq hsep hfold hreg x hx
    rw [heq]
    exact hxv
  · have hdst : ∀ q ∈ ps, q.pred = pred → q.dst ≠ x := by
      intro q hq hp hcon
      exact hx ((paramsOf_mem ps x).mpr ⟨q, hq, hcon⟩)
    have hm : m' x = m x := phiFoldEnv_not_dst pred ps m m' hfold x hdst
    have he : env' x = env x := bindParams_not_mem hbind hx
    rw [hm] at hxv
    rw [he]
    exact hag x v hxv hne

/-- **Agreement propagates across every join the encoder emits.** The checks
are exactly the fold's hypotheses, as in `params_hold_fold_of_checks` — so the
fuel induction needs no extra assumptions on encoder output. -/
theorem agrees_after_edge_of_checks (ps : List Phi) (pred : Morph.MIR.BlockId)
    (hnd : noDupPairs ps = true) (hnc : noPhiChain ps = true)
    {args : List Reg} {vs : List Value} {env env' : Env} {m m' : Morph.MIR.Env}
    (hargs : argsFor ps pred (paramsOf ps) = some args)
    (heval : evalArgs env args = some vs)
    (hbind : bindParams env (paramsOf ps) vs = some env')
    (hfold : phiFoldEnv pred m ps = some m')
    (hreg : ∀ q ∈ ps, q.pred = pred → env q.src = m q.src)
    (hag : AgreesOnValues m env) :
    AgreesOnValues m' env' :=
  agrees_after_edge ps pred hargs heval hbind
    (noDupPairs_huniq ps hnd pred) (noPhiChain_hsep ps hnc pred) hfold hreg hag

/-! ## The body bridge: the edge parameter is inert off phis

The phi phase (`execInstrsFullFrom_split`) separates a block's walk into the
fold over its leading phis and the walk over the rest. What the rest *is* — a
straight-line body the encoder accepted — is what makes the second half
reusable: `instrEncode` refuses `.phi`, so an encoded body has no phi at all,
and on a phi-free list the edge parameter changes nothing. The certificate
(a fold result plus a `Trace` over the body) therefore determines the MIR walk
on both entry shapes, which is the MIR half of the single-block step.
-/

/-- An encoded body has no phi: `instrEncode` refuses `.phi`. -/
theorem instrEncodes_noPhi {is : List Morph.MIR.Instr} {cs : List Instr}
    (h : instrEncodes is = some cs) :
    ∀ i ∈ is, ∀ dst pred src, i ≠ .phi dst pred src := by
  induction is generalizing cs with
  | nil => simp
  | cons j js ih =>
    intro i hi dst pred src hphi
    rcases instrEncodes_cons.mp h with ⟨c, cs', henc, henc', rfl⟩
    rcases List.mem_cons.mp hi with rfl | hmem
    · subst hphi
      simp [instrEncode] at henc
    · exact ih henc' i hmem dst pred src hphi

/-- Off phis the edge parameter is inert. -/
theorem execInstrsFullFrom_of_noPhi (prev : Option Morph.MIR.BlockId)
    (fenv : Morph.MIR.FullEnv) :
    ∀ (is : List Morph.MIR.Instr),
      (∀ i ∈ is, ∀ dst pred src, i ≠ .phi dst pred src) →
      Morph.MIR.execInstrsFullFrom prev fenv is = Morph.MIR.execInstrsFull fenv is
  | [], _ => by rfl
  | j :: js, h => by
    by_cases hj : ∃ dst pred src, j = .phi dst pred src
    · obtain ⟨dst, pred, src, rfl⟩ := hj
      exact absurd rfl (h _ List.mem_cons_self dst pred src)
    · simp only [not_exists] at hj
      have hrest : ∀ i ∈ js, ∀ dst pred src, i ≠ .phi dst pred src :=
        fun i hi d p s => h i (List.mem_cons_of_mem _ hi) d p s
      rw [Morph.MIR.execInstrsFullFrom_nonphi prev fenv hj]
      cases he : Morph.MIR.evalInstrFull fenv j with
      | none => simp [Morph.MIR.execInstrsFull, he]
      | some fenv' =>
        simp only [Morph.MIR.execInstrsFull, he]
        exact execInstrsFullFrom_of_noPhi prev fenv' js hrest

/-- Leading phis re-emitted from `Phi` are skipped at the entry block, which has
no incoming edge for them to match. -/
theorem execInstrsFullFrom_none_phis (fenv : Morph.MIR.FullEnv) :
    ∀ (phis : List Phi) (rest : List Morph.MIR.Instr),
      Morph.MIR.execInstrsFullFrom none fenv (phis.map toInstr ++ rest) =
        Morph.MIR.execInstrsFullFrom none fenv rest
  | [], rest => by simp
  | q :: qs, rest => by
    simp only [List.map_cons, List.cons_append, toInstr]
    rw [Morph.MIR.execInstrsFullFrom_phi_none]
    exact execInstrsFullFrom_none_phis fenv qs rest

/-- **The certificate determines the MIR walk.** A fold result plus a `Trace`
over the body fix the block's `execInstrsFullFrom` outcome on both entry
shapes: at the entry the leading phis are dead and the body runs from the entry
environment; on an edge the fold runs first and the body from the folded
environment. The store is threaded untouched, as `Trace` promises. -/
theorem block_exec_of_cert (prev : Option Morph.MIR.BlockId)
    (fenv : Morph.MIR.FullEnv)
    (is : List Morph.MIR.Instr) {mMid m' : Morph.MIR.Env}
    (hfold : match prev with
      | none => mMid = fenv.env
      | some p => phiFoldEnv p fenv.env (splitPhis is).1 = some mMid)
    (htr : Trace (splitPhis is).2 mMid m')
    (hnoPhi : ∀ i ∈ (splitPhis is).2, ∀ dst pred src, i ≠ .phi dst pred src) :
    Morph.MIR.execInstrsFullFrom prev fenv is = some ⟨m', fenv.store⟩ := by
  cases prev with
  | none =>
    subst hfold
    rw [splitPhis_reconstruct is, execInstrsFullFrom_none_phis fenv _ _,
      execInstrsFullFrom_of_noPhi none fenv _ hnoPhi]
    exact trace_execInstrsFull htr fenv.store
  | some p =>
    have hfold' : phiFoldEnv p fenv.env (splitPhis is).1 = some mMid := hfold
    simp only [execInstrsFullFrom_split p fenv is, hfold']
    rw [execInstrsFullFrom_of_noPhi (some p) ⟨mMid, fenv.store⟩ _ hnoPhi]
    exact trace_execInstrsFull htr fenv.store

/-! ## Inverting a successful block encoding

The fuel induction cases on the MIR terminator and needs the encoded block's
pieces — its parameter list, its encoded body, its terminator — as equations.
`encodeBlock`'s two gates become the two `= true` hypotheses every later lemma
takes, which is why the `_of_checks` forms compose without further casing.
-/

/-- A successful `encodeBlock` exposes its pieces. -/
theorem encodeBlock_inv {f : Morph.MIR.Func} {b : Morph.MIR.Block} {cb : Block}
    (h : encodeBlock f b = some cb) :
    ∃ (cs : List Instr) (t : Term),
      noDupPairs (splitPhis b.instrs).1 = true ∧
      noPhiChain (splitPhis b.instrs).1 = true ∧
      instrEncodes (splitPhis b.instrs).2 = some cs ∧
      encodeTerm f b = some t ∧
      cb = ⟨b.id, paramsOf (splitPhis b.instrs).1, cs, t⟩ := by
  cases hnd : noDupPairs (splitPhis b.instrs).1 with
  | false =>
    have hnone : encodeBlock f b = none := by
      unfold encodeBlock
      simp [hnd]
    rw [hnone] at h
    exact absurd h (by simp)
  | true =>
    cases hnc : noPhiChain (splitPhis b.instrs).1 with
    | false =>
      have hnone : encodeBlock f b = none := by
        unfold encodeBlock
        simp [hnd, hnc]
      rw [hnone] at h
      exact absurd h (by simp)
    | true =>
      have hunfold : encodeBlock f b =
          (instrEncodes (splitPhis b.instrs).2).bind fun is =>
            (encodeTerm f b).bind fun t =>
              some ⟨b.id, paramsOf (splitPhis b.instrs).1, is, t⟩ := by
        unfold encodeBlock
        simp [hnd, hnc]
      rw [hunfold] at h
      cases his : instrEncodes (splitPhis b.instrs).2 with
      | none => simp [his] at h
      | some cs =>
        simp only [his, Option.bind_some] at h
        cases ht : encodeTerm f b with
        | none => simp [ht] at h
        | some t =>
          simp only [ht, Option.bind_some, Option.some.injEq] at h
          exact ⟨cs, t, rfl, rfl, rfl, rfl, h.symm⟩

end Cfg
end Morph.Clif
