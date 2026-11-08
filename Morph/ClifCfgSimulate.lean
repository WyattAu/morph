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

end Cfg
end Morph.Clif
