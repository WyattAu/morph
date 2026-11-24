/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Proofs.Call.AppUnfold
import Morph.HIRFunc
import Morph.HIRToMIRTotal
import Morph.Frontend.HIRInterp

/-!
# Call-fragment correctness (Stage C item C8c, HIR→MIR bridge)

Loop 187. The agreement the stage statements need when they are restated
for calls: a successfully lowered call program whose HIR oracle reaches a
value runs to that same value through the call-aware MIR executor. The
proof is one-directional (HIR success implies MIR agreement), like every
bridge before it, and it composes four facts:

- `evalHIR_app_lam`: a succeeding HIR application evaluated its function
  position to a `lam` and all its actuals to values;
- `filterMap_all_some`: `appBinds` kept every pair exactly when it kept
  `n` of them — the counting fact the bind correspondence needs;
- `findFunc_lowerCallProg`: first-match resolution agrees on both sides
  (both tables are first-match over the same order, the `"main"` guard
  keeps the entry out of the way, and `Nodup` keeps duplicates out);
- `LamEnv`: every `lam` the HIR environment holds comes from the function
  table — pushed and updated bindings are literals (`IsStraight`
  initializers evaluate to literals by `lower_total`), so the invariant
  survives the statement walk and every applied `lam` is a table entry.

The reversal fix (`vs.reverse` in `lowerCallStmts`) is what makes the
bind correspondence true: HIR params list innermost-first while MIR binds
positionally, so the call delivers actuals back-to-front.
-/

namespace Morph.Proofs.Call

open Morph.HIR Morph.Core Morph.HIRFunc Morph.HIRToMIR Morph.HIRToMIRCorrect
  Morph.Frontend.HIREval Morph.Frontend.HIRInterp
open Morph.MIR hiding Func

/-! ## Evaluator facts -/

/-- A succeeding HIR application evaluated its function position to a
`lam` and all its actuals to values. The repo's `bind_some_eq` idiom,
for `evalHIR` rather than the surface evaluator. -/
theorem evalHIR_app_lam {fuel : Nat} {env : HEnv} {fid : HIR.Id}
    {args : List HIR.Expr} {r : HIR.Expr}
    (h : evalHIR (fuel + 1) env (.app fid args) = some r) :
    ∃ params body argv, lookupHEnv env fid = some (.lam params body) ∧
      args.mapM (evalHIR fuel env) = some argv := by
  simp only [evalHIR] at h
  obtain ⟨fn, hfn, hrest⟩ := bind_some_eq h
  cases fn with
  | lam params body =>
      dsimp only at hrest
      by_cases har : args.length ≠ params.length
      · rw [if_pos har] at hrest
        simp at hrest
      · rw [if_neg har] at hrest
        obtain ⟨argv, hargv, _⟩ := bind_some_eq hrest
        exact ⟨params, body, argv, hfn, hargv⟩
  | var id => simp at hrest
  | lit v => simp at hrest
  | unop op e => simp at hrest
  | binop op a b => simp at hrest
  | app f a => simp at hrest
  | «let» i b => simp at hrest
  | ifThenElse c t f => simp at hrest
  | whileLoop c b => simp at hrest
  | «match» s a => simp at hrest
  | block es => simp at hrest
  | infer => simp at hrest

/-- `filterMap` never produces more than it consumes. -/
theorem filterMap_length_le {α β : Type} (f : α → Option β) :
    ∀ l : List α, (l.filterMap f).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a rest ih =>
      cases hfa : f a with
      | none =>
          simp only [List.filterMap_cons_none hfa]
          exact Nat.le_succ_of_le ih
      | some b =>
          simp only [List.filterMap_cons_some hfa, List.length_cons]
          exact Nat.succ_le_succ ih

/-- `filterMap` kept everything exactly when it kept `length` many: every
input maps to `some`. The counting fact the bind correspondence needs —
from `binds.length = n` (the arm's length test passed) to every index
pair landing in `appBinds` (via `appBinds_mem`). -/
theorem filterMap_all_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (_hlen : (l.filterMap f).length = l.length) (x : α),
      x ∈ l → ∃ y, f x = some y := by
  intro l
  induction l with
  | nil =>
      intro _hlen x hx
      simp at hx
  | cons a rest ih =>
      intro hlen x hx
      cases hfa : f a with
      | none =>
          rw [List.filterMap_cons_none hfa] at hlen
          have hle := filterMap_length_le f rest
          simp only [List.length_cons] at hlen
          omega
      | some b =>
          rw [List.filterMap_cons_some hfa] at hlen
          simp only [List.length_cons] at hlen
          have hlen' : (rest.filterMap f).length = rest.length := by omega
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨b, hfa⟩
          · exact ih hlen' x hx

/-- Every `range` index that lands in `appBinds` does so with `some` —
from the arm's length test to per-index success. -/
theorem appBinds_all_some {params : List HIR.Id} {argv : List HIR.Expr}
    {binds : HEnv}
    (hbinds : binds = appBinds params argv)
    (hblen : binds.length = params.length) (j : Nat) (hj : j < params.length) :
    ∃ p v, params[j]? = some p ∧ argv[params.length - 1 - j]? = some v := by
  have happ : appBinds params argv = (List.range params.length).filterMap
      (fun j => match params[j]?, argv[params.length - 1 - j]? with
      | some p, some v => some (p, v)
      | _, _ => none) := rfl
  have hlen : ((List.range params.length).filterMap fun j =>
      match params[j]?, argv[params.length - 1 - j]? with
      | some p, some v => some (p, v)
      | _, _ => none).length = (List.range params.length).length := by
    rw [← happ, ← hbinds, hblen, List.length_range]
  have hmem : j ∈ List.range params.length := List.mem_range.mpr hj
  obtain ⟨y, hy⟩ :=
    filterMap_all_some _ _ hlen j hmem
  have key : ∀ (a : Option HIR.Id) (b : Option HIR.Expr),
      (match a, b with
      | some p, some v => some (p, v)
      | _, _ => none) = some y →
      ∃ p v, a = some p ∧ b = some v := by
    intro a b h
    cases a with
    | none => simp at h
    | some p =>
        cases b with
        | none => simp at h
        | some v => exact ⟨p, v, rfl, rfl⟩
  exact key _ _ hy

/-! ## Execution bridges -/

/-- Emitted code is never a phi. -/
theorem IsPure_not_phi {i : Instr} (h : IsPure i) :
    ∀ dst pred src, i ≠ .phi dst pred src := by
  intro dst pred src heq
  cases h with
  | const dst v => simp at heq
  | copy dst src => simp at heq
  | unop dst op src τ => simp at heq
  | binop dst op l r τ => simp at heq

/-- On phi-free code the edge-aware walk is the plain one (`prev = none`
skips every phi, and there are none to skip). -/
theorem execInstrsFullFrom_none_of_pure (fenv : FullEnv) :
    ∀ is : List Instr, (∀ i ∈ is, IsPure i) →
      execInstrsFullFrom none fenv is = execInstrsFull fenv is := by
  intro is
  induction is generalizing fenv with
  | nil => intro _; rfl
  | cons i rest ih =>
      intro hpure
      have hi : IsPure i := hpure i (List.mem_cons_self ..)
      have hrest : ∀ j ∈ rest, IsPure j := by
        intro j hj
        exact hpure j (List.mem_cons_of_mem _ hj)
      cases i with
      | phi dst pred src =>
          exact absurd rfl (IsPure_not_phi hi dst pred src)
      | const dst v =>
          simp only [execInstrsFullFrom, execInstrsFull]
          split
          · rfl
          · rename_i fenv' _
            rw [ih fenv' hrest]
      | copy dst src =>
          simp only [execInstrsFullFrom, execInstrsFull]
          split
          · rfl
          · rename_i fenv' _
            rw [ih fenv' hrest]
      | unop dst op src τ =>
          simp only [execInstrsFullFrom, execInstrsFull]
          split
          · rfl
          · rename_i fenv' _
            rw [ih fenv' hrest]
      | binop dst op l r τ =>
          simp only [execInstrsFullFrom, execInstrsFull]
          split
          · rfl
          · rename_i fenv' _
            rw [ih fenv' hrest]
      | load dst loc cap => cases hi
      | store loc src cap => cases hi
      | alloc dst cap τ => cases hi
      | free loc => cases hi
      | call dst fn args => cases hi
      | allocClosure dst fn caps => cases hi
      | callClosure dst clo args => cases hi

/-! ## Argument agreement -/

/-- `lowerArgs` emits pure code. -/
theorem lowerArgs_isPure (ρ : List (HIR.Id × ValId)) :
    ∀ (supply : Nat) (args : List HIR.Expr) (vs : List ValId)
      (ias : List Instr) (s' : Nat),
      lowerArgs ρ supply args = some (vs, ias, s') →
      ∀ i ∈ ias, IsPure i := by
  intro supply args
  induction args generalizing supply with
  | nil =>
      intro vs ias s' h i hi
      simp only [lowerArgs] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      simp at hi
  | cons a as ih =>
      intro vs ias s' h i hi
      cases h1 : lowerExpr ρ supply a with
      | none =>
          simp [lowerArgs, h1] at h
      | some p =>
          obtain ⟨va, ia, s1⟩ := p
          cases h2 : lowerArgs ρ s1 as with
          | none =>
              simp [lowerArgs, h1, h2] at h
          | some q =>
              obtain ⟨vs', ias', s2⟩ := q
              simp only [lowerArgs, h1, h2] at h
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              simp only [List.mem_append] at hi
              rcases hi with hi | hi
              · exact (lower_isPure.1 _ _ _ _ _ _ h1) i hi
              · exact ih s1 vs' ias' s' h2 i hi

/-- `lowerArgs` allocates at or above the incoming supply. -/
theorem lowerArgs_defs_gt (ρ : List (HIR.Id × ValId)) :
    ∀ (supply : Nat) (args : List HIR.Expr) (vs : List ValId)
      (ias : List Instr) (s' : Nat),
      lowerArgs ρ supply args = some (vs, ias, s') →
      ∀ d, d ∈ ias.flatMap defOf → supply ≤ d := by
  intro supply args
  induction args generalizing supply with
  | nil =>
      intro vs ias s' h d hd
      simp only [lowerArgs] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      simp at hd
  | cons a as ih =>
      intro vs ias s' h d hd
      cases h1 : lowerExpr ρ supply a with
      | none =>
          simp [lowerArgs, h1] at h
      | some p =>
          obtain ⟨va, ia, s1⟩ := p
          cases h2 : lowerArgs ρ s1 as with
          | none =>
              simp [lowerArgs, h1, h2] at h
          | some q =>
              obtain ⟨vs', ias', s2⟩ := q
              simp only [lowerArgs, h1, h2] at h
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              simp only [List.flatMap_append] at hd
              rcases List.mem_append.mp hd with hd | hd
              · exact (lower_defs_gt.1 _ _ _ _ _ _ h1) d hd
              · exact Nat.le_trans (lower_mono.1 _ _ _ _ _ _ h1)
                  (ih s1 vs' ias' s' h2 d hd)

/-- Lowered arguments evaluate to the oracle's actuals: every actual's
register holds its literal value after the emitted code runs, in order,
and the environment relation survives. The composition lower_total
cannot do alone (it speaks one expression at a time), built from its
conclusion plus register preservation across the later pieces. -/
theorem lowerArgs_agree (ρ : List (HIR.Id × ValId)) :
    ∀ (supply : Nat) (args : List HIR.Expr) (vs : List ValId)
      (ias : List Instr) (s' : Nat),
      lowerArgs ρ supply args = some (vs, ias, s') →
      (∀ a ∈ args, IsStraight a) →
      FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fuel : Nat) (argv : List HIR.Expr),
      args.mapM (evalHIR fuel henv) = some argv →
      ∃ fenv1, execInstrsFull fenv ias = some fenv1 ∧
        fenv1.store = fenv.store ∧ vs.length = argv.length ∧
        (∀ (j : Nat) (w : HIR.Expr), argv[j]? = some w →
          ∃ u v, vs[j]? = some u ∧ w = HIR.Expr.lit v ∧
            fenv1.env u = some v) ∧
        RelEnv henv ρ fenv1.env := by
  intro supply args
  induction args generalizing supply with
  | nil =>
      intro vs ias s' h _ _ henv fenv hrel fuel argv hmap
      simp only [lowerArgs] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      cases argv with
      | nil => exact ⟨fenv, rfl, rfl, rfl, by simp, hrel⟩
      | cons a as => simp at hmap
  | cons a as ih =>
      intro vs ias s' h hstr hf henv fenv hrel fuel argv hmap
      cases h1 : lowerExpr ρ supply a with
      | none =>
          simp [lowerArgs, h1] at h
      | some p =>
          obtain ⟨va, ia, s1⟩ := p
          cases h2 : lowerArgs ρ s1 as with
          | none =>
              simp [lowerArgs, h1, h2] at h
          | some q =>
              obtain ⟨vs', ias', s2⟩ := q
              simp only [lowerArgs, h1, h2] at h
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              have hstra : IsStraight a :=
                hstr a (List.mem_cons_self ..)
              have hstrs : ∀ b ∈ as, IsStraight b := by
                intro b hb
                exact hstr b (List.mem_cons_of_mem _ hb)
              obtain ⟨y, ys', rfl, heval, hmap'⟩ :=
                mapM_cons_inv (evalHIR fuel henv) a as argv hmap
              obtain ⟨hlit, fenv', hexec, hstore, w0, hr0, hw0⟩ :=
                lower_total.1 _ _ _ _ _ _ h1 hstra hf _ _ hrel _ _ heval
              have hle : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ h1
              have hva : va < s1 := lower_result_lt.1 _ _ _ _ _ _ h1 hf
              have hf' : FreshAbove ρ s1 := FreshAbove.mono _ _ _ hle hf
              have hrel' : RelEnv henv ρ fenv'.env :=
                RelEnv_exec _ _ _ _ _ _ _ h1 _ _ hrel hf hexec
              obtain ⟨fenv1, hexec', hstore', hlen, hmem, hrel1⟩ :=
                ih s1 vs' ias' s' h2 hstrs hf' _ _ hrel' _ _ hmap'
              have hdef : ∀ d, d ∈ ias'.flatMap defOf → s1 ≤ d :=
                lowerArgs_defs_gt ρ s1 as vs' ias' s' h2
              have hpure : ∀ i ∈ ias', IsPure i :=
                lowerArgs_isPure ρ s1 as vs' ias' s' h2
              refine ⟨fenv1, ?_, ?_, ?_, ?_, hrel1⟩
              · rw [execInstrsFull_append, hexec]
                exact hexec'
              · rw [hstore', hstore]
              · simp only [List.length_cons, hlen]
              · intro j w hj
                cases j with
                | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
                    subst hj
                    exact ⟨va, w0, by simp, hr0,
                      Eq.trans (execInstrsFull_preservLow s1 fenv' ias' fenv1
                        hpure hdef hexec' va hva).1 hw0⟩
                | succ j =>
                    simp only [List.getElem?_cons_succ] at hj
                    obtain ⟨u, v, hvs, rfl, hreg⟩ := hmem j _ hj
                    simp only [List.getElem?_cons_succ]
                    exact ⟨u, v, hvs, rfl, hreg⟩

/-! ## Table correspondence -/

/-- Every `lam` the HIR environment holds comes from the function table.
Pushed and updated bindings are literals (`IsStraight` initializers
evaluate to literals), so the invariant survives the statement walk and
every applied `lam` is a table entry. -/
def LamEnv (tab : List Func) (henv : HEnv) : Prop :=
  ∀ id p b, lookupHEnv henv id = some (.lam p b) →
    ∃ f ∈ tab, f.name = id ∧ f.params = p ∧ f.body = b

/-- Pushing a literal preserves `LamEnv`. -/
theorem LamEnv_push_lit {tab : List Func} {henv : HEnv} {id : HIR.Id}
    {w : Value} (h : LamEnv tab henv) :
    LamEnv tab ((id, HIR.Expr.lit w) :: henv) := by
  intro id' p b hlook
  by_cases heq : id = id'
  · subst heq
    simp [lookupHEnv] at hlook
  · rw [lookupHEnv_cons_ne heq] at hlook
    exact h id' p b hlook

/-- Updating to a literal preserves `LamEnv`. -/
theorem LamEnv_update_lit {tab : List Func} {henv : HEnv} {id : HIR.Id}
    {w : Value} (h : LamEnv tab henv) :
    LamEnv tab (updateHEnv henv id (HIR.Expr.lit w)) := by
  intro id' p b hlook
  by_cases heq : id' = id
  · subst heq
    rw [lookupHEnv_updateHEnv_head] at hlook
    simp at hlook
  · rw [lookupHEnv_updateHEnv_ne _ _ _ _ heq] at hlook
    exact h id' p b hlook

/-- First-match lookup is unique under `Nodup` names. -/
theorem findHIRFunc_unique {tab : List Func}
    (hnodup : (tab.map (fun f => f.name)).Nodup)
    {fid : HIR.Id} {f0 f1 : Func}
    (h0 : findHIRFunc tab fid = some f0)
    (hmem : f1 ∈ tab) (hname : f1.name = fid) : f0 = f1 := by
  induction tab generalizing fid f0 f1 with
  | nil => simp [findHIRFunc] at h0
  | cons g gs ih =>
      simp only [findHIRFunc] at h0
      by_cases hg : g.name = fid
      · rw [if_pos hg] at h0
        obtain rfl := Option.some.inj h0
        rcases List.mem_cons.mp hmem with rfl | hmem
        · rfl
        · exfalso
          have hnd : g.name ∉ gs.map (fun f => f.name) :=
            (List.nodup_cons.mp hnodup).1
          exact hnd (List.mem_map.mpr ⟨f1, hmem, hname.trans hg.symm⟩)
      · rw [if_neg hg] at h0
        have hnodup' : (gs.map (fun f => f.name)).Nodup :=
          (List.nodup_cons.mp hnodup).2
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact absurd hname hg
        · exact ih hnodup' h0 hmem hname

/-- Lowering preserves the function name. -/
theorem lowerFunc_name {f : Func} {mf : MIR.Func}
    (h : lowerFunc f = some mf) : mf.name = f.name.name := by
  unfold lowerFunc at h
  split at h
  · next hno =>
      dsimp only at h
      cases hbody : lowerExpr (List.zip f.params (List.range' 1 f.params.length))
          (f.params.length + 1) f.body with
      | none => simp [hbody] at h
      | some p =>
          obtain ⟨v, is, s⟩ := p
          simp only [hbody] at h
          obtain rfl := Option.some.inj h
          rfl
  · next hno => simp at h

/-- Successful lookup returns a table member. -/
theorem findHIRFunc_mem {tab : List Func} {fid : HIR.Id} {f : Func}
    (h : findHIRFunc tab fid = some f) : f ∈ tab := by
  induction tab with
  | nil => simp [findHIRFunc] at h
  | cons g gs ih =>
      simp only [findHIRFunc] at h
      by_cases hg : g.name = fid
      · rw [if_pos hg] at h
        obtain rfl := Option.some.inj h
        exact List.mem_cons_self ..
      · rw [if_neg hg] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- Successful lookup returns the looked-up name. -/
theorem findHIRFunc_name {tab : List Func} {fid : HIR.Id} {f : Func}
    (h : findHIRFunc tab fid = some f) : f.name = fid := by
  induction tab with
  | nil => simp [findHIRFunc] at h
  | cons g gs ih =>
      simp only [findHIRFunc] at h
      by_cases hg : g.name = fid
      · rw [if_pos hg] at h
        obtain rfl := Option.some.inj h
        exact hg
      · rw [if_neg hg] at h
        exact ih h

/-- Name-string uniqueness implies full-id uniqueness (same string
implies same id is false in general, but distinct strings force
distinct ids — the contrapositive that `Nodup` needs). -/
theorem nodup_names_of_nodup_nameStrings {tab : List Func}
    (h : (tab.map fun f => f.name.name).Nodup) :
    (tab.map (fun f => f.name)).Nodup := by
  induction tab with
  | nil => exact List.nodup_nil
  | cons g gs ih =>
      have hcons := List.nodup_cons.mp h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hcons.2⟩
      intro hmem
      apply hcons.1
      obtain ⟨f, hfm, hfeq⟩ := List.mem_map.mp hmem
      exact List.mem_map.mpr ⟨f, hfm, congrArg HIR.Id.name hfeq⟩

/-- Program table lookup mirrors HIR table lookup: first-match on both
sides over the same order, the `"main"` guard keeping the entry out of
the way. Needs every table function to lower (from `mapM` success), no
`"main"`-named function (from the guard), and unique name strings —
HIR lookup compares full ids while MIR lookup compares names, so a
same-name-different-index duplicate would resolve differently. -/
theorem findFunc_lowerCallProg {tab : List Func} {funcsMIR : List MIR.Func}
    {mainM : MIR.Func}
    (hmap : tab.mapM lowerFunc = some funcsMIR)
    (hmain : mainM.name = "main")
    (hnomain : ∀ f ∈ tab, f.name.name ≠ "main")
    (hnodup : (tab.map fun f => f.name.name).Nodup)
    {fid : HIR.Id} {f : Func} (hfind : findHIRFunc tab fid = some f)
    {mf : MIR.Func} (hlow : lowerFunc f = some mf) :
    findFunc ⟨mainM :: funcsMIR⟩ fid.name = some mf := by
  induction tab generalizing funcsMIR with
  | nil => simp [findHIRFunc] at hfind
  | cons g gs ih =>
      simp only [findHIRFunc] at hfind
      obtain ⟨mg, restMIR, rfl, hmg, hrest⟩ :=
        mapM_cons_inv lowerFunc g gs funcsMIR hmap
      have hmgname : mg.name = g.name.name := lowerFunc_name hmg
      have hnodup' : (gs.map fun f => f.name.name).Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hnomain' : ∀ f ∈ gs, f.name.name ≠ "main" := by
        intro f hf
        exact hnomain f (List.mem_cons_of_mem _ hf)
      by_cases hg : g.name = fid
      · rw [if_pos hg] at hfind
        obtain rfl := Option.some.inj hfind
        obtain rfl := Option.some.inj (hmg.symm.trans hlow)
        have hne : (mainM.name == fid.name) = false := by
          have hgg : fid.name = g.name.name := congrArg HIR.Id.name hg.symm
          rw [hmain, hgg]
          have hfid : g.name.name ≠ "main" :=
            hnomain g (List.mem_cons_self ..)
          cases heq : (("main" : String) == g.name.name) with
          | true => exact absurd (beq_iff_eq.mp heq) (fun h => hfid h.symm)
          | false => rfl
        simp only [findFunc, List.find?_cons, hne, hmgname, hg,
          beq_self_eq_true]
      · rw [if_neg hg] at hfind
        have hfound : findFunc ⟨mainM :: restMIR⟩ fid.name = some mf :=
          ih hrest hnomain' hnodup' hfind
        have hne_main : (mainM.name == fid.name) = false := by
          rw [hmain]
          have hfid : fid.name ≠ "main" := by
            have hfm : f ∈ gs := findHIRFunc_mem hfind
            have hfn : f.name = fid := findHIRFunc_name hfind
            have hnm := hnomain' f hfm
            rwa [hfn] at hnm
          cases heq : (("main" : String) == fid.name) with
          | true => exact absurd (beq_iff_eq.mp heq) (fun h => hfid h.symm)
          | false => rfl
        have hne_g : (mg.name == fid.name) = false := by
          rw [hmgname]
          have hfid : g.name.name ≠ fid.name := by
            intro hcon
            have hmem : f ∈ gs := findHIRFunc_mem hfind
            have hfname : f.name = fid := findHIRFunc_name hfind
            have hdup : g.name.name ∈ gs.map fun f => f.name.name :=
              List.mem_map.mpr ⟨f, hmem, by rw [hfname]; exact hcon.symm⟩
            have hnd : g.name.name ∉ gs.map fun f => f.name.name := by
              have hnc := (List.nodup_cons.mp hnodup).1
              simpa using hnc
            exact hnd hdup
          cases heq : ((g.name.name : String) == fid.name) with
          | true => exact absurd (beq_iff_eq.mp heq) hfid
          | false => rfl
        simp only [findFunc, List.find?_cons, hne_main, hne_g] at hfound ⊢
        exact hfound

/-! ## Binder agreement -/

/-- Pure instructions never read as calls. -/
theorem IsPure_noCall {i : Instr} (h : IsPure i) : i.isCall = false := by
  cases h <;> rfl

/-- Lowering success forces straight actuals, arm by arm (`lowerExpr`
only succeeds on `IsStraight`). -/
theorem lowerArgs_all_straight (ρ : List (HIR.Id × ValId)) :
    ∀ (supply : Nat) (args : List HIR.Expr) (vs : List ValId)
      (ias : List Instr) (s' : Nat),
      lowerArgs ρ supply args = some (vs, ias, s') →
      ∀ a ∈ args, IsStraight a := by
  intro supply args
  induction args generalizing supply with
  | nil =>
      intro vs ias s' h a ha
      simp at ha
  | cons a as ih =>
      intro vs ias s' h b hb
      cases h1 : lowerExpr ρ supply a with
      | none => simp [lowerArgs, h1] at h
      | some p =>
          obtain ⟨va, ia, s1⟩ := p
          cases h2 : lowerArgs ρ s1 as with
          | none => simp [lowerArgs, h1, h2] at h
          | some q =>
              obtain ⟨vs', ias', s2⟩ := q
              simp only [lowerArgs, h1, h2] at h
              rcases List.mem_cons.mp hb with rfl | hb
              · exact lower_isStraight.1 _ _ _ _ _ _ h1
              · exact ih s1 vs' ias' s2 h2 b hb

/-- A succeeding `mapM` preserves length. -/
theorem mapM_some_length {α β : Type} {f : α → Option β} {l : List α}
    {r : List β} (h : l.mapM f = some r) : r.length = l.length := by
  have := mapM_length f l r h
  omega

/-- A `mapM` run is determined pointwise by index lookups. -/
theorem mapM_of_pointwise {α β : Type} {l : List α} {f : α → Option β}
    {r : List β} (hlen : l.length = r.length)
    (hmem : ∀ (j : Nat) (a : α), l[j]? = some a →
      ∃ b, r[j]? = some b ∧ f a = some b) :
    l.mapM f = some r := by
  induction l generalizing r with
  | nil =>
      cases r with
      | nil => rfl
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases r with
      | nil => simp at hlen
      | cons b bs =>
          obtain ⟨b', hb', hfb'⟩ := hmem 0 a rfl
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb'
          subst hb'
          have hlen' : as.length = bs.length := by simpa using hlen
          have hmem' : ∀ (j : Nat) (a' : α), as[j]? = some a' →
              ∃ b'', bs[j]? = some b'' ∧ f a' = some b'' := by
            intro j a' ha'
            have hcons : (a :: as)[j + 1]? = some a' := by simpa using ha'
            obtain ⟨b'', hb'', hfb''⟩ := hmem (j + 1) a' hcons
            simp only [List.getElem?_cons_succ] at hb''
            exact ⟨b'', hb'', hfb''⟩
          exact (mapM_cons_eq f a as b bs).mpr ⟨hfb', ih (r := bs) hlen' hmem'⟩

/-- A `filterMap` that never drops preserves length. -/
theorem length_filterMap_of_all_some {α β : Type} {l : List α}
    {f : α → Option β} (h : ∀ x ∈ l, ∃ y, f x = some y) :
    (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      obtain ⟨y, hy⟩ := h a List.mem_cons_self
      simp only [List.filterMap_cons, hy, List.length_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `appBinds` keeps every pair when the arities match. -/
theorem appBinds_length {params : List HIR.Id} {argv : List HIR.Expr}
    (hlen : params.length = argv.length) :
    (appBinds params argv).length = params.length := by
  unfold appBinds
  rw [length_filterMap_of_all_some]
  · simp [List.length_range]
  · intro j hj
    rw [List.mem_range] at hj
    have harg : params.length - 1 - j < argv.length := by omega
    refine ⟨(params[j]'hj, argv[params.length - 1 - j]'harg), ?_⟩
    simp [List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩,
      List.getElem?_eq_some_iff.mpr ⟨harg, rfl⟩]

/-- First-match lookup resolves from membership plus key uniqueness. -/
theorem lookupHEnv_first_match {l : HEnv} {p : HIR.Id} {v : HIR.Expr}
    (hmem : (p, v) ∈ l) (huniq : ∀ q ∈ l, q.1 = p → q.2 = v) :
    lookupHEnv l p = some v := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      rcases List.mem_cons.mp hmem with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simp [lookupHEnv]
      · simp only [lookupHEnv]
        by_cases ha : a = p
        · have hv : b = v := huniq (a, b) List.mem_cons_self ha
          rw [if_pos ha, hv]
        · rw [if_neg ha]
          exact ih h (fun q hq hq1 => huniq q (List.mem_cons_of_mem _ hq) hq1)

/-- Index lookup into `appBinds`: with duplicate-free parameters, the
binding at `params[j]` is exactly `argv[n - 1 - j]`. -/
theorem lookupHEnv_appBinds {params : List HIR.Id} {argv : List HIR.Expr}
    (hnd : params.Nodup) {j : Nat} {p : HIR.Id} {v : HIR.Expr}
    (hp : params[j]? = some p) (hv : argv[params.length - 1 - j]? = some v) :
    lookupHEnv (appBinds params argv) p = some v := by
  apply lookupHEnv_first_match (appBinds_mem hp hv)
  intro q hq hq1
  unfold appBinds at hq
  simp only [List.mem_filterMap] at hq
  obtain ⟨j', hj'range, hj'match⟩ := hq
  cases hpar : params[j']? with
  | none => rw [hpar] at hj'match; simp at hj'match
  | some p' =>
      cases hav : argv[params.length - 1 - j']? with
      | none => rw [hpar, hav] at hj'match; simp at hj'match
      | some v' =>
          rw [hpar, hav] at hj'match
          simp only [] at hj'match
          obtain ⟨rfl, rfl⟩ := Option.some.inj hj'match
          have hpp : p' = p := hq1
          have hjj : j' = j := by
            obtain ⟨hlt', heq'⟩ := List.getElem?_eq_some_iff.mp hpar
            obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hp
            have hpair := List.pairwise_iff_getElem.mp
              (List.nodup_iff_pairwise_ne.mp hnd)
            rcases Nat.lt_trichotomy j' j with hlt2 | heq2 | hgt2
            · exfalso
              exact hpair j' j hlt' hlt hlt2 (by rw [heq', hpp, heq])
            · exact heq2
            · exfalso
              exact hpair j j' hlt hlt' hgt2 (by rw [heq, ← hpp, heq'])
          subst hjj
          rw [hav] at hv
          exact Option.some.inj hv

/-- A `rhoLookup` hit in a zipped register file gives the index and the
register. -/
theorem rhoLookup_zip_get {params : List HIR.Id} {rs : List Nat}
    {id : HIR.Id} {u : Nat}
    (    h : rhoLookup (params.zip rs) id = some u) :
    ∃ (j : Nat) (v : Nat), rs[j]? = some v ∧ params[j]? = some id ∧ u = v := by
  induction params generalizing rs with
  | nil => simp [List.zip_nil_left, rhoLookup] at h
  | cons a as ih =>
      cases rs with
      | nil => rw [List.zip_nil_right] at h; simp [rhoLookup] at h
      | cons r rs =>
          rw [List.zip_cons_cons] at h
          simp only [rhoLookup] at h
          by_cases heq : a = id
          · rw [if_pos heq] at h
            obtain rfl := Option.some.inj h
            exact ⟨0, r, by rfl, by simp only [List.getElem?_cons_zero, heq], rfl⟩
          · rw [if_neg heq] at h
            obtain ⟨j, v, hjrs, hjas, huv⟩ := ih h
            exact ⟨j + 1, v, by simpa using hjrs, by simpa using hjas, huv⟩

/-- Second components survive zipping. -/
theorem mem_zip_snd {α β : Type} {l₁ : List α} {l₂ : List β} {x : α} {y : β}
    (h : (x, y) ∈ l₁.zip l₂) : y ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp [List.zip] at h
  | cons a as ih =>
      cases l₂ with
      | nil => simp [List.zip] at h
      | cons b bs =>
          simp only [List.zip] at h
          rcases List.mem_cons.mp h with h | h
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih h)

/-- `Env.update` writes the register it names. -/
theorem envUpdate_self {m : MIR.Env} {d : ValId} {v : Value} :
    m.update d v d = some v := by
  simp [Env.update]

/-- `Env.update` leaves every other register alone. -/
theorem envUpdate_other {m : MIR.Env} {d x : ValId} {v : Value} (h : x ≠ d) :
    m.update d v x = m x := by
  have hbeq : (x == d) = false := by
    cases heq : (x == d) with
    | true => exact absurd (beq_iff_eq.mp heq) h
    | false => rfl
  simp [Env.update, hbeq]

/-- Positional binder lookup: with duplicate-free registers, the bound
register reads back its value. -/
theorem bindCallArgs_getElem {ps : List (ValId × Typ)} {ws : List Value}
    {env : MIR.Env} (h : bindCallArgs ps ws = some env) {i : Nat}
    (hi : i < ps.length) (hlen : ps.length = ws.length)
    (hnd : (ps.map Prod.fst).Nodup) :
    env (ps[i]'hi).1 = some (ws[i]'(by omega)) := by
  induction ps generalizing ws env i with
  | nil => simp at hi
  | cons p ps ih =>
      obtain ⟨v, τ⟩ := p
      cases ws with
      | nil => simp at hlen
      | cons w ws =>
          have hi' : i < ((v, τ) :: ps).length := hi
          simp only [List.length_cons] at hi hlen hnd
          cases i with
          | zero =>
              simp only [bindCallArgs] at h
              cases hbind : bindCallArgs ps ws with
              | none => simp [hbind] at h
              | some env' =>
                  simp only [hbind] at h
                  obtain rfl := Option.some.inj h
                  have h0 : ((((v, τ) :: ps)[0]'hi').1) = v := by simp
                  have hw0 : (((w :: ws)[0]'(by simp only [List.length_cons]; omega))) = w := by simp
                  rw [h0, hw0]
                  exact envUpdate_self
          | succ n =>
              have hn : n < ps.length := by omega
              have hlen' : ps.length = ws.length := by omega
              have hnd' : (ps.map Prod.fst).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hnotin : v ∉ ps.map Prod.fst :=
                (List.nodup_cons.mp hnd).1
              simp only [bindCallArgs] at h
              cases hbind : bindCallArgs ps ws with
              | none => simp [hbind] at h
              | some env' =>
                  simp only [hbind] at h
                  obtain rfl := Option.some.inj h
                  have ihv := ih (ws := ws) (env := env') (i := n)
                    hbind hn hlen' hnd'
                  have hget1 : ((((v, τ) :: ps)[n + 1]'hi').1) = (ps[n]'hn).1 := by
                    simp
                  rw [hget1]
                  have hget2 : (((w :: ws)[n + 1]'(by simp only [List.length_cons]; omega))) = (ws[n]'(by omega)) := by
                    simp
                  rw [hget2]
                  have hmem : (ps[n]'hn).1 ∈ ps.map Prod.fst :=
                    List.mem_map.mpr ⟨ps[n]'hn, List.getElem_mem hn, rfl⟩
                  have hne : (ps[n]'hn).1 ≠ v := fun hcon => hnotin (hcon ▸ hmem)
                  rw [envUpdate_other hne]
                  exact ihv

/-- Binding succeeds on matching arity. -/
theorem bindCallArgs_some_of_length {ps : List (ValId × Typ)}
    {ws : List Value} (hlen : ps.length = ws.length) :
    ∃ env, bindCallArgs ps ws = some env := by
  induction ps generalizing ws with
  | nil =>
      cases ws with
      | nil => exact ⟨_, rfl⟩
      | cons w ws => simp at hlen
  | cons p ps ih =>
      obtain ⟨v, τ⟩ := p
      cases ws with
      | nil => simp at hlen
      | cons w ws =>
          have hlen' : ps.length = ws.length := by
            simpa using hlen
          obtain ⟨env', hbind⟩ := ih (ws := ws) hlen'
          simp only [bindCallArgs, hbind]
          exact ⟨_, rfl⟩

/-- A miss on the prefix is a miss on the whole append. -/
theorem lookupHEnv_append_none {l₁ l₂ : HEnv} {id : HIR.Id}
    (h : lookupHEnv l₁ id = none) :
    lookupHEnv (l₁ ++ l₂) id = lookupHEnv l₂ id := by
  induction l₁ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      simp only [lookupHEnv] at h
      by_cases ha : a = id
      · rw [if_pos ha] at h
        simp at h
      · rw [if_neg ha] at h
        simp only [List.cons_append, lookupHEnv, if_neg ha]
        exact ih h

/-- A hit on the prefix survives the append. -/
theorem lookupHEnv_append_some {l₁ l₂ : HEnv} {id : HIR.Id} {v : HIR.Expr}
    (h : lookupHEnv l₁ id = some v) :
    lookupHEnv (l₁ ++ l₂) id = some v := by
  induction l₁ with
  | nil => simp [lookupHEnv] at h
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      simp only [lookupHEnv] at h
      by_cases ha : a = id
      · rw [if_pos ha] at h
        simp only [List.cons_append, lookupHEnv, if_pos ha]
        exact h
      · rw [if_neg ha] at h
        simp only [List.cons_append, lookupHEnv, if_neg ha]
        exact ih h

/-- The concrete binding list the HIR oracle runs under: every table
function as a `lam`, ahead of the caller environment. -/
def lamEnv (tab : List Func) : HEnv :=
  tab.map fun f => (f.name, HIR.Expr.lam f.params f.body)

/-- First-match table lookup and first-match environment lookup agree. -/
theorem lookupHEnv_lamEnv_of_find {tab : List Func} {fid : HIR.Id}
    {f : Func} (h : findHIRFunc tab fid = some f) :
    lookupHEnv (lamEnv tab) fid = some (.lam f.params f.body) := by
  induction tab with
  | nil => simp [findHIRFunc] at h
  | cons g gs ih =>
      simp only [findHIRFunc] at h
      by_cases heq : g.name = fid
      · rw [if_pos heq] at h
        obtain rfl := Option.some.inj h
        simp only [lamEnv, List.map_cons, lookupHEnv, if_pos heq]
      · rw [if_neg heq] at h
        have hrec := ih h
        simp only [lamEnv, List.map_cons, lookupHEnv, if_neg heq]
        exact hrec

/-- Every `lam` in the table binding list comes from the table. -/
theorem lamEnv_self (tab : List Func) : LamEnv tab (lamEnv tab) := by
  intro id p b hlook
  induction tab with
  | nil => simp [lamEnv, lookupHEnv] at hlook
  | cons g gs ih =>
      simp only [lamEnv, List.map_cons, lookupHEnv] at hlook
      by_cases heq : g.name = id
      · rw [if_pos heq] at hlook
        simp only [Option.some.injEq, HIR.Expr.lam.injEq] at hlook
        obtain ⟨rfl, rfl⟩ := hlook
        exact ⟨g, List.mem_cons_self, heq, rfl, rfl⟩
      · rw [if_neg heq] at hlook
        obtain ⟨f, hmem, hname, hparams, hbody⟩ := ih hlook
        exact ⟨f, List.mem_cons_of_mem _ hmem, hname, hparams, hbody⟩

/-- `LamEnv` survives environment append. -/
theorem LamEnv_append {tab : List Func} {l₁ l₂ : HEnv}
    (h₁ : LamEnv tab l₁) (h₂ : LamEnv tab l₂) :
    LamEnv tab (l₁ ++ l₂) := by
  intro id p b hlook
  cases h1 : lookupHEnv l₁ id with
  | some v =>
      have happ := lookupHEnv_append_some (l₂ := l₂) h1
      rw [happ] at hlook
      obtain rfl := Option.some.inj hlook
      exact h₁ id p b h1
  | none =>
      rw [lookupHEnv_append_none h1] at hlook
      exact h₂ id p b hlook

/-- A lowered function exposes its body lowering and its shape. -/
theorem lowerFunc_inv {f : Func} {mf : MIR.Func}
    (h : lowerFunc f = some mf) :
    ∃ v is s', lowerExpr (List.zip f.params (List.range' 1 f.params.length))
        (f.params.length + 1) f.body = some (v, is, s') ∧
      exprNoApp f.body = true ∧
      mf = ⟨f.name.name, (List.range' 1 f.params.length).map (fun (x : ValId) => (x, Typ.unitType)),
        [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0, .unitType⟩ := by
  unfold lowerFunc at h
  cases hno : exprNoApp f.body with
  | false => simp [hno] at h
  | true =>
      simp [hno] at h
      cases hle : lowerExpr (List.zip f.params (List.range' 1 f.params.length))
          (f.params.length + 1) f.body with
      | none => simp [hle] at h
      | some q =>
          obtain ⟨v, is, s'⟩ := q
          simp only [hle] at h
          obtain rfl := Option.some.inj h
          exact ⟨v, is, s', rfl, rfl, rfl⟩

/-- The argument values a lowered call delivers, as `Value`s. -/
theorem lowerArgs_agree_vals (ρ : List (HIR.Id × ValId)) :
    ∀ (supply : Nat) (args : List HIR.Expr) (vs : List ValId)
      (ias : List Instr) (s' : Nat),
      lowerArgs ρ supply args = some (vs, ias, s') →
      FreshAbove ρ supply →
      ∀ (henv : HEnv) (fenv : FullEnv), RelEnv henv ρ fenv.env →
      ∀ (fuel : Nat) (argv : List HIR.Expr),
      args.mapM (evalHIR fuel henv) = some argv →
      ∃ fenv1 argvW, execInstrsFull fenv ias = some fenv1 ∧
        fenv1.store = fenv.store ∧ argv = argvW.map HIR.Expr.lit ∧
        vs.mapM fenv1.env = some argvW ∧ RelEnv henv ρ fenv1.env := by
  intro supply args
  induction args generalizing supply with
  | nil =>
      intro vs ias s' h hf henv fenv hrel fuel argv hmap
      simp only [lowerArgs] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      cases argv with
      | nil => exact ⟨fenv, [], rfl, rfl, rfl, rfl, hrel⟩
      | cons b bs => simp [List.mapM_nil] at hmap
  | cons a as ih =>
      intro vs ias s' h hf henv fenv hrel fuel argv hmap
      cases h1 : lowerExpr ρ supply a with
      | none => simp [lowerArgs, h1] at h
      | some p =>
          obtain ⟨va, ia, s1⟩ := p
          cases h2 : lowerArgs ρ s1 as with
          | none => simp [lowerArgs, h1, h2] at h
          | some q =>
              obtain ⟨vs', ias', s2⟩ := q
              simp only [lowerArgs, h1, h2] at h
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              have hstra : IsStraight a := lower_isStraight.1 _ _ _ _ _ _ h1
              obtain ⟨y, ys', rfl, heval, hmap'⟩ :=
                mapM_cons_inv (evalHIR fuel henv) a as argv hmap
              obtain ⟨hlit, fenv', hexec, hstore, w, hr0, hw0⟩ :=
                lower_total.1 _ _ _ _ _ _ h1 hstra hf _ _ hrel _ _ heval
              have hle : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ h1
              have hva : va < s1 := lower_result_lt.1 _ _ _ _ _ _ h1 hf
              have hf' : FreshAbove ρ s1 := FreshAbove.mono _ _ _ hle hf
              have hrel' : RelEnv henv ρ fenv'.env :=
                RelEnv_exec _ _ _ _ _ _ _ h1 _ _ hrel hf hexec
              obtain ⟨fenv1, ws, hexec', hstore', hws, hmapW, hrel1⟩ :=
                ih s1 vs' ias' s' h2 hf' _ _ hrel' _ _ hmap'
              have hdef : ∀ d, d ∈ ias'.flatMap defOf → s1 ≤ d :=
                lowerArgs_defs_gt ρ s1 as vs' ias' s' h2
              have hpure : ∀ i ∈ ias', IsPure i :=
                lowerArgs_isPure ρ s1 as vs' ias' s' h2
              refine ⟨fenv1, w :: ws, ?_, ?_, ?_, ?_, hrel1⟩
              · rw [execInstrsFull_append, hexec]
                exact hexec'
              · rw [hstore', hstore]
              · simp [hr0, hws]
              · exact (mapM_cons_eq _ _ _ _ _).mpr
                  ⟨Eq.trans (execInstrsFull_preservLow s1 fenv' ias' fenv1
                    hpure hdef hexec' va hva).1 hw0, hmapW⟩

/-- The bind correspondence: HIR `appBinds` and MIR `bindCallArgs` deliver
the same values — params `[j]` takes actuals `[n - 1 - j]` on both sides,
the reversal making the register order match the innermost-first order. -/
theorem relEnv_appBinds_bindCallArgs {params : List HIR.Id}
    {argv : List HIR.Expr} {argvW : List Value}
    (hargv : argv = argvW.map HIR.Expr.lit)
    (hlen : params.length = argv.length)
    (hnd : params.Nodup)
    {envCal : MIR.Env}
    (hbind : bindCallArgs ((List.range' 1 params.length).map (fun (x : ValId) => (x, Typ.unitType)))
      argvW.reverse = some envCal) :
    RelEnv (appBinds params argv)
      (List.zip params (List.range' 1 params.length)) envCal := by
  intro id u hlook
  obtain ⟨j, r, hjrs, hjas, huv⟩ := rhoLookup_zip_get hlook
  obtain ⟨hlt_rs, hr_eq⟩ := List.getElem?_eq_some_iff.mp hjrs
  simp only [List.length_range'] at hlt_rs
  have hr : r = 1 + j := by
    have hgr := List.getElem?_range' (s := 1) (step := 1) (i := j)
      (n := params.length) hlt_rs
    rw [hjrs] at hgr
    have hinj := Option.some.inj hgr
    omega
  have hlenW : argvW.length = params.length := by
    rw [hlen, hargv, List.length_map]
  have hjlt : params.length - 1 - j < params.length := by omega
  have hjltW : params.length - 1 - j < argvW.length := by omega
  have hargvj : argv[params.length - 1 - j]? =
      some (HIR.Expr.lit argvW[params.length - 1 - j]) := by
    have h2 : argvW[params.length - 1 - j]? = some argvW[params.length - 1 - j] :=
      List.getElem?_eq_some_iff.mpr ⟨hjltW, rfl⟩
    rw [hargv, List.getElem?_map, h2, Option.map_some]
  have hlookB : lookupHEnv (appBinds params argv) id =
      some (HIR.Expr.lit argvW[params.length - 1 - j]) :=
    lookupHEnv_appBinds hnd hjas hargvj
  have hpslen : ((List.range' 1 params.length).map (fun (x : ValId) => (x, Typ.unitType))).length =
      params.length := by simp [List.length_map, List.length_range']
  have hlenR : ((List.range' 1 params.length).map (fun (x : ValId) => (x, Typ.unitType))).length =
      (argvW.reverse).length := by
    simp [List.length_map, List.length_range', List.length_reverse, hlenW]
  have hndR : ((((List.range' 1 params.length).map (fun (x : ValId) => (x, Typ.unitType)))).map
      Prod.fst).Nodup := by
    have heq : ((((List.range' 1 params.length).map (fun (x : ValId) => (x, Typ.unitType)))).map
        Prod.fst) = List.range' 1 params.length := by
      rw [List.map_map]
      have hcomp : (Prod.fst ∘ (fun (x : ValId) => (x, Typ.unitType))) = fun x => x := rfl
      rw [hcomp]
      exact List.map_id _
    rw [heq]
    exact List.nodup_range'
  have hjlen : j < ((List.range' 1 params.length).map (fun (x : ValId) => (x, Typ.unitType))).length := by
    simpa [List.length_map, List.length_range'] using hlt_rs
  have hMIR := bindCallArgs_getElem hbind hjlen hlenR hndR
  have hrevlen : (argvW.reverse).length = argvW.length := by simp
  have hjrev : j < (argvW.reverse).length := by omega
  have hwsome : (argvW.reverse)[j]? = some argvW[params.length - 1 - j] := by
    have hjW : j < argvW.length := by omega
    rw [List.getElem?_reverse hjW, hlenW]
    exact List.getElem?_eq_some_iff.mpr ⟨hjltW, rfl⟩
  have hMIRval : envCal ((((List.range' 1 params.length).map
      (fun (x : ValId) => (x, Typ.unitType)))[j]'hjlen).1) =
      some argvW[params.length - 1 - j] := by
    have h2 := List.getElem?_eq_some_iff.mpr ⟨hjrev, rfl⟩
    have hpay : (argvW.reverse)[j]'hjrev = argvW[params.length - 1 - j] :=
      (Option.some.inj (hwsome.symm.trans h2)).symm
    exact hMIR.trans (congrArg some hpay)
  have hpssome : ((((List.range' 1 params.length).map
      (fun (x : ValId) => (x, Typ.unitType))))[j]?) =
      some ((1 + j, Typ.unitType)) := by
    rw [List.getElem?_map, List.getElem?_range' hlt_rs]
    simp only [Option.map_some]
    have harith : 1 + 1 * j = 1 + j := by omega
    rw [harith]
  have hps : ((((List.range' 1 params.length).map
      (fun (x : ValId) => (x, Typ.unitType))))[j]'hjlen) = ((1 + j), Typ.unitType) := by
    have h2 := List.getElem?_eq_some_iff.mpr ⟨hjlen, rfl⟩
    rw [hpssome] at h2
    exact Option.some.inj h2 |>.symm
  have hreg : (((((List.range' 1 params.length).map
      (fun (x : ValId) => (x, Typ.unitType))))[j]'hjlen).1) = 1 + j := by rw [hps]
  refine ⟨argvW[params.length - 1 - j], hlookB, ?_⟩
  rw [huv, hr, ←hreg] at ⊢
  exact hMIRval

/-- A resolved callee runs to the value the HIR oracle computed: the
call-free body runs through the fixed-fuel single-block executor, and
`lower_total` ties the emitted code to the HIR evaluation under the
bound-argument binding. -/
theorem callee_agree {params : List HIR.Id} {body : HIR.Expr}
    {v : ValId} {is : List Instr} {s' : Nat}
    (hle : lowerExpr (List.zip params (List.range' 1 params.length))
      (params.length + 1) body = some (v, is, s'))
    (hnd : params.Nodup)
    {argv : List HIR.Expr} {argvW : List Value}
    (hargv : argv = argvW.map HIR.Expr.lit)
    (hlen : params.length = argv.length)
    (henvRest : HEnv)
    {fuelCal : Nat} {r : HIR.Expr}
    (heval : evalHIR fuelCal (appBinds params argv ++ henvRest) body = some r)
    {fuelM : Nat} (store : Store) (envCal : MIR.Env)
    (hbind : bindCallArgs ((List.range' 1 params.length).map (fun (x : ValId) => (x, Typ.unitType)))
      argvW.reverse = some envCal)
    {mf : MIR.Func} {entry : MIR.Block}
    (hblocks : mf.blocks = [entry])
    (hentry : entry = ⟨0, [.const 0 .unit] ++ is, .return_ v⟩) :
    ∃ w, r = HIR.Expr.lit w ∧
      execBlockFrom (fuelM + 1) mf none entry ⟨envCal, store⟩ = some w := by
  subst hentry
  have hstraight : IsStraight body := lower_isStraight.1 _ _ _ _ _ _ hle
  have hlenW : argvW.length = params.length := by
    rw [hlen, hargv, List.length_map]
  have hfCal : FreshAbove (List.zip params (List.range' 1 params.length))
      (params.length + 1) := by
    intro j' u hmem
    have huR := mem_zip_snd hmem
    rw [List.mem_range'] at huR
    obtain ⟨i, hi, hui⟩ := huR
    rw [Nat.one_mul] at hui
    rw [hui]
    simpa [Nat.add_comm] using Nat.add_lt_add_left hi 1
  have hrelB : RelEnv (appBinds params argv)
      (List.zip params (List.range' 1 params.length)) envCal :=
    relEnv_appBinds_bindCallArgs hargv hlen hnd hbind
  have hconst : execInstrsFull (⟨envCal, store⟩ : FullEnv) [.const 0 .unit] =
      some ⟨envCal.update 0 .unit, store⟩ := by
    simp [execInstrsFull, evalInstrFull]
  have hrelB' : RelEnv (appBinds params argv ++ henvRest)
      (List.zip params (List.range' 1 params.length))
      (envCal.update 0 .unit) := by
    intro j' u hlook
    obtain ⟨w, hlookB, hreg⟩ := hrelB j' u hlook
    refine ⟨w, lookupHEnv_append_some hlookB, ?_⟩
    have hne : u ≠ 0 := by
      obtain ⟨j, r, hjrs, hjas, huv⟩ := rhoLookup_zip_get hlook
      obtain ⟨hlt_rs, -⟩ := List.getElem?_eq_some_iff.mp hjrs
      have hgr := List.getElem?_range' (s := 1) (step := 1) (i := j)
        (n := params.length) (by simpa [List.length_range'] using hlt_rs)
      rw [hjrs] at hgr
      have hinj := Option.some.inj hgr
      rw [huv, hinj, Nat.one_mul, Nat.add_comm 1 j]
      exact Nat.succ_ne_zero _
    rw [envUpdate_other hne]
    exact hreg
  obtain ⟨hlit, fenvB, hexecB, hstoreB, w, hrw, hwreg⟩ :=
    lower_total.1 _ _ _ _ _ _ hle hstraight hfCal _ ⟨envCal.update 0 .unit, store⟩
      hrelB' _ _ heval
  have hexecFull : execInstrsFull (⟨envCal, store⟩ : FullEnv)
      ([.const 0 .unit] ++ is) = some fenvB := by
    simp only [execInstrsFull_append, hconst, hexecB]
  have hexecFrom : execInstrsFullFrom none (⟨envCal, store⟩ : FullEnv)
      ([.const 0 .unit] ++ is) = some fenvB := by
    rw [execInstrsFullFrom_none_of_pure]
    · exact hexecFull
    · intro i hi
      rcases List.mem_append.mp hi with h | h
      · simp at h
        subst h
        exact IsPure.const _ _
      · exact lower_isPure.1 _ _ _ _ _ _ hle i h
  refine ⟨w, hrw, ?_⟩
  simp only [execBlockFrom]
  show (match execInstrsFullFrom none (⟨envCal, store⟩ : FullEnv)
      ((⟨0, [.const 0 .unit] ++ is, .return_ v⟩ : MIR.Block).instrs) with
    | none => none
    | some fenv' =>
        match (⟨0, [.const 0 .unit] ++ is, .return_ v⟩ : MIR.Block).terminator with
        | .return_ v => fenv'.env v
        | .goto t =>
            match findBlock mf t with
            | some b' => execBlockFrom fuelM mf (some 0) b' fenv'
            | none => none
        | .branch c tt ff =>
            match fenv'.boolOf c with
            | some true =>
                match findBlock mf tt with
                | some b' => execBlockFrom fuelM mf (some 0) b' fenv'
                | none => none
            | some false =>
                match findBlock mf ff with
                | some b' => execBlockFrom fuelM mf (some 0) b' fenv'
                | none => none
            | none => none
        | .switch _ _ _ => none) = some w
  rw [show ((⟨0, [.const 0 .unit] ++ is, .return_ v⟩ : MIR.Block).instrs =
      ([.const 0 .unit] ++ is)) from rfl,
    show ((⟨0, [.const 0 .unit] ++ is, .return_ v⟩ : MIR.Block).terminator =
      (.return_ v)) from rfl]
  rw [hexecFrom]
  simp only []
  exact hwreg

end Morph.Proofs.Call
