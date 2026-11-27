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
          cases hinf : inferBody [] [] is v with
          | none => rw [hinf] at h; simp at h
          | some τ => rw [hinf] at h; obtain rfl := Option.some.inj h; rfl
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
    ∃ v is s' τ, lowerExpr (List.zip f.params (List.range' 1 f.params.length))
        (f.params.length + 1) f.body = some (v, is, s') ∧
      exprNoApp f.body = true ∧
      inferBody [] [] is v = some τ ∧
      mf = ⟨f.name.name, (List.range' 1 f.params.length).map (fun (x : ValId) => (x, Typ.unitType)),
        [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0, τ⟩ := by
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
          cases hinf : inferBody [] [] is v with
          | none => rw [hinf] at h; simp at h
          | some τ =>
              rw [hinf] at h
              simp only [hinf] at h
              refine ⟨v, is, s', τ, rfl, rfl, hinf, ?_⟩
              exact Option.some.inj h.symm

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

/-! ## Call-aware composition

The statement induction (`lowerCallStmts_total`, next) composes three
facts: lowered argument code runs under the call-aware executor exactly
as under the plain one (it is pure), instruction lists split
sequentially, and reversed actuals map to reversed values. The single
`.call` step is isolated last, so the induction only rewrites with it.
-/

/-- `mapM` success survives reversal, pointwise. -/
theorem mapM_reverse_some {α β : Type} {f : α → Option β} {l : List α}
    {r : List β} (h : l.mapM f = some r) :
    l.reverse.mapM f = some r.reverse := by
  have hlen : l.length = r.length := (mapM_some_length h).symm
  apply mapM_of_pointwise (l := l.reverse) (r := r.reverse)
    (by simp [hlen])
  intro j a ha
  obtain ⟨hltRev, _⟩ := List.getElem?_eq_some_iff.mp ha
  have hlenRev : l.reverse.length = l.length := by simp
  have hjL : j < l.length := hlenRev ▸ hltRev
  have hLa : l[l.length - 1 - j]? = some a := by
    have hrev := List.getElem?_reverse hjL
    have hsymm := hrev.symm.trans ha
    simpa using hsymm
  obtain ⟨b, hbr, hfb⟩ := mapM_pointwise f l r h _ _ hLa
  have hjR : j < r.length := hlen ▸ hjL
  have hrIdx : l.length - 1 - j = r.length - 1 - j := by rw [hlen]
  rw [hrIdx] at hbr
  have hRev := List.getElem?_reverse hjR
  exact ⟨b, by rw [hRev]; exact hbr, hfb⟩

/-- Sequential composition for the call-aware walk: running `l₁ ++ l₂`
is running `l₁`, then `l₂`. Mirrors `execInstrsFull_append`; the `.call`
arm threads its updated environment into the induction hypothesis, every
other arm mirrors `execInstrsCall_of_noCall`. -/
theorem execInstrsCall_append (prog : MIR.Program) (fuel : Nat)
    (prev : Option MIR.BlockId) (fenv : FullEnv) (l₁ l₂ : List Instr) :
    execInstrsCall prog fuel prev fenv (l₁ ++ l₂) =
      match execInstrsCall prog fuel prev fenv l₁ with
      | none => none
      | some fenv' => execInstrsCall prog fuel prev fenv' l₂ := by
  induction l₁ generalizing fenv with
  | nil => simp [execInstrsCall]
  | cons i rest ih =>
      simp only [List.cons_append]
      cases i with
      | phi dst pred src =>
          cases prev with
          | none =>
              simp only [execInstrsCall]
              exact ih fenv
          | some p =>
              by_cases hp : pred = p
              · subst hp
                cases hsrc : fenv.env src with
                | none => simp [execInstrsCall, hsrc]
                | some v => simp [execInstrsCall, hsrc, ih]
              · simp [execInstrsCall, hp, ih]
      | call dst fn args =>
          cases hfind : findFunc prog fn with
          | none =>
              simp [execInstrsCall, hfind]
          | some callee =>
              cases hargs : args.mapM fenv.env with
              | none =>
                  simp [execInstrsCall, hfind, hargs]
              | some argv =>
                  cases hbind : bindCallArgs callee.params argv with
                  | none =>
                      simp [execInstrsCall, hfind, hargs, hbind]
                  | some envCal =>
                      cases hentry : findBlock callee callee.entry with
                      | none =>
                          simp [execInstrsCall, hfind, hargs, hbind, hentry]
                      | some entry =>
                          cases hrun : execBlockFrom fuel callee none entry
                              ⟨envCal, fenv.store⟩ with
                          | none =>
                              simp [execInstrsCall, hfind, hargs, hbind, hentry,
                                hrun]
                          | some w =>
                              cases dst with
                              | none =>
                                  simp [execInstrsCall, hfind, hargs, hbind,
                                    hentry, hrun, ih]
                              | some d =>
                                  simp [execInstrsCall, hfind, hargs, hbind,
                                    hentry, hrun, ih]
      | const dst v =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.const dst v) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | copy dst src =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.copy dst src) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | unop dst op src τ =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.unop dst op src τ) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | binop dst op l r τ =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.binop dst op l r τ) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | load dst loc cap =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.load dst loc cap) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | store loc src cap =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.store loc src cap) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | alloc dst cap τ =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.alloc dst cap τ) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | free loc =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.free loc) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | allocClosure dst fn captures =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.allocClosure dst fn captures) with
          | none => rfl
          | some fenv1 => exact ih fenv1
      | callClosure dst clo args =>
          simp only [execInstrsCall]
          cases _ : evalInstrFull fenv (.callClosure dst clo args) with
          | none => rfl
          | some fenv1 => exact ih fenv1

/-- Pure prefixes run identically under both executors: the shape the
`lowerArgs` prefix of every call arm uses. -/
theorem execInstrsCall_pure_prefix (prog : MIR.Program) (fuel : Nat)
    (fenv : FullEnv) (ias : List Instr)
    (hpure : ∀ i ∈ ias, IsPure i) (fenv1 : FullEnv)
    (hexec : execInstrsFull fenv ias = some fenv1) :
    execInstrsCall prog fuel none fenv ias = some fenv1 := by
  have hno : ∀ i ∈ ias, i.isCall = false :=
    fun i hi => IsPure_noCall (hpure i hi)
  have h1 : execInstrsCall prog fuel none fenv ias =
      execInstrsFullFromIn prog none fenv ias :=
    execInstrsCall_of_noCall prog fuel none fenv ias hno
  rw [h1, execInstrsFullFromIn_eq]
  have h2 : execInstrsFullFrom none fenv ias = execInstrsFull fenv ias :=
    execInstrsFullFrom_none_of_pure fenv ias hpure
  rw [h2, hexec]

/-- One `.call` step, isolated: with the callee resolved, actuals read,
arguments bound, entry found, and the call-free body run, the instruction
writes the result (or discards it for `dst = none`). -/
theorem execInstrsCall_call_step (prog : MIR.Program) (fuel : Nat)
    (prev : Option MIR.BlockId) (fenv1 : FullEnv) (fn : FnId)
    (argRegs : List ValId) (dst : Option ValId)
    (callee : MIR.Func) (argv : List Value) (envCal : MIR.Env)
    (entry : MIR.Block) (w : Value)
    (hfind : findFunc prog fn = some callee)
    (hargs : argRegs.mapM fenv1.env = some argv)
    (hbind : bindCallArgs callee.params argv = some envCal)
    (hentry : findBlock callee callee.entry = some entry)
    (hrun : execBlockFrom fuel callee none entry ⟨envCal, fenv1.store⟩ =
      some w) :
    execInstrsCall prog fuel prev fenv1 [.call dst fn argRegs] =
      match dst with
      | none => some fenv1
      | some d => some ⟨fenv1.env.update d w, fenv1.store⟩ := by
  simp only [execInstrsCall, hfind, hargs, hbind, hentry, hrun]
  cases dst with
  | none => rfl
  | some d => rfl

/-! ## Statement induction: supply monotonicity and member lookup -/

/-- `lowerArgs` never decreases the supply. -/
theorem lowerArgs_mono (ρ : List (HIR.Id × ValId)) :
    ∀ (supply : Nat) (args : List HIR.Expr) (vs : List ValId)
      (ias : List Instr) (s' : Nat),
      lowerArgs ρ supply args = some (vs, ias, s') → supply ≤ s' := by
  intro supply args
  induction args generalizing supply with
  | nil =>
      intro vs ias s' h
      simp only [lowerArgs] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      exact Nat.le_refl _
  | cons a as ih =>
      intro vs ias s' h
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
              exact Nat.le_trans (lower_mono.1 _ _ _ _ _ _ h1) (ih s1 vs' ias' s' h2)

/-- A `mapM` success pins every member input to some output. -/
theorem mapM_mem_some {α β : Type} {f : α → Option β} {l : List α}
    {r : List β} (h : l.mapM f = some r) {x : α} (hmem : x ∈ l) :
    ∃ y, f x = some y := by
  induction l generalizing r with
  | nil =>
      simp at hmem
  | cons a as ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem2
      · obtain ⟨y, ys', rfl, h1, _⟩ := mapM_cons_inv f x as r h
        exact ⟨y, h1⟩
      · obtain ⟨y, ys', rfl, _, htail⟩ := mapM_cons_inv f a as r h
        exact ih htail hmem2

/-! ## Statement induction: the shared call prefix -/

/-- The shared call prefix: resolve the callee, run the lowered actuals,
bind them back-to-front, run the call-free body, and step the single
`.call`. Returns the post-call environment with the result register,
the HIR value equation, and the preserved relation. Every call arm
(`varDecl`/`assign`/`returnStmt` over `.app`) composes this with its
own tail. -/
theorem callStep_agree (tab : List Func) (ρ : List (HIR.Id × ValId))
    (supply : Nat) (fid : HIR.Id) (args : List HIR.Expr)
    (vs : List ValId) (ias : List Instr) (s1 : Nat)
    (hargs : lowerArgs ρ supply args = some (vs, ias, s1))
    (henv : HEnv) (fenv : FullEnv) (hrel : RelEnv henv ρ fenv.env)
    (hf : FreshAbove ρ supply) (hlam : LamEnv tab henv)
    {f : Func} (hfind : findHIRFunc tab fid = some f)
    (hguard : f.params.length = args.length ∧ exprNoApp f.body = true)
    (prog : MIR.Program) (funcsMIR : List MIR.Func) (fuelM : Nat)
    (hmap : tab.mapM lowerFunc = some funcsMIR)
    (hndp : ∀ f ∈ tab, f.params.Nodup)
    (hnodup : (tab.map fun f => f.name).Nodup)
    (hres : ∀ fid f mf, findHIRFunc tab fid = some f → lowerFunc f = some mf →
      findFunc prog fid.name = some mf)
    {r : HIR.Expr} (hev : evalHIR 256 henv (.app fid args) = some r) :
    ∃ (fenvMid : FullEnv) (wC : Value),
      execInstrsCall prog (fuelM + 1) none fenv
        (ias ++ [.call (some s1) f.name.name vs.reverse]) = some fenvMid ∧
      r = HIR.Expr.lit wC ∧ fenvMid.env s1 = some wC ∧
      fenvMid.store = fenv.store ∧ RelEnv henv ρ fenvMid.env ∧
      (∀ u, u < supply → fenvMid.env u = fenv.env u) := by
  have hev256 : evalHIR (255 + 1) henv (.app fid args) = some r := hev
  obtain ⟨params, body, argv, hfn, hargsMap⟩ := evalHIR_app_lam hev256
  obtain ⟨f', hmem', hname', hparams', hbody'⟩ := hlam _ _ _ hfn
  have hfeq : f = f' := findHIRFunc_unique hnodup hfind hmem' hname'
  subst hfeq
  have hlenMap : argv.length = args.length := mapM_some_length hargsMap
  have harity : args.length = params.length := by rw [← hparams', hguard.1]
  have hlen : params.length = argv.length := by
    rw [← hparams', hguard.1]
    exact hlenMap.symm
  have hblen : (appBinds params argv).length = params.length :=
    appBinds_length hlen
  have hunfold := evalHIR_app_unfold hfn hargsMap harity
    (rfl : appBinds params argv = appBinds params argv) hblen
  rw [hev256] at hunfold
  have heval : evalHIR 255 (appBinds params argv ++ henv) body = some r :=
    hunfold.symm
  obtain ⟨fenv1, argvW, hexecFull, hstoreArgs, hargvEq, hmapW, hrel1⟩ :=
    lowerArgs_agree_vals ρ supply args vs ias s1 hargs hf henv fenv hrel
      255 argv hargsMap
  have hlenW : argvW.length = params.length := by
    rw [hlen, hargvEq, List.length_map]
  have hnd : params.Nodup := by
    rw [← hparams']
    exact hndp f hmem'
  obtain ⟨mfC, hlowC⟩ := mapM_mem_some hmap (findHIRFunc_mem hfind)
  obtain ⟨vC, isC, sC, τC, hleC, hnoC, hinfC, hshapeC⟩ := lowerFunc_inv hlowC
  rw [hparams', hbody'] at hleC
  have hfname : f.name.name = fid.name :=
    congrArg HIR.Id.name (findHIRFunc_name hfind)
  have hfindProg : findFunc prog f.name.name = some mfC := by
    have h1 := hres fid f mfC hfind hlowC
    rwa [← hfname] at h1
  have hbindLen : ((List.range' 1 params.length).map
      (fun (x : ValId) => (x, Typ.unitType))).length =
      (argvW.reverse).length := by
    simp [List.length_map, List.length_range', List.length_reverse, hlenW]
  obtain ⟨envCal, hbind⟩ := bindCallArgs_some_of_length hbindLen
  have hps : mfC.params = ((List.range' 1 params.length).map
      (fun (x : ValId) => (x, Typ.unitType))) := by rw [hshapeC, hparams']
  have hbindM : bindCallArgs mfC.params argvW.reverse = some envCal := by
    rw [hps]
    exact hbind
  have hmapWRev : vs.reverse.mapM fenv1.env = some argvW.reverse :=
    mapM_reverse_some hmapW
  have hblocks : mfC.blocks =
      [⟨0, [.const 0 .unit] ++ isC, .return_ vC⟩] := by rw [hshapeC]
  have hentryBlock : findBlock mfC mfC.entry =
      some (⟨0, [.const 0 .unit] ++ isC, .return_ vC⟩ : MIR.Block) := by
    rw [hshapeC]
    rfl
  obtain ⟨wC, hrw, hrunBlock⟩ :=
    callee_agree (fuelM := fuelM) hleC hnd hargvEq hlen henv heval
      fenv1.store envCal hbind hblocks rfl
  have hrunStep : execInstrsCall prog (fuelM + 1) none fenv1
      [.call (some s1) f.name.name vs.reverse] =
      some ⟨fenv1.env.update s1 wC, fenv1.store⟩ :=
    execInstrsCall_call_step prog (fuelM + 1) none fenv1 f.name.name
      vs.reverse (some s1) mfC argvW.reverse envCal _ wC hfindProg
      hmapWRev hbindM hentryBlock hrunBlock
  have hpureArgs : ∀ i ∈ ias, IsPure i :=
    lowerArgs_isPure ρ supply args vs ias s1 hargs
  have hdefArgs : ∀ d, d ∈ ias.flatMap defOf → supply ≤ d :=
    lowerArgs_defs_gt ρ supply args vs ias s1 hargs
  have hexecArgs : execInstrsCall prog (fuelM + 1) none fenv ias =
      some fenv1 :=
    execInstrsCall_pure_prefix prog (fuelM + 1) fenv ias hpureArgs fenv1
      hexecFull
  have hexecPre : execInstrsCall prog (fuelM + 1) none fenv
      (ias ++ [.call (some s1) f.name.name vs.reverse]) =
      some ⟨fenv1.env.update s1 wC, fenv1.store⟩ := by
    simp only [execInstrsCall_append, hexecArgs, hrunStep]
  have hs1 : supply ≤ s1 := lowerArgs_mono ρ supply args vs ias s1 hargs
  have hrelMid : RelEnv henv ρ (fenv1.env.update s1 wC) := by
    intro j u hlook
    obtain ⟨w, hlookB, hreg⟩ := hrel1 j u hlook
    have hmem : (j, u) ∈ ρ := rhoLookup_some_mem ρ j u hlook
    have hne : u ≠ s1 := by
      have hlt : u < supply := hf j u hmem
      exact fun hcon => (Nat.not_lt.mpr hs1) (hcon ▸ hlt)
    refine ⟨w, hlookB, ?_⟩
    rw [envUpdate_other hne]
    exact hreg
  have hpresMid : ∀ u, u < supply →
      (⟨fenv1.env.update s1 wC, fenv1.store⟩ : FullEnv).env u =
        fenv.env u := by
    intro u hu
    have hne : u ≠ s1 := fun hcon => (Nat.not_lt.mpr hs1) (hcon ▸ hu)
    show (fenv1.env.update s1 wC) u = fenv.env u
    rw [envUpdate_other hne]
    exact (execInstrsFull_preservLow supply fenv ias fenv1 hpureArgs
      hdefArgs hexecFull u hu).1
  refine ⟨⟨fenv1.env.update s1 wC, fenv1.store⟩, wC, hexecPre, hrw,
    envUpdate_self, hstoreArgs, hrelMid, hpresMid⟩

/-! ## Straightness from lowering success -/

/-- A successful lowering is straight: every arm that can succeed has a
matching `IsStraight` constructor (the operator arms keep their `≠ none`
side conditions), and every failing arm reduces the hypothesis to `False`.
Proved by `lowerExpr.mutual_induct`, the same inductor as `lower_total` —
plain `induction` does not support the nested `HIR.Expr`. The block
cons/singleton cases feed their head/tail IHs directly, so no `mutual`
block is needed. -/
theorem lower_isStraight :
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (e : HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → IsStraight e) ∧
    (∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (es : List HIR.Expr)
      (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → ∀ e ∈ es, IsStraight e) := by
  refine lowerExpr.mutual_induct
    (motive_1 := fun ρ supply e => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerExpr ρ supply e = some (v, is, s') → IsStraight e)
    (motive_2 := fun ρ supply es => ∀ (v : ValId) (is : List Instr) (s' : Nat),
      lowerBlock ρ supply es = some (v, is, s') → ∀ e ∈ es, IsStraight e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- lit
    intro ρ supply v v' is' s' _h
    exact .lit v
  · -- var
    intro ρ supply id v' is' s' _h
    exact .var id
  · -- unop, success
    intro ρ supply op e u v0 ie s1 h1 h2 ih v' is' s' _h
    exact .unop op e (by rw [h2]; exact Option.some_ne_none _) (ih v0 ie s1 h1)
  · -- unop, fail
    intro ρ supply op e hfail ih v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toUnOp op with
    | none => simp at h
    | some u =>
        cases he : lowerExpr ρ supply e with
        | none => simp at h
        | some p => exact False.elim (hfail u p.1 p.2.1 p.2.2 hto he)
  · -- binop, success
    intro ρ supply op a b bo va ia s1 h1 h2 vb ib s2 h3 ihA ihB v' is' s' _h
    exact .binop op a b (by rw [h2]; exact Option.some_ne_none _)
      (ihA va ia s1 h1) (ihB vb ib s2 h3)
  · -- binop, body fail
    intro ρ supply op a b bo va ia s1 h1 h2 h3 ihA ihB v' is' s' h
    simp only [lowerExpr, h1, h2, h3] at h
    simp at h
  · -- binop, operator fail
    intro ρ supply op a b hfail ihA v' is' s' h
    simp only [lowerExpr] at h
    cases hto : toBinOp op with
    | none => simp at h
    | some bo =>
        cases ha : lowerExpr ρ supply a with
        | none => simp at h
        | some p => exact False.elim (hfail bo p.1 p.2.1 p.2.2 hto ha)
  · -- let, success
    intro ρ supply id init body va ia s1 h1 vb ib s2 h2 ihI ihB v' is' s' _h
    exact .let_ id init body (ihI va ia s1 h1) (ihB vb ib s2 h2)
  · -- let, body fail
    intro ρ supply id init body va ia s1 h1 h2 ihI ihB v' is' s' h
    simp only [lowerExpr, h1, h2] at h
    simp at h
  · -- let, init fail
    intro ρ supply id init body hfail ihI v' is' s' h
    simp only [lowerExpr, hfail] at h
    simp at h
  · -- block delegate
    intro ρ supply es ih v' is' s' h
    simp only [lowerExpr] at h
    exact .block es (ih v' is' s' h)
  · -- non-lowering constructors
    intro t ρ supply d1 d2 d3 d4 d5 d6 v' is' s' h
    cases t with
    | lit v => exact False.elim (d1 v rfl)
    | var id => exact False.elim (d2 id rfl)
    | unop op e => exact False.elim (d3 op e rfl)
    | binop op a b => exact False.elim (d4 op a b rfl)
    | «let» id a b => exact False.elim (d5 id a b rfl)
    | block es => exact False.elim (d6 es rfl)
    | app f args => simp [lowerExpr] at h
    | lam p b => simp [lowerExpr] at h
    | ifThenElse c t f => simp [lowerExpr] at h
    | whileLoop c b => simp [lowerExpr] at h
    | «match» s a => simp [lowerExpr] at h
    | infer => simp [lowerExpr] at h
  · -- block, empty
    intro ρ supply v' is' s' _h e hmem
    simp at hmem
  · -- block, singleton
    intro ρ supply e ih v' is' s' h x hx
    simp only [lowerBlock] at h
    cases he : lowerExpr ρ supply e with
    | none => simp [he] at h
    | some p =>
        obtain ⟨va, ia, s1⟩ := p
        rcases List.mem_cons.mp hx with rfl | hnil
        · exact ih va ia s1 he
        · simp at hnil
  · -- block, cons
    intro ρ supply e es hne vb ib s2 h1 vb' ib' s2' h2 ihE ihEs v' is' s' _h x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ihE vb ib s2 h1
    · exact ihEs vb' ib' s2' h2 x hmem
  · -- block, tail fail
    intro ρ supply e es hne vb ib s2 h1 h2 ihE ihEs v' is' s' h
    simp only [lowerBlock, h1, h2] at h
    simp at h
  · -- block, head fail
    intro ρ supply e es hne hfail ihE v' is' s' h
    simp only [lowerBlock, hfail] at h
    simp at h

/-- A successful block lowering has straight elements. -/
theorem lowerBlock_isStraight (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (es : List HIR.Expr) (v : ValId) (is : List Instr) (s' : Nat)
    (h : lowerBlock ρ supply es = some (v, is, s')) :
    ∀ e ∈ es, IsStraight e :=
  lower_isStraight.2 ρ supply es v is s' h

/-! ## Statement induction: the call prefix composes -/

/-- Statement-level totality for the call fragment: when `lowerCallStmts`
succeeds and the HIR statement machine reaches a value, the emitted
instruction sequence runs through the call-aware executor to a final
environment holding that value in the result register, leaving the store
alone, and agreeing with the source environment. Non-call positions go
through `lower_total.1` (straightness comes from `lower_isStraight`,
purity from `lower_isPure`, lifting via `execInstrsCall_pure_prefix`);
call positions go through `callStep_agree`. -/
theorem lowerCallStmts_total (tab : List Func) (prog : MIR.Program)
    (funcsMIR : List MIR.Func) (fuelM : Nat)
    (hmap : tab.mapM lowerFunc = some funcsMIR)
    (hndp : ∀ f ∈ tab, f.params.Nodup)
    (hnodup : (tab.map fun f => f.name).Nodup)
    (hres : ∀ (fid : HIR.Id) (f : Func) (mf : MIR.Func),
      findHIRFunc tab fid = some f → lowerFunc f = some mf →
      findFunc prog fid.name = some mf) :
    ∀ (ρ : List (HIR.Id × ValId)) (supply : Nat) (lastVal : ValId)
      (ss : List HIR.Stmt) (ρ' : List (HIR.Id × ValId)) (v : ValId)
      (is : List Instr) (s' : Nat),
      lowerCallStmts tab ρ supply lastVal ss = some (ρ', v, is, s') →
      FreshAbove ρ supply → lastVal < supply →
      ∀ (acc : Value) (henv : HEnv) (fenv : FullEnv),
      LamEnv tab henv →
      RelEnv henv ρ fenv.env → fenv.env lastVal = some acc →
      ∀ (fuel : Nat) (henv' : HEnv) (out : HFlow) (w : Value),
      runHIRStmts fuel henv ss (.value (.lit acc)) = (out, henv') →
      runValue? out = some (.lit w) →
      ∃ fenv', execInstrsCall prog (fuelM + 1) none fenv is = some fenv' ∧
        fenv'.env v = some w ∧ fenv'.store = fenv.store ∧
        RelEnv henv' ρ' fenv'.env := by
  intro ρ supply lastVal ss
  induction ss generalizing ρ supply lastVal with
  | nil =>
    intro ρ' v is s' h _hf _hlast acc henv fenv _hlam hrel hacc fuel henv' out w hrun hval
    simp only [lowerCallStmts] at h
    have hp : (ρ, lastVal, ([] : List Instr), supply) = (ρ', v, is, s') :=
      Option.some.inj h
    have hρ' : ρ' = ρ :=
      (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
    have hv : v = lastVal :=
      (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
    have his : is = [] :=
      (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
    cases fuel with
    | zero =>
      have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
      rw [hout] at hval
      simp [runValue?] at hval
    | succ f =>
      have hstep : runHIRStmts (Nat.succ f) henv ([] : List HIR.Stmt) (.value (.lit acc))
          = (.value (.lit acc), henv) := rfl
      rw [hstep] at hrun
      have hout : out = .value (.lit acc) := (congrArg Prod.fst hrun).symm
      have hhenv : henv' = henv := (congrArg Prod.snd hrun).symm
      subst hout
      have hw : w = acc := (HIR.Expr.lit.inj (Option.some.inj hval)).symm
      refine ⟨fenv, ?_, ?_, rfl, ?_⟩
      · rw [his]; rfl
      · rw [hv, hw]; exact hacc
      · rw [hρ', hhenv]; exact hrel
  | cons st rest ih =>
    cases st with
    | exprStmt e =>
      intro ρ' v is s' h hf hlast acc henv fenv hlam hrel hacc fuel henv' out w hrun hval
      by_cases happ : ∃ fid args, e = .app fid args
      · obtain ⟨fid, args, rfl⟩ := happ
        rw [lowerCallStmts.eq_2] at h
        simp at h
      · have hneg : ∀ (fid : HIR.Id) (args : List HIR.Expr),
            e = .app fid args → False := by
          intro fid args hcon
          exact happ ⟨fid, args, hcon⟩
        rw [lowerCallStmts.eq_3 _ _ _ _ _ _ hneg] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerCallStmts tab ρ s1 v0 rest with
          | none => rw [hr] at h; simp at h
          | some q =>
            obtain ⟨ρ'', v', ie', s2⟩ := q
            rw [hr] at h
            simp only [] at h
            have hp : (ρ'', v', ie ++ ie', s2) = (ρ', v, is, s') := Option.some.inj h
            have hρ' : ρ' = ρ'' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
            have hv : v = v' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
            have his : is = ie ++ ie' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
            cases fuel with
            | zero =>
              have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
              rw [hout] at hval
              simp [runValue?] at hval
            | succ f =>
              have hstep : runHIRStmts (Nat.succ f) henv (.exprStmt e :: rest)
                  (.value (.lit acc)) =
                  (match evalHIR 256 henv e with
                    | none => (HFlow.stuck, henv)
                    | some v => runHIRStmts f henv rest (.value v)) := rfl
              rw [hstep] at hrun
              cases hev : evalHIR 256 henv e with
              | none =>
                rw [hev] at hrun
                have hout : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hout] at hval
                simp [runValue?] at hval
              | some r =>
                rw [hev] at hrun
                have hstr : IsStraight e := lower_isStraight.1 ρ supply e v0 ie s1 he
                obtain ⟨fenv1, hexec1, hstore1, wE, hrE, hregE⟩ :=
                  (lower_total.1 ρ supply e v0 ie s1 he hstr hf henv fenv hrel 256 r hev).2
                rw [hrE] at hrun
                have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                have hf1 : FreshAbove ρ s1 := FreshAbove.mono ρ supply s1 hs1 hf
                have hrel1 : RelEnv henv ρ fenv1.env :=
                  RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1 hrel hf hexec1
                have hlast1 : v0 < s1 := lower_result_lt.1 ρ supply e v0 ie s1 he hf
                have hpure : ∀ i ∈ ie, IsPure i := lower_isPure.1 ρ supply e v0 ie s1 he
                have hexecCall1 : execInstrsCall prog (fuelM + 1) none fenv ie =
                    some fenv1 :=
                  execInstrsCall_pure_prefix prog (fuelM + 1) fenv ie hpure fenv1 hexec1
                obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
                  ih ρ s1 v0 ρ'' v' ie' s2 hr hf1 hlast1 wE henv fenv1 hlam hrel1 hregE
                    f henv' out w hrun hval
                refine ⟨fenv', ?_, ?_, ?_, ?_⟩
                · rw [his, execInstrsCall_append, hexecCall1]; exact hexec'
                · rw [hv]; exact hreg'
                · rw [hstore', hstore1]
                · rw [hρ']; exact hrel'
    | varDecl id τ init =>
      intro ρ' v is s' h hf hlast acc henv fenv hlam hrel hacc fuel henv' out w hrun hval
      by_cases happ : ∃ fid args, init = .app fid args
      · obtain ⟨fid, args, rfl⟩ := happ
        rw [lowerCallStmts.eq_4] at h
        cases hf0 : findHIRFunc tab fid with
        | none => rw [hf0] at h; simp at h
        | some f =>
          rw [hf0] at h
          simp only [] at h
          by_cases hguard : f.params.length = args.length ∧ exprNoApp f.body = true
          · rw [if_pos hguard] at h
            cases ha : lowerArgs ρ supply args with
            | none => rw [ha] at h; simp at h
            | some p =>
              obtain ⟨vs, ias, s1⟩ := p
              rw [ha] at h
              simp only [] at h
              cases hr : lowerCallStmts tab ((id, s1) :: ρ) (s1 + 1) lastVal rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                obtain ⟨ρ'', v', ia', s2⟩ := q
                rw [hr] at h
                simp only [] at h
                have hp : (ρ'', v', (ias ++ [.call (some s1) f.name.name vs.reverse]) ++ ia', s2) =
                    (ρ', v, is, s') := Option.some.inj h
                have hρ' : ρ' = ρ'' :=
                  (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
                have hv : v = v' :=
                  (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
                have his : is = (ias ++ [.call (some s1) f.name.name vs.reverse]) ++ ia' :=
                  (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
                cases fuel with
                | zero =>
                  have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
                  rw [hout] at hval
                  simp [runValue?] at hval
                | succ ff =>
                  have hstep : runHIRStmts (Nat.succ ff) henv
                      (.varDecl id τ (.app fid args) :: rest) (.value (.lit acc)) =
                      (match evalHIR 256 henv (.app fid args) with
                        | none => (HFlow.stuck, henv)
                        | some v => runHIRStmts ff ((id, v) :: henv) rest
                            (.value (.lit acc))) := rfl
                  rw [hstep] at hrun
                  cases hev : evalHIR 256 henv (.app fid args) with
                  | none =>
                    rw [hev] at hrun
                    have hout : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hout] at hval
                    simp [runValue?] at hval
                  | some r =>
                    rw [hev] at hrun
                    obtain ⟨fenvMid, wC, hexecPre, hrw, hregC, hstoreC, hrelMid, hpresMid⟩ :=
                      callStep_agree tab ρ supply fid args vs ias s1 ha henv fenv hrel hf hlam
                        hf0 hguard prog funcsMIR fuelM hmap hndp hnodup hres hev
                    rw [hrw] at hrun
                    have hs1 : supply ≤ s1 := lowerArgs_mono ρ supply args vs ias s1 ha
                    have hf1 : FreshAbove ((id, s1) :: ρ) (s1 + 1) := by
                      intro j u hmem
                      rcases List.mem_cons.mp hmem with heq | hmem
                      · cases heq
                        exact Nat.lt_succ_self s1
                      · exact Nat.lt_of_lt_of_le
                          (Nat.lt_of_lt_of_le (hf j u hmem) hs1) (Nat.le_succ s1)
                    have hrel2 : RelEnv ((id, .lit wC) :: henv) ((id, s1) :: ρ)
                        fenvMid.env := by
                      intro j u hlook
                      by_cases hid : id = j
                      · subst hid
                        have hu : u = s1 := by
                          have hh : rhoLookup ((id, s1) :: ρ) id = some s1 :=
                            rhoLookup_cons_head id s1 ρ
                          rw [hh] at hlook
                          exact (Option.some.inj hlook).symm
                        subst hu
                        exact ⟨wC, by simp [lookupHEnv], hregC⟩
                      · have hlook' : rhoLookup ρ j = some u := by
                          rw [rhoLookup_cons_ne hid] at hlook
                          exact hlook
                        obtain ⟨w', hlookH, hreg⟩ := hrelMid j u hlook'
                        exact ⟨w', by rw [lookupHEnv_cons_ne hid]; exact hlookH, hreg⟩
                    have hacc1 : fenvMid.env lastVal = some acc := by
                      rw [hpresMid lastVal hlast]; exact hacc
                    have hlast1 : lastVal < s1 + 1 :=
                      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlast hs1) (Nat.le_succ s1)
                    have hlam1 : LamEnv tab ((id, HIR.Expr.lit wC) :: henv) :=
                      LamEnv_push_lit hlam
                    obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
                      ih ((id, s1) :: ρ) (s1 + 1) lastVal ρ'' v' ia' s2 hr hf1 hlast1 acc
                        ((id, .lit wC) :: henv) fenvMid hlam1 hrel2 hacc1 ff henv' out w hrun hval
                    refine ⟨fenv', ?_, ?_, ?_, ?_⟩
                    · rw [his, execInstrsCall_append, hexecPre]; exact hexec'
                    · rw [hv]; exact hreg'
                    · rw [hstore', hstoreC]
                    · rw [hρ']; exact hrel'
          · rw [if_neg hguard] at h; simp at h
      · have hneg : ∀ (fid : HIR.Id) (args : List HIR.Expr),
            init = .app fid args → False := by
          intro fid args hcon
          exact happ ⟨fid, args, hcon⟩
        rw [lowerCallStmts.eq_5 _ _ _ _ _ _ _ _ hneg] at h
        cases he : lowerExpr ρ supply init with
        | none => rw [he] at h; simp at h
        | some p =>
          obtain ⟨va, ia, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerCallStmts tab ((id, va) :: ρ) s1 lastVal rest with
          | none => rw [hr] at h; simp at h
          | some q =>
            obtain ⟨ρ'', v', ia', s2⟩ := q
            rw [hr] at h
            simp only [] at h
            have hp : (ρ'', v', ia ++ ia', s2) = (ρ', v, is, s') := Option.some.inj h
            have hρ' : ρ' = ρ'' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
            have hv : v = v' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
            have his : is = ia ++ ia' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
            cases fuel with
            | zero =>
              have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
              rw [hout] at hval
              simp [runValue?] at hval
            | succ f =>
              have hstep : runHIRStmts (Nat.succ f) henv (.varDecl id τ init :: rest)
                  (.value (.lit acc)) =
                  (match evalHIR 256 henv init with
                    | none => (HFlow.stuck, henv)
                    | some v => runHIRStmts f ((id, v) :: henv) rest (.value (.lit acc))) := rfl
              rw [hstep] at hrun
              cases hev : evalHIR 256 henv init with
              | none =>
                rw [hev] at hrun
                have hout : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hout] at hval
                simp [runValue?] at hval
              | some r =>
                rw [hev] at hrun
                have hstr : IsStraight init :=
                  lower_isStraight.1 ρ supply init va ia s1 he
                obtain ⟨fenv1, hexec1, hstore1, wE, hrE, hregE⟩ :=
                  (lower_total.1 ρ supply init va ia s1 he hstr hf henv fenv hrel 256 r hev).2
                rw [hrE] at hrun
                have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                have hva : va < s1 := lower_result_lt.1 ρ supply init va ia s1 he hf
                have hf1 : FreshAbove ((id, va) :: ρ) s1 := by
                  intro j u hmem
                  rcases List.mem_cons.mp hmem with heq | hmem
                  · cases heq
                    exact hva
                  · exact Nat.lt_of_lt_of_le (hf j u hmem) hs1
                have hrel1 : RelEnv henv ρ fenv1.env :=
                  RelEnv_exec henv ρ supply init va ia s1 he fenv fenv1 hrel hf hexec1
                have hrel2 : RelEnv ((id, .lit wE) :: henv) ((id, va) :: ρ) fenv1.env := by
                  intro j u hlook
                  by_cases hid : id = j
                  · subst hid
                    have hu : u = va := by
                      have hh : rhoLookup ((id, va) :: ρ) id = some va :=
                        rhoLookup_cons_head id va ρ
                      rw [hh] at hlook
                      exact (Option.some.inj hlook).symm
                    subst hu
                    exact ⟨wE, by simp [lookupHEnv], hregE⟩
                  · have hlook' : rhoLookup ρ j = some u := by
                      rw [rhoLookup_cons_ne hid] at hlook
                      exact hlook
                    obtain ⟨w', hlookH, hreg⟩ := hrel1 j u hlook'
                    exact ⟨w', by rw [lookupHEnv_cons_ne hid]; exact hlookH, hreg⟩
                have hacc1 : fenv1.env lastVal = some acc := by
                  rw [lower_preserv_regs ρ supply init va ia s1 he fenv fenv1 hexec1 lastVal hlast]
                  exact hacc
                have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
                have hpure : ∀ i ∈ ia, IsPure i := lower_isPure.1 ρ supply init va ia s1 he
                have hexecCall1 : execInstrsCall prog (fuelM + 1) none fenv ia =
                    some fenv1 :=
                  execInstrsCall_pure_prefix prog (fuelM + 1) fenv ia hpure fenv1 hexec1
                have hlam1 : LamEnv tab ((id, HIR.Expr.lit wE) :: henv) :=
                  LamEnv_push_lit hlam
                obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
                  ih ((id, va) :: ρ) s1 lastVal ρ'' v' ia' s2 hr hf1 hlast1 acc
                    ((id, .lit wE) :: henv) fenv1 hlam1 hrel2 hacc1 f henv' out w hrun hval
                refine ⟨fenv', ?_, ?_, ?_, ?_⟩
                · rw [his, execInstrsCall_append, hexecCall1]; exact hexec'
                · rw [hv]; exact hreg'
                · rw [hstore', hstore1]
                · rw [hρ']; exact hrel'
    | assign id e =>
      intro ρ' v is s' h hf hlast acc henv fenv hlam hrel hacc fuel henv' out w hrun hval
      by_cases happ : ∃ fid args, e = .app fid args
      · obtain ⟨fid, args, rfl⟩ := happ
        rw [lowerCallStmts.eq_6] at h
        cases hf0 : findHIRFunc tab fid with
        | none => rw [hf0] at h; simp at h
        | some f =>
          rw [hf0] at h
          simp only [] at h
          by_cases hguard : f.params.length = args.length ∧ exprNoApp f.body = true
          · rw [if_pos hguard] at h
            cases ha : lowerArgs ρ supply args with
            | none => rw [ha] at h; simp at h
            | some p =>
              obtain ⟨vs, ias, s1⟩ := p
              rw [ha] at h
              simp only [] at h
              cases hr : lowerCallStmts tab (updAssoc ρ id s1) (s1 + 1) lastVal rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                obtain ⟨ρ'', v', ia', s2⟩ := q
                rw [hr] at h
                simp only [] at h
                have hp : (ρ'', v', (ias ++ [.call (some s1) f.name.name vs.reverse]) ++ ia', s2) =
                    (ρ', v, is, s') := Option.some.inj h
                have hρ' : ρ' = ρ'' :=
                  (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
                have hv : v = v' :=
                  (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
                have his : is = (ias ++ [.call (some s1) f.name.name vs.reverse]) ++ ia' :=
                  (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
                cases fuel with
                | zero =>
                  have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
                  rw [hout] at hval
                  simp [runValue?] at hval
                | succ ff =>
                  have hstep : runHIRStmts (Nat.succ ff) henv
                      (.assign id (.app fid args) :: rest) (.value (.lit acc)) =
                      (match evalHIR 256 henv (.app fid args) with
                        | none => (HFlow.stuck, henv)
                        | some v => runHIRStmts ff (updateHEnv henv id v) rest
                            (.value (.lit acc))) := rfl
                  rw [hstep] at hrun
                  cases hev : evalHIR 256 henv (.app fid args) with
                  | none =>
                    rw [hev] at hrun
                    have hout : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hout] at hval
                    simp [runValue?] at hval
                  | some r =>
                    rw [hev] at hrun
                    obtain ⟨fenvMid, wC, hexecPre, hrw, hregC, hstoreC, hrelMid, hpresMid⟩ :=
                      callStep_agree tab ρ supply fid args vs ias s1 ha henv fenv hrel hf hlam
                        hf0 hguard prog funcsMIR fuelM hmap hndp hnodup hres hev
                    rw [hrw] at hrun
                    have hs1 : supply ≤ s1 := lowerArgs_mono ρ supply args vs ias s1 ha
                    have hf1 : FreshAbove (updAssoc ρ id s1) (s1 + 1) := by
                      intro j u hmem
                      rcases updAssoc_mem ρ id s1 j u hmem with ⟨-, hwu⟩ | hmem
                      · rw [hwu]
                        exact Nat.lt_succ_self s1
                      · exact Nat.lt_of_lt_of_le
                          (Nat.lt_of_lt_of_le (hf j u hmem) hs1) (Nat.le_succ s1)
                    have hrel2 : RelEnv (updateHEnv henv id (.lit wC)) (updAssoc ρ id s1)
                        fenvMid.env :=
                      RelEnv_update ρ henv fenvMid.env id s1 wC hrelMid hregC
                    have hacc1 : fenvMid.env lastVal = some acc := by
                      rw [hpresMid lastVal hlast]; exact hacc
                    have hlast1 : lastVal < s1 + 1 :=
                      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlast hs1) (Nat.le_succ s1)
                    have hlam1 : LamEnv tab (updateHEnv henv id (HIR.Expr.lit wC)) :=
                      LamEnv_update_lit hlam
                    obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
                      ih (updAssoc ρ id s1) (s1 + 1) lastVal ρ'' v' ia' s2 hr hf1 hlast1 acc
                        (updateHEnv henv id (.lit wC)) fenvMid hlam1 hrel2 hacc1 ff henv' out w hrun hval
                    refine ⟨fenv', ?_, ?_, ?_, ?_⟩
                    · rw [his, execInstrsCall_append, hexecPre]; exact hexec'
                    · rw [hv]; exact hreg'
                    · rw [hstore', hstoreC]
                    · rw [hρ']; exact hrel'
          · rw [if_neg hguard] at h; simp at h
      · have hneg : ∀ (fid : HIR.Id) (args : List HIR.Expr),
            e = .app fid args → False := by
          intro fid args hcon
          exact happ ⟨fid, args, hcon⟩
        rw [lowerCallStmts.eq_7 _ _ _ _ _ _ _ hneg] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerCallStmts tab (updAssoc ρ id v0) s1 lastVal rest with
          | none => rw [hr] at h; simp at h
          | some q =>
            obtain ⟨ρ'', v', ie', s2⟩ := q
            rw [hr] at h
            simp only [] at h
            have hp : (ρ'', v', ie ++ ie', s2) = (ρ', v, is, s') := Option.some.inj h
            have hρ' : ρ' = ρ'' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
            have hv : v = v' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
            have his : is = ie ++ ie' :=
              (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
            cases fuel with
            | zero =>
              have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
              rw [hout] at hval
              simp [runValue?] at hval
            | succ f =>
              have hstep : runHIRStmts (Nat.succ f) henv (.assign id e :: rest)
                  (.value (.lit acc)) =
                  (match evalHIR 256 henv e with
                    | none => (HFlow.stuck, henv)
                    | some v => runHIRStmts f (updateHEnv henv id v) rest
                        (.value (.lit acc))) := rfl
              rw [hstep] at hrun
              cases hev : evalHIR 256 henv e with
              | none =>
                rw [hev] at hrun
                have hout : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hout] at hval
                simp [runValue?] at hval
              | some r =>
                rw [hev] at hrun
                have hstr : IsStraight e := lower_isStraight.1 ρ supply e v0 ie s1 he
                obtain ⟨fenv1, hexec1, hstore1, wE, hrE, hregE⟩ :=
                  (lower_total.1 ρ supply e v0 ie s1 he hstr hf henv fenv hrel 256 r hev).2
                rw [hrE] at hrun
                have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                have hva : v0 < s1 := lower_result_lt.1 ρ supply e v0 ie s1 he hf
                have hf1 : FreshAbove (updAssoc ρ id v0) s1 := by
                  intro j u hmem
                  rcases updAssoc_mem ρ id v0 j u hmem with ⟨-, hwu⟩ | hmem
                  · rw [hwu]
                    exact hva
                  · exact Nat.lt_of_lt_of_le (hf j u hmem) hs1
                have hrel1 : RelEnv henv ρ fenv1.env :=
                  RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1 hrel hf hexec1
                have hrel2 : RelEnv (updateHEnv henv id (.lit wE)) (updAssoc ρ id v0)
                    fenv1.env :=
                  RelEnv_update ρ henv fenv1.env id v0 wE hrel1 hregE
                have hacc1 : fenv1.env lastVal = some acc := by
                  rw [lower_preserv_regs ρ supply e v0 ie s1 he fenv fenv1 hexec1 lastVal hlast]
                  exact hacc
                have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
                have hpure : ∀ i ∈ ie, IsPure i := lower_isPure.1 ρ supply e v0 ie s1 he
                have hexecCall1 : execInstrsCall prog (fuelM + 1) none fenv ie =
                    some fenv1 :=
                  execInstrsCall_pure_prefix prog (fuelM + 1) fenv ie hpure fenv1 hexec1
                have hlam1 : LamEnv tab (updateHEnv henv id (HIR.Expr.lit wE)) :=
                  LamEnv_update_lit hlam
                obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
                  ih (updAssoc ρ id v0) s1 lastVal ρ'' v' ie' s2 hr hf1 hlast1 acc
                    (updateHEnv henv id (.lit wE)) fenv1 hlam1 hrel2 hacc1 f henv' out w hrun hval
                refine ⟨fenv', ?_, ?_, ?_, ?_⟩
                · rw [his, execInstrsCall_append, hexecCall1]; exact hexec'
                · rw [hv]; exact hreg'
                · rw [hstore', hstore1]
                · rw [hρ']; exact hrel'
    | returnStmt e =>
      intro ρ' v is s' h hf hlast acc henv fenv hlam hrel hacc fuel henv' out w hrun hval
      by_cases happ : ∃ fid args, e = .app fid args
      · obtain ⟨fid, args, rfl⟩ := happ
        rw [lowerCallStmts.eq_8] at h
        cases hf0 : findHIRFunc tab fid with
        | none => rw [hf0] at h; simp at h
        | some f =>
          rw [hf0] at h
          simp only [] at h
          by_cases hguard : f.params.length = args.length ∧ exprNoApp f.body = true
          · rw [if_pos hguard] at h
            cases ha : lowerArgs ρ supply args with
            | none => rw [ha] at h; simp at h
            | some p =>
              obtain ⟨vs, ias, s1⟩ := p
              rw [ha] at h
              simp only [] at h
              have hp : (ρ, s1, ias ++ [.call (some s1) f.name.name vs.reverse], s1 + 1) =
                  (ρ', v, is, s') := Option.some.inj h
              have hρ' : ρ' = ρ :=
                (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
              have hv : v = s1 :=
                (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
              have his : is = ias ++ [.call (some s1) f.name.name vs.reverse] :=
                (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
              cases fuel with
              | zero =>
                have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
                rw [hout] at hval
                simp [runValue?] at hval
              | succ ff =>
                have hstep : runHIRStmts (Nat.succ ff) henv
                    (.returnStmt (.app fid args) :: rest) (.value (.lit acc)) =
                    (match evalHIR 256 henv (.app fid args) with
                      | none => (HFlow.stuck, henv)
                      | some v => (HFlow.returned v, henv)) := rfl
                rw [hstep] at hrun
                cases hev : evalHIR 256 henv (.app fid args) with
                | none =>
                  rw [hev] at hrun
                  have hout : out = .stuck := (congrArg Prod.fst hrun).symm
                  rw [hout] at hval
                  simp [runValue?] at hval
                | some r =>
                  rw [hev] at hrun
                  have hout : out = .returned r := (congrArg Prod.fst hrun).symm
                  have hhenv : henv' = henv := (congrArg Prod.snd hrun).symm
                  subst hout
                  have hrl : r = .lit w := Option.some.inj hval
                  obtain ⟨fenvMid, wC, hexecPre, hrw, hregC, hstoreC, hrelMid, _⟩ :=
                    callStep_agree tab ρ supply fid args vs ias s1 ha henv fenv hrel hf hlam
                      hf0 hguard prog funcsMIR fuelM hmap hndp hnodup hres hev
                  have hwC : wC = w := HIR.Expr.lit.inj (hrw.symm.trans hrl)
                  refine ⟨fenvMid, ?_, ?_, hstoreC, ?_⟩
                  · rw [his]; exact hexecPre
                  · rw [hv, ← hwC]; exact hregC
                  · rw [hρ', hhenv]; exact hrelMid
          · rw [if_neg hguard] at h; simp at h
      · have hneg : ∀ (fid : HIR.Id) (args : List HIR.Expr),
            e = .app fid args → False := by
          intro fid args hcon
          exact happ ⟨fid, args, hcon⟩
        rw [lowerCallStmts.eq_9 _ _ _ _ _ _ hneg] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
          obtain ⟨ve, ie, s1⟩ := p
          rw [he] at h
          simp only [Option.map_some] at h
          have hp : (ρ, ve, ie, s1) = (ρ', v, is, s') := Option.some.inj h
          have hρ' : ρ' = ρ :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.1) hp).symm
          have hv : v = ve :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.1) hp).symm
          have his : is = ie :=
            (congrArg (fun p : List (HIR.Id × ValId) × ValId × List Instr × Nat => p.2.2.1) hp).symm
          cases fuel with
          | zero =>
            have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
            rw [hout] at hval
            simp [runValue?] at hval
          | succ f =>
            have hstep : runHIRStmts (Nat.succ f) henv (.returnStmt e :: rest)
                (.value (.lit acc)) =
                (match evalHIR 256 henv e with
                  | none => (HFlow.stuck, henv)
                  | some v => (HFlow.returned v, henv)) := rfl
            rw [hstep] at hrun
            cases hev : evalHIR 256 henv e with
            | none =>
              rw [hev] at hrun
              have hout : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hout] at hval
              simp [runValue?] at hval
            | some r =>
              rw [hev] at hrun
              have hout : out = .returned r := (congrArg Prod.fst hrun).symm
              have hhenv : henv' = henv := (congrArg Prod.snd hrun).symm
              subst hout
              have hrl : r = .lit w := Option.some.inj hval
              have hstr : IsStraight e := lower_isStraight.1 ρ supply e ve ie s1 he
              obtain ⟨fenv', hexec', hstore', wE, hrE, hregE⟩ :=
                (lower_total.1 ρ supply e ve ie s1 he hstr hf henv fenv hrel 256 r hev).2
              have hwE : w = wE := by
                rw [hrl] at hrE
                exact HIR.Expr.lit.inj hrE
              subst hwE
              have hpure : ∀ i ∈ ie, IsPure i := lower_isPure.1 ρ supply e ve ie s1 he
              have hexecCall : execInstrsCall prog (fuelM + 1) none fenv ie =
                  some fenv' :=
                execInstrsCall_pure_prefix prog (fuelM + 1) fenv ie hpure fenv' hexec'
              refine ⟨fenv', ?_, ?_, hstore', ?_⟩
              · rw [his]; exact hexecCall
              · rw [hv]; exact hregE
              · rw [hρ', hhenv]
                exact RelEnv_exec henv ρ supply e ve ie s1 he fenv fenv' hrel hf hexec'
    | nop =>
      intro ρ' v is s' h hf hlast acc henv fenv hlam hrel hacc fuel henv' out w hrun hval
      rw [lowerCallStmts.eq_10] at h
      cases fuel with
      | zero =>
        have hout := runHIRStmts_zero_stuck henv _ _ henv' out hrun
        rw [hout] at hval
        simp [runValue?] at hval
      | succ f =>
        have hstep : runHIRStmts (Nat.succ f) henv (.nop :: rest) (.value (.lit acc))
            = runHIRStmts f henv rest (.value (.lit acc)) := rfl
        rw [hstep] at hrun
        exact ih ρ supply lastVal ρ' v is s' h hf hlast acc henv fenv hlam hrel hacc
          f henv' out w hrun hval
    | «break» =>
      intro ρ' v is s' h
      simp only [lowerCallStmts] at h
      simp at h
    | «continue» =>
      intro ρ' v is s' h
      simp only [lowerCallStmts] at h
      simp at h
    | whileLoop cond body =>
      intro ρ' v is s' h
      simp only [lowerCallStmts] at h
      simp at h
    | ifStmt cond th el =>
      intro ρ' v is s' h
      simp only [lowerCallStmts] at h
      simp at h
    | matchStmt scrut arms =>
      intro ρ' v is s' h
      simp only [lowerCallStmts] at h
      simp at h

/-! ## Program level: entry dispatch through the call executor -/

/-- Program-level correctness (C8c exit): when `lowerCallProg` accepts a
call program and the HIR statement machine reaches a literal value under
the table binding list, the entry dispatch through the call-aware executor
returns that same value. The HIR side runs under `lamEnv` (every applied
`lam` is a table entry by `lamEnv_self`); the MIR side runs the `"main"`
block (unit prologue plus the lowered statements) and returns its result
register. Machine failure still carries no claim about the source. -/
theorem lowerCallProg_correct (p : CallProg) (prog : MIR.Program)
    (store : Store) (h : lowerCallProg p = some prog)
    (_hok : CallProgOk p)
    (hndp : ∀ f ∈ p.funcs, f.params.Nodup)
    (hnodupId : (p.funcs.map fun f => f.name).Nodup)
    (hnodup : (p.funcs.map fun f => f.name.name).Nodup)
    (fuelM : Nat) (fuelH : Nat) (henv' : HEnv) (out : HFlow) (w : Value)
    (hrun : runHIRStmts fuelH (lamEnv p.funcs) p.main (.value (.lit .unit)) =
      (out, henv'))
    (hval : runValue? out = some (.lit w)) :
    ∃ mf : MIR.Func, findFunc prog "main" = some mf ∧
      execFuncCall prog (fuelM + 1) mf ⟨fun _ => none, store⟩ = some w := by
  simp only [lowerCallProg] at h
  cases hg : p.funcs.any (fun f => f.name.name == "main") with
  | true =>
    rw [if_pos hg] at h
    simp at h
  | false =>
    have hnc : ¬ p.funcs.any (fun f => f.name.name == "main") = true := by
      simp [hg]
    rw [if_neg hnc] at h
    cases hm : p.funcs.mapM lowerFunc with
    | none => rw [hm] at h; simp at h
    | some funcsMIR =>
      rw [hm] at h
      simp only [] at h
      cases hst : lowerCallStmts p.funcs [] 1 0 p.main with
      | none => rw [hst] at h; simp at h
      | some q =>
        obtain ⟨ρ', v, is, s'⟩ := q
        rw [hst] at h
        simp only [] at h
        cases hinf : inferBody
            (List.map (fun mf => (mf.name, mf.retType)) funcsMIR) [] is v with
        | none => rw [hinf] at h; simp at h
        | some τ =>
          rw [hinf] at h
          have hprog : prog =
              ⟨⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0,
                τ⟩ :: funcsMIR⟩ :=
            (Option.some.inj h).symm
          have hnomain : ∀ f ∈ p.funcs, f.name.name ≠ "main" := by
            intro f hmem hcon
            have h1 : p.funcs.any (fun f => f.name.name == "main") = true := by
              rw [List.any_eq_true]
              exact ⟨f, hmem, by simp [hcon]⟩
            rw [hg] at h1
            exact Bool.noConfusion h1
          have hres : ∀ (fid : HIR.Id) (f : Func) (mf : MIR.Func),
              findHIRFunc p.funcs fid = some f → lowerFunc f = some mf →
              findFunc prog fid.name = some mf := by
            intro fid f mf hfind hlow
            have hmem : f ∈ p.funcs := findHIRFunc_mem hfind
            obtain ⟨mf', hlow'⟩ := mapM_mem_some hm hmem
            have hmeq : mf' = mf := Option.some.inj (hlow'.symm.trans hlow)
            subst hmeq
            rw [hprog]
            exact findFunc_lowerCallProg hm rfl hnomain hnodup hfind hlow
          have hfindMain : findFunc prog "main" =
              some (⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0,
                τ⟩ : MIR.Func) := by
            rw [hprog]
            simp [findFunc]
          have hconst : execInstrsCall prog (fuelM + 1) none
              ⟨fun _ => none, store⟩ [.const 0 .unit] =
              some ⟨Morph.MIR.Env.update (fun _ => none) 0 .unit, store⟩ :=
            rfl
          obtain ⟨fenv', hexec', hreg', hstore', hrel'⟩ :=
            lowerCallStmts_total p.funcs prog funcsMIR fuelM hm hndp hnodupId hres
              [] 1 0 p.main ρ' v is s' hst (FreshAbove_nil 1) Nat.zero_lt_one
              .unit (lamEnv p.funcs)
              ⟨Morph.MIR.Env.update (fun _ => none) 0 .unit, store⟩
              (lamEnv_self p.funcs) (RelEnv_nil _ _) (prologue_env_zero store)
              fuelH henv' out w hrun hval
          have hblock : execInstrsCall prog (fuelM + 1) none
              ⟨fun _ => none, store⟩ ([.const 0 .unit] ++ is) = some fenv' := by
            rw [execInstrsCall_append, hconst]
            exact hexec'
          have hfindBlk : findBlock
              (⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0,
                τ⟩ : MIR.Func)
              (⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0,
                τ⟩ : MIR.Func).entry =
              some (⟨0, [.const 0 .unit] ++ is, .return_ v⟩ : MIR.Block) :=
            findBlock_singleton _ _ rfl rfl
          have hexecBlk : execBlockCall prog (fuelM + 1)
              (⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0,
                τ⟩ : MIR.Func)
              none (⟨0, [.const 0 .unit] ++ is, .return_ v⟩ : MIR.Block)
              ⟨fun _ => none, store⟩ = some w := by
            simp only [execBlockCall, hblock, hreg']
          refine ⟨⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0,
            τ⟩, hfindMain, ?_⟩
          simp only [execFuncCall, hfindBlk]
          exact hexecBlk

end Morph.Proofs.Call
