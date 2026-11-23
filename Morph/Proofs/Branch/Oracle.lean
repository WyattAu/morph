/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal
import Morph.Proofs.Branch.Merge
import Morph.Proofs.Branch.Fragments
import Morph.Proofs.Branch.Fuel
import Morph.Proofs.Branch.LoopAlloc
import Morph.Proofs.Branch.Assembly
import Morph.Proofs.Branch.Equations
import Morph.HIRToMIRLower
import Morph.Proofs.Branch.Infra
import Morph.Proofs.Branch.ArmTotal
import Morph.Proofs.Branch.ArmBroke
import Morph.Proofs.Branch.ArmContinued
import Morph.Proofs.Branch.LoopBodyRun

/-!
# Stage C oracle facts: `runHIRWhile` cases, lookup preservation, eval literals

Sixth proof leaf out of the `HIRToMIRBranch` monolith: the interpreter-side
facts the bind-arm and spine workers cite — `runHIRWhile_value_unit`,
`runHIRWhile_outcome`, `whileLoop_correct_fresh`, `lowerCond_exec_agree`,
the `runHIRWhile_succ_*` cases, `dedupIds_mem`, `mergeIds_agree`,
`mkCarried_lookup_ne` / `mkCarried_mem_lookup`, `runHIRStmts_arm_lookup`,
the `evalHIR_straight_varfree_lit` / `evalHIR_list_lit` mutual pair, and
the `runHIRStmts_arm_lookup_diff` / `bindArm_lookup_diff` /
`bindArm_binds_lit` family (moved verbatim).
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- A `while` loop's value outcome is always the unit literal: `break` exits
as completed and a `false` condition ends the loop, both yielding unit. By
induction on fuel. -/
theorem runHIRWhile_value_unit (fuel : Nat) (henv : HEnv) (c : HIR.Expr)
    (body : List HIR.Stmt) (v : HIR.Expr) (env' : HEnv) :
    runHIRWhile fuel henv c body = ((.value v), env') → v = .lit .unit := by
  induction fuel generalizing henv with
  | zero =>
      intro hcon
      have hz : runHIRWhile 0 henv c body = (.stuck, henv) := rfl
      rw [hz] at hcon
      simp at hcon
  | succ fh ih =>
      intro hcon
      simp only [runHIRWhile] at hcon
      cases hev : evalHIR 256 henv c with
      | none => rw [hev] at hcon; simp at hcon
      | some r =>
          rw [hev] at hcon
          cases r with
          | lit w =>
              cases w with
              | bool b =>
                  cases b with
                  | true =>
                      simp only [] at hcon
                      cases hb : runHIRStmts fh henv body
                          (.value (.lit .unit)) with
                      | mk res env'' =>
                          rw [hb] at hcon
                          cases res with
                          | value u =>
                              simp only [] at hcon
                              exact ih env'' hcon
                          | returned e =>
                              simp only [] at hcon
                              simp at hcon
                          | broke =>
                              simp only [] at hcon
                              exact (HFlow.value.inj
                                (congrArg Prod.fst hcon)).symm
                          | continued =>
                              simp only [] at hcon
                              exact ih env'' hcon
                          | stuck =>
                              simp only [] at hcon
                              simp at hcon
                  | false =>
                      simp only [] at hcon
                      exact (HFlow.value.inj
                        (congrArg Prod.fst hcon)).symm
              | _ =>
                  simp only [] at hcon
                  simp at hcon
          | _ =>
              simp only [] at hcon
              simp at hcon

/-- A `while` loop never leaks `break`/`continue`: `break` exits as a unit
value and `continue` recurses. By induction on fuel, generalizing the outcome
so the recursive cases reuse the hypothesis directly. -/
theorem runHIRWhile_outcome (fuel : Nat) (henv : HEnv) (c : HIR.Expr)
    (body : List HIR.Stmt) (res : HFlow) (env' : HEnv) :
    runHIRWhile fuel henv c body = (res, env') →
    res ≠ .broke ∧ res ≠ .continued := by
  induction fuel generalizing henv res env' with
  | zero =>
      intro hcon
      have hz : runHIRWhile 0 henv c body = (.stuck, henv) := rfl
      rw [hz] at hcon
      have hr : res = .stuck := (congrArg Prod.fst hcon).symm
      subst hr
      exact ⟨by simp, by simp⟩
  | succ fh ih =>
      intro hcon
      simp only [runHIRWhile] at hcon
      cases hev : evalHIR 256 henv c with
      | none =>
          rw [hev] at hcon
          simp only [] at hcon
          have hr : res = .stuck := (congrArg Prod.fst hcon).symm
          subst hr
          exact ⟨by simp, by simp⟩
      | some r =>
          rw [hev] at hcon
          cases r with
          | lit w =>
              cases w with
              | bool b =>
                  cases b with
                  | true =>
                      simp only [] at hcon
                      cases hb : runHIRStmts fh henv body
                          (.value (.lit .unit)) with
                      | mk res' env'' =>
                          rw [hb] at hcon
                          cases res' with
                          | value u =>
                              simp only [] at hcon
                              exact ih env'' res env' hcon
                          | returned e =>
                              simp only [] at hcon
                              have hr : res = .returned e :=
                                (congrArg Prod.fst hcon).symm
                              subst hr
                              exact ⟨by simp, by simp⟩
                          | broke =>
                              simp only [] at hcon
                              have hr : res = .value (.lit .unit) :=
                                (congrArg Prod.fst hcon).symm
                              subst hr
                              exact ⟨by simp, by simp⟩
                          | continued =>
                              simp only [] at hcon
                              exact ih env'' res env' hcon
                          | stuck =>
                              simp only [] at hcon
                              have hr : res = .stuck :=
                                (congrArg Prod.fst hcon).symm
                              subst hr
                              exact ⟨by simp, by simp⟩
                  | false =>
                      simp only [] at hcon
                      have hr : res = .value (.lit .unit) :=
                        (congrArg Prod.fst hcon).symm
                      subst hr
                      exact ⟨by simp, by simp⟩
              | _ =>
                  simp only [] at hcon
                  have hr : res = .stuck :=
                    (congrArg Prod.fst hcon).symm
                  subst hr
                  exact ⟨by simp, by simp⟩
          | _ =>
              simp only [] at hcon
              have hr : res = .stuck := (congrArg Prod.fst hcon).symm
              subst hr
              exact ⟨by simp, by simp⟩

/-- The freshness conjunct of `whileLoop_correct`, proved outright (C7-core,
piece 1 glue): the body lowering runs under the carried env `ρb`, so
`loopBody_fresh` plus the `mkCarried` growth fact yields `FreshAbove lb.ρ
(lb.supply + 1)`. The three `whileLoop_correct` use-sites take `hfrX` from
the deferred theorem; this is its proof. -/
theorem whileLoop_correct_fresh (budget : Nat)
    (bId nextB : MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (c : HIR.Expr) (body rest : List HIR.Stmt)
    (carried : List (HIR.Id × ValId)) (sA : Nat) (ρb : List (HIR.Id × ValId))
    (vc : ValId) (ic : List MIR.Instr) (s1 : Nat)
    (lb lr : Lowered) (phis : List MIR.Instr)
    (hmk : mkCarried ρ supply
        ((dedupIds (assignedIds body)).filterMap
          (fun id => (rhoLookup ρ id).map (fun _ => id))) =
        some (carried, sA, ρb))
    (hcond : lowerExpr ρb sA c = some (vc, ic, s1))
    (hbody : lowerStmtsCFG (nextB + 2) (some nextB) false ρb (s1 + 1)
        (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body = some lb)
    (_hrest : lowerStmtsCFG (nextB + 1) none false ρb (lb.supply + 1) lb.next
        lb.supply true none rest = some lr)
    (_hphis : mkHeaderPhis ρ bId carried
        ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
        (lb.blocks.filterMap (fun b =>
          match b.terminator with
          | .goto t =>
              if t == nextB &&
                  b.id != (lb.blocks.getLast?.map fun b => b.id).getD
                    (nextB + 2) then
                some b.id
              else none
          | _ => none)) = some phis)
    (hloop : LoopStmts budget body) (_hrestP : BranchStmts budget rest)
    (_hstr : IsStraight c) (_hlt : SLWeight c < budget)
    (hfresh : FreshAbove ρ supply) :
    FreshAbove ρb (lb.supply + 1) := by
  have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
  have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
  have hgrow : s1 + 1 ≤ lb.supply :=
    (lowerStmtsCFG_loopBody_inv budget _ _ _ _ _ _ _ _ _ _ hbody hloop).2.1
  exact FreshAbove.mono ρb sA (lb.supply + 1) (by omega) hfrb

/-- Condition instructions execute to the oracle's value (C7-core, piece 2a):
`lowerExpr` code is phi-free (`lower_isPure`/`IsPure_not_phi`), so the
program- and edge-aware executor agrees with the straight-line one
(`execInstrsFullFromIn_of_noPhi`), and `lower_total.1` says that run stores
the evaluated literal at the result register. The main induction cites this
for every header visit; re-establishing `RelEnv` under the carried env is
piece 4 (header-phi chaining), not here. -/
theorem lowerCond_exec_agree (budget : Nat)
    (ρb : List (HIR.Id × ValId)) (sA : Nat) (c : HIR.Expr)
    (vc : ValId) (ic : List MIR.Instr) (s1 : Nat)
    (hcond : lowerExpr ρb sA c = some (vc, ic, s1))
    (hstr : IsStraight c) (_hlt : SLWeight c < budget)
    (hfresh : FreshAbove ρb sA)
    (henv : HEnv) (fenv : FullEnv)
    (hrel : RelEnv henv ρb fenv.env)
    (prog : Program) (prev : Option MIR.BlockId)
    (r : HIR.Expr) (heval : evalHIR 256 henv c = some r) :
    ∃ w, r = .lit w ∧
      ∃ fenv', execInstrsFullFromIn prog prev fenv ic = some fenv' ∧
        fenv'.store = fenv.store ∧ fenv'.env vc = some w := by
  obtain ⟨⟨w, hrw⟩, fenv', hexec, hstore, w', hrw', hreg⟩ :=
    lower_total.1 _ _ _ _ _ _ hcond hstr hfresh _ _ hrel _ _ heval
  have hww : w = w' := HIR.Expr.lit.inj (hrw.symm.trans hrw')
  have hnp : ∀ dst pred src, .phi dst pred src ∉ ic := by
    intro d p s hm
    exact IsPure_not_phi (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p s rfl
  refine ⟨w, hrw, fenv', ?_, hstore, hww ▸ hreg⟩
  rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
  exact hexec

/-- Triage for the C7 soundness obstruction below: a register mapping whose
id is unbound in the HIR env refutes `RelEnv` for every MIR env. -/
theorem RelEnv_of_lookup_none {henv : HEnv} {ρ : List (HIR.Id × ValId)}
    {fenv : Morph.MIR.Env} {id : HIR.Id} {u : ValId}
    (hρ : rhoLookup ρ id = some u) (hnone : lookupHEnv henv id = none) :
    ¬ RelEnv henv ρ fenv := by
  intro hrel
  obtain ⟨w, hw, _⟩ := hrel id u hρ
  simp [hnone] at hw

/-- C7 fragment fix pin (was: soundness obstruction for `whileLoop_correct`).
`varDecl` under `loop = some` is refused by `lowerStmtsCFG`, so a loop body
declaring a fresh variable no longer lowers at all: the old refutation
(`while false { varDecl x … }` exiting with `lb.ρ ∋ (x, _)` while `x` is
unbound in `henv`) is unstatable, since its `= some lb` hypothesis is now
`False` by computation. `RelEnv_of_lookup_none` above stays as the triage
lemma pinning why the old behavior was unsound. -/
example : lowerStmtsCFG 2 (some 0) false ([] : List (HIR.Id × ValId)) 1 3 0
    true (some ⟨0, 1, []⟩)
    [.varDecl ⟨0, "x"⟩ Typ.intType (.lit (.int 1))] = none := by
  simp

/-! ## Oracle-side while cases (C7-core, piece 0)

The induction inside `whileLoop_correct` splits on the oracle's fuel and on
the condition/body outcomes. These helpers prove those splits against the
oracle alone, so the main proof cites them instead of redoing the unfolding:
at fuel 0 the loop is stuck (both conclusions vacuous); at `fh + 1` a false
condition exits with unit, a `broke` body exits with unit,
`continued`/value bodies recurse, and `returned`/`stuck` bodies, a failed
condition, and a non-boolean condition all propagate as stuck. -/
theorem runHIRWhile_zero_eq (henv : HEnv) (c : HIR.Expr)
    (body : List HIR.Stmt) :
    runHIRWhile 0 henv c body = (.stuck, henv) := rfl

/-- At fuel 0 the loop is stuck, so both of `whileLoop_correct`'s conclusions
hold vacuously for any `P`/`Q`. -/
theorem whileLoop_zero_vac {P : Prop} {Q : HIR.Expr → Prop}
    {henv : HEnv} {c : HIR.Expr} {body : List HIR.Stmt}
    {res : HFlow} {env' : HEnv}
    (hrun : runHIRWhile 0 henv c body = (res, env')) :
    ((res = .value (.lit .unit)) → P) ∧ (∀ e, res = .returned e → Q e) := by
  rw [runHIRWhile_zero_eq] at hrun
  cases hrun
  exact ⟨fun h => False.elim (HFlow.noConfusion h),
    fun e h => False.elim (HFlow.noConfusion h)⟩

/-- One oracle step with a false condition exits immediately with unit. -/
theorem runHIRWhile_succ_false {fh : Nat} {henv : HEnv} {c : HIR.Expr}
    {body : List HIR.Stmt}
    (hcond : evalHIR 256 henv c = some (.lit (.bool false))) :
    runHIRWhile (fh + 1) henv c body = (.value (.lit .unit), henv) := by
  simp only [runHIRWhile, hcond]

/-- Zero-trip pin (Loop 183 probe, HIR side): a loop whose condition is false
on entry exits with unit and the environment untouched, so the pre-loop
binding (`x = 5` in `x = 5; while (x < 2) { x = x + 1 }; x`) survives zero
trips on the oracle side. The MIR side — `rest` lowered under the body-entry
env `ρb` — is what `whileLoop_correct` must now match. -/
example (henv : HEnv) (body : List HIR.Stmt) (fh : Nat) :
    runHIRWhile (fh + 1) henv (.lit (.bool false)) body =
      (.value (.lit .unit), henv) :=
  runHIRWhile_succ_false rfl

/-- One oracle step with a true condition and a `broke` body exits with unit. -/
theorem runHIRWhile_succ_true_broke {fh : Nat} {henv : HEnv} {c : HIR.Expr}
    {body : List HIR.Stmt} {envB : HEnv}
    (hcond : evalHIR 256 henv c = some (.lit (.bool true)))
    (hbody : runHIRStmts fh henv body (.value (.lit .unit)) = (.broke, envB)) :
    runHIRWhile (fh + 1) henv c body = (.value (.lit .unit), envB) := by
  simp only [runHIRWhile, hcond, hbody]

/-- `continued` bodies recurse into the next iteration. -/
theorem runHIRWhile_succ_true_cont {fh : Nat} {henv : HEnv} {c : HIR.Expr}
    {body : List HIR.Stmt} {envB : HEnv}
    (hcond : evalHIR 256 henv c = some (.lit (.bool true)))
    (hbody : runHIRStmts fh henv body (.value (.lit .unit)) =
      (.continued, envB)) :
    runHIRWhile (fh + 1) henv c body = runHIRWhile fh envB c body := by
  simp only [runHIRWhile, hcond, hbody]

/-- Value bodies (e.g. an empty body, or `continue`-free fall-through) recurse
into the next iteration with the body's final environment. -/
theorem runHIRWhile_succ_true_value {fh : Nat} {henv : HEnv} {c : HIR.Expr}
    {body : List HIR.Stmt} {u : HIR.Expr} {envB : HEnv}
    (hcond : evalHIR 256 henv c = some (.lit (.bool true)))
    (hbody : runHIRStmts fh henv body (.value (.lit .unit)) = (.value u, envB)) :
    runHIRWhile (fh + 1) henv c body = runHIRWhile fh envB c body := by
  simp only [runHIRWhile, hcond, hbody]

/-- `returned` bodies propagate out of the loop. -/
theorem runHIRWhile_succ_true_ret {fh : Nat} {henv : HEnv} {c : HIR.Expr}
    {body : List HIR.Stmt} {e : HIR.Expr} {envB : HEnv}
    (hcond : evalHIR 256 henv c = some (.lit (.bool true)))
    (hbody : runHIRStmts fh henv body (.value (.lit .unit)) =
      (.returned e, envB)) :
    runHIRWhile (fh + 1) henv c body = (.returned e, envB) := by
  simp only [runHIRWhile, hcond, hbody]

/-- `stuck` bodies propagate out of the loop. -/
theorem runHIRWhile_succ_true_stuck {fh : Nat} {henv : HEnv} {c : HIR.Expr}
    {body : List HIR.Stmt} {envB : HEnv}
    (hcond : evalHIR 256 henv c = some (.lit (.bool true)))
    (hbody : runHIRStmts fh henv body (.value (.lit .unit)) = (.stuck, envB)) :
    runHIRWhile (fh + 1) henv c body = (.stuck, envB) := by
  simp only [runHIRWhile, hcond, hbody]

/-- A failed condition evaluation stalls the loop. -/
theorem runHIRWhile_succ_cond_none {fh : Nat} {henv : HEnv} {c : HIR.Expr}
    {body : List HIR.Stmt}
    (hcond : evalHIR 256 henv c = none) :
    runHIRWhile (fh + 1) henv c body = (.stuck, henv) := by
  simp only [runHIRWhile, hcond]

/-! ## Loop-carried membership helpers (C7 spine pieces)

The re-entry argument classifies body-exit lookups: an id assigned in the
body resolves through its carried pair, otherwise its register is untouched.
These close over `mkCarried` and `dedupIds` alone. -/

/-- Derived `BEq` on `HIR.Id` is lawful (fields are `Nat`/`String`, both
lawful), so `List.contains` reflects membership. Needed for `dedupIds_mem`
below; `HIREval` notes the instance was missing, and the fact itself is what
`LawfulBEq` means, so providing it is sound. -/
instance : LawfulBEq HIR.Id where
  eq_of_beq := by
    intro a b h
    obtain ⟨i1, n1⟩ := a
    obtain ⟨i2, n2⟩ := b
    simp only [BEq.beq] at h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    have e1 : i1 = i2 := LawfulBEq.eq_of_beq h1
    have e2 : n1 = n2 := LawfulBEq.eq_of_beq h2
    simp [e1, e2]
  rfl := by
    intro a
    obtain ⟨i, n⟩ := a
    show ((i == i) && (n == n)) = true
    simp

/-- `dedupIds` keeps every member (first occurrence survives the fold). -/
theorem dedupIds_mem {ids : List HIR.Id} {id : HIR.Id}
    (hmem : id ∈ ids) : id ∈ dedupIds ids := by
  have aux : ∀ (l acc : List HIR.Id) (x : HIR.Id),
      x ∈ acc ∨ x ∈ l →
        x ∈ l.foldl (fun acc j => if acc.contains j then acc else acc ++ [j]) acc := by
    intro l acc x hx
    induction l generalizing acc with
    | nil =>
        simp only [List.foldl_nil]
        rcases hx with hx | hx
        · exact hx
        · simp at hx
    | cons hd tl ih =>
        simp only [List.foldl_cons]
        by_cases hc : (acc.contains hd) = true
        · have hstep : x ∈ acc ∨ x ∈ tl := by
            rcases hx with hx | hx
            · exact Or.inl hx
            · simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact Or.inl (List.contains_iff_mem.mp hc)
              · exact Or.inr hx
          rw [if_pos hc]
          exact ih _ hstep
        · have hstep : x ∈ (acc ++ [hd]) ∨ x ∈ tl := by
            rcases hx with hx | hx
            · exact Or.inl (List.mem_append_left _ hx)
            · simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact Or.inl (List.mem_append_right _ (List.mem_cons_self ..))
              · exact Or.inr hx
          rw [if_neg hc]
          rcases hstep with hstep | hstep
          · exact ih _ (Or.inl hstep)
          · exact ih _ (Or.inr hstep)
  exact aux ids [] id (Or.inr hmem)

/-- Unmerged ids look up identically on both sides: if `id` occurs in the
pre-branch env but the merge set skips it, neither arm exit rebinds it.
The fold adds exactly the differing ids it reaches with a clean
accumulator (`List.contains` reflects membership via the `LawfulBEq`
instance above); contraposing gives agreement. The future merge-join
`RelEnv` assembly cites this for the unmerged part of `ρm` transport. -/
theorem mergeIds_agree {ρ ltρ leρ : List (HIR.Id × ValId)} {id : HIR.Id}
    (hmem : id ∈ ρ.map Prod.fst) (hnin : id ∉ mergeIds ρ ltρ leρ) :
    rhoLookup ltρ id = rhoLookup ρ id ∧ rhoLookup leρ id = rhoLookup ρ id := by
  have hmono : ∀ (l acc : List HIR.Id) (x : HIR.Id), x ∈ acc →
      x ∈ l.foldl (fun acc j =>
        if acc.contains j then acc
        else if rhoLookup ltρ j != rhoLookup ρ j ||
                rhoLookup leρ j != rhoLookup ρ j then acc ++ [j]
        else acc) acc := by
    intro l acc x hx
    induction l generalizing acc with
    | nil => simpa [List.foldl_nil]
    | cons hd tl ih =>
        simp only [List.foldl_cons]
        by_cases hc : acc.contains hd = true
        · rw [if_pos hc]
          exact ih acc hx
        · rw [if_neg hc]
          by_cases hd2 : (rhoLookup ltρ hd != rhoLookup ρ hd ||
              rhoLookup leρ hd != rhoLookup ρ hd) = true
          · rw [if_pos hd2]
            exact ih _ (List.mem_append_left _ hx)
          · rw [if_neg hd2]
            exact ih acc hx
  have aux : ∀ (l acc : List HIR.Id),
      (∀ x ∈ acc, rhoLookup ltρ x ≠ rhoLookup ρ x ∨
        rhoLookup leρ x ≠ rhoLookup ρ x) →
      (∀ x ∈ acc, x ≠ id) →
      (rhoLookup ltρ id ≠ rhoLookup ρ id ∨
        rhoLookup leρ id ≠ rhoLookup ρ id) →
      id ∈ l →
      id ∈ l.foldl (fun acc j =>
        if acc.contains j then acc
        else if rhoLookup ltρ j != rhoLookup ρ j ||
                rhoLookup leρ j != rhoLookup ρ j then acc ++ [j]
        else acc) acc := by
    intro l acc hdiff hne hD hmeml
    induction l generalizing acc with
    | nil => simp at hmeml
    | cons hd tl ih =>
        simp only [List.foldl_cons]
        by_cases hc : acc.contains hd = true
        · rw [if_pos hc]
          have hstep : id ∈ tl := by
            rcases List.mem_cons.mp hmeml with h | h
            · subst h
              exact absurd rfl (hne id (List.contains_iff_mem.mp hc))
            · exact h
          exact ih acc hdiff hne hstep
        · rw [if_neg hc]
          by_cases hd2 : (rhoLookup ltρ hd != rhoLookup ρ hd ||
              rhoLookup leρ hd != rhoLookup ρ hd) = true
          · rw [if_pos hd2]
            have hDhd : rhoLookup ltρ hd ≠ rhoLookup ρ hd ∨
                rhoLookup leρ hd ≠ rhoLookup ρ hd := by
              simpa using hd2
            by_cases heq : hd = id
            · have hid : id ∈ acc ++ [hd] := by
                rw [heq]
                exact List.mem_append_right _ (List.mem_cons_self ..)
              exact hmono tl (acc ++ [hd]) id hid
            · have hdiff' : ∀ x ∈ acc ++ [hd],
                  rhoLookup ltρ x ≠ rhoLookup ρ x ∨
                    rhoLookup leρ x ≠ rhoLookup ρ x := by
                intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hdiff x hx
                · rw [List.mem_singleton.mp hx]
                  exact hDhd
              have hne' : ∀ x ∈ acc ++ [hd], x ≠ id := by
                intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hne x hx
                · rw [List.mem_singleton.mp hx]
                  exact heq
              have hmemt : id ∈ tl := by
                rcases List.mem_cons.mp hmeml with h | h
                · exact absurd h.symm heq
                · exact h
              exact ih (acc ++ [hd]) hdiff' hne' hmemt
          · rw [if_neg hd2]
            have hstep : id ∈ tl := by
              rcases List.mem_cons.mp hmeml with h | h
              · subst h
                have hcon : ¬ (rhoLookup ltρ id ≠ rhoLookup ρ id ∨
                    rhoLookup leρ id ≠ rhoLookup ρ id) := by
                  simpa using hd2
                exact absurd hD hcon
              · exact h
            exact ih acc hdiff hne hstep
  have hDIFF : ¬ (rhoLookup ltρ id ≠ rhoLookup ρ id ∨
      rhoLookup leρ id ≠ rhoLookup ρ id) := by
    intro hD
    have hfin := aux (ρ.map Prod.fst) [] (by simp) (by simp) hD hmem
    exact hnin hfin
  rw [not_or] at hDIFF
  obtain ⟨h1, h2⟩ := hDIFF
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- Updates for other ids preserve lookups through `mkCarried`. -/
theorem mkCarried_lookup_ne {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} {id : HIR.Id}
    (hne : id ∉ ids)
    (h : mkCarried ρ s ids = some (cs, s', ρ')) :
    rhoLookup ρ' id = rhoLookup ρ id := by
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | cons hd tl ih =>
      simp only [mkCarried] at h
      cases hρ : rhoLookup ρ hd with
      | none => rw [hρ] at h; simp at h
      | some _ =>
          rw [hρ] at h
          cases hrec : mkCarried (updAssoc ρ hd s) (s + 1) tl with
          | none => rw [hrec] at h; simp at h
          | some q =>
              obtain ⟨cs', s'', ρ''⟩ := q
              rw [hrec] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              have hne_hd : ¬ hd = id :=
                fun heq => hne (heq ▸ List.mem_cons_self ..)
              have hne_tl : id ∉ tl := fun hm => hne (List.mem_cons_of_mem _ hm)
              have hstep : rhoLookup (updAssoc ρ hd s) id = rhoLookup ρ id :=
                rhoLookup_updAssoc_ne hne_hd ρ
              exact (ih hne_tl hrec).trans hstep

/-- Every id fed to `mkCarried` resolves through its carried pair: the
allocation for its (last) update is the final lookup, and the pair is in
the carried list. No deduplication hypothesis is needed — later updates
simply shadow earlier ones and the induction follows the last one. -/
theorem mkCarried_mem_lookup {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} {id : HIR.Id}
    (hmem : id ∈ ids)
    (h : mkCarried ρ s ids = some (cs, s', ρ')) :
    ∃ r, rhoLookup ρ' id = some r ∧ (id, r) ∈ cs := by
  induction ids generalizing ρ s cs s' ρ' with
  | nil => simp at hmem
  | cons hd tl ih =>
      simp only [mkCarried] at h
      cases hρ : rhoLookup ρ hd with
      | none => rw [hρ] at h; simp at h
      | some v =>
          rw [hρ] at h
          cases hrec : mkCarried (updAssoc ρ hd s) (s + 1) tl with
          | none => rw [hrec] at h; simp at h
          | some q =>
              obtain ⟨cs', s'', ρ''⟩ := q
              rw [hrec] at h
              simp only [] at h
              have eL : ((hd, s) :: cs', s'', ρ'') = (cs, s', ρ') :=
                Option.some.inj h
              have e1 : (hd, s) :: cs' = cs := congrArg Prod.fst eL
              have e3 : ρ'' = ρ' := congrArg (Prod.snd ∘ Prod.snd) eL
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · by_cases htl : id ∈ tl
                · obtain ⟨r, hrlook, hrmem⟩ := ih htl hrec
                  have h2 := List.mem_cons_of_mem (id, s) hrmem
                  rw [e1] at h2
                  rw [e3] at hrlook
                  exact ⟨r, hrlook, h2⟩
                · refine ⟨s, ?_, ?_⟩
                  · rw [← e3]
                    have hpres : rhoLookup ρ'' id =
                        rhoLookup (updAssoc ρ id s) id :=
                      mkCarried_lookup_ne htl hrec
                    simp only [hpres, rhoLookup_updAssoc_id, hρ, Option.map_some]
                  · rw [← e1]
                    exact List.mem_cons_self ..
              · obtain ⟨r, hrlook, hrmem⟩ := ih hmem hrec
                have h2 := List.mem_cons_of_mem (hd, s) hrmem
                rw [e1] at h2
                rw [e3] at hrlook
                exact ⟨r, hrlook, h2⟩

-- Per-constructor cases of `runHIRStmts_loopBody_lookup` (spine L2).
--
-- `LoopStmts` lives in the file's `mutual` block, which the `induction`
-- tactic does not support (see `LoopStmts_to_BranchStmts`), so the L2
-- preservation proof is factored: one flat helper per constructor proved
-- below, plus a dispatcher (induction on the statement list, `cases` on the
-- derivation) after the last helper. Each helper takes the tail induction
-- hypothesis `ih` explicitly where its constructor has a `LoopStmts` tail.
/-- Arms never rebind: `ArmStmts` has no `assign`/`varDecl`, and expression
statements, conditions and returns only evaluate. The loop-body HIR
preservation cites this for both arms of every `if`. -/
theorem runHIRStmts_arm_lookup (budget : Nat) {ss : List HIR.Stmt}
    (hss : ArmStmts budget ss) :
    ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv ss acc = (out, henv') →
      lookupHEnv henv' id = lookupHEnv henv id := by
  induction hss with
  | nil =>
      intro fuel henv henv' acc out id hrun
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          rw [runHIRStmts_nil] at hrun
          cases hrun
          rfl
  | exprStmt e rest hstr _ hrs ih =>
      intro fuel henv henv' acc out id hrun
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              exact ih _ _ _ _ _ _ hrun
  | nop rest hrs ih =>
      intro fuel henv henv' acc out id hrun
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          exact ih _ _ _ _ _ _ hrun
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      intro fuel henv henv' acc out id hrun
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv c with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
          | some v =>
              rw [hev] at hrun
              split at hrun
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : v = HIR.Expr.lit (.bool true) := by
                  simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv th
                    (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have h1 := iht _ _ _ _ _ id har
                        have h2 := ihr _ _ _ _ _ id hrun
                        rw [h2, h1]
                    | broke =>
                        simp only [] at hrun
                        cases hrun
                        exact iht _ _ _ _ _ id har
                    | continued =>
                        simp only [] at hrun
                        cases hrun
                        exact iht _ _ _ _ _ id har
                    | returned e =>
                        simp only [] at hrun
                        cases hrun
                        exact iht _ _ _ _ _ id har
                    | stuck =>
                        simp only [] at hrun
                        cases hrun
                        exact iht _ _ _ _ _ id har
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : v = HIR.Expr.lit (.bool false) := by
                  simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv el
                    (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have h1 := ihe _ _ _ _ _ id har
                        have h2 := ihr _ _ _ _ _ id hrun
                        rw [h2, h1]
                    | broke =>
                        simp only [] at hrun
                        cases hrun
                        exact ihe _ _ _ _ _ id har
                    | continued =>
                        simp only [] at hrun
                        cases hrun
                        exact ihe _ _ _ _ _ id har
                    | returned e =>
                        simp only [] at hrun
                        cases hrun
                        exact ihe _ _ _ _ _ id har
                    | stuck =>
                        simp only [] at hrun
                        cases hrun
                        exact ihe _ _ _ _ _ id har
              · cases hrun
                rfl
  | returnStmt e rest hstr _ =>
      intro fuel henv henv' acc out id hrun
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
  | breakStmt rest hrs ih =>
      intro fuel henv henv' acc out id hrun
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hrun
          rfl
  | continueStmt rest hrs ih =>
      intro fuel henv henv' acc out id hrun
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hrun
          rfl

-- Closed straight expressions evaluate to literals, and so does every element
-- of a successful closed-straight block evaluation. Mutual: the `block` case
-- delegates to the list half, whose cons case delegates back.
mutual
/-- A closed straight expression evaluates to a literal. -/
theorem evalHIR_straight_varfree_lit (e : HIR.Expr) :
    VarFree e → IsStraight e →
    ∀ (fuel : Nat) (henv : HEnv) (v : HIR.Expr),
      evalHIR fuel henv e = some v → ∃ w, v = .lit w := by
  intro hvf hstr fuel henv v h
  cases fuel with
  | zero => simp [evalHIR] at h
  | succ fuel =>
      cases e with
      | var id => cases hvf
      | lit val =>
          simp [evalHIR] at h
          exact ⟨_, h.symm⟩
      | unop op e =>
          cases hvf with
          | unop _ _ hv =>
          cases hstr with
          | unop _ _ _ hs =>
          simp only [evalHIR] at h
          obtain ⟨v', heval, hmatch⟩ := bind_some_eq h
          obtain ⟨w', heval'⟩ := evalHIR_straight_varfree_lit e hv hs fuel henv v' heval
          subst heval'
          simp only at hmatch
          cases hr : Executable.evalUnop op (.lit w') with
          | none => simp [hr] at hmatch
          | some w'' =>
              simp [hr] at hmatch
              cases w'' with
              | lit w =>
                  obtain rfl := Option.some.inj hmatch
                  exact ⟨w, rfl⟩
              | _ => simp at hmatch
      | binop op a b =>
          cases hvf with
          | binop _ _ _ hva hvb =>
          cases hstr with
          | binop _ _ _ _ ha hb =>
          simp only [evalHIR] at h
          obtain ⟨va, hevala, hrest⟩ := bind_some_eq h
          obtain ⟨vb, hevalb, hmatch⟩ := bind_some_eq hrest
          obtain ⟨wa, hevala'⟩ := evalHIR_straight_varfree_lit a hva ha fuel henv va hevala
          obtain ⟨wb, hevalb'⟩ := evalHIR_straight_varfree_lit b hvb hb fuel henv vb hevalb
          subst hevala'
          subst hevalb'
          simp only at hmatch
          cases hr : Executable.evalBinop op (.lit wa) (.lit wb) with
          | none => simp [hr] at hmatch
          | some w'' =>
              simp [hr] at hmatch
              cases w'' with
              | lit w =>
                  obtain rfl := Option.some.inj hmatch
                  exact ⟨w, rfl⟩
              | _ => simp at hmatch
      | app fid args => cases hstr
      | lam params body => cases hstr
      | «let» id init body =>
          cases hvf with
          | let_ _ _ _ hvInit hvBody =>
          cases hstr with
          | let_ _ _ _ hsInit hsBody =>
          simp only [evalHIR] at h
          obtain ⟨vi, hevali, hbody⟩ := bind_some_eq h
          obtain ⟨wi, hevali'⟩ := evalHIR_straight_varfree_lit init hvInit hsInit fuel henv vi hevali
          subst hevali'
          exact evalHIR_straight_varfree_lit body hvBody hsBody fuel ((id, .lit wi) :: henv) v hbody
      | ifThenElse c t f => cases hstr
      | whileLoop c body => cases hstr
      | «match» scrut arms => cases hstr
      | block es =>
          cases hvf with
          | block _ hallv =>
          cases hstr with
          | block _ halls =>
          simp only [evalHIR] at h
          obtain ⟨vs, hmap, hmatch⟩ := bind_some_eq h
          have hlit := evalHIR_list_lit es hallv halls fuel henv vs hmap
          cases hvs : vs with
          | nil =>
              simp [hvs] at hmatch
              subst hmatch
              exact ⟨.unit, rfl⟩
          | cons v0 vr =>
              simp only [hvs] at hmatch
              have hne : (v0 :: vr) ≠ [] := by simp
              have hlast : (v0 :: vr).getLast? = some ((v0 :: vr).getLast hne) :=
                List.getLast?_eq_some_getLast hne
              have hgi : (v0 :: vr).getLast! = (v0 :: vr).getLast hne := by
                simp only [List.getLast!_eq_getLast?_getD, hlast, Option.getD_some]
              rw [hgi] at hmatch
              obtain rfl := Option.some.inj hmatch
              rw [hvs] at hlit
              exact hlit _ (List.getLast_mem hne)
      | infer => cases hstr

/-- Every element of a successful closed-straight block evaluation is a literal. -/
theorem evalHIR_list_lit (es : List HIR.Expr) :
    (∀ x ∈ es, VarFree x) → (∀ x ∈ es, IsStraight x) →
    ∀ (fuel : Nat) (henv : HEnv) (vs : List HIR.Expr),
      es.mapM (evalHIR fuel henv) = some vs →
      ∀ v ∈ vs, ∃ w, v = .lit w := by
  intro hallv halls fuel henv vs h v hmem
  cases es with
  | nil =>
      cases vs with
      | nil => simp at hmem
      | cons v0 vr => simp at h
  | cons e0 er =>
      have h0v : VarFree e0 := hallv _ (List.mem_cons_self ..)
      have h0s : IsStraight e0 := halls _ (List.mem_cons_self ..)
      have hrv : ∀ x ∈ er, VarFree x :=
        fun x hx => hallv x (List.mem_cons_of_mem _ hx)
      have hrs : ∀ x ∈ er, IsStraight x :=
        fun x hx => halls x (List.mem_cons_of_mem _ hx)
      obtain ⟨v0, vr, he0, htail, hvs⟩ := mapM_cons_destr h
      subst hvs
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact evalHIR_straight_varfree_lit e0 h0v h0s fuel henv v he0
      · exact evalHIR_list_lit er hrv hrs fuel henv vr htail v hmem
end

/- `boundIds` lives in `Morph.Proofs.Branch.Merge` (L0 proof-crate leaf). -/

/-- C2c HIR fact: an arm run preserves every lookup outside its bound set.
Phase B moved the binding-arm induction to `runHIRStmts_bindArm_lookup_diff`
(which the merge proof cites per arm); this stays as the one-line corollary
for the binding-free fragment. `runHIRStmts_arm_lookup` keeps its own
induction rather than deriving from the binding version: `returnStmt` is
terminal in `ArmStmts` with an unconstrained tail, so `boundIds` can be
nonempty while the run still preserves every lookup (terminality, not
binding-freedom) — the side condition would be unprovable there. -/
theorem runHIRStmts_arm_lookup_diff (budget : Nat) {ss : List HIR.Stmt}
    (hss : ArmStmts budget ss) :
    ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv ss acc = (out, henv') →
      id ∉ boundIds ss →
      lookupHEnv henv' id = lookupHEnv henv id := by
  intro fuel henv henv' acc out id hrun _hnin
  exact runHIRStmts_arm_lookup budget hss _ _ _ _ _ _ hrun

/-- C2c HIR fact over binding arms: a `BindArmStmts` run preserves every
lookup outside its bound set. This is the per-constructor induction the
merge proof cites to discharge the side condition per arm: `varDecl`
resp. `assign` touch only their own id (via `lookupHEnv_cons_ne` resp.
`lookupHEnv_updateHEnv_ne`), and the `if` case splits the `boundIds`
append across both arms and the rest. -/
theorem runHIRStmts_bindArm_lookup_diff (budget : Nat) {ss : List HIR.Stmt}
    (hss : BindArmStmts budget ss) :
    ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv ss acc = (out, henv') →
      id ∉ boundIds ss →
      lookupHEnv henv' id = lookupHEnv henv id := by
  induction hss with
  | nil =>
      intro fuel henv henv' acc out id hrun _hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          rw [runHIRStmts_nil] at hrun
          cases hrun
          rfl
  | exprStmt e rest hstr _ hrs ih =>
      intro fuel henv henv' acc out id hrun hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              have hnin_rest : id ∉ boundIds rest := by
                intro hm
                exact hnin (by simp [boundIds, hm])
              exact ih _ _ _ _ _ _ hrun hnin_rest
  | varDecl id' τ init rest hstr _ hrs _ ih =>
      intro fuel henv henv' acc out id hrun hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv
              (.varDecl id' τ init :: rest) acc =
              (match evalHIR 256 henv init with
                | none => (HFlow.stuck, henv)
                | some v => runHIRStmts fh ((id', v) :: henv) rest acc) := rfl
          rw [hstep] at hrun
          cases hev : evalHIR 256 henv init with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              have hne : id ≠ id' := by
                intro heq
                subst heq
                simp [boundIds] at hnin
              have hnin_rest : id ∉ boundIds rest := by
                intro hm
                exact hnin (by simp [boundIds, hm])
              have h1 := ih _ _ _ _ _ _ hrun hnin_rest
              rw [h1]
              exact lookupHEnv_cons_ne (Ne.symm hne)
  | assign id' e rest hstr _ hrs _ ih =>
      intro fuel henv henv' acc out id hrun hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv
              (.assign id' e :: rest) acc =
              (match evalHIR 256 henv e with
                | none => (HFlow.stuck, henv)
                | some v => runHIRStmts fh (updateHEnv henv id' v) rest acc) :=
            rfl
          rw [hstep] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              have hne : id ≠ id' := by
                intro heq
                subst heq
                simp [boundIds] at hnin
              have hnin_rest : id ∉ boundIds rest := by
                intro hm
                exact hnin (by simp [boundIds, hm])
              have h1 := ih _ _ _ _ _ _ hrun hnin_rest
              rw [h1]
              exact lookupHEnv_updateHEnv_ne (Ne.symm hne)
  | nop rest hrs ih =>
      intro fuel henv henv' acc out id hrun hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          have hnin_rest : id ∉ boundIds rest := by
            intro hm
            exact hnin (by simp [boundIds, hm])
          exact ih _ _ _ _ _ _ hrun hnin_rest
  | ifStmt c th el rest hstr _ hath hael hrs ihr =>
      intro fuel henv henv' acc out id hrun hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          have hnin_all : id ∉ boundIds th ++ boundIds el ++ boundIds rest := by
            simpa [boundIds] using hnin
          simp only [List.mem_append, not_or] at hnin_all
          obtain ⟨⟨hnin_th, hnin_el⟩, hnin_rest⟩ := hnin_all
          cases hev : evalHIR 256 henv c with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
          | some v =>
              rw [hev] at hrun
              split at hrun
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : v = HIR.Expr.lit (.bool true) := by
                  simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv th
                    (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have h1 := runHIRStmts_arm_lookup_diff budget hath _ _ _ _ _ _ har hnin_th
                        have h2 := ihr _ _ _ _ _ _ hrun hnin_rest
                        rw [h2, h1]
                    | broke =>
                        simp only [] at hrun
                        cases hrun
                        exact runHIRStmts_arm_lookup_diff budget hath _ _ _ _ _ _ har hnin_th
                    | continued =>
                        simp only [] at hrun
                        cases hrun
                        exact runHIRStmts_arm_lookup_diff budget hath _ _ _ _ _ _ har hnin_th
                    | returned e =>
                        simp only [] at hrun
                        cases hrun
                        exact runHIRStmts_arm_lookup_diff budget hath _ _ _ _ _ _ har hnin_th
                    | stuck =>
                        simp only [] at hrun
                        cases hrun
                        exact runHIRStmts_arm_lookup_diff budget hath _ _ _ _ _ _ har hnin_th
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : v = HIR.Expr.lit (.bool false) := by
                  simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv el
                    (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have h1 := runHIRStmts_arm_lookup_diff budget hael _ _ _ _ _ _ har hnin_el
                        have h2 := ihr _ _ _ _ _ _ hrun hnin_rest
                        rw [h2, h1]
                    | broke =>
                        simp only [] at hrun
                        cases hrun
                        exact runHIRStmts_arm_lookup_diff budget hael _ _ _ _ _ _ har hnin_el
                    | continued =>
                        simp only [] at hrun
                        cases hrun
                        exact runHIRStmts_arm_lookup_diff budget hael _ _ _ _ _ _ har hnin_el
                    | returned e =>
                        simp only [] at hrun
                        cases hrun
                        exact runHIRStmts_arm_lookup_diff budget hael _ _ _ _ _ _ har hnin_el
                    | stuck =>
                        simp only [] at hrun
                        cases hrun
                        exact runHIRStmts_arm_lookup_diff budget hael _ _ _ _ _ _ har hnin_el
              · cases hrun
                rfl
  | returnStmt e rest hstr _ =>
      intro fuel henv henv' acc out id hrun _hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              rfl
  | breakStmt rest hrs ih =>
      intro fuel henv henv' acc out id hrun _hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hrun
          rfl
  | continueStmt rest hrs ih =>
      intro fuel henv henv' acc out id hrun _hnin
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hrun
          rfl

/-- C2c HIR fact over binding arms: a post-run lookup is either a literal
or the pre-run lookup unchanged. `varDecl`/`assign` bind `VarFree` straight
inits (`evalHIR_straight_varfree_lit`), everything else preserves the env;
the `if` case composes the taken-arm disjunction with the rest disjunction,
and terminal outcomes (`return`/`break`/`continue`/stuck) stop in an env the
arm IH already covers. No `boundIds` side condition is needed (the claim is
outcome-agnostic): untaken-arm ids simply take the unchanged right
branch. The future top-level binding-arm `RelEnv` assembly cites this for
arm-post literals: the left branch is a literal, the right branch goes
through the outer branch-point `RelEnv` at an unmerged id. -/
theorem runHIRStmts_bindArm_binds_lit (budget : Nat) {ss : List HIR.Stmt}
    (hss : BindArmStmts budget ss) :
    ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
      (v : HIR.Expr),
      runHIRStmts fuel henv ss acc = (out, henv') →
      lookupHEnv henv' id = some v →
      (∃ w, v = .lit w) ∨ lookupHEnv henv id = some v := by
  induction hss with
  | nil =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          rw [runHIRStmts_nil] at hrun
          cases hrun
          exact Or.inr hlook
  | exprStmt e rest hstr _ hrs ih =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              exact Or.inr hlook
          | some ev =>
              rw [hev] at hrun
              simp only [] at hrun
              exact ih _ _ _ _ _ _ _ hrun hlook
  | varDecl id' τ init rest hstr _ hrs hfree ih =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv
              (.varDecl id' τ init :: rest) acc =
              (match evalHIR 256 henv init with
                | none => (HFlow.stuck, henv)
                | some ev => runHIRStmts fh ((id', ev) :: henv) rest acc) := rfl
          rw [hstep] at hrun
          cases hev : evalHIR 256 henv init with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              exact Or.inr hlook
          | some ev =>
              rw [hev] at hrun
              simp only [] at hrun
              have h1 := ih _ _ _ _ _ _ _ hrun hlook
              rcases h1 with h1 | h1
              · exact Or.inl h1
              · by_cases heq : id = id'
                · subst heq
                  rw [lookupHEnv_cons_head] at h1
                  obtain rfl := Option.some.inj h1
                  obtain ⟨w, hw⟩ :=
                    evalHIR_straight_varfree_lit init hfree hstr 256 henv ev hev
                  exact Or.inl ⟨w, hw⟩
                · rw [lookupHEnv_cons_ne (Ne.symm heq)] at h1
                  exact Or.inr h1
  | assign id' e rest hstr _ hrs hfree ih =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv
              (.assign id' e :: rest) acc =
              (match evalHIR 256 henv e with
                | none => (HFlow.stuck, henv)
                | some ev =>
                    runHIRStmts fh (updateHEnv henv id' ev) rest acc) :=
            rfl
          rw [hstep] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              exact Or.inr hlook
          | some ev =>
              rw [hev] at hrun
              simp only [] at hrun
              have h1 := ih _ _ _ _ _ _ _ hrun hlook
              rcases h1 with h1 | h1
              · exact Or.inl h1
              · by_cases heq : id = id'
                · subst heq
                  rw [lookupHEnv_updateHEnv_head] at h1
                  cases hpre : lookupHEnv henv id with
                  | none => simp [hpre] at h1
                  | some vpre =>
                      simp only [hpre, Option.map_some, Option.some.injEq] at h1
                      obtain rfl := h1
                      obtain ⟨w, hw⟩ :=
                        evalHIR_straight_varfree_lit e hfree hstr 256 henv ev hev
                      exact Or.inl ⟨w, hw⟩
                · have h2 : lookupHEnv henv id = some v := by
                    have hne : ¬ id' = id := Ne.symm heq
                    rwa [lookupHEnv_updateHEnv_ne hne] at h1
                  exact Or.inr h2
  | nop rest hrs ih =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          simp only [runHIRStmts] at hrun
          exact ih _ _ _ _ _ _ _ hrun hlook
  | ifStmt c th el rest hstr _ hath hael hrs ihr =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv c with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              exact Or.inr hlook
          | some ev =>
              rw [hev] at hrun
              split at hrun
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : ev = HIR.Expr.lit (.bool true) := by
                  simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv th
                    (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have h1 := ihr _ _ _ _ _ _ _ hrun hlook
                        rcases h1 with h1 | h1
                        · exact Or.inl h1
                        · have hpres := runHIRStmts_arm_lookup budget hath _ _ _ _ _ id har
                          rw [hpres] at h1
                          exact Or.inr h1
                    | broke =>
                        simp only [] at hrun
                        cases hrun
                        exact Or.inr ((runHIRStmts_arm_lookup budget hath _ _ _ _ _ id har) ▸ hlook)
                    | continued =>
                        simp only [] at hrun
                        cases hrun
                        exact Or.inr ((runHIRStmts_arm_lookup budget hath _ _ _ _ _ id har) ▸ hlook)
                    | returned e =>
                        simp only [] at hrun
                        cases hrun
                        exact Or.inr ((runHIRStmts_arm_lookup budget hath _ _ _ _ _ id har) ▸ hlook)
                    | stuck =>
                        simp only [] at hrun
                        cases hrun
                        exact Or.inr ((runHIRStmts_arm_lookup budget hath _ _ _ _ _ id har) ▸ hlook)
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : ev = HIR.Expr.lit (.bool false) := by
                  simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv el
                    (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have h1 := ihr _ _ _ _ _ _ _ hrun hlook
                        rcases h1 with h1 | h1
                        · exact Or.inl h1
                        · have hpres := runHIRStmts_arm_lookup budget hael _ _ _ _ _ id har
                          rw [hpres] at h1
                          exact Or.inr h1
                    | broke =>
                        simp only [] at hrun
                        cases hrun
                        exact Or.inr ((runHIRStmts_arm_lookup budget hael _ _ _ _ _ id har) ▸ hlook)
                    | continued =>
                        simp only [] at hrun
                        cases hrun
                        exact Or.inr ((runHIRStmts_arm_lookup budget hael _ _ _ _ _ id har) ▸ hlook)
                    | returned e =>
                        simp only [] at hrun
                        cases hrun
                        exact Or.inr ((runHIRStmts_arm_lookup budget hael _ _ _ _ _ id har) ▸ hlook)
                    | stuck =>
                        simp only [] at hrun
                        cases hrun
                        exact Or.inr ((runHIRStmts_arm_lookup budget hael _ _ _ _ _ id har) ▸ hlook)
              · cases hrun
                exact Or.inr hlook
  | returnStmt e rest hstr _ =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              exact Or.inr hlook
          | some ev =>
              rw [hev] at hrun
              simp only [] at hrun
              cases hrun
              exact Or.inr hlook
  | breakStmt rest hrs ih =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hrun
          exact Or.inr hlook
  | continueStmt rest hrs ih =>
      intro fuel henv henv' acc out id v hrun hlook
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          exact Or.inr hlook
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hrun
          exact Or.inr hlook

end Morph.HIRToMIRCorrect
