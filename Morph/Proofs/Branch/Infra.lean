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

/-!
# Stage C infrastructure: growth, freshness, and executor equations

First proof leaf out of the `HIRToMIRBranch` monolith: the C3 groundwork
the arm/loop workers all cite — `lowerStmtsCFG_arm_rho`, the `_inv` /
`_fresh` families, `BranchStep`/`BranchStmts`/`ArmStmts` inversions,
`execBlockFromIn` / `execInstrsFullFromIn` equations, the merge/join
executors, and the assembly helpers (`if_assembly_exit`, `getLast?_mem`,
`arrNe_restExit`). Moved verbatim; the monolith imports this back.
Later workers (`lowerStmtsCFG_arm_total` onward) stay in the monolith
until their own layer is cut.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-! ## C3 infrastructure: the lowering only grows, and block ids are unique

Loop 174. C3's induction runs the lowered blocks, so it needs three facts
about `lowerStmtsCFG`: supply and block ids only grow, every produced block
id lies in `[nextB, L.next)`, and the produced id sets are duplicate-free.
The induction is on the fragment predicates (`BranchStmts`/`ArmStmts`), not
on the statement list — an `if`'s arms are not structural subterms of the
list, but they are subterms of the predicate proof, and `ArmStmts` having no
`varDecl`/`assign` constructor is what discharges the lowering's arm refusal
without an extra contradiction case. -/

/- Block-assembly lemmas (`nodup_concat`, `findBlock_of_nodup_mem`,
`if_assembly_nodup`, `while_assembly_nodup`, `if_asm_mem_*`) live in
`Morph.Proofs.Branch.Assembly` (L0 proof crate: `Core`/`Total` only).
This module imports it back. -/




/-- Arm lowering never rebinds: for `ArmStmts` (no `varDecl`/`assign`
constructors) `ρ` flows through unchanged. Phase B accepts binds in
top-level arms, but those programs have no `ArmStmts` derivation, so this
still holds as stated — and the C3 workers cite it to discharge the merge
(`mergeIds ρ lt.ρ le.ρ = []`) on the old join path. The worker needs it to
transport the arm's `RelEnv` into the rest segment. -/
theorem lowerStmtsCFG_arm_rho (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal loop ss = some L →
      ArmStmts budget ss →
      L.ρ = ρ := by
  intro bId cont ρ supply nextB lastVal hasVal loop ss L h hss
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal loop L with
  | nil =>
      simp only [lowerStmtsCFG.eq_def] at h
      cases hv : hasVal with
      | true =>
          simp only [hv] at h
          obtain rfl := Option.some.inj h
          rfl
      | false =>
          simp only [hv] at h
          obtain rfl := Option.some.inj h
          rfl
  | exprStmt e rest hstr _ hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v0 true loop rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              show q.ρ = ρ
              exact ih _ _ _ _ _ _ _ _ _ hr
  | nop rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases hr : lowerStmtsCFG bId cont true ρ supply nextB lastVal
          hasVal loop rest with
      | none => rw [hr] at h; simp at h
      | some q =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          show q.ρ = ρ
          exact ih _ _ _ _ _ _ _ _ _ hr
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      simp only [lowerStmtsCFG] at h
      cases heC : lowerExpr ρ supply c with
      | none => rw [heC] at h; simp at h
      | some p =>
          obtain ⟨vc, ic, s1⟩ := p
          rw [heC] at h
          simp only [] at h
          cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
              (nextB + 3) lastVal false loop th with
          | none => rw [ht] at h; simp at h
          | some lt =>
              rw [ht] at h
              simp only [] at h
              cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                  lt.supply lt.next lastVal false loop el with
              | none => rw [he] at h; simp at h
              | some le =>
                  rw [he] at h
                  simp only [] at h
                  -- Phase B: binding-free arms have an empty merge set.
                  have hltρ : lt.ρ = ρ := iht _ _ _ _ _ _ _ _ _ ht
                  have hleρ : le.ρ = ρ := ihe _ _ _ _ _ _ _ _ _ he
                  have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                    rw [hltρ, hleρ]
                    exact mergeIds_self ρ
                  rw [hm] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                      (le.supply + 1) le.next le.supply true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      show lr.ρ = ρ
                      exact ihr _ _ _ _ _ _ _ _ _ hr
  | returnStmt e rest hstr _ =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          obtain rfl := Option.some.inj h
          rfl
  | breakStmt rest _ =>
      cases hlo : loop with
      | none => simp [hlo] at h
      | some info =>
          simp only [lowerStmtsCFG, hlo] at h
          cases hc : carryCopies ρ info.carried with
          | none => rw [hc] at h; simp at h
          | some copies =>
              rw [hc] at h
              obtain rfl := Option.some.inj h
              rfl
  | continueStmt rest _ =>
      cases hlo : loop with
      | none => simp [hlo] at h
      | some info =>
          simp only [lowerStmtsCFG, hlo] at h
          cases hc : carryCopies ρ info.carried with
          | none => rw [hc] at h; simp at h
          | some copies =>
              rw [hc] at h
              obtain rfl := Option.some.inj h
              rfl
theorem lowerStmtsCFG_arm_inv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal loop ss = some L →
      ArmStmts budget ss →
      nextB ≤ L.next ∧ supply ≤ L.supply ∧
        (∀ b ∈ L.blocks, nextB ≤ b.id ∧ b.id < L.next) ∧
        (L.blocks.map Block.id).Nodup := by
  intro bId cont ρ supply nextB lastVal hasVal loop ss L h hss
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal loop L with
  | nil =>
      simp only [lowerStmtsCFG.eq_def] at h
      cases hv : hasVal with
      | true =>
          simp only [hv] at h
          simp at h
          subst h
          exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
            List.nodup_nil⟩
      | false =>
          simp only [hv] at h
          simp at h
          subst h
          -- The valueless arm emits `const unit` into a fresh register.
          exact ⟨Nat.le_refl _, Nat.le_succ _, fun b hb => by simp at hb,
            List.nodup_nil⟩
  | exprStmt e rest hstr _ hrs ih =>
      simp at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp at h
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v0 true loop rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp at h
              subst h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr
              exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
  | nop rest hrs ih =>
      simp at h
      cases hr : lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal loop rest with
      | none => rw [hr] at h; simp at h          | some q =>
              rw [hr] at h
              simp at h
              subst h
              obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr
              exact ⟨hmn, hms, hbnd, hnod⟩
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      simp only [lowerStmtsCFG] at h
      cases heC : lowerExpr ρ supply c with
      | none => rw [heC] at h; simp at h
      | some p =>
          obtain ⟨vc, ic, s1⟩ := p
          rw [heC] at h
          simp only [] at h
          cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
              (nextB + 3) lastVal false loop th with
          | none => rw [ht] at h; simp at h
          | some lt =>
              rw [ht] at h
              simp only [] at h
              cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                  lt.supply lt.next lastVal false loop el with
              | none => rw [he] at h; simp at h
              | some le =>
                  rw [he] at h
                  simp only [] at h
                  -- Phase B: binding-free arms have an empty merge set.
                  have hltρ : lt.ρ = ρ :=
                    lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                  have hleρ : le.ρ = ρ :=
                    lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                  have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                    rw [hltρ, hleρ]
                    exact mergeIds_self ρ
                  rw [hm] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                      (le.supply + 1) le.next le.supply true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      dsimp only at ⊢
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                      obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                        iht _ _ _ _ _ _ _ _ _ ht
                      obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                        ihe _ _ _ _ _ _ _ _ _ he
                      obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                        ihr _ _ _ _ _ _ _ _ _ hr
                      refine ⟨by omega, by omega, ?_, ?_⟩
                      · intro b hb
                        simp only [List.mem_append, List.mem_singleton] at hb
                        rcases hb with (((((hb | rfl) | hb) | rfl) | rfl) | hb)
                        · obtain ⟨hlo, hhi⟩ := hbndt b hb
                          exact ⟨Nat.le_trans (Nat.le_add_right _ _) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_trans hmne
                              (Nat.le_trans hmnr (Nat.le_succ _)))⟩
                        · exact ⟨Nat.le_refl _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_add_right _ _) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · obtain ⟨hlo, hhi⟩ := hbnde b hb
                          exact ⟨Nat.le_trans (Nat.le_trans
                              (Nat.le_add_right _ _) hmnt) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_trans hmnr
                              (Nat.le_succ _))⟩
                        · exact ⟨Nat.le_succ _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_trans (Nat.le_succ _)
                                  (Nat.le_succ _)) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · exact ⟨Nat.le_add_right _ _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_succ _) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · obtain ⟨hlo, hhi⟩ := hbndr b hb
                          exact ⟨Nat.le_trans (Nat.le_trans
                              (Nat.le_trans (Nat.le_add_right _ _)
                                hmnt) hmne) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                      · exact if_assembly_nodup (A := lt.blocks)
                          (B := le.blocks) (C := lr.blocks)
                          (thenB := ⟨nextB, lt.instrs, lt.term⟩)
                          (elseB := ⟨nextB + 1, le.instrs, le.term⟩)
                          (joinB := ⟨nextB + 2,
                            [Instr.phi le.supply ((lt.blocks.getLast?.map
                              (fun b => b.id)).getD nextB) lt.val,
                             Instr.phi le.supply ((le.blocks.getLast?.map
                              (fun b => b.id)).getD (nextB + 1)) le.val] ++
                              lr.instrs,
                            lr.term⟩)
                          hmnt hmne hmnr hbndt hbnde hbndr
                          rfl rfl rfl hnodt hnode hnodr
  | returnStmt e rest hstr _ =>
      simp at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp at h
          subst h
          have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
          exact ⟨Nat.le_refl _, hs1, fun b hb => by simp at hb,
            List.nodup_nil⟩
  | breakStmt rest hrs ih =>
      -- A `break` is terminal (like `return`): under `loop = none` it
      -- refuses, under `some` it snapshots the carried regs then exits.
      cases hlo : loop with
      | none => simp [hlo] at h
      | some info =>
          simp only [lowerStmtsCFG, hlo] at h
          cases hc : carryCopies ρ info.carried with
          | none => simp [hc] at h
          | some copies =>
              simp [hc] at h
              subst h
              exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
                List.nodup_nil⟩
  | continueStmt rest hrs ih =>
      cases hlo : loop with
      | none => simp [hlo] at h
      | some info =>
          simp only [lowerStmtsCFG, hlo] at h
          cases hc : carryCopies ρ info.carried with
          | none => simp [hc] at h
          | some copies =>
              simp [hc] at h
              subst h
              exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
                List.nodup_nil⟩

/-- Static invariant for loop bodies: the `branch_inv` conclusion under a
`LoopStmts` hypothesis. `branch_inv` cites this for a loop body, which is not
a structural subterm of the enclosing statement list. List induction (the
`induction` tactic does not support the `mutual` inductive) plus `cases`
inversion of the body proof; each `if` arm cites `arm_inv` as in `branch_inv`. -/
theorem lowerStmtsCFG_loopBody_inv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop ss = some L →
      LoopStmts budget ss →
      nextB ≤ L.next ∧ supply ≤ L.supply ∧
        (∀ b ∈ L.blocks, nextB ≤ b.id ∧ b.id < L.next) ∧
        (L.blocks.map Block.id).Nodup := by
  intro bId cont ρ supply nextB lastVal hasVal loop ss
  induction ss generalizing bId cont ρ supply nextB lastVal hasVal loop with
  | nil =>
      intro L h hss
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          simp at h
          subst h
          exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
            List.nodup_nil⟩
  | cons s rest ih =>
      intro L h hss
      cases hss with
      | exprStmt e rest hstr _ hrs =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp at h
              cases hr : lowerStmtsCFG bId cont false ρ s1 nextB v0 true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp at h
                  subst h
                  have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr hrs
                  exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
      | varDecl id τ init rest hstr _ hrs _ =>
          cases hlo : loop with
          | some _ => simp [hlo] at h
          | none =>
              simp [hlo] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp at h
                  cases hr : lowerStmtsCFG bId cont false ((id, vb) :: ρ) s1
                      nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp at h
                      subst h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr hrs
                      exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
      | assign id e rest hstr _ hrs _ =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp at h
              cases hr : lowerStmtsCFG bId cont false (updAssoc ρ id v) s1
                  nextB lastVal true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp at h
                  subst h
                  have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr hrs
                  exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
      | nop rest hrs =>
          simp at h
          cases hr : lowerStmtsCFG bId cont false ρ supply nextB
              lastVal hasVal loop rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp at h
              subst h
              obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr hrs
              exact ⟨hmn, hms, hbnd, hnod⟩
      | ifStmt c th el rest hstr _ hath hael hrs _ _ =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                  (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                      true ρ lt.supply lt.next lastVal false loop el with
                  | none => rw [he] at h; simp at h
                  | some le =>
                      rw [he] at h
                      simp only [] at h
                      -- Phase B: binding-free arms have an empty merge set.
                      have hltρ : lt.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                      have hleρ : le.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                      have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                        rw [hltρ, hleρ]
                        exact mergeIds_self ρ
                      rw [hm] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont false ρ
                          (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          obtain rfl := Option.some.inj h
                          dsimp only at ⊢
                          have hs1 : supply ≤ s1 :=
                            lower_mono.1 _ _ _ _ _ _ heC
                          obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath
                          obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he
                              hael
                          obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                            ih _ _ _ _ _ _ _ _ _ hr hrs
                          refine ⟨by omega, by omega, ?_, ?_⟩
                          · intro b hb
                            simp only [List.mem_append, List.mem_singleton] at hb
                            rcases hb with (((((hb | rfl) | hb) | rfl) | rfl) | hb)
                            · obtain ⟨hlo, hhi⟩ := hbndt b hb
                              exact ⟨Nat.le_trans (Nat.le_add_right _ _) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_trans hmne
                                  (Nat.le_trans hmnr (Nat.le_succ _)))⟩
                            · exact ⟨Nat.le_refl _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_add_right _ _) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · obtain ⟨hlo, hhi⟩ := hbnde b hb
                              exact ⟨Nat.le_trans (Nat.le_trans
                                  (Nat.le_add_right _ _) hmnt) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_trans hmnr
                                  (Nat.le_succ _))⟩
                            · exact ⟨Nat.le_succ _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_trans (Nat.le_succ _)
                                      (Nat.le_succ _)) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · exact ⟨Nat.le_add_right _ _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_succ _) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · obtain ⟨hlo, hhi⟩ := hbndr b hb
                              exact ⟨Nat.le_trans (Nat.le_trans
                                  (Nat.le_trans (Nat.le_add_right _ _)
                                    hmnt) hmne) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                          · exact if_assembly_nodup (A := lt.blocks)
                              (B := le.blocks) (C := lr.blocks)
                              (thenB := ⟨nextB, lt.instrs, lt.term⟩)
                              (elseB := ⟨nextB + 1, le.instrs, le.term⟩)
                              (joinB := ⟨nextB + 2,
                                [Instr.phi le.supply ((lt.blocks.getLast?.map
                                  (fun b => b.id)).getD nextB) lt.val,
                                 Instr.phi le.supply ((le.blocks.getLast?.map
                                  (fun b => b.id)).getD (nextB + 1)) le.val] ++
                                  lr.instrs,
                                lr.term⟩)
                              hmnt hmne hmnr hbndt hbnde hbndr
                              rfl rfl rfl hnodt hnode hnodr
      | ifStmtBreak c th el rest hstr _ hath hael hrs harm =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                  (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                      true ρ lt.supply lt.next lastVal false loop el with
                  | none => rw [he] at h; simp at h
                  | some le =>
                      rw [he] at h
                      simp only [] at h
                      -- Phase B: binding-free arms have an empty merge set.
                      have hltρ : lt.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                      have hleρ : le.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                      have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                        rw [hltρ, hleρ]
                        exact mergeIds_self ρ
                      rw [hm] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont false ρ
                          (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          obtain rfl := Option.some.inj h
                          dsimp only at ⊢
                          have hs1 : supply ≤ s1 :=
                            lower_mono.1 _ _ _ _ _ _ heC
                          obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath
                          obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he
                              hael
                          obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                            ih _ _ _ _ _ _ _ _ _ hr hrs
                          refine ⟨by omega, by omega, ?_, ?_⟩
                          · intro b hb
                            simp only [List.mem_append, List.mem_singleton] at hb
                            rcases hb with (((((hb | rfl) | hb) | rfl) | rfl) | hb)
                            · obtain ⟨hlo, hhi⟩ := hbndt b hb
                              exact ⟨Nat.le_trans (Nat.le_add_right _ _) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_trans hmne
                                  (Nat.le_trans hmnr (Nat.le_succ _)))⟩
                            · exact ⟨Nat.le_refl _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_add_right _ _) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · obtain ⟨hlo, hhi⟩ := hbnde b hb
                              exact ⟨Nat.le_trans (Nat.le_trans
                                  (Nat.le_add_right _ _) hmnt) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_trans hmnr
                                  (Nat.le_succ _))⟩
                            · exact ⟨Nat.le_succ _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_trans (Nat.le_succ _)
                                      (Nat.le_succ _)) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · exact ⟨Nat.le_add_right _ _,
                                Nat.lt_of_le_of_lt (Nat.le_trans
                                  (Nat.le_trans (Nat.le_trans
                                    (Nat.le_succ _) hmnt) hmne) hmnr)
                                  (Nat.lt_succ_self _)⟩
                            · obtain ⟨hlo, hhi⟩ := hbndr b hb
                              exact ⟨Nat.le_trans (Nat.le_trans
                                  (Nat.le_trans (Nat.le_add_right _ _)
                                    hmnt) hmne) hlo,
                                Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                          · exact if_assembly_nodup (A := lt.blocks)
                              (B := le.blocks) (C := lr.blocks)
                              (thenB := ⟨nextB, lt.instrs, lt.term⟩)
                              (elseB := ⟨nextB + 1, le.instrs, le.term⟩)
                              (joinB := ⟨nextB + 2,
                                [Instr.phi le.supply ((lt.blocks.getLast?.map
                                  (fun b => b.id)).getD nextB) lt.val,
                                 Instr.phi le.supply ((le.blocks.getLast?.map
                                  (fun b => b.id)).getD (nextB + 1)) le.val] ++
                                  lr.instrs,
                                lr.term⟩)
                              hmnt hmne hmnr hbndt hbnde hbndr
                              rfl rfl rfl hnodt hnode hnodr
      | returnStmt e rest hstr _ =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp at h
              subst h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              exact ⟨Nat.le_refl _, hs1, fun b hb => by simp at hb,
                List.nodup_nil⟩
      | breakStmt rest _ =>
          cases hlo : loop with
          | none => simp [hlo] at h
          | some info =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hc : carryCopies ρ info.carried with
              | none => simp [hc] at h
              | some copies =>
                  simp [hc] at h
                  subst h
                  exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
                    List.nodup_nil⟩
      | continueStmt rest _ =>
          cases hlo : loop with
          | none => simp [hlo] at h
          | some info =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hc : carryCopies ρ info.carried with
              | none => simp [hc] at h
              | some copies =>
                  simp [hc] at h
                  subst h
                  exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
                    List.nodup_nil⟩

/-! ## Freshness is preserved (C7-core, piece 1)

`whileLoop_correct` concludes `FreshAbove lb.ρ (lb.supply + 1)` — the loop
body's exit env mentions only registers below its supply — and all three
`whileLoop_correct` use-sites take that fact from the deferred theorem. These
three lemmas prove it outright, mirroring the `branch_inv`/`arm_inv`/
`loopBody_inv` trio case-for-case (same inductions, same supply-growth facts
from `arm_inv`, only the conclusion changes): arm lowering never rebinds, so
its input freshness suffices; loop bodies and branch programs thread it
through `lowerExpr` (`lower_result_lt`), `varDecl` (fresh head register),
`assign` (`updAssoc_mem`), and the `mkCarried` allocation
(`mkCarried_growth_fresh`). -/
theorem lowerStmtsCFG_arm_fresh (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal loop ss = some L →
      ArmStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      FreshAbove L.ρ L.supply := by
  intro bId cont ρ supply nextB lastVal hasVal loop ss L h hss hfresh hlast
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal loop L with
  | nil =>
      simp only [lowerStmtsCFG.eq_def] at h
      cases hv : hasVal with
      | true =>
          simp only [hv] at h
          simp at h
          subst h
          exact hfresh
      | false =>
          simp only [hv] at h
          simp at h
          subst h
          exact FreshAbove.mono ρ supply (supply + 1) (Nat.le_succ _) hfresh
  | exprStmt e rest hstr _ hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v true loop rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              have hv : v < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
              have hq := ih _ _ _ _ _ _ _ _ _ hr
                (FreshAbove.mono ρ supply s1 hs1 hfresh) hv
              obtain rfl := Option.some.inj h
              exact hq
  | nop rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      exact ih _ _ _ _ _ _ _ _ _ h hfresh hlast  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      simp only [lowerStmtsCFG] at h
      cases heC : lowerExpr ρ supply c with
      | none => rw [heC] at h; simp at h
      | some p =>
          obtain ⟨vc, ic, s1⟩ := p
          rw [heC] at h
          simp only [] at h
          cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
              (nextB + 3) lastVal false loop th with
          | none => rw [ht] at h; simp at h
          | some lt =>
              rw [ht] at h
              simp only [] at h
              cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                  lt.supply lt.next lastVal false loop el with
              | none => rw [he] at h; simp at h
              | some le =>
                  rw [he] at h
                  simp only [] at h
                  -- Phase B: binding-free arms have an empty merge set.
                  have hltρ : lt.ρ = ρ :=
                    lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                  have hleρ : le.ρ = ρ :=
                    lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                  have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                    rw [hltρ, hleρ]
                    exact mergeIds_self ρ
                  rw [hm] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                      (le.supply + 1) le.next le.supply true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                      have hlt : s1 ≤ lt.supply :=
                        (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht
                          hath).2.1
                      have hle : lt.supply ≤ le.supply :=
                        (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he
                          hael).2.1
                      have hq := ihr _ _ _ _ _ _ _ _ _ hr
                        (FreshAbove.mono ρ supply (le.supply + 1) (by omega)
                          hfresh)
                        (Nat.lt_succ_self _)
                      obtain rfl := Option.some.inj h
                      dsimp only at ⊢
                      exact hq
  | returnStmt e rest hstr _ =>
      simp at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp at h
          subst h
          exact FreshAbove.mono ρ supply s1
            (lower_mono.1 _ _ _ _ _ _ he) hfresh
  | breakStmt rest hrs ih =>
      cases hlo : loop with
      | none => simp [hlo] at h
      | some info =>
          simp only [lowerStmtsCFG, hlo] at h
          cases hc : carryCopies ρ info.carried with
          | none => simp [hc] at h
          | some copies =>
              simp [hc] at h
              subst h
              exact hfresh
  | continueStmt rest hrs ih =>
      cases hlo : loop with
      | none => simp [hlo] at h
      | some info =>
          simp only [lowerStmtsCFG, hlo] at h
          cases hc : carryCopies ρ info.carried with
          | none => simp [hc] at h
          | some copies =>
              simp [hc] at h
              subst h
              exact hfresh

/-- Freshness is preserved by loop-body lowering (list induction plus `cases`
inversion, exactly as in `loopBody_inv`; each `if` arm cites `arm_fresh`). -/
theorem lowerStmtsCFG_loopBody_fresh (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop ss = some L →
      LoopStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      FreshAbove L.ρ L.supply := by
  intro bId cont ρ supply nextB lastVal hasVal loop ss
  induction ss generalizing bId cont ρ supply nextB lastVal hasVal loop with
  | nil =>
      intro L h hss hfresh hlast
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          simp at h
          subst h
          exact hfresh
  | cons s rest ih =>
      intro L h hss hfresh hlast
      cases hss with
      | exprStmt e rest hstr _ hloop =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp at h
              cases hr : lowerStmtsCFG bId cont false ρ s1 nextB v true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp at h
                  have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  have hv : v < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
                  have hq := ih _ _ _ _ _ _ _ _ _ hr hloop
                    (FreshAbove.mono ρ supply s1 hs1 hfresh) hv
                  subst h
                  exact hq
      | varDecl id τ init rest hstr _ hloop _ =>
          cases hlo : loop with
          | some _ => simp [hlo] at h
          | none =>
              simp [hlo] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp at h
                  cases hr : lowerStmtsCFG bId cont false ((id, vb) :: ρ) s1
                      nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp at h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      have hvb : vb < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
                      have hfr1 : FreshAbove ((id, vb) :: ρ) s1 := by
                        intro j v hmem
                        simp only [List.mem_cons, Prod.mk.injEq] at hmem
                        rcases hmem with ⟨rfl, rfl⟩ | hmem
                        · exact hvb
                        · exact Nat.lt_of_lt_of_le (hfresh _ _ hmem) hs1
                      have hq := ih _ _ _ _ _ _ _ _ _ hr hloop hfr1
                        (Nat.lt_of_lt_of_le hlast hs1)
                      subst h
                      exact hq
      | assign id e rest hstr _ hloop _ =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp at h
              cases hr : lowerStmtsCFG bId cont false (updAssoc ρ id v) s1
                  nextB lastVal true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp at h
                  have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  have hv : v < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
                  have hfr1 : FreshAbove (updAssoc ρ id v) s1 := by
                    intro j w hmem
                    rcases updAssoc_mem ρ id v j w hmem with ⟨rfl, rfl⟩ | hmem
                    · exact hv
                    · exact Nat.lt_of_lt_of_le (hfresh _ _ hmem) hs1
                  have hq := ih _ _ _ _ _ _ _ _ _ hr hloop hfr1
                    (Nat.lt_of_lt_of_le hlast hs1)
                  subst h
                  exact hq
      | nop rest hloop =>
          simp only [lowerStmtsCFG] at h
          exact ih _ _ _ _ _ _ _ _ L h hloop hfresh hlast
      | ifStmt c th el rest hstr _ hath hael hloop _ _ =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                  (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                      true ρ lt.supply lt.next lastVal false loop el with
                  | none => rw [he] at h; simp at h
                  | some le =>
                      rw [he] at h
                      simp only [] at h
                      -- Phase B: binding-free arms have an empty merge set.
                      have hltρ : lt.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                      have hleρ : le.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                      have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                        rw [hltρ, hleρ]
                        exact mergeIds_self ρ
                      rw [hm] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont false ρ
                          (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                          have hlt : s1 ≤ lt.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht
                              hath).2.1
                          have hle : lt.supply ≤ le.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he
                              hael).2.1
                          have hq := ih _ _ _ _ _ _ _ _ _ hr hloop
                            (FreshAbove.mono ρ supply (le.supply + 1) (by omega)
                              hfresh)
                            (Nat.lt_succ_self _)
                          obtain rfl := Option.some.inj h
                          dsimp only at ⊢
                          exact hq
      | ifStmtBreak c th el rest hstr _ hath hael hloop _ =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                  (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                      true ρ lt.supply lt.next lastVal false loop el with
                  | none => rw [he] at h; simp at h
                  | some le =>
                      rw [he] at h
                      simp only [] at h
                      -- Phase B: binding-free arms have an empty merge set.
                      have hltρ : lt.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                      have hleρ : le.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                      have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                        rw [hltρ, hleρ]
                        exact mergeIds_self ρ
                      rw [hm] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont false ρ
                          (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                          have hlt : s1 ≤ lt.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht
                              hath).2.1
                          have hle : lt.supply ≤ le.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he
                              hael).2.1
                          have hq := ih _ _ _ _ _ _ _ _ _ hr hloop
                            (FreshAbove.mono ρ supply (le.supply + 1) (by omega)
                              hfresh)
                            (Nat.lt_succ_self _)
                          obtain rfl := Option.some.inj h
                          dsimp only at ⊢
                          exact hq
      | returnStmt e rest hstr _ =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp at h
              subst h
              exact FreshAbove.mono ρ supply s1
                (lower_mono.1 _ _ _ _ _ _ he) hfresh
      | breakStmt rest hloop =>
          cases hlo : loop with
          | none => simp [hlo] at h
          | some info =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hc : carryCopies ρ info.carried with
              | none => simp [hc] at h
              | some copies =>
                  simp [hc] at h
                  subst h
                  exact hfresh
      | continueStmt rest hloop =>
          cases hlo : loop with
          | none => simp [hlo] at h
          | some info =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hc : carryCopies ρ info.carried with
              | none => simp [hc] at h
              | some copies =>
                  simp [hc] at h
                  subst h
                  exact hfresh

/-- Freshness is preserved by branch lowering: the `branch_inv` induction
with a freshness conclusion. The `whileStmt` body cites `loopBody_fresh`
(exactly as `branch_inv` cites `loopBody_inv`); arms cite `arm_fresh`. -/
theorem lowerStmtsCFG_branch_fresh (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop ss = some L →
      BranchStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      FreshAbove L.ρ L.supply := by
  intro bId cont ρ supply nextB lastVal hasVal loop ss
  induction ss generalizing bId cont ρ supply nextB lastVal hasVal loop with
  | nil =>
      intro L h hss hfresh hlast
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          simp at h
          subst h
          exact hfresh
  | cons s rest ih =>
      intro L h hss hfresh hlast
      cases hss with
      | cons hs hrs =>
          cases hs with
          | exprStmt e hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId cont false ρ s1 nextB v true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      have hv : v < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
                      have hq := ih _ _ _ _ _ _ _ _ _ hr hrs
                        (FreshAbove.mono ρ supply s1 hs1 hfresh) hv
                      obtain rfl := Option.some.inj h
                      exact hq
          | varDecl id τ init hstr _ =>
              cases hlo : loop with
              | some _ => simp [hlo] at h
              | none =>
                  simp [hlo] at h
                  cases he : lowerExpr ρ supply init with
                  | none => rw [he] at h; simp at h
                  | some p =>
                      obtain ⟨vb, ib, s1⟩ := p
                      rw [he] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG bId cont false ((id, vb) :: ρ) s1
                          nextB lastVal true none rest with
                      | none => rw [hr] at h; simp at h
                      | some q =>
                          rw [hr] at h
                          simp only [] at h
                          have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                          have hvb : vb < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
                          have hfr1 : FreshAbove ((id, vb) :: ρ) s1 := by
                            intro j v hmem
                            simp only [List.mem_cons, Prod.mk.injEq] at hmem
                            rcases hmem with ⟨rfl, rfl⟩ | hmem
                            · exact hvb
                            · exact Nat.lt_of_lt_of_le (hfresh _ _ hmem) hs1
                          have hq := ih _ _ _ _ _ _ _ _ _ hr hrs hfr1
                            (Nat.lt_of_lt_of_le hlast hs1)
                          obtain rfl := Option.some.inj h
                          exact hq
          | assign id e hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId cont false (updAssoc ρ id v) s1
                      nextB lastVal true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      have hv : v < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
                      have hfr1 : FreshAbove (updAssoc ρ id v) s1 := by
                        intro j w hmem
                        rcases updAssoc_mem ρ id v j w hmem with ⟨rfl, rfl⟩ | hmem
                        · exact hv
                        · exact Nat.lt_of_lt_of_le (hfresh _ _ hmem) hs1
                      have hq := ih _ _ _ _ _ _ _ _ _ hr hrs hfr1
                        (Nat.lt_of_lt_of_le hlast hs1)
                      obtain rfl := Option.some.inj h
                      exact hq
          | nop =>
              simp only [lowerStmtsCFG] at h
              exact ih _ _ _ _ _ _ _ _ _ h hrs hfresh hlast
          | ifStmt c th el hstr _ hath hael =>
              simp only [lowerStmtsCFG] at h
              cases heC : lowerExpr ρ supply c with
              | none => rw [heC] at h; simp at h
              | some p =>
                  obtain ⟨vc, ic, s1⟩ := p
                  rw [heC] at h
                  simp only [] at h
                  cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                      (nextB + 3) lastVal false loop th with
                  | none => rw [ht] at h; simp at h
                  | some lt =>
                      rw [ht] at h
                      simp only [] at h
                      cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                          true ρ lt.supply lt.next lastVal false loop el with
                      | none => rw [he] at h; simp at h
                      | some le =>
                          rw [he] at h
                          simp only [] at h
                          -- Phase B: binding-free arms have an empty merge set.
                          have hltρ : lt.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                          have hleρ : le.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                          have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                            rw [hltρ, hleρ]
                            exact mergeIds_self ρ
                          rw [hm] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) cont false ρ
                              (le.supply + 1) le.next le.supply true loop rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                              have hlt : s1 ≤ lt.supply :=
                                (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht
                                  hath).2.1
                              have hle : lt.supply ≤ le.supply :=
                                (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he
                                  hael).2.1
                              have hq := ih _ _ _ _ _ _ _ _ _ hr hrs
                                (FreshAbove.mono ρ supply (le.supply + 1) (by omega)
                                  hfresh)
                                (Nat.lt_succ_self _)
                              obtain rfl := Option.some.inj h
                              dsimp only at ⊢
                              exact hq
          | breakStmt =>
              cases hlo : loop with
              | none => simp [hlo] at h
              | some info =>
                  simp only [lowerStmtsCFG, hlo] at h
                  cases hc : carryCopies ρ info.carried with
                  | none => simp [hc] at h
                  | some copies =>
                      simp [hc] at h
                      subst h
                      exact hfresh
          | continueStmt =>
              cases hlo : loop with
              | none => simp [hlo] at h
              | some info =>
                  simp only [lowerStmtsCFG, hlo] at h
                  cases hc : carryCopies ρ info.carried with
                  | none => simp [hc] at h
                  | some copies =>
                      simp [hc] at h
                      subst h
                      exact hfresh
          | whileStmt c body hstr _ hloop =>
              cases hlo : loop with
              | some info => simp [hlo] at h
              | none =>
                  rw [hlo] at h
                  simp only [lowerStmtsCFG] at h
                  cases hm : mkCarried ρ supply ((dedupIds (assignedIds body)).filterMap
                      (fun id => (rhoLookup ρ id).map (fun _ => id))) with
                  | none => rw [hm] at h; simp at h
                  | some q =>
                      obtain ⟨carried, sA, ρb⟩ := q
                      rw [hm] at h
                      simp only [] at h
                      cases heC : lowerExpr ρb sA c with
                      | none => rw [heC] at h; simp at h
                      | some p =>
                          obtain ⟨vc, ic, s1⟩ := p
                          rw [heC] at h
                          simp only [] at h
                          cases hb : lowerStmtsCFG (nextB + 2) (some nextB) false ρb
                              (s1 + 1) (nextB + 3) s1 true
                              (loop := some ⟨nextB, nextB + 1, carried⟩) body with
                          | none => rw [hb] at h; simp at h
                          | some lb =>
                              rw [hb] at h
                              simp only [] at h
                              cases hr : lowerStmtsCFG (nextB + 1) cont false ρb
                                  (lb.supply + 1) lb.next lb.supply true none rest with
                              | none => rw [hr] at h; simp at h
                              | some lr =>
                                  rw [hr] at h
                                  simp only [] at h
                                  cases hp : mkHeaderPhis ρ bId carried
                                      ((lb.blocks.getLast?.map fun b => b.id).getD
                                        (nextB + 2))
                                      lb.ρ
                                      (backEdgePreds lb nextB) with
                                  | none => rw [hp] at h; simp at h
                                  | some phis =>
                                      rw [hp] at h
                                      simp only [] at h
                                      have hfrb : FreshAbove ρb sA :=
                                        (mkCarried_growth_fresh hfresh hm).2
                                      have hsA : sA ≤ s1 :=
                                        lower_mono.1 _ _ _ _ _ _ heC
                                      have hbody : FreshAbove lb.ρ lb.supply :=
                                        lowerStmtsCFG_loopBody_fresh budget _ _ _ _ _ _ _ _ _ _ hb
                                          hloop
                                          (FreshAbove.mono ρb sA (s1 + 1) (by omega)
                                            hfrb)
                                          (Nat.lt_succ_self _)
                                      have hgrow : s1 + 1 ≤ lb.supply :=
                                        (lowerStmtsCFG_loopBody_inv budget _ _ _ _ _ _ _ _ _ _ hb
                                          hloop).2.1
                                      have hfrb' : FreshAbove ρb (lb.supply + 1) :=
                                        FreshAbove.mono ρb sA (lb.supply + 1)
                                          (by omega) hfrb
                                      have hq := ih _ _ _ _ _ _ _ _ _ hr hrs hfrb'
                                        (Nat.lt_succ_self _)
                                      obtain rfl := Option.some.inj h
                                      dsimp only at ⊢
                                      exact hq
      | returnStmt e rest hstr _ =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp at h
              subst h
              exact FreshAbove.mono ρ supply s1
                (lower_mono.1 _ _ _ _ _ _ he) hfresh

/-- Master invariant over the straight-line-carrying fragment: supply and
block ids only grow, every produced block id is fresh for the call and
below the returned supply of ids, and the produced ids are duplicate-free.
`arm` is fixed `false`: bindings are allowed and the lowering handles them. -/
theorem lowerStmtsCFG_branch_inv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop ss = some L →
      BranchStmts budget ss →
      nextB ≤ L.next ∧ supply ≤ L.supply ∧
        (∀ b ∈ L.blocks, nextB ≤ b.id ∧ b.id < L.next) ∧
        (L.blocks.map Block.id).Nodup := by
  intro bId cont ρ supply nextB lastVal hasVal loop ss
  induction ss generalizing bId cont ρ supply nextB lastVal hasVal loop with
  | nil =>
      intro L h hss
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          simp at h
          subst h
          exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
            List.nodup_nil⟩
  | cons s rest ih =>
      intro L h hss
      cases hss with
      | cons hs hrs =>
          cases hs with
          | exprStmt e hstr _ =>
              simp at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v0, ie, s1⟩ := p
                  rw [he] at h
                  simp at h
                  cases hr : lowerStmtsCFG bId cont false ρ s1 nextB v0 true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp at h
                      subst h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr hrs
                      exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
          | varDecl id τ init hstr _ =>
              cases hlo : loop with
              | some _ => simp [hlo] at h
              | none =>
                  simp [hlo] at h
                  cases he : lowerExpr ρ supply init with
                  | none => rw [he] at h; simp at h
                  | some p =>
                      obtain ⟨vb, ib, s1⟩ := p
                      rw [he] at h
                      simp at h
                      cases hr : lowerStmtsCFG bId cont false ((id, vb) :: ρ) s1
                          nextB lastVal true none rest with
                      | none => rw [hr] at h; simp at h
                      | some q =>
                          rw [hr] at h
                          simp at h
                          subst h
                          have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                          obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr hrs
                          exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
          | assign id e hstr _ =>
              simp at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp at h
                  cases hr : lowerStmtsCFG bId cont false (updAssoc ρ id v) s1
                      nextB lastVal true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp at h
                      subst h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr hrs
                      exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
          | nop =>
              simp at h
              cases hr : lowerStmtsCFG bId cont false ρ supply nextB
                  lastVal hasVal loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp at h
                  subst h
                  obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ _ hr hrs
                  exact ⟨hmn, hms, hbnd, hnod⟩
          | ifStmt c th el hstr _ hath hael =>
              -- Peel with `unfold`, never `simp`: full `simp` normalizes the
              -- block assembly (`[T] ++ X` to `T :: X`), breaking the syntactic
              -- match the membership split and `if_assembly_nodup` need.
              simp only [lowerStmtsCFG] at h
              cases heC : lowerExpr ρ supply c with
              | none => rw [heC] at h; simp at h
              | some p =>
                  obtain ⟨vc, ic, s1⟩ := p
                  rw [heC] at h
                  simp only [] at h
                  cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                      (nextB + 3) lastVal false loop th with
                  | none => rw [ht] at h; simp at h
                  | some lt =>
                      rw [ht] at h
                      simp only [] at h
                      cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                          true ρ lt.supply lt.next lastVal false loop el with
                      | none => rw [he] at h; simp at h
                      | some le =>
                          rw [he] at h
                          simp only [] at h
                          -- Phase B: binding-free arms have an empty merge set.
                          have hltρ : lt.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                          have hleρ : le.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                          have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                            rw [hltρ, hleρ]
                            exact mergeIds_self ρ
                          rw [hm] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) cont false ρ
                              (le.supply + 1) le.next le.supply true loop rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              obtain rfl := Option.some.inj h
                              dsimp only at ⊢
                              have hs1 : supply ≤ s1 :=
                                lower_mono.1 _ _ _ _ _ _ heC
                              obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath
                              obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he
                                  hael
                              obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                                ih _ _ _ _ _ _ _ _ _ hr hrs
                              refine ⟨by omega, by omega, ?_, ?_⟩
                              · intro b hb
                                simp only [List.mem_append, List.mem_singleton] at hb
                                rcases hb with (((((hb | rfl) | hb) | rfl) | rfl) | hb)
                                · obtain ⟨hlo, hhi⟩ := hbndt b hb
                                  exact ⟨Nat.le_trans (Nat.le_add_right _ _) hlo,
                                    Nat.lt_of_lt_of_le hhi (Nat.le_trans hmne
                                      (Nat.le_trans hmnr (Nat.le_succ _)))⟩
                                · exact ⟨Nat.le_refl _,
                                    Nat.lt_of_le_of_lt (Nat.le_trans
                                      (Nat.le_trans (Nat.le_trans
                                        (Nat.le_add_right _ _) hmnt) hmne) hmnr)
                                      (Nat.lt_succ_self _)⟩
                                · obtain ⟨hlo, hhi⟩ := hbnde b hb
                                  exact ⟨Nat.le_trans (Nat.le_trans
                                      (Nat.le_add_right _ _) hmnt) hlo,
                                    Nat.lt_of_lt_of_le hhi (Nat.le_trans hmnr
                                      (Nat.le_succ _))⟩
                                · exact ⟨Nat.le_succ _,
                                    Nat.lt_of_le_of_lt (Nat.le_trans
                                      (Nat.le_trans (Nat.le_trans
                                        (Nat.le_trans (Nat.le_succ _)
                                          (Nat.le_succ _)) hmnt) hmne) hmnr)
                                      (Nat.lt_succ_self _)⟩
                                · exact ⟨Nat.le_add_right _ _,
                                    Nat.lt_of_le_of_lt (Nat.le_trans
                                      (Nat.le_trans (Nat.le_trans
                                        (Nat.le_succ _) hmnt) hmne) hmnr)
                                      (Nat.lt_succ_self _)⟩
                                · obtain ⟨hlo, hhi⟩ := hbndr b hb
                                  exact ⟨Nat.le_trans (Nat.le_trans
                                      (Nat.le_trans (Nat.le_add_right _ _)
                                        hmnt) hmne) hlo,
                                    Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                              · exact if_assembly_nodup (A := lt.blocks)
                                  (B := le.blocks) (C := lr.blocks)
                                  (thenB := ⟨nextB, lt.instrs, lt.term⟩)
                                  (elseB := ⟨nextB + 1, le.instrs, le.term⟩)
                                  (joinB := ⟨nextB + 2,
                                    [Instr.phi le.supply ((lt.blocks.getLast?.map
                                      (fun b => b.id)).getD nextB) lt.val,
                                     Instr.phi le.supply ((le.blocks.getLast?.map
                                      (fun b => b.id)).getD (nextB + 1)) le.val] ++
                                      lr.instrs,
                                    lr.term⟩)
                                  hmnt hmne hmnr hbndt hbnde hbndr
                                  rfl rfl rfl hnodt hnode hnodr
          | breakStmt =>
              cases hlo : loop with
              | none => simp [hlo] at h
              | some info =>
                  simp only [lowerStmtsCFG, hlo] at h
                  cases hc : carryCopies ρ info.carried with
                  | none => simp [hc] at h
                  | some copies =>
                      simp [hc] at h
                      subst h
                      exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
                        List.nodup_nil⟩
          | continueStmt =>
              cases hlo : loop with
              | none => simp [hlo] at h
              | some info =>
                  simp only [lowerStmtsCFG, hlo] at h
                  cases hc : carryCopies ρ info.carried with
                  | none => simp [hc] at h
                  | some copies =>
                      simp [hc] at h
                      subst h
                      exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
                        List.nodup_nil⟩
          | whileStmt c body hstr _ hloop =>
              cases hlo : loop with
              | some info => simp [hlo] at h
              | none =>
                  rw [hlo] at h
                  simp only [lowerStmtsCFG] at h
                  cases hm : mkCarried ρ supply ((dedupIds (assignedIds body)).filterMap
                      (fun id => (rhoLookup ρ id).map (fun _ => id))) with
                  | none => rw [hm] at h; simp at h
                  | some q =>
                      obtain ⟨carried, sA, ρb⟩ := q
                      rw [hm] at h
                      simp only [] at h
                      cases heC : lowerExpr ρb sA c with
                      | none => rw [heC] at h; simp at h
                      | some p =>
                          obtain ⟨vc, ic, s1⟩ := p
                          rw [heC] at h
                          simp only [] at h
                          cases hb : lowerStmtsCFG (nextB + 2) (some nextB) false ρb
                              (s1 + 1) (nextB + 3) s1 true
                              (loop := some ⟨nextB, nextB + 1, carried⟩) body with
                          | none => rw [hb] at h; simp at h
                          | some lb =>
                              rw [hb] at h
                              simp only [] at h
                              cases hr : lowerStmtsCFG (nextB + 1) cont false ρb
                                  (lb.supply + 1) lb.next lb.supply true none rest with
                              | none => rw [hr] at h; simp at h
                              | some lr =>
                                  rw [hr] at h
                                  simp only [] at h
                                  cases hp : mkHeaderPhis ρ bId carried
                                      ((lb.blocks.getLast?.map fun b => b.id).getD
                                        (nextB + 2))
                                      lb.ρ
                                      (backEdgePreds lb nextB) with
                                  | none => rw [hp] at h; simp at h
                                  | some phis =>
                                      rw [hp] at h
                                      obtain rfl := Option.some.inj h
                                      dsimp only at ⊢
                                      have hsA : supply ≤ sA := mkCarried_le hm
                                      have hs1 : sA ≤ s1 :=
                                        lower_mono.1 _ _ _ _ _ _ heC
                                      obtain ⟨hmnb, hmsb, hbndb, hnodlb⟩ :=
                                        lowerStmtsCFG_loopBody_inv budget _ _ _ _ _ _ _ _ _ _ hb hloop
                                      obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                                        ih _ _ _ _ _ _ _ _ _ hr hrs
                                      refine ⟨by omega, by omega, ?_, ?_⟩
                                      · intro b hb
                                        simp only [List.mem_append, List.mem_singleton] at hb
                                        rcases hb with ((((hb | rfl) | rfl) | rfl) | hb)
                                        · obtain ⟨hlo, hhi⟩ := hbndb b hb
                                          exact ⟨by omega,
                                            Nat.lt_of_lt_of_le hhi (by omega)⟩
                                        · exact ⟨Nat.le_add_right _ _,
                                            Nat.lt_of_lt_of_le
                                              (show nextB + 2 < lb.next from by omega)
                                              hmnr⟩
                                        · exact ⟨Nat.le_refl _,
                                            Nat.lt_of_lt_of_le
                                              (show nextB < lb.next from by omega)
                                              hmnr⟩
                                        · exact ⟨Nat.le_succ _,
                                            Nat.lt_of_lt_of_le
                                              (show nextB + 1 < lb.next from by omega)
                                              hmnr⟩
                                        · obtain ⟨hlo, hhi⟩ := hbndr b hb
                                          exact ⟨by omega,
                                            Nat.lt_of_lt_of_le hhi (by omega)⟩
                                      · exact while_assembly_nodup hmnb hmnr hbndb hbndr
                                          rfl rfl rfl hnodlb hnodr
      | returnStmt e _ hstr _ =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp at h
              subst h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              exact ⟨Nat.le_refl _, hs1, fun b hb => by simp at hb,
                List.nodup_nil⟩


/-! ## The boundary is real

The four facts below are the ones an auditor would ask for: `if` is in, nesting
is in, a loop body is in (nesting is not), and a binding arm is out (until C2c). -/

/-- A two-arm `return` program is in the fragment. -/
example :
    BranchStmts 256
      [.ifStmt (.lit (.bool true)) [.returnStmt (.lit (.int 1))]
        [.returnStmt (.lit (.int 2))]] :=
  .cons (.ifStmt (.lit (.bool true)) _ _
    (.lit _) (by simp [SLWeight])
    (.returnStmt _ _ (.lit _) (by simp [SLWeight]))
    (.returnStmt _ _ (.lit _) (by simp [SLWeight]))) .nil

/-- Nested `if`s: the arms are fragments in their own right. -/
example :
    BranchStmts 256
      [.ifStmt (.lit (.bool true))
        [.ifStmt (.lit (.bool false)) [.nop] []]
        []] :=
  .cons (.ifStmt (.lit (.bool true)) _ _
    (.lit _) (by simp [SLWeight])
    (.ifStmt (.lit (.bool false)) _ _ _
      (.lit _) (by simp [SLWeight]) (.nop [] .nil) .nil .nil)
    .nil) .nil

/-- A loop with an empty body is in the fragment (C7): the header carries
nothing and the body is one empty block. -/
example : BranchStmts 256 [.whileLoop (.lit (.bool true)) []] :=
  .cons (.whileStmt _ _ (.lit _) (by simp [SLWeight]) .nil) .nil

/-- Nesting is outside the fragment: `LoopStmts` has no `while` arm, so the
inner loop cannot unify with any body constructor. -/
example : ¬ BranchStmts 256
    [.whileLoop (.lit (.bool true)) [.whileLoop (.lit (.bool false)) []]] := by
  intro h
  cases h with
  | cons hs _ =>
      cases hs with
      | whileStmt _ _ _ _ hloop => cases hloop

/-- A binding `if` arm is outside the fragment: `ArmStmts` has no `varDecl`. -/
example : ¬ ArmStmts 256 [.varDecl ⟨0, "x"⟩ Typ.intType (.lit (.int 1))] := by
  intro h
  cases h

/-! ## C3 worker helpers: inversions, one-block steps, phi pairs

Loop 175. The worker induction (next) mirrors `lowerStmts_total`: list
induction for the body, predicate induction for the arms, expression steps
via `lower_total.1`, environment preservation via `RelEnv_exec`. What is new
is block dispatch, so these helpers isolate it: projection-style inversions
(the `StraightStmts_*` idiom — `cases` on the predicate never touches the
locals the worker still needs), one-block unfold equations for each
terminator, the join's phi pair firing on the taken edge, and the bridge
from edge-aware execution back to `execInstrsFull` for phi-free expression
code. -/

theorem BranchStep_exprStmt {budget : Nat} {e : HIR.Expr}
    (h : BranchStep budget (.exprStmt e)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | exprStmt _ hs hb => exact ⟨hs, hb⟩

theorem BranchStep_varDecl {budget : Nat} {id : HIR.Id} {τ : Typ}
    {init : HIR.Expr} (h : BranchStep budget (.varDecl id τ init)) :
    IsStraight init ∧ SLWeight init < budget := by
  cases h with
  | varDecl _ _ _ hs hb => exact ⟨hs, hb⟩

theorem BranchStep_assign {budget : Nat} {id : HIR.Id} {e : HIR.Expr}
    (h : BranchStep budget (.assign id e)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | assign _ _ hs hb => exact ⟨hs, hb⟩

theorem BranchStep_if {budget : Nat} {c : HIR.Expr} {th el : List HIR.Stmt}
    (h : BranchStep budget (.ifStmt c th el)) :
    IsStraight c ∧ SLWeight c < budget ∧
      ArmStmts budget th ∧ ArmStmts budget el := by
  cases h with
  | ifStmt _ _ _ hs hb ht he => exact ⟨hs, hb, ht, he⟩

theorem BranchStmts_exprStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : BranchStmts budget (.exprStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget ∧ BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      obtain ⟨hstr, hb⟩ := BranchStep_exprStmt hs
      exact ⟨hstr, hb, hrs⟩

theorem BranchStmts_varDecl {budget : Nat} {id : HIR.Id} {τ : Typ}
    {init : HIR.Expr} {rest : List HIR.Stmt}
    (h : BranchStmts budget (.varDecl id τ init :: rest)) :
    IsStraight init ∧ SLWeight init < budget ∧ BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      obtain ⟨hstr, hb⟩ := BranchStep_varDecl hs
      exact ⟨hstr, hb, hrs⟩

theorem BranchStmts_assign {budget : Nat} {id : HIR.Id} {e : HIR.Expr}
    {rest : List HIR.Stmt} (h : BranchStmts budget (.assign id e :: rest)) :
    IsStraight e ∧ SLWeight e < budget ∧ BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      obtain ⟨hstr, hb⟩ := BranchStep_assign hs
      exact ⟨hstr, hb, hrs⟩

theorem BranchStmts_nop {budget : Nat} {rest : List HIR.Stmt}
    (h : BranchStmts budget (.nop :: rest)) : BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      cases hs with
      | nop => exact hrs

theorem BranchStmts_returnStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : BranchStmts budget (.returnStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | cons hs _ => cases hs
  | returnStmt _ _ hs hb => exact ⟨hs, hb⟩

theorem BranchStmts_if {budget : Nat} {c : HIR.Expr} {th el rest : List HIR.Stmt}
    (h : BranchStmts budget (.ifStmt c th el :: rest)) :
    IsStraight c ∧ SLWeight c < budget ∧
      ArmStmts budget th ∧ ArmStmts budget el ∧ BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      obtain ⟨hstr, hb, ht, he⟩ := BranchStep_if hs
      exact ⟨hstr, hb, ht, he, hrs⟩

theorem ArmStmts_exprStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : ArmStmts budget (.exprStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget ∧ ArmStmts budget rest := by
  cases h with
  | exprStmt _ _ hs hb hr => exact ⟨hs, hb, hr⟩

theorem ArmStmts_nop {budget : Nat} {rest : List HIR.Stmt}
    (h : ArmStmts budget (.nop :: rest)) : ArmStmts budget rest := by
  cases h with
  | nop _ hr => exact hr

theorem ArmStmts_if {budget : Nat} {c : HIR.Expr} {th el rest : List HIR.Stmt}
    (h : ArmStmts budget (.ifStmt c th el :: rest)) :
    IsStraight c ∧ SLWeight c < budget ∧
      ArmStmts budget th ∧ ArmStmts budget el ∧ ArmStmts budget rest := by
  cases h with
  | ifStmt _ _ _ _ hs hb ht he hr => exact ⟨hs, hb, ht, he, hr⟩

theorem ArmStmts_returnStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : ArmStmts budget (.returnStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | returnStmt _ _ hs hb => exact ⟨hs, hb⟩

/-- One block, `return` terminator: run the instructions, read the register. -/
theorem execBlockFromIn_return (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId) (is : List Instr) (v : ValId)
    (fenv fenv' : FullEnv)
    (hexec : execInstrsFullFromIn prog prev fenv is = some fenv') :
    execBlockFromIn prog (F + 1) f prev ⟨id, is, .return_ v⟩ fenv =
      fenv'.env v := by
  have hstep : execBlockFromIn prog (F + 1) f prev ⟨id, is, .return_ v⟩ fenv =
      (match execInstrsFullFromIn prog prev fenv is with
       | none => none
       | some fenv' => fenv'.env v) := rfl
  rw [hstep, hexec]

/-- One block, `goto` terminator: run the instructions, continue at the target
with the block as the predecessor edge. -/
theorem execBlockFromIn_goto (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId) (is : List Instr)
    (t : MIR.BlockId) (fenv fenv' : FullEnv) (b' : Block)
    (hexec : execInstrsFullFromIn prog prev fenv is = some fenv')
    (hfind : findBlock f t = some b') :
    execBlockFromIn prog (F + 1) f prev ⟨id, is, .goto t⟩ fenv =
      execBlockFromIn prog F f (some id) b' fenv' := by
  have hstep : execBlockFromIn prog (F + 1) f prev ⟨id, is, .goto t⟩ fenv =
      (match execInstrsFullFromIn prog prev fenv is with
       | none => none
       | some fenv' =>
           match findBlock f t with
           | some b' => execBlockFromIn prog F f (some id) b' fenv'
           | none => none) := rfl
  rw [hstep, hexec, hfind]

/-- Replacing an entry block's instruction prefix with its result: when the
prefix runs to `fenv1`, the block runs the same as the suffix block from
`fenv1`. The worker uses it to peel expression code (`ie`) off the front of
an entry block, leaving the rest segment's entry for the induction
hypothesis. -/
theorem execBlockFromIn_instrs_prefix (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId)
    (pre suf : List Instr) (t : Terminator) (fenv fenv1 : FullEnv)
    (happ : execInstrsFullFromIn prog prev fenv (pre ++ suf) =
      execInstrsFullFromIn prog prev fenv1 suf) :
    execBlockFromIn prog (F + 1) f prev ⟨id, pre ++ suf, t⟩ fenv =
      execBlockFromIn prog (F + 1) f prev ⟨id, suf, t⟩ fenv1 := by
  simp only [execBlockFromIn, happ]

/-- One block, `branch` terminator, condition true: continue at `t`. -/
theorem execBlockFromIn_branch_true (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId) (is : List Instr)
    (c : ValId) (t e : MIR.BlockId) (fenv fenv' : FullEnv) (b' : Block)
    (hexec : execInstrsFullFromIn prog prev fenv is = some fenv')
    (hbool : fenv'.boolOf c = some true)
    (hfind : findBlock f t = some b') :
    execBlockFromIn prog (F + 1) f prev ⟨id, is, .branch c t e⟩ fenv =
      execBlockFromIn prog F f (some id) b' fenv' := by
  have hstep : execBlockFromIn prog (F + 1) f prev ⟨id, is, .branch c t e⟩ fenv =
      (match execInstrsFullFromIn prog prev fenv is with
       | none => none
       | some fenv' =>
           match fenv'.boolOf c with
           | some true =>
               match findBlock f t with
               | some b' => execBlockFromIn prog F f (some id) b' fenv'
               | none => none
           | some false =>
               match findBlock f e with
               | some b' => execBlockFromIn prog F f (some id) b' fenv'
               | none => none
           | none => none) := rfl
  rw [hstep, hexec]
  simp only [hbool, hfind]

/-- One block, `branch` terminator, condition false: continue at `e`. -/
theorem execBlockFromIn_branch_false (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId) (is : List Instr)
    (c : ValId) (t e : MIR.BlockId) (fenv fenv' : FullEnv) (b' : Block)
    (hexec : execInstrsFullFromIn prog prev fenv is = some fenv')
    (hbool : fenv'.boolOf c = some false)
    (hfind : findBlock f e = some b') :
    execBlockFromIn prog (F + 1) f prev ⟨id, is, .branch c t e⟩ fenv =
      execBlockFromIn prog F f (some id) b' fenv' := by
  have hstep : execBlockFromIn prog (F + 1) f prev ⟨id, is, .branch c t e⟩ fenv =
      (match execInstrsFullFromIn prog prev fenv is with
       | none => none
       | some fenv' =>
           match fenv'.boolOf c with
           | some true =>
               match findBlock f t with
               | some b' => execBlockFromIn prog F f (some id) b' fenv'
               | none => none
           | some false =>
               match findBlock f e with
               | some b' => execBlockFromIn prog F f (some id) b' fenv'
               | none => none
           | none => none) := rfl
  rw [hstep, hexec]
  simp only [hbool, hfind]

/-- The join's phi pair on the taken edge: arriving from `p` fires the
`p`-phi, skips the other edge's phi, and runs the rest of the block with the
merged register bound. The miss side needs the edges distinct, which the
worker has from the exit-id ranges. -/
theorem execInstrsFullFromIn_phis_hit (prog : Program) (p : MIR.BlockId)
    (fenv : FullEnv) (vm : ValId) (te ee : MIR.BlockId) (tv ev : ValId)
    (ris : List Instr) (wv : Value)
    (hte : te = p) (hne : ee ≠ p) (hsrc : fenv.env tv = some wv) :
    execInstrsFullFromIn prog (some p) fenv
        ([.phi vm te tv, .phi vm ee ev] ++ ris) =
      execInstrsFullFromIn prog (some p)
        ⟨fenv.env.update vm wv, fenv.store⟩ ris := by
  simp only [List.cons_append, List.nil_append]
  rw [execInstrsFullFromIn_eq, execInstrsFullFromIn_eq,
    execInstrsFullFrom_phi_hit _ _ _ _ _ _ hte, hsrc]
  simp only [execInstrsFullFrom_phi_miss _ _ _ _ _ _ hne]

/-- A pure instruction is never a phi: the worker feeds this to the bridge
below for every expression-emitted instruction. -/
theorem IsPure_not_phi {i : Instr} (h : IsPure i) (dst : ValId)
    (pred : MIR.BlockId) (src : ValId) : i ≠ .phi dst pred src := by
  cases h with
  | const _ _ => simp
  | copy _ _ => simp
  | unop _ _ _ _ => simp
  | binop _ _ _ _ _ => simp

/-- Edge-aware execution agrees with straight-line execution on phi-free
instruction lists: the program parameter is inert (that is
`execInstrsFullFromIn_eq`) and the edge parameter only matters to phis. The
worker uses it to run `lowerExpr` code inside blocks via `lower_total.1`. -/
theorem execInstrsFullFromIn_of_noPhi (prog : Program) (prev : Option MIR.BlockId)
    (fenv : FullEnv) (is : List Instr)
    (h : ∀ dst pred src, .phi dst pred src ∉ is) :
    execInstrsFullFromIn prog prev fenv is = execInstrsFull fenv is := by
  rw [execInstrsFullFromIn_eq]
  induction is generalizing fenv with
  | nil => rfl
  | cons i rest ih =>
      have hhead : ∀ dst pred src, i ≠ .phi dst pred src := by
        intro dst pred src hphi
        exact h dst pred src (hphi ▸ List.mem_cons_self)
      rw [execInstrsFullFrom_nonphi prev fenv hhead]
      cases he : evalInstrFull fenv i with
      | none => simp only [execInstrsFull, he]
      | some fenv' =>
          simp only [execInstrsFull, he]
          exact ih fenv'
            (fun d p s hm => h d p s (List.mem_cons_of_mem _ hm))

/-- A boolean register reads back through `boolOf`. -/
theorem boolOf_of_lit (fenv : FullEnv) (c : ValId) (b : Bool)
    (h : fenv.env c = some (Value.bool b)) : fenv.boolOf c = some b := by
  simp only [FullEnv.boolOf, h]

/-- Edge-aware execution splits over instruction append: run the prefix,
then run the suffix from the resulting environment. The worker uses it to
separate expression code (run env-explicitly via `lower_total.1`) from the
rest of an entry block. -/
theorem execInstrsFullFrom_append (prev : Option MIR.BlockId) (fenv : FullEnv)
    (l₁ l₂ : List Instr) :
    execInstrsFullFrom prev fenv (l₁ ++ l₂) =
      match execInstrsFullFrom prev fenv l₁ with
      | none => none
      | some fenv1 => execInstrsFullFrom prev fenv1 l₂ := by
  induction l₁ generalizing fenv with
  | nil => simp [execInstrsFullFrom]
  | cons i rest ih =>
      by_cases hi : ∃ dst pred src, i = .phi dst pred src
      · obtain ⟨dst, pred, src, rfl⟩ := hi
        cases prev with
        | none =>
            simp only [List.cons_append]
            rw [execInstrsFullFrom_phi_none, execInstrsFullFrom_phi_none, ih]
        | some p =>
            by_cases hp : pred = p
            · cases hsrc : fenv.env src with
              | none =>
                  have h1 : execInstrsFullFrom (some p) fenv
                      (.phi dst pred src :: (rest ++ l₂)) = none := by
                    rw [execInstrsFullFrom_phi_hit _ _ _ _ _ _ hp, hsrc]
                  have h2 : execInstrsFullFrom (some p) fenv
                      (.phi dst pred src :: rest) = none := by
                    rw [execInstrsFullFrom_phi_hit _ _ _ _ _ _ hp, hsrc]
                  simp only [List.cons_append]
                  rw [h1, h2]
              | some v =>
                  have h1 : execInstrsFullFrom (some p) fenv
                      (.phi dst pred src :: (rest ++ l₂)) =
                      execInstrsFullFrom (some p)
                        ⟨fenv.env.update dst v, fenv.store⟩ (rest ++ l₂) := by
                    rw [execInstrsFullFrom_phi_hit _ _ _ _ _ _ hp, hsrc]
                  have h2 : execInstrsFullFrom (some p) fenv
                      (.phi dst pred src :: rest) =
                      execInstrsFullFrom (some p)
                        ⟨fenv.env.update dst v, fenv.store⟩ rest := by
                    rw [execInstrsFullFrom_phi_hit _ _ _ _ _ _ hp, hsrc]
                  simp only [List.cons_append]
                  rw [h1, h2, ih]
            · have h1 : execInstrsFullFrom (some p) fenv
                    (.phi dst pred src :: (rest ++ l₂)) =
                    execInstrsFullFrom (some p) fenv (rest ++ l₂) :=
                execInstrsFullFrom_phi_miss _ _ _ _ _ _ hp
              have h2 : execInstrsFullFrom (some p) fenv
                    (.phi dst pred src :: rest) =
                    execInstrsFullFrom (some p) fenv rest :=
                execInstrsFullFrom_phi_miss _ _ _ _ _ _ hp
              simp only [List.cons_append]
              rw [h1, h2, ih]
      · have hnp : ∀ dst pred src, i ≠ .phi dst pred src :=
          fun d p s h => hi ⟨d, p, s, h⟩
        simp only [List.cons_append]
        rw [execInstrsFullFrom_nonphi prev fenv hnp]
        cases he : evalInstrFull fenv i with
        | none =>
            have h1 : execInstrsFullFrom prev fenv (i :: rest) = none := by
              rw [execInstrsFullFrom_nonphi prev fenv hnp, he]
            rw [h1]
        | some fenv' =>
            have h1 : execInstrsFullFrom prev fenv (i :: rest) =
                execInstrsFullFrom prev fenv' rest := by
              rw [execInstrsFullFrom_nonphi prev fenv hnp, he]
            rw [h1]
            simp only [ih]

/-- Program-aware execution splits too: the program parameter is inert. -/
theorem execInstrsFullFromIn_append (prog : Program)
    (prev : Option MIR.BlockId) (fenv : FullEnv) (l₁ l₂ : List Instr) :
    execInstrsFullFromIn prog prev fenv (l₁ ++ l₂) =
      match execInstrsFullFromIn prog prev fenv l₁ with
      | none => none
      | some fenv1 => execInstrsFullFromIn prog prev fenv1 l₂ := by
  simp only [execInstrsFullFromIn_eq, execInstrsFullFrom_append]

/-- A lowered entry block never starts with a phi: `L.instrs` is expression
code (`lower_isPure`), and phis only appear in join blocks, which live in
`L.blocks`. The worker uses it to run entry instructions edge-blind via
`execInstrsFullFromIn_of_noPhi`. The induction is on the list, not the
fragment predicates: `L.instrs` depends only on the spine (never on arms),
so the `if` case needs no induction hypothesis. -/
theorem lowerStmtsCFG_instrs_pure :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (arm : Bool)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal none ss = some L →
      ∀ i ∈ L.instrs, IsPure i := by
  intro bId cont arm ρ supply nextB lastVal hasVal ss
  induction ss generalizing bId cont arm ρ supply nextB lastVal hasVal with
  | nil =>
      intro L h i hi
      cases arm with
      | true =>
          cases hasVal with
          | false =>
              simp only [lowerStmtsCFG.eq_def] at h
              obtain rfl := Option.some.inj h
              dsimp only at hi
              simp only [List.mem_singleton] at hi
              subst hi
              exact IsPure.const _ _
          | true =>
              simp only [lowerStmtsCFG.eq_def] at h
              obtain rfl := Option.some.inj h
              dsimp only at hi
              simp at hi
      | false =>
          simp only [lowerStmtsCFG.eq_def] at h
          obtain rfl := Option.some.inj h
          dsimp only at hi
          simp at hi
  | cons s rest ih =>
      cases s with
      | exprStmt e =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId cont arm ρ s1 nextB v0 true none rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  simp only [List.mem_append] at hi
                  rcases hi with hi | hi
                  · exact lower_isPure.1 _ _ _ _ _ _ he _ hi
                  · exact ih _ _ _ _ _ _ _ _ _ hr _ hi
      | varDecl id τ init =>
          intro L h i hi
          cases arm with
          | true =>
              -- Phase B: top-level arms (`loop = none` here) may bind; the
              -- emitted code is expression code either way.
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId cont true ((id, vb) :: ρ) s1
                      nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      simp only [List.mem_append] at hi
                      rcases hi with hi | hi
                      · exact lower_isPure.1 _ _ _ _ _ _ he _ hi
                      · exact ih _ _ _ _ _ _ _ _ _ hr _ hi
          | false =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId cont false ((id, vb) :: ρ) s1
                      nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      simp only [List.mem_append] at hi
                      rcases hi with hi | hi
                      · exact lower_isPure.1 _ _ _ _ _ _ he _ hi
                      · exact ih _ _ _ _ _ _ _ _ _ hr _ hi
      | assign id e =>
          intro L h i hi
          cases arm with
          | true =>
              -- Phase B: top-level arms (`loop = none` here) may bind; the
              -- emitted code is expression code either way.
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId cont true (updAssoc ρ id v)
                      s1 nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      simp only [List.mem_append] at hi
                      rcases hi with hi | hi
                      · exact lower_isPure.1 _ _ _ _ _ _ he _ hi
                      · exact ih _ _ _ _ _ _ _ _ _ hr _ hi
          | false =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId cont false (updAssoc ρ id v)
                      s1 nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      simp only [List.mem_append] at hi
                      rcases hi with hi | hi
                      · exact lower_isPure.1 _ _ _ _ _ _ he _ hi
                      · exact ih _ _ _ _ _ _ _ _ _ hr _ hi
      | nop =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases hr : lowerStmtsCFG bId cont arm ρ supply nextB lastVal
              hasVal none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              obtain rfl := Option.some.inj h
              exact ih _ _ _ _ _ _ _ _ _ hr _ hi
      | ifStmt c th el =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                  (nextB + 3) lastVal false none th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                      lt.supply lt.next lastVal false none el with
                  | none => rw [he] at h; simp at h
                  | some le =>
                      rw [he] at h
                      simp only [] at h
                      -- Phase B: list induction covers binding arms too, so
                      -- the merge set may be nonempty. Either way the entry
                      -- block holds only the condition code `ic`.
                      cases hm : mergeIds ρ lt.ρ le.ρ with
                      | nil =>
                          rw [hm] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) cont arm ρ
                              (le.supply + 1) le.next le.supply true none rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              obtain rfl := Option.some.inj h
                              exact lower_isPure.1 _ _ _ _ _ _ heC _ hi
                      | cons hd tl =>
                          rw [hm] at h
                          simp only [] at h
                          cases hmphi : mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                              ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                              ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                              (hd :: tl) with
                          | none => rw [hmphi] at h; simp at h
                          | some q =>
                              obtain ⟨mphis, s2, ρm⟩ := q
                              rw [hmphi] at h
                              simp only [] at h
                              cases hr : lowerStmtsCFG (nextB + 2) cont arm ρm
                                  s2 le.next le.supply true none rest with
                              | none => rw [hr] at h; simp at h
                              | some lr =>
                                  rw [hr] at h
                                  simp only [] at h
                                  obtain rfl := Option.some.inj h
                                  exact lower_isPure.1 _ _ _ _ _ _ heC _ hi
      | returnStmt e =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              exact lower_isPure.1 _ _ _ _ _ _ he _ hi
      | «break» =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          simp at h
      | «continue» =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          simp at h
      | whileLoop c body =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases hm : mkCarried ρ supply
              ((dedupIds (assignedIds body)).filterMap
                (fun id => (rhoLookup ρ id).map (fun _ => id))) with
          | none => rw [hm] at h; simp at h
          | some q =>
              obtain ⟨carried, sA, ρb⟩ := q
              rw [hm] at h
              simp only [] at h
              cases heC : lowerExpr ρb sA c with
              | none => rw [heC] at h; simp at h
              | some p =>
                  obtain ⟨vc, ic, s1⟩ := p
                  rw [heC] at h
                  simp only [] at h
                  cases hb : lowerStmtsCFG (nextB + 2) (some nextB) false ρb
                      (s1 + 1) (nextB + 3) s1 true
                      (loop := some ⟨nextB, nextB + 1, carried⟩) body with
                  | none => rw [hb] at h; simp at h
                  | some lb =>
                      rw [hb] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 1) cont arm ρb
                          (lb.supply + 1) lb.next lb.supply true none rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          cases hp : mkHeaderPhis ρ bId carried
                              ((lb.blocks.getLast?.map fun b => b.id).getD
                                (nextB + 2))
                              lb.ρ
                              (backEdgePreds lb nextB) with
                          | none => rw [hp] at h; simp at h
                          | some _ =>
                              rw [hp] at h
                              simp only [] at h
                              obtain rfl := Option.some.inj h
                              simp at hi
      | matchStmt _ _ =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          simp at h

/-- Merge-phi execution (C2c join core): running the merge phis from the
taken arm's exit block writes each merged id's fresh register with the
value that id holds in the arm-exit env, and leaves every other register
untouched. The caller supplies the arm-exit values (`hvals`: every merged
id's arm-exit register is bound in the arrival env) and arm-register
freshness (`hfreshT`: arm-exit registers sit strictly below the merge
window, so later pairs cannot clobber the sources earlier pairs read).
The taken arm is `predT` here; the symmetric `predE` case is the same
lemma with the arm sides swapped. The future top-level binding-arm join
feeds this `hvals` from the arm-exit `RelEnv` plus a binds-literals fact,
`hfreshT` from arm freshness, and assembles `RelEnv` over `ρm` from the
two conclusions plus `mkMergePhis_lookup_unmerged`/`_mem`. -/
theorem mkMergePhis_exec (prog : Program)
    {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {mids : List HIR.Id}
    {mphis : List Instr} {s2 : Nat} {ρm : List (HIR.Id × ValId)}
    (hmk : mkMergePhis ρ ltρ leρ s predT predE mids = some (mphis, s2, ρm))
    {fenv : FullEnv} {p : MIR.BlockId}
    (hT : predT = p) (hE : predE ≠ p)
    (hvals : ∀ id ∈ mids, ∀ srcT : ValId, rhoLookup ltρ id = some srcT →
      ∃ w, fenv.env srcT = some w)
    (hfreshT : ∀ id srcT, id ∈ mids → rhoLookup ltρ id = some srcT →
      srcT < s) :
    ∃ fenv', execInstrsFullFromIn prog (some p) fenv mphis = some fenv' ∧
      (∀ id r, id ∈ mids → rhoLookup ρm id = some r →
        ∀ srcT w, rhoLookup ltρ id = some srcT → fenv.env srcT = some w →
        fenv'.env r = some w) ∧
      (∀ r', r' < s ∨ s2 ≤ r' → fenv'.env r' = fenv.env r') := by
  revert hmk hvals hfreshT
  induction mids generalizing ρ s fenv mphis s2 ρm with
  | nil =>
      intro hmk _ _
      simp only [mkMergePhis] at hmk
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hmk
      refine ⟨fenv, by simp [execInstrsFullFromIn_eq], ?_, ?_⟩
      · intro id r hmem
        simp at hmem
      · intro r' _
        rfl
  | cons mid mids ih =>
      intro hmk hvals hfreshT
      simp only [mkMergePhis] at hmk
      cases hT0 : rhoLookup ltρ mid with
      | none => rw [hT0] at hmk; simp at hmk
      | some srcT =>
          rw [hT0] at hmk
          cases hE0 : rhoLookup leρ mid with
          | none => rw [hE0] at hmk; simp at hmk
          | some srcE =>
              rw [hE0] at hmk
              cases hrec : mkMergePhis ρ ltρ leρ (s + 1) predT predE mids with
              | none => rw [hrec] at hmk; simp at hmk
              | some q =>
                  obtain ⟨phis', s'', ρ''⟩ := q
                  rw [hrec] at hmk
                  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hmk
                  obtain ⟨w, hw⟩ := hvals mid (List.mem_cons_self ..) srcT hT0
                  have hvals_tail : ∀ id ∈ mids, ∀ srcT' : ValId,
                      rhoLookup ltρ id = some srcT' →
                      ∃ w', (fenv.env.update s w) srcT' = some w' := by
                    intro id hmem srcT' hlook
                    obtain ⟨w', hw'⟩ := hvals id
                      (List.mem_cons_of_mem _ hmem) srcT' hlook
                    have hlt : srcT' < s := hfreshT id srcT'
                      (List.mem_cons_of_mem _ hmem) hlook
                    have hne : srcT' ≠ s := Nat.ne_of_lt hlt
                    exact ⟨w', by simp [Env.update, hne, hw']⟩
                  have hfreshT_tail : ∀ id srcT', id ∈ mids →
                      rhoLookup ltρ id = some srcT' → srcT' < s + 1 := by
                    intro id srcT' hmem hlook
                    have hlt : srcT' < s := hfreshT id srcT'
                      (List.mem_cons_of_mem _ hmem) hlook
                    exact Nat.lt_of_lt_of_le hlt (Nat.le_succ s)
                  obtain ⟨fenv', hexec_tail, hvals_tail, hframe_tail⟩ :=
                    ih (fenv := ⟨fenv.env.update s w, fenv.store⟩) hrec
                      hvals_tail hfreshT_tail
                  have hexec_head : execInstrsFullFromIn prog (some p) fenv
                      ([MIR.Instr.phi s predT srcT,
                        MIR.Instr.phi s predE srcE] ++ phis') =
                      execInstrsFullFromIn prog (some p)
                        ⟨fenv.env.update s w, fenv.store⟩ phis' :=
                    execInstrsFullFromIn_phis_hit prog p fenv s predT predE
                      srcT srcE phis' w hT hE hw
                  refine ⟨fenv', by rw [hexec_head]; exact hexec_tail, ?_, ?_⟩
                  · intro id r hmem hlook srcT' w' hlookT hw'
                    by_cases heq : id = mid
                    · subst heq
                      rw [rhoLookup_cons_head] at hlook
                      obtain rfl := Option.some.inj hlook
                      have hsrc : srcT' = srcT := Option.some.inj
                        (hlookT.symm.trans hT0)
                      rw [hsrc] at hw'
                      have hw'w : w = w' := Option.some.inj
                        (hw.symm.trans hw')
                      rw [← hw'w]
                      have hframe_s : fenv'.env s =
                          (fenv.env.update s w) s :=
                        hframe_tail s (Or.inl (Nat.lt_succ_self s))
                      rw [hframe_s]
                      simp [Env.update]
                    · have hmem_tail : id ∈ mids := by
                        rcases List.mem_cons.mp hmem with h | h
                        · exact absurd h heq
                        · exact h
                      rw [rhoLookup_cons_ne (Ne.symm heq)] at hlook
                      have hw1 : (fenv.env.update s w) srcT' = some w' := by
                        have hlt : srcT' < s := hfreshT id srcT'
                          (List.mem_cons_of_mem _ hmem_tail) hlookT
                        have hne : srcT' ≠ s := Nat.ne_of_lt hlt
                        simp [Env.update, hne, hw']
                      exact hvals_tail id r hmem_tail hlook srcT' w' hlookT hw1
                  · intro r' hr'
                    have h1 : fenv'.env r' = (fenv.env.update s w) r' := by
                      apply hframe_tail
                      rcases hr' with hlt | hge
                      · exact Or.inl (Nat.lt_of_lt_of_le hlt (Nat.le_succ s))
                      · exact Or.inr hge
                    rw [h1]
                    rcases hr' with hlt | hge
                    · have hne : r' ≠ s := Nat.ne_of_lt hlt
                      simp [Env.update, hne]
                    · have hlt2 : s < s2 := by
                        have hle := mkMergePhis_le hrec
                        omega
                      have hne : r' ≠ s := by omega
                      simp [Env.update, hne]

/-- Else-side merge-phis execution (C2c mirror): the same per-pair induction
as `mkMergePhis_exec`, but arriving from `predE` — the head pair misses
then hits (`phi_miss`/`phi_hit` instead of `phis_hit`), and values plus
freshness come from the else arm (`leρ`). The else-side join peel cites
this for the merge tail. -/
theorem mkMergePhis_execE (prog : Program)
    {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {mids : List HIR.Id}
    {mphis : List Instr} {s2 : Nat} {ρm : List (HIR.Id × ValId)}
    (hmk : mkMergePhis ρ ltρ leρ s predT predE mids = some (mphis, s2, ρm))
    {fenv : FullEnv} {p : MIR.BlockId}
    (hT : predT ≠ p) (hE : predE = p)
    (hvals : ∀ id ∈ mids, ∀ srcE : ValId, rhoLookup leρ id = some srcE →
      ∃ w, fenv.env srcE = some w)
    (hfreshE : ∀ id srcE, id ∈ mids → rhoLookup leρ id = some srcE →
      srcE < s) :
    ∃ fenv', execInstrsFullFromIn prog (some p) fenv mphis = some fenv' ∧
      (∀ id r, id ∈ mids → rhoLookup ρm id = some r →
        ∀ srcE w, rhoLookup leρ id = some srcE → fenv.env srcE = some w →
        fenv'.env r = some w) ∧
      (∀ r', r' < s ∨ s2 ≤ r' → fenv'.env r' = fenv.env r') := by
  revert hmk hvals hfreshE
  induction mids generalizing ρ s fenv mphis s2 ρm with
  | nil =>
      intro hmk _ _
      simp only [mkMergePhis] at hmk
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hmk
      refine ⟨fenv, by simp [execInstrsFullFromIn_eq], ?_, ?_⟩
      · intro id r hmem
        simp at hmem
      · intro r' _
        rfl
  | cons mid mids ih =>
      intro hmk hvals hfreshE
      simp only [mkMergePhis] at hmk
      cases hT0 : rhoLookup ltρ mid with
      | none => rw [hT0] at hmk; simp at hmk
      | some srcT =>
          rw [hT0] at hmk
          cases hE0 : rhoLookup leρ mid with
          | none => rw [hE0] at hmk; simp at hmk
          | some srcE =>
              rw [hE0] at hmk
              cases hrec : mkMergePhis ρ ltρ leρ (s + 1) predT predE mids with
              | none => rw [hrec] at hmk; simp at hmk
              | some q =>
                  obtain ⟨phis', s'', ρ''⟩ := q
                  rw [hrec] at hmk
                  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hmk
                  obtain ⟨w, hw⟩ := hvals mid (List.mem_cons_self ..) srcE hE0
                  have hvals_tail : ∀ id ∈ mids, ∀ srcE' : ValId,
                      rhoLookup leρ id = some srcE' →
                      ∃ w', (fenv.env.update s w) srcE' = some w' := by
                    intro id hmem srcE' hlook
                    obtain ⟨w', hw'⟩ := hvals id
                      (List.mem_cons_of_mem _ hmem) srcE' hlook
                    have hlt : srcE' < s := hfreshE id srcE'
                      (List.mem_cons_of_mem _ hmem) hlook
                    have hne : srcE' ≠ s := Nat.ne_of_lt hlt
                    exact ⟨w', by simp [Env.update, hne, hw']⟩
                  have hfreshE_tail : ∀ id srcE', id ∈ mids →
                      rhoLookup leρ id = some srcE' → srcE' < s + 1 := by
                    intro id srcE' hmem hlook
                    have hlt : srcE' < s := hfreshE id srcE'
                      (List.mem_cons_of_mem _ hmem) hlook
                    exact Nat.lt_of_lt_of_le hlt (Nat.le_succ s)
                  obtain ⟨fenv', hexec_tail, hvals_tail, hframe_tail⟩ :=
                    ih (fenv := ⟨fenv.env.update s w, fenv.store⟩) hrec
                      hvals_tail hfreshE_tail
                  have hexec_head : execInstrsFullFromIn prog (some p) fenv
                      ([MIR.Instr.phi s predT srcT,
                        MIR.Instr.phi s predE srcE] ++ phis') =
                      execInstrsFullFromIn prog (some p)
                        ⟨fenv.env.update s w, fenv.store⟩ phis' := by
                    simp only [List.cons_append, List.nil_append]
                    rw [execInstrsFullFromIn_eq, execInstrsFullFromIn_eq,
                      execInstrsFullFrom_phi_miss _ _ _ _ _ _ hT,
                      execInstrsFullFrom_phi_hit _ _ _ _ _ _ hE, hw]
                  refine ⟨fenv', by rw [hexec_head]; exact hexec_tail, ?_, ?_⟩
                  · intro id r hmem hlook srcE' w' hlookE hw'
                    by_cases heq : id = mid
                    · subst heq
                      rw [rhoLookup_cons_head] at hlook
                      obtain rfl := Option.some.inj hlook
                      have hsrc : srcE' = srcE := Option.some.inj
                        (hlookE.symm.trans hE0)
                      rw [hsrc] at hw'
                      have hw'w : w = w' := Option.some.inj
                        (hw.symm.trans hw')
                      rw [← hw'w]
                      have hframe_s : fenv'.env s =
                          (fenv.env.update s w) s :=
                        hframe_tail s (Or.inl (Nat.lt_succ_self s))
                      rw [hframe_s]
                      simp [Env.update]
                    · have hmem_tail : id ∈ mids := by
                        rcases List.mem_cons.mp hmem with h | h
                        · exact absurd h heq
                        · exact h
                      rw [rhoLookup_cons_ne (Ne.symm heq)] at hlook
                      have hw1 : (fenv.env.update s w) srcE' = some w' := by
                        have hlt : srcE' < s := hfreshE id srcE'
                          (List.mem_cons_of_mem _ hmem_tail) hlookE
                        have hne : srcE' ≠ s := Nat.ne_of_lt hlt
                        simp [Env.update, hne, hw']
                      exact hvals_tail id r hmem_tail hlook srcE' w' hlookE hw1
                  · intro r' hr'
                    have h1 : fenv'.env r' = (fenv.env.update s w) r' := by
                      apply hframe_tail
                      rcases hr' with hlt | hge
                      · exact Or.inl (Nat.lt_of_lt_of_le hlt (Nat.le_succ s))
                      · exact Or.inr hge
                    rw [h1]
                    rcases hr' with hlt | hge
                    · have hne : r' ≠ s := Nat.ne_of_lt hlt
                      simp [Env.update, hne]
                    · have hlt2 : s < s2 := by
                        have hle := mkMergePhis_le hrec
                        omega
                      have hne : r' ≠ s := by omega
                      simp [Env.update, hne]

/-- The full join prefix (value-phi pair then merge phis) executes with
per-merged values plus the value register: the value write lands below the
merge window (`hvm`), so it never clobbers an arm register (`hne`), and the
merge-phi frame composes with the value write for every register but `vm`.
The future top-level binding-arm `RelEnv` assembly cites this for the MIR
side; it supplies `hvals` from the arm-exit relation and `hfreshT`/`hne`/
`hvm` from arm freshness plus supply monotonicity. -/
theorem joinPrefix_exec (prog : Program)
    {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {p : MIR.BlockId}
    {vm vT vE : ValId} {wv : Value}
    {mphis : List Instr} {s2 : Nat} {ρm : List (HIR.Id × ValId)}
    (hmk : mkMergePhis ρ ltρ leρ s predT predE (mergeIds ρ ltρ leρ) =
      some (mphis, s2, ρm))
    {fenvT : FullEnv}
    (hT : predT = p) (hE : predE ≠ p)
    (hvalT : fenvT.env vT = some wv)
    (hvals : ∀ id ∈ mergeIds ρ ltρ leρ, ∀ srcT : ValId,
      rhoLookup ltρ id = some srcT → ∃ w, fenvT.env srcT = some w)
    (hfreshT : ∀ id srcT, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup ltρ id = some srcT → srcT < s)
    (hne : ∀ id srcT, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup ltρ id = some srcT → srcT ≠ vm)
    (hvm : vm < s) :
    ∃ fenv' : FullEnv,
      execInstrsFullFromIn prog (some p) fenvT
        ([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis) =
        some fenv' ∧
      fenv'.env vm = some wv ∧
      (∀ id r, id ∈ mergeIds ρ ltρ leρ → rhoLookup ρm id = some r →
        ∀ srcT w, rhoLookup ltρ id = some srcT → fenvT.env srcT = some w →
        fenv'.env r = some w) ∧
      (∀ r', (r' < s ∨ s2 ≤ r') → r' ≠ vm →
        fenv'.env r' = fenvT.env r') := by
  have hexec_head : execInstrsFullFromIn prog (some p) fenvT
      ([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis) =
      execInstrsFullFromIn prog (some p)
        ⟨fenvT.env.update vm wv, fenvT.store⟩ mphis :=
    execInstrsFullFromIn_phis_hit prog p fenvT vm predT predE
      vT vE mphis wv hT hE hvalT
  have hvals1 : ∀ id ∈ mergeIds ρ ltρ leρ, ∀ srcT : ValId,
      rhoLookup ltρ id = some srcT →
      ∃ w, (fenvT.env.update vm wv) srcT = some w := by
    intro id hmem srcT hlook
    obtain ⟨w, hw⟩ := hvals id hmem srcT hlook
    have hne' : srcT ≠ vm := hne id srcT hmem hlook
    exact ⟨w, by simp [Env.update, hne', hw]⟩
  obtain ⟨fenv', hexec_tail, hvals_tail, hframe_tail⟩ :=
    mkMergePhis_exec prog (fenv := ⟨fenvT.env.update vm wv, fenvT.store⟩)
      hmk (p := p) hT hE hvals1 hfreshT
  refine ⟨fenv', by rw [hexec_head]; exact hexec_tail, ?_, ?_, ?_⟩
  · have h1 : fenv'.env vm = (fenvT.env.update vm wv) vm :=
      hframe_tail vm (Or.inl hvm)
    simpa [Env.update] using h1
  · intro id r hmem hlook srcT w hlookT hwT
    have hne' : srcT ≠ vm := hne id srcT hmem hlookT
    have hw1 : (fenvT.env.update vm wv) srcT = some w := by
      simp [Env.update, hne', hwT]
    exact hvals_tail id r hmem hlook srcT w hlookT hw1
  · intro r' hr hne'
    have h1 : fenv'.env r' = (fenvT.env.update vm wv) r' :=
      hframe_tail r' hr
    rw [h1]
    simp [Env.update, hne']

/-- Else-side full join prefix (C2c mirror): the value-phi pair misses then
hits from `predE`, then the merge tail runs via `mkMergePhis_execE`. Same
conclusion shape as `joinPrefix_exec` with else-arm roles. -/
theorem joinPrefix_execE (prog : Program)
    {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {p : MIR.BlockId}
    {vm vT vE : ValId} {wv : Value}
    {mphis : List Instr} {s2 : Nat} {ρm : List (HIR.Id × ValId)}
    (hmk : mkMergePhis ρ ltρ leρ s predT predE (mergeIds ρ ltρ leρ) =
      some (mphis, s2, ρm))
    {fenvT : FullEnv}
    (hT : predT ≠ p) (hE : predE = p)
    (hvalE : fenvT.env vE = some wv)
    (hvals : ∀ id ∈ mergeIds ρ ltρ leρ, ∀ srcE : ValId,
      rhoLookup leρ id = some srcE → ∃ w, fenvT.env srcE = some w)
    (hfreshE : ∀ id srcE, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup leρ id = some srcE → srcE < s)
    (hne : ∀ id srcE, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup leρ id = some srcE → srcE ≠ vm)
    (hvm : vm < s) :
    ∃ fenv', execInstrsFullFromIn prog (some p) fenvT
        ([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis) =
        some fenv' ∧
      fenv'.env vm = some wv ∧
      (∀ id r, id ∈ mergeIds ρ ltρ leρ → rhoLookup ρm id = some r →
        ∀ srcE w, rhoLookup leρ id = some srcE → fenvT.env srcE = some w →
        fenv'.env r = some w) ∧
      (∀ r', (r' < s ∨ s2 ≤ r') → r' ≠ vm →
        fenv'.env r' = fenvT.env r') := by
  have hexec_head : execInstrsFullFromIn prog (some p) fenvT
      ([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis) =
      execInstrsFullFromIn prog (some p)
        ⟨fenvT.env.update vm wv, fenvT.store⟩ mphis := by
    simp only [List.cons_append, List.nil_append]
    rw [execInstrsFullFromIn_eq, execInstrsFullFromIn_eq,
      execInstrsFullFrom_phi_miss _ _ _ _ _ _ hT,
      execInstrsFullFrom_phi_hit _ _ _ _ _ _ hE, hvalE]
  have hvals1 : ∀ id ∈ mergeIds ρ ltρ leρ, ∀ srcE : ValId,
      rhoLookup leρ id = some srcE →
      ∃ w, (fenvT.env.update vm wv) srcE = some w := by
    intro id hmem srcE hlook
    obtain ⟨w, hw⟩ := hvals id hmem srcE hlook
    have hne' : srcE ≠ vm := hne id srcE hmem hlook
    exact ⟨w, by simp [Env.update, hne', hw]⟩
  obtain ⟨fenv', hexec_tail, hvals_tail, hframe_tail⟩ :=
    mkMergePhis_execE prog (fenv := ⟨fenvT.env.update vm wv, fenvT.store⟩)
      hmk (p := p) hT hE hvals1 hfreshE
  refine ⟨fenv', by rw [hexec_head]; exact hexec_tail, ?_, ?_, ?_⟩
  · have h1 : fenv'.env vm = (fenvT.env.update vm wv) vm :=
      hframe_tail vm (Or.inl hvm)
    simpa [Env.update] using h1
  · intro id r hmem hlook srcE w hlookE hwE
    have hne' : srcE ≠ vm := hne id srcE hmem hlookE
    have hw1 : (fenvT.env.update vm wv) srcE = some w := by
      simp [Env.update, hne', hwE]
    exact hvals_tail id r hmem hlook srcE w hlookE hw1
  · intro r' hr hne'
    have h1 : fenv'.env r' = (fenvT.env.update vm wv) r' :=
      hframe_tail r' hr
    rw [h1]
    simp [Env.update, hne']

/- Assembly membership lifts (`if_asm_mem_*`: by-part membership plus the
arrival-label lifts) live in `Morph.Proofs.Branch.Assembly`. Workers feed
them to `hsub`/`findBlock_of_nodup_mem` without re-counting the append
nesting at every call site. -/


/-- Branch-mode lowering over a binding-free list preserves `ρ`: an `if`'s
arms preserve it (`arm_rho`) and the rest stays in the outer env, so with no
`varDecl`/`assign` (impossible for `ArmStmts`) nothing rebinds. The
loop-body worker cites this for an `ifStmtBreak` tail: after an arm `break`
the static exit env is exactly the `if`-point env, matching the HIR env the
`break` stopped in. -/
theorem lowerStmtsCFG_branchArm_rho (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop ss = some L →
      ArmStmts budget ss →
      L.ρ = ρ := by
  intro bId cont ρ supply nextB lastVal hasVal loop ss L h hss
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal loop L with
  | nil =>
      simp only [lowerStmtsCFG.eq_def] at h
      obtain rfl := Option.some.inj h
      rfl
  | exprStmt e rest hstr _ hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont false ρ s1 nextB v0 true loop rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              obtain rfl := Option.some.inj h
              show q.ρ = ρ
              exact ih _ _ _ _ _ _ _ _ _ hr
  | nop rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases hr : lowerStmtsCFG bId cont false ρ supply nextB lastVal
          hasVal loop rest with
      | none => rw [hr] at h; simp at h
      | some q =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          show q.ρ = ρ
          exact ih _ _ _ _ _ _ _ _ _ hr
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      simp only [lowerStmtsCFG] at h
      cases heC : lowerExpr ρ supply c with
      | none => rw [heC] at h; simp at h
      | some p =>
          obtain ⟨vc, ic, s1⟩ := p
          rw [heC] at h
          simp only [] at h
          cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
              (nextB + 3) lastVal false loop th with
          | none => rw [ht] at h; simp at h
          | some lt =>
              rw [ht] at h
              simp only [] at h
              cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                  lt.supply lt.next lastVal false loop el with
              | none => rw [he] at h; simp at h
              | some le =>
                  rw [he] at h
                  simp only [] at h
                  -- Phase B: binding-free arms have an empty merge set.
                  have hltρ : lt.ρ = ρ :=
                    lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                  have hleρ : le.ρ = ρ :=
                    lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                  have hm : mergeIds ρ lt.ρ le.ρ = [] := by
                    rw [hltρ, hleρ]
                    exact mergeIds_self ρ
                  rw [hm] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) cont false ρ
                      (le.supply + 1) le.next le.supply true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      obtain rfl := Option.some.inj h
                      show lr.ρ = ρ
                      exact ihr _ _ _ _ _ _ _ _ _ hr
  | returnStmt e rest hstr _ =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          obtain rfl := Option.some.inj h
          rfl
  | breakStmt rest _ =>
      cases hlo : loop with
      | none => simp [hlo] at h
      | some info =>
          simp only [lowerStmtsCFG, hlo] at h
          cases hc : carryCopies ρ info.carried with
          | none => rw [hc] at h; simp at h
          | some copies =>
              rw [hc] at h
              obtain rfl := Option.some.inj h
              rfl
  | continueStmt rest _ =>
      cases hlo : loop with
      | none => simp [hlo] at h
      | some info =>
          simp only [lowerStmtsCFG, hlo] at h
          cases hc : carryCopies ρ info.carried with
          | none => rw [hc] at h; simp at h
          | some copies =>
              rw [hc] at h
              obtain rfl := Option.some.inj h
              rfl

/-- A block whose instructions are phi-free runs the same from any
predecessor edge: the program parameter is inert on non-phis
(`execInstrsFullFromIn_eq`) and the terminator dispatch never consults the
edge. The worker uses it to align the rest segment's entry (reached from
the arm's exit) with the induction hypothesis (stated from the rest's own
exit). -/
theorem execBlockFromIn_prev_irrelevant_of_noPhi (prog : Program) (F : Nat)
    (f : Func) (prev1 prev2 : Option MIR.BlockId) (b : Block)
    (fenv : FullEnv)
    (h : ∀ dst pred src, .phi dst pred src ∉ b.instrs) :
    execBlockFromIn prog F f prev1 b fenv =
      execBlockFromIn prog F f prev2 b fenv := by
  cases F with
  | zero => rfl
  | succ F' =>
      have h1 : ∀ (p : Option MIR.BlockId),
          execInstrsFullFromIn prog p fenv b.instrs =
            execInstrsFull fenv b.instrs :=
        fun p => execInstrsFullFromIn_of_noPhi prog p fenv b.instrs h
      simp only [execBlockFromIn, h1]

/-- The assembly's exit is the tail's exit: with `[J]` emitted before
`lr.blocks`, `getLast?` finds the tail's last block (or `J` itself when the
tail is block-free, whose id is the join). The worker rewrites its goal
with this to meet the rest segment's induction hypothesis. -/
theorem if_assembly_exit {lt le lr : List Block} {T E J : Block}
    {bId nextJoin : MIR.BlockId}
    (hJ : J.id = nextJoin) :
    (((lt ++ [T] ++ le ++ [E] ++ [J] ++ lr).getLast?.map
      (fun b => b.id)).getD bId) =
    ((lr.getLast?.map (fun b => b.id)).getD nextJoin) := by
  cases hlr : lr with
  | nil =>
      subst hlr
      have hX : (lt ++ [T] ++ le ++ [E] ++ [J]).getLast? = some J :=
        List.getLast?_concat
      rw [List.append_nil, hX]
      show J.id = nextJoin
      exact hJ
  | cons hd tl =>
      have hne : hd :: tl ≠ [] := by simp
      have hsome : (hd :: tl).getLast? = some ((hd :: tl).getLast hne) :=
        (List.getLast?_eq_some_getLast hne).symm
      have h1 : (lt ++ [T] ++ le ++ [E] ++ [J] ++ (hd :: tl)).getLast? =
          (hd :: tl).getLast? := by
        rw [List.getLast?_append, hsome]
        rfl
      rw [h1, hsome]
      simp

/-- `getLast?` only returns members: the worker needs it to place an arm's
exit block inside its id range. -/
theorem getLast?_mem {α : Type} :
    ∀ {l : List α} {a : α}, l.getLast? = some a → a ∈ l
  | [], _ => by
      intro h
      exact absurd h (by simp)
  | hd :: tl, _ => by
      intro h
      have hne : hd :: tl ≠ [] := by simp
      have hg := List.getLast?_eq_some_getLast hne
      rw [hg] at h
      have ha : _ = (hd :: tl).getLast hne := (Option.some.inj h).symm
      rw [ha]
      exact List.getLast_mem hne

/-- An arrival label from an arm entry or arm block can never equal the
rest exit: entries sit strictly below the join id, arm blocks sit below
the rest floor, and the rest exit is the join id or a rest block. Used
to discharge the FALL-gated `RelEnv` implication at arm-abort sites. -/
theorem arrNe_restExit {arr e armLo armHi restLo exitD : Nat}
    {arm lr : List Block} (harr : arr = e ∨ arr ∈ arm.map Block.id)
    (hrange_arm : ∀ b ∈ arm, armLo ≤ b.id ∧ b.id < armHi)
    (hrange_rest : ∀ b ∈ lr, restLo ≤ b.id)
    (hne_entry : e ≠ exitD) (hexit_lt : exitD < armLo)
    (he2 : e + 1 + 1 ≤ restLo) (hchain : armHi ≤ restLo) :
    arr ≠ ((lr.getLast?.map fun b => b.id)).getD exitD := by

  intro hEq
  cases harr with
  | inl heq =>
      subst heq
      cases hlast : lr.getLast? with
      | none =>
          rw [hlast] at hEq
          simp only [Option.map_none, Option.getD_none] at hEq
          exact absurd hEq hne_entry
      | some bb =>
          have hbr := hrange_rest bb (getLast?_mem hlast)
          rw [hlast] at hEq
          simp only [Option.map_some, Option.getD_some] at hEq
          omega
  | inr hmem =>
      obtain ⟨b, hb, hid⟩ := List.mem_map.mp hmem
      have hid' : b.id = arr := hid
      have hbnd := hrange_arm b hb
      cases hlast : lr.getLast? with
      | none =>
          rw [hlast] at hEq
          simp only [Option.map_none, Option.getD_none] at hEq
          omega
      | some bb =>
          have hbr := hrange_rest bb (getLast?_mem hlast)
          rw [hlast] at hEq
          simp only [Option.map_some, Option.getD_some] at hEq
          have hlt : b.id < bb.id :=
            Nat.lt_of_lt_of_le hbnd.2 (Nat.le_trans hchain hbr)
          rw [hid', hEq] at hlt
          exact Nat.lt_irrefl _ hlt

end Morph.HIRToMIRCorrect
