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
import Morph.Proofs.Branch.Oracle

/-!
# Stage C binding arms: `lowerStmtsCFG_bindArm_total` and its groundwork

Seventh proof leaf out of the `HIRToMIRBranch` monolith: the C2c
binding-arm family — `lowerStmtsCFG_bindArm_rho_agree`, `_inv`, `_fresh`,
the `relEnv_bindArm_join` pair, the `bindArm_join_exec` pair,
`lowerStmtsCFG_bindArm_grows`, and `lowerStmtsCFG_bindArm_total`
(moved verbatim, ~4k lines). It cites the Arm leaves and the Oracle
leaf; the loop-lookup section and everything downstream cite this leaf.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- C2c lowering over binding arms only rebinds bound ids: an id outside
`boundIds` looks up identically in the arm-exit env and the entry env.
`varDecl` conses (shadowing needs the `≠`), `assign` goes through
`updAssoc` (`rhoLookup_updAssoc_ne`), binding-free statements thread the
env through, and the `if` case composes the two arm agreements with the
rest agreement — across the merged env via `mergeIds_mem_diff` (both sides
agree at an unbound id, so it is unmerged) plus
`mkMergePhis_lookup_unmerged`. `break`/`continue` refuse under
`loop = none`, making those cases vacuous. The future top-level
binding-arm `RelEnv` assembly cites this to confine the merge set to
arm-bound ids. -/
theorem lowerStmtsCFG_bindArm_rho_agree (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (ss : List HIR.Stmt) (L : Lowered) (j : HIR.Id),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal none ss =
        some L →
      BindArmStmts budget ss →
      j ∉ boundIds ss → rhoLookup L.ρ j = rhoLookup ρ j := by
  intro bId cont ρ supply nextB lastVal hasVal ss L j h hss hj
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal L j with
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
      simp only [boundIds] at hj
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v0 true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              show rhoLookup q.ρ j = rhoLookup ρ j
              exact ih _ _ _ _ _ _ _ _ _ hr hj
  | varDecl id τ init rest hstr _ hrs hfree ih =>
      simp only [boundIds, List.mem_cons, not_or] at hj
      obtain ⟨hne_j, hjr⟩ := hj
      have hne : ¬ id = j := fun he => hne_j he.symm
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply init with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨vb, ib, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ((id, vb) :: ρ) s1 nextB
              lastVal true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              show rhoLookup q.ρ j = rhoLookup ρ j
              have ihj := ih _ _ _ _ _ _ _ _ _ hr hjr
              have hstep : rhoLookup ((id, vb) :: ρ) j = rhoLookup ρ j := by
                simp [rhoLookup, hne]
              rw [ihj]
              exact hstep
  | assign id e rest hstr _ hrs hfree ih =>
      simp only [boundIds, List.mem_cons, not_or] at hj
      obtain ⟨hne_j, hjr⟩ := hj
      have hne : ¬ id = j := Ne.symm hne_j
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true (updAssoc ρ id v) s1 nextB
              lastVal true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              show rhoLookup q.ρ j = rhoLookup ρ j
              have ihj := ih _ _ _ _ _ _ _ _ _ hr hjr
              have hstep : rhoLookup (updAssoc ρ id v) j = rhoLookup ρ j :=
                rhoLookup_updAssoc_ne hne ρ
              rw [ihj]
              exact hstep
  | nop rest hrs ih =>
      simp only [boundIds] at hj
      simp only [lowerStmtsCFG] at h
      cases hr : lowerStmtsCFG bId cont true ρ supply nextB lastVal
          hasVal none rest with
      | none => rw [hr] at h; simp at h
      | some q =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          show rhoLookup q.ρ j = rhoLookup ρ j
          exact ih _ _ _ _ _ _ _ _ _ hr hj
  | ifStmt c th el rest hstr _ hath hael hrs ihr =>
      simp only [boundIds] at hj
      have hjt : j ∉ boundIds th := by
        intro hm
        apply hj
        simp [hm]
      have hje : j ∉ boundIds el := by
        intro hm
        apply hj
        simp [hm]
      have hjr : j ∉ boundIds rest := by
        intro hm
        apply hj
        simp [hm]
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
                  have hltEq : lt.ρ = ρ :=
                    lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                  have hlt : rhoLookup lt.ρ j = rhoLookup ρ j := by rw [hltEq]
                  have hleEq : le.ρ = ρ :=
                    lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                  have hle : rhoLookup le.ρ j = rhoLookup ρ j := by rw [hleEq]
                  cases hm : mergeIds ρ lt.ρ le.ρ with
                  | nil =>
                      rw [hm] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                          (le.supply + 1) le.next le.supply true none rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          show rhoLookup lr.ρ j = rhoLookup ρ j
                          exact ihr _ _ _ _ _ _ _ _ _ hr hjr
                  | cons hd tl =>
                      rw [hm] at h
                      simp only [] at h
                      cases hmk : mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                          ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                          ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                          (hd :: tl) with
                      | none => rw [hmk] at h; simp at h
                      | some q =>
                          obtain ⟨mphis, s2, ρm⟩ := q
                          rw [hmk] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) cont true ρm
                              s2 le.next le.supply true none rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              obtain rfl := Option.some.inj h
                              show rhoLookup lr.ρ j = rhoLookup ρ j
                              have hrj := ihr _ _ _ _ _ _ _ _ _ hr hjr
                              have hnm : j ∉ hd :: tl := by
                                rw [← hm]
                                intro hmem
                                rcases mergeIds_mem_diff hmem with hdif | hdif
                                · exact hdif hlt
                                · exact hdif hle
                              have hmg := mkMergePhis_lookup_unmerged hmk hnm
                              rw [hrj]
                              exact hmg
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
  | breakStmt rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      simp at h
  | continueStmt rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      simp at h

/-- Static invariant for binding arms (C2c arm-exit infrastructure): the
`arm_inv` conclusion under a `BindArmStmts` hypothesis at top level
(`arm = true`, `loop = none`). The `if` case splits on the merge decision:
the empty-merge path mirrors `arm_inv` (tail under the pre-branch env);
the merge path threads the supply through `mkMergePhis` (`mkMergePhis_le`)
and lowers the tail under the merged env. Block ids are unaffected by the
extra merge phis, so the bounds/nodup assembly is identical on both paths.
The future top-level binding-arm C3 case cites this for the block bounds
and the supply chains its freshness and frame facts need. -/
theorem lowerStmtsCFG_bindArm_inv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal none ss =
        some L →
      BindArmStmts budget ss →
      nextB ≤ L.next ∧ supply ≤ L.supply ∧
        (∀ b ∈ L.blocks, nextB ≤ b.id ∧ b.id < L.next) ∧
        (L.blocks.map Block.id).Nodup := by
  intro bId cont ρ supply nextB lastVal hasVal ss L h hss
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal L with
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
          exact ⟨Nat.le_refl _, Nat.le_succ _, fun b hb => by simp at hb,
            List.nodup_nil⟩
  | exprStmt e rest hstr _ hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v0 true none
              rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              show nextB ≤ q.next ∧ supply ≤ q.supply ∧
                (∀ b ∈ q.blocks, nextB ≤ b.id ∧ b.id < q.next) ∧
                (q.blocks.map Block.id).Nodup
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr
              exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
  | varDecl id τ init rest hstr _ hrs hfree ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply init with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨vb, ib, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ((id, vb) :: ρ) s1 nextB
              lastVal true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              show nextB ≤ q.next ∧ supply ≤ q.supply ∧
                (∀ b ∈ q.blocks, nextB ≤ b.id ∧ b.id < q.next) ∧
                (q.blocks.map Block.id).Nodup
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr
              exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
  | assign id e rest hstr _ hrs hfree ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true (updAssoc ρ id v) s1 nextB
              lastVal true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              show nextB ≤ q.next ∧ supply ≤ q.supply ∧
                (∀ b ∈ q.blocks, nextB ≤ b.id ∧ b.id < q.next) ∧
                (q.blocks.map Block.id).Nodup
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr
              exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
  | nop rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases hr : lowerStmtsCFG bId cont true ρ supply nextB lastVal
          hasVal none rest with
      | none => rw [hr] at h; simp at h
      | some q =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          exact ih _ _ _ _ _ _ _ _ hr
  | ifStmt c th el rest hstr _ hath hael hrs ihr =>
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
                  cases hm : mergeIds ρ lt.ρ le.ρ with
                  | nil =>
                      rw [hm] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                          (le.supply + 1) le.next le.supply true none rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          dsimp only at ⊢
                          have hs1 : supply ≤ s1 :=
                            lower_mono.1 _ _ _ _ _ _ heC
                          obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath
                          obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he hael
                          obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                            ihr _ _ _ _ _ _ _ _ hr
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
                  | cons hd tl =>
                      rw [hm] at h
                      simp only [] at h
                      cases hmk : mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                          ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                          ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                          (hd :: tl) with
                      | none => rw [hmk] at h; simp at h
                      | some q =>
                          obtain ⟨mphis, s2, ρm⟩ := q
                          rw [hmk] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) cont true ρm
                              s2 le.next le.supply true none rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              obtain rfl := Option.some.inj h
                              dsimp only at ⊢
                              have hs1 : supply ≤ s1 :=
                                lower_mono.1 _ _ _ _ _ _ heC
                              have hle2 : le.supply + 1 ≤ s2 :=
                                mkMergePhis_le hmk
                              obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath
                              obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he hael
                              obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                                ihr _ _ _ _ _ _ _ _ hr
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
                                      mphis ++ lr.instrs,
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
      simp only [lowerStmtsCFG] at h
      simp at h
  | continueStmt rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      simp at h

/-- Freshness for binding arms (C2c arm-exit infrastructure): the
`arm_fresh` conclusion under a `BindArmStmts` hypothesis at top level
(`arm = true`, `loop = none`). `varDecl` conses the fresh head register,
`assign` threads freshness through `updAssoc` (`updAssoc_mem`), and the
`if` case crosses the merge via `mkMergePhis_growth_fresh` (supply and
freshness through the allocation, then the tail induction). The future
top-level binding-arm C3 case feeds `hfreshT`/`hne`/`hvm` to the join
assembly from this plus supply monotonicity. -/
theorem lowerStmtsCFG_bindArm_fresh (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal none ss =
        some L →
      BindArmStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      FreshAbove L.ρ L.supply := by
  intro bId cont ρ supply nextB lastVal hasVal ss L h hss hfresh hlast
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal L with
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
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v true none
              rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              have hv : v < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
              have hq := ih _ _ _ _ _ _ _ _ hr
                (FreshAbove.mono ρ supply s1 hs1 hfresh) hv
              obtain rfl := Option.some.inj h
              exact hq
  | varDecl id τ init rest hstr _ hrs hfree ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply init with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨vb, ib, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ((id, vb) :: ρ) s1 nextB
              lastVal true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              have hv : vb < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
              have hfr : FreshAbove ((id, vb) :: ρ) s1 := by
                intro j v hmem
                rcases List.mem_cons.mp hmem with h | h
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                  exact hv
                · exact Nat.lt_of_lt_of_le (hfresh j v h) hs1
              have hlast' : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
              have hq := ih _ _ _ _ _ _ _ _ hr hfr hlast'
              obtain rfl := Option.some.inj h
              exact hq
  | assign id e rest hstr _ hrs hfree ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true (updAssoc ρ id v) s1 nextB
              lastVal true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              have hv : v < s1 := lower_result_lt.1 _ _ _ _ _ _ he hfresh
              have hfr : FreshAbove (updAssoc ρ id v) s1 := by
                intro j w hmem
                rcases updAssoc_mem ρ id v j w hmem with ⟨rfl, hwu⟩ | h
                · rw [hwu]
                  exact hv
                · exact Nat.lt_of_lt_of_le (hfresh j w h) hs1
              have hlast' : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
              have hq := ih _ _ _ _ _ _ _ _ hr hfr hlast'
              obtain rfl := Option.some.inj h
              exact hq
  | nop rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      exact ih _ _ _ _ _ _ _ _ h hfresh hlast
  | ifStmt c th el rest hstr _ hath hael hrs ihr =>
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
                  cases hm : mergeIds ρ lt.ρ le.ρ with
                  | nil =>
                      rw [hm] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                          (le.supply + 1) le.next le.supply true none rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          have hs1 : supply ≤ s1 :=
                            lower_mono.1 _ _ _ _ _ _ heC
                          have hst : s1 ≤ lt.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              ht hath).2.1
                          have hse : lt.supply ≤ le.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              he hael).2.1
                          have hq := ihr _ _ _ _ _ _ _ _ hr
                            (FreshAbove.mono ρ supply (le.supply + 1)
                              (by omega) hfresh)
                            (Nat.lt_succ_self _)
                          obtain rfl := Option.some.inj h
                          dsimp only at ⊢
                          exact hq
                  | cons hd tl =>
                      rw [hm] at h
                      simp only [] at h
                      cases hmk : mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                          ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                          ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                          (hd :: tl) with
                      | none => rw [hmk] at h; simp at h
                      | some q =>
                          obtain ⟨mphis, s2, ρm⟩ := q
                          rw [hmk] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) cont true ρm
                              s2 le.next le.supply true none rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              have hs1 : supply ≤ s1 :=
                                lower_mono.1 _ _ _ _ _ _ heC
                              have hst : s1 ≤ lt.supply :=
                                (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                                  ht hath).2.1
                              have hse : lt.supply ≤ le.supply :=
                                (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                                  he hael).2.1
                              have hle2 : le.supply + 1 ≤ s2 :=
                                mkMergePhis_le hmk
                              have hfrρ : FreshAbove ρ (le.supply + 1) :=
                                FreshAbove.mono ρ supply (le.supply + 1)
                                  (by omega) hfresh
                              obtain ⟨-, hfrm⟩ :=
                                mkMergePhis_growth_fresh hfrρ hmk
                              have hlast2 : le.supply < s2 :=
                                Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle2
                              have hq := ihr _ _ _ _ _ _ _ _ hr hfrm hlast2
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
      simp only [lowerStmtsCFG] at h
      simp at h
  | continueStmt rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      simp at h

/-- Merge-join `RelEnv` assembly (C2c join core, taken-arm side): running the
join prefix (value-phi pair plus merge phis) from the taken arm's exit env
yields an env related over the merged env `ρm` to the taken arm's HIR exit
env. Merged ids read the taken side's value through the phi conclusion
(`hvals` comes from the arm-exit `RelEnv` plus `mkMergePhis_mem_lookup`);
unmerged ids transport across `mkMergePhis_lookup_unmerged` — both arm
exits agree with pre-branch there (`mergeIds_agree`), so the taken arm's
exit `RelEnv` gives the literal and the value, and the join frame (plus
pre-branch freshness below the value register) carries the register over.
Besides the relation it returns the value-register fact, the merged-value
transport, and the frame, so the tail worker gets everything
`joinPrefix_exec` provides without re-running the prefix. The future
top-level binding-arm C3 case feeds `hrelT` from its arm worker and
`hfreshT`/`hne`/`hvm`/`hfrρ` from binding-arm freshness plus supply
monotonicity; the symmetric else-side case swaps the arm roles. -/
theorem relEnv_bindArm_join (prog : Program)
    {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {p : MIR.BlockId}
    {vm vT vE : ValId} {wv : Value}
    {mphis : List Instr} {s2 : Nat} {ρm : List (HIR.Id × ValId)}
    (hmk : mkMergePhis ρ ltρ leρ s predT predE (mergeIds ρ ltρ leρ) =
      some (mphis, s2, ρm))
    {henvT : HEnv} {fenvT : FullEnv}
    (hT : predT = p) (hE : predE ≠ p)
    (hrelT : RelEnv henvT ltρ fenvT.env)
    (hvalT : fenvT.env vT = some wv)
    (hfreshT : ∀ id srcT, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup ltρ id = some srcT → srcT < s)
    (hne : ∀ id srcT, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup ltρ id = some srcT → srcT ≠ vm)
    (hvm : vm < s)
    (hfrρ : FreshAbove ρ vm) :
    ∃ fenv' : FullEnv,
      execInstrsFullFromIn prog (some p) fenvT
        ([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis) =
        some fenv' ∧
      fenv'.env vm = some wv ∧
      (∀ id r, id ∈ mergeIds ρ ltρ leρ → rhoLookup ρm id = some r →
        ∀ srcT w, rhoLookup ltρ id = some srcT → fenvT.env srcT = some w →
        fenv'.env r = some w) ∧
      (∀ r', (r' < s ∨ s2 ≤ r') → r' ≠ vm → fenv'.env r' = fenvT.env r') ∧
      RelEnv henvT ρm fenv'.env := by
  have hvals : ∀ id ∈ mergeIds ρ ltρ leρ, ∀ srcT : ValId,
      rhoLookup ltρ id = some srcT → ∃ w, fenvT.env srcT = some w := by
    intro id hmem srcT hlook
    obtain ⟨w, _, hw⟩ := hrelT id srcT hlook
    exact ⟨w, hw⟩
  obtain ⟨fenv', hexec, hvm', hmerged, hframe⟩ :=
    joinPrefix_exec prog hmk hT hE hvalT hvals hfreshT hne hvm
  refine ⟨fenv', hexec, hvm', hmerged, hframe, ?_⟩
  intro id r hr
  by_cases hmem : id ∈ mergeIds ρ ltρ leρ
  · obtain ⟨r', hrr', _, _⟩ := mkMergePhis_lookup_mem hmk hmem
    have hreq : r' = r := Option.some.inj (hrr'.symm.trans hr)
    obtain ⟨srcT, hlookT⟩ := (mkMergePhis_mem_lookup hmk hmem).1
    obtain ⟨w, hlit, hwT⟩ := hrelT id srcT hlookT
    have hv : fenv'.env r = some w := by
      have h2 := hmerged id r' hmem hrr' srcT w hlookT hwT
      rwa [hreq] at h2
    exact ⟨w, hlit, hv⟩
  · have hρ : rhoLookup ρ id = some r := by
      have hun := mkMergePhis_lookup_unmerged hmk hmem
      rw [hr] at hun
      exact hun.symm
    have hmemfst : id ∈ ρ.map Prod.fst := by
      have hpair : (id, r) ∈ ρ := rhoLookup_some_mem ρ id r hρ
      exact List.mem_map.mpr ⟨(id, r), hpair, rfl⟩
    have hag := mergeIds_agree hmemfst hmem
    have hlt : rhoLookup ltρ id = some r := by
      rw [hag.1]
      exact hρ
    obtain ⟨w, hlit, hwT⟩ := hrelT id r hlt
    have hltvm : r < vm := hfrρ id r (rhoLookup_some_mem ρ id r hρ)
    have hrvm : r ≠ vm := Nat.ne_of_lt hltvm
    have hrs : r < s := Nat.lt_of_lt_of_le hltvm (Nat.le_of_lt hvm)
    have hfr : fenv'.env r = fenvT.env r := hframe r (Or.inl hrs) hrvm
    exact ⟨w, hlit, hfr.trans hwT⟩

/-- Else-side `RelEnv` assembly (C2c mirror): the join prefix executes from
the else arm (`joinPrefix_execE`), merged ids read through the merge and
unmerged ids fall back to the pre-branch env — now with else-arm roles. -/
theorem relEnv_bindArm_joinE (prog : Program)
    {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {p : MIR.BlockId}
    {vm vT vE : ValId} {wv : Value}
    {mphis : List Instr} {s2 : Nat} {ρm : List (HIR.Id × ValId)}
    (hmk : mkMergePhis ρ ltρ leρ s predT predE (mergeIds ρ ltρ leρ) =
      some (mphis, s2, ρm))
    {henvT : HEnv} {fenvT : FullEnv}
    (hT : predT ≠ p) (hE : predE = p)
    (hrelE : RelEnv henvT leρ fenvT.env)
    (hvalE : fenvT.env vE = some wv)
    (hfreshE : ∀ id srcE, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup leρ id = some srcE → srcE < s)
    (hne : ∀ id srcE, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup leρ id = some srcE → srcE ≠ vm)
    (hvm : vm < s)
    (hfrρ : FreshAbove ρ vm) :
    ∃ fenv' : FullEnv,
      execInstrsFullFromIn prog (some p) fenvT
        ([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis) =
        some fenv' ∧
      fenv'.env vm = some wv ∧
      (∀ id r, id ∈ mergeIds ρ ltρ leρ → rhoLookup ρm id = some r →
        ∀ srcE w, rhoLookup leρ id = some srcE → fenvT.env srcE = some w →
        fenv'.env r = some w) ∧
      (∀ r', (r' < s ∨ s2 ≤ r') → r' ≠ vm → fenv'.env r' = fenvT.env r') ∧
      RelEnv henvT ρm fenv'.env := by
  have hvals : ∀ id ∈ mergeIds ρ ltρ leρ, ∀ srcE : ValId,
      rhoLookup leρ id = some srcE → ∃ w, fenvT.env srcE = some w := by
    intro id hmem srcE hlook
    obtain ⟨w, _, hw⟩ := hrelE id srcE hlook
    exact ⟨w, hw⟩
  obtain ⟨fenv', hexec, hvm', hmerged, hframe⟩ :=
    joinPrefix_execE prog hmk hT hE hvalE hvals hfreshE hne hvm
  refine ⟨fenv', hexec, hvm', hmerged, hframe, ?_⟩
  intro id r hr
  by_cases hmem : id ∈ mergeIds ρ ltρ leρ
  · obtain ⟨r', hrr', _, _⟩ := mkMergePhis_lookup_mem hmk hmem
    have hreq : r' = r := Option.some.inj (hrr'.symm.trans hr)
    obtain ⟨srcE, hlookE⟩ := (mkMergePhis_mem_lookup hmk hmem).2
    obtain ⟨w, hlit, hwE⟩ := hrelE id srcE hlookE
    have hv : fenv'.env r = some w := by
      have h2 := hmerged id r' hmem hrr' srcE w hlookE hwE
      rwa [hreq] at h2
    exact ⟨w, hlit, hv⟩
  · have hρ : rhoLookup ρ id = some r := by
      have hun := mkMergePhis_lookup_unmerged hmk hmem
      rw [hr] at hun
      exact hun.symm
    have hmemfst : id ∈ ρ.map Prod.fst := by
      have hpair : (id, r) ∈ ρ := rhoLookup_some_mem ρ id r hρ
      exact List.mem_map.mpr ⟨(id, r), hpair, rfl⟩
    have hag := mergeIds_agree hmemfst hmem
    have hle : rhoLookup leρ id = some r := by
      rw [hag.2]
      exact hρ
    obtain ⟨w, hlit, hwE⟩ := hrelE id r hle
    have hltvm : r < vm := hfrρ id r (rhoLookup_some_mem ρ id r hρ)
    have hrvm : r ≠ vm := Nat.ne_of_lt hltvm
    have hrs : r < s := Nat.lt_of_lt_of_le hltvm (Nat.le_of_lt hvm)
    have hfr : fenv'.env r = fenvT.env r := hframe r (Or.inl hrs) hrvm
    exact ⟨w, hlit, hfr.trans hwE⟩

/-- Join execution composition (C2c join core, tail half): the join prefix
followed by the tail `instrs` runs as the tail `instrs` from the post-join
env (`execInstrsFullFromIn_append` plus the prefix execution). The tail
worker feeds this equation to `execBlockFromIn_instrs_prefix`, peeling the
merge phis off the join block and continuing with the tail entry from
`fenv'` — where the relation, value, and frame facts above hold. -/
theorem bindArm_join_exec (prog : Program)
    {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {p : MIR.BlockId}
    {vm vT vE : ValId} {wv : Value}
    {mphis : List Instr} {s2 : Nat} {ρm : List (HIR.Id × ValId)}
    (hmk : mkMergePhis ρ ltρ leρ s predT predE (mergeIds ρ ltρ leρ) =
      some (mphis, s2, ρm))
    {henvT : HEnv} {fenvT : FullEnv}
    (hT : predT = p) (hE : predE ≠ p)
    (hrelT : RelEnv henvT ltρ fenvT.env)
    (hvalT : fenvT.env vT = some wv)
    (hfreshT : ∀ id srcT, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup ltρ id = some srcT → srcT < s)
    (hne : ∀ id srcT, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup ltρ id = some srcT → srcT ≠ vm)
    (hvm : vm < s)
    (hfrρ : FreshAbove ρ vm)
    {lr : Lowered} :
    ∃ fenv' : FullEnv,
      execInstrsFullFromIn prog (some p) fenvT
        (([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis) ++
          lr.instrs) =
        execInstrsFullFromIn prog (some p) fenv' lr.instrs ∧
      RelEnv henvT ρm fenv'.env ∧
      fenv'.env vm = some wv ∧
      (∀ r', (r' < s ∨ s2 ≤ r') → r' ≠ vm → fenv'.env r' = fenvT.env r') := by
  obtain ⟨fenv', hexec, hvm', -, hframe, hrel⟩ :=
    relEnv_bindArm_join prog hmk hT hE hrelT hvalT hfreshT hne hvm hfrρ
  refine ⟨fenv', ?_, hrel, hvm', hframe⟩
  have happ := execInstrsFullFromIn_append prog (some p) fenvT
    ([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis)
    lr.instrs
  rw [hexec] at happ
  simpa only [] using happ

/-- Else-side join execution composition (C2c mirror): same shape as
`bindArm_join_exec` with else-arm roles — the else-side tail worker feeds
this to `execBlockFromIn_instrs_prefix`. -/
theorem bindArm_join_execE (prog : Program)
    {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {p : MIR.BlockId}
    {vm vT vE : ValId} {wv : Value}
    {mphis : List Instr} {s2 : Nat} {ρm : List (HIR.Id × ValId)}
    (hmk : mkMergePhis ρ ltρ leρ s predT predE (mergeIds ρ ltρ leρ) =
      some (mphis, s2, ρm))
    {henvT : HEnv} {fenvT : FullEnv}
    (hT : predT ≠ p) (hE : predE = p)
    (hrelE : RelEnv henvT leρ fenvT.env)
    (hvalE : fenvT.env vE = some wv)
    (hfreshE : ∀ id srcE, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup leρ id = some srcE → srcE < s)
    (hne : ∀ id srcE, id ∈ mergeIds ρ ltρ leρ →
      rhoLookup leρ id = some srcE → srcE ≠ vm)
    (hvm : vm < s)
    (hfrρ : FreshAbove ρ vm)
    {lr : Lowered} :
    ∃ fenv' : FullEnv,
      execInstrsFullFromIn prog (some p) fenvT
        (([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis) ++
          lr.instrs) =
        execInstrsFullFromIn prog (some p) fenv' lr.instrs ∧
      RelEnv henvT ρm fenv'.env ∧
      fenv'.env vm = some wv ∧
      (∀ r', (r' < s ∨ s2 ≤ r') → r' ≠ vm → fenv'.env r' = fenvT.env r') := by
  obtain ⟨fenv', hexec, hvm', -, hframe, hrel⟩ :=
    relEnv_bindArm_joinE prog hmk hT hE hrelE hvalE hfreshE hne hvm hfrρ
  refine ⟨fenv', ?_, hrel, hvm', hframe⟩
  have happ := execInstrsFullFromIn_append prog (some p) fenvT
    ([MIR.Instr.phi vm predT vT, MIR.Instr.phi vm predE vE] ++ mphis)
    lr.instrs
  rw [hexec] at happ
  simpa only [] using happ

/-- Arm lowering only grows the env domain: every pre-branch binding still
resolves (possibly to a newer register) at arm exit. `varDecl` conses,
`assign` repoints via a forward `updAssoc` membership split, and the `if`
case crosses the merge via `mkMergePhis_mem_of_mem` (the merge path) or
identity (the empty path). The top-level binding-arm case feeds this to
`mkMergePhis_of_covers` to discharge the merge decision. -/
theorem lowerStmtsCFG_bindArm_grows (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal none ss =
        some L →
      BindArmStmts budget ss →
      ∀ (j : HIR.Id) (v : ValId), (j, v) ∈ ρ → ∃ v', (j, v') ∈ L.ρ := by
  intro bId cont ρ supply nextB lastVal hasVal ss L h hss
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal L with
  | nil =>
      intro j v hmem
      simp only [lowerStmtsCFG.eq_def] at h
      cases hv : hasVal with
      | true =>
          simp only [hv] at h
          simp at h
          subst h
          exact ⟨v, hmem⟩
      | false =>
          simp only [hv] at h
          simp at h
          subst h
          exact ⟨v, hmem⟩
  | exprStmt e rest hstr _ hrs ih =>
      intro j v hmem
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v0 true none
              rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              exact ih _ _ _ _ _ _ _ _ hr j v hmem
  | varDecl id τ init rest hstr _ hrs hfree ih =>
      intro j v hmem
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply init with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨vb, ib, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ((id, vb) :: ρ) s1 nextB
              lastVal true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              exact ih _ _ _ _ _ _ _ _ hr j v
                (List.mem_cons.mpr (Or.inr hmem))
  | assign id e rest hstr _ hrs hfree ih =>
      intro j v hmem
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨vv, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true (updAssoc ρ id vv) s1
              nextB lastVal true none rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              have hsub : ∀ (σ : List (HIR.Id × ValId)) (a : HIR.Id)
                  (b : ValId), (a, b) ∈ σ →
                  ∃ b', (a, b') ∈ updAssoc σ id vv := by
                intro σ
                induction σ with
                | nil => intro a b hm; simp at hm
                | cons pp rest ihσ =>
                    obtain ⟨k, u⟩ := pp
                    intro a b hm
                    simp only [updAssoc]
                    by_cases heq : k = id
                    · rw [if_pos heq]
                      simp only [List.mem_cons] at hm
                      rcases hm with hm | hm
                      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
                        exact ⟨vv, List.mem_cons.mpr (Or.inl rfl)⟩
                      · exact ⟨b, List.mem_cons.mpr (Or.inr hm)⟩
                    · rw [if_neg heq]
                      simp only [List.mem_cons] at hm
                      rcases hm with hm | hm
                      · obtain ⟨h1, h2⟩ := Prod.mk.inj hm
                        exact ⟨u, List.mem_cons.mpr (Or.inl (by rw [h1]))⟩
                      · obtain ⟨b', hb'⟩ := ihσ a b hm
                        exact ⟨b', List.mem_cons.mpr (Or.inr hb')⟩
              obtain ⟨v', hv'⟩ := hsub ρ j v hmem
              exact ih _ _ _ _ _ _ _ _ hr j v' hv'
  | nop rest hrs ih =>
      intro j v hmem
      simp only [lowerStmtsCFG] at h
      cases hr : lowerStmtsCFG bId cont true ρ supply nextB lastVal
          hasVal none rest with
      | none => rw [hr] at h; simp at h
      | some q =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          exact ih _ _ _ _ _ _ _ _ hr j v hmem
  | ifStmt c th el rest hstr _ hath hael hrs ihr =>
      intro j v hmem
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
                  cases hm : mergeIds ρ lt.ρ le.ρ with
                  | nil =>
                      rw [hm] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                          (le.supply + 1) le.next le.supply true none rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          exact ihr _ _ _ _ _ _ _ _ hr j v hmem
                  | cons hd tl =>
                      have hltEq : lt.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                      have hleEq : le.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                      have hlt : ∀ id ∈ hd :: tl, ∃ w,
                          rhoLookup lt.ρ id = some w := by
                        intro id hmem'
                        have hdom : ∃ w, rhoLookup ρ id = some w := by
                          have hmm : id ∈ mergeIds ρ lt.ρ le.ρ := by
                            rw [hm]; exact hmem'
                          exact mergeIds_mem_lookup hmm
                        obtain ⟨w, hw⟩ := hdom
                        exact ⟨w, by rw [hltEq]; exact hw⟩
                      have hle : ∀ id ∈ hd :: tl, ∃ w,
                          rhoLookup le.ρ id = some w := by
                        intro id hmem'
                        have hdom : ∃ w, rhoLookup ρ id = some w := by
                          have hmm : id ∈ mergeIds ρ lt.ρ le.ρ := by
                            rw [hm]; exact hmem'
                          exact mergeIds_mem_lookup hmm
                        obtain ⟨w, hw⟩ := hdom
                        exact ⟨w, by rw [hleEq]; exact hw⟩
                      rw [hm] at h
                      simp only [] at h
                      obtain ⟨mphis, s2, ρm, hmk⟩ :=
                        mkMergePhis_of_covers hlt hle
                      rw [hmk] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont true ρm
                          s2 le.next le.supply true none rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          exact ihr _ _ _ _ _ _ _ _ hr j v
                            (mkMergePhis_mem_of_mem hmk hmem)
  | returnStmt e rest hstr _ =>
      intro j v hmem
      simp at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨vv, ie, s1⟩ := p
          rw [he] at h
          simp at h
          subst h
          exact ⟨v, hmem⟩
  | breakStmt rest hrs ih =>
      intro j v hmem
      simp only [lowerStmtsCFG] at h
      simp at h
  | continueStmt rest hrs ih =>
      intro j v hmem
      simp only [lowerStmtsCFG] at h
      simp at h

/-- C2c worker (top-level binding arms, `loop = none`): arm-mode execution
correctness under `BindArmStmts`. Same arrival-eq conclusion shape as
`lowerStmtsCFG_arm_total`, minus the register-preservation frame (an arm
`assign` may rewrite a register below `supply`) and with `loop` fixed to
`none` (the lowering refuses bindings under `loop = some _`, so those cases
are vacuous; `break`/`continue` likewise refuse). The top-level binding-arm
C3 case discharges its worker contracts (`harmT`/`harmE`) from this. -/
theorem lowerStmtsCFG_bindArm_total (budget : Nat) :
    ∀ (bId j : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId (some j) true ρ supply nextB lastVal hasVal none ss =
        some L →
      BindArmStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      (hasVal = false → accH = .unit) →
      fenv.env lastVal = some accH →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv ss (.value (.lit accH)) = (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId)
        (jblock : Block) (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      findBlock f j = some jblock →
      ∀ (fuelB C : Nat), F ≥ blockBound fuelB ss + C →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
        ∃ F' fenv_arr, F' ≤ F ∧ F' ≥ C ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv
            = execBlockFromIn prog F' f
                (some ((L.blocks.getLast?.map (fun b => b.id)).getD bId))
                jblock fenv_arr ∧
          RelEnv henv' L.ρ fenv_arr.env ∧ fenv_arr.env L.val = some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
        execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
          some w_e) := by
  intro bId j ρ supply nextB lastVal hasVal ss L h hss hfresh hlast
  induction hss generalizing bId j ρ supply nextB lastVal hasVal L with
  | nil =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG.eq_def] at h
        cases hv : hasVal with
        | false =>
            simp only [hv] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                have h2 : henv = henv' := congrArg Prod.snd hrun
                have hu : u = .lit accH := by
                  rw [← h1] at hout
                  exact (HFlow.value.inj hout).symm
                have hacc : accH = .unit := hval0 hv
                cases F with
                | zero =>
                    have hbb : blockBound fuelB ([] : List HIR.Stmt)
                        = 1 := by simp [blockBound]
                    omega
                | succ F' =>
                    have hnp : ∀ dst pred src,
                        .phi dst pred src ∉ ([.const supply .unit] : List Instr) := by
                      intro d p s hm
                      simp only [List.mem_singleton] at hm
                      exact IsPure_not_phi (IsPure.const _ _)
                        _ _ _ hm.symm
                    have hexec : execInstrsFullFromIn prog prev fenv
                        [.const supply .unit] =
                        some ⟨fenv.env.update supply .unit, fenv.store⟩ := by
                      rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
                      exact execInstrsFull_singleton _ _ _
                        (by simp [evalInstrFull])
                    refine ⟨accH, hu, F',
                      ⟨fenv.env.update supply .unit, fenv.store⟩,
                      Nat.le_succ _, ?_, ?_, ?_, ?_⟩
                    · have hbb : blockBound fuelB ([] : List HIR.Stmt)
                          = 1 := by simp [blockBound]
                      omega
                    · dsimp only
                      exact execBlockFromIn_goto prog F' f prev bId
                        [.const supply .unit] j fenv _ jblock hexec hfind
                    · rw [← h2]
                      intro id u hlook
                      obtain ⟨w, hlookH, hreg0⟩ := hrel id u hlook
                      have hu2 : u < supply :=
                        hfresh id u (rhoLookup_some_mem ρ id u hlook)
                      have hne : u ≠ supply := Nat.ne_of_lt hu2
                      refine ⟨w, hlookH, ?_⟩
                      have hupd : (fenv.env.update supply .unit) u
                          = fenv.env u := by simp [Env.update, hne]
                      show (fenv.env.update supply .unit) u = some w
                      rw [hupd]
                      exact hreg0
                    · simp [Env.update, hacc]
          | true =>
              simp only [hv] at h
              obtain rfl := Option.some.inj h
              cases fuelH with
              | zero =>
                  have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                      (.value (.lit accH)) = (.stuck, henv) := rfl
                  rw [hz] at hrun
                  have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                  rw [hst] at hout
                  exact absurd hout (by simp)
              | succ fh =>
                  have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                      (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                  rw [hstep] at hrun
                  have h1 : (.value (.lit accH)) = out :=
                    congrArg Prod.fst hrun
                  have h2 : henv = henv' := congrArg Prod.snd hrun
                  have hu : u = .lit accH := by
                    rw [← h1] at hout
                    exact (HFlow.value.inj hout).symm
                  cases F with
                  | zero =>
                      have hbb : blockBound fuelB ([] : List HIR.Stmt)
                          = 1 := by simp [blockBound]
                      omega
                  | succ F' =>
                      refine ⟨accH, hu, F', fenv, Nat.le_succ _, ?_, ?_,
                        ?_, ?_⟩
                      · have hbb : blockBound fuelB ([] : List HIR.Stmt)
                            = 1 := by simp [blockBound]
                        omega
                      · dsimp only
                        exact execBlockFromIn_goto prog F' f prev bId [] j
                          fenv fenv jblock rfl hfind
                      · rw [← h2]; exact hrel
                      · exact hreg
      · intro e hout
        simp only [lowerStmtsCFG.eq_def] at h
        cases hv : hasVal with
        | false =>
            simp only [hv] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                rw [← h1] at hout
                exact absurd hout (by simp)
        | true =>
            simp only [hv] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                rw [← h1] at hout
                exact absurd hout (by simp)
  | exprStmt e rest hstr _ hrs ih =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v0, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            cases hr : lowerStmtsCFG bId (some j) true ρ s1 nextB v0 true
                none rest with
            | none => rw [hr] at h; simp at h
            | some Lr =>
                rw [hr] at h
                obtain rfl := Option.some.inj h
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.exprStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv (.exprStmt e :: rest)
                        (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => runHIRStmts fh henv rest (.value v)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                            hregE⟩ :=
                          lower_total.1 ρ supply e v0 ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        rw [hrE] at hrun
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        have hregE' : fenv1.env v0 = some wE := hww ▸ hregE
                        have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                        have hf1 : FreshAbove ρ s1 :=
                          FreshAbove.mono ρ supply s1 hs1 hfresh
                        have hlast1 : v0 < s1 :=
                          lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                        have hrel1 : RelEnv henv ρ fenv1.env :=
                          RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1
                            hrel hfresh hexec1
                        have hnp_ie : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                        have hexec_ie : execInstrsFullFromIn prog prev fenv ie
                            = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp_ie]
                          exact hexec1
                        have happ : execInstrsFullFromIn prog prev fenv
                            (ie ++ Lr.instrs) =
                            execInstrsFullFromIn prog prev fenv1 Lr.instrs := by
                          rw [execInstrsFullFromIn_append, hexec_ie]
                        have hbb : blockBound fuelB (.exprStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        cases F with
                        | zero =>
                            have h1 : blockBound fuelB rest ≥ 1 := by
                              rw [blockBound]; omega
                            omega
                        | succ F'' =>
                            have hLHS : execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, ie ++ Lr.instrs, Lr.term⟩ fenv =
                                execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, Lr.instrs, Lr.term⟩ fenv1 :=
                                execBlockFromIn_instrs_prefix prog F'' f prev bId ie
                                Lr.instrs Lr.term fenv fenv1 happ
                            have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                              rw [← hbb]; exact hg
                            have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                              fun b hb => hsub b hb
                            obtain ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                                hrel_arr, hreg_arr⟩ :=((ih bId j ρ s1 nextB v0 true Lr hr hf1 hlast1 wE henv fenv1 hrel1 (fun hh => absurd hh (by simp)) hregE'
                                fh henv' out hrun prog f prev jblock (F'' + 1)
                                hsub' hnodf hfind fuelB C hg' u).1 hout)
                            exact ⟨w_u, hu, F', fenv_arr, hle, hge,
                              hLHS.trans heq_rest, hrel_arr, hreg_arr⟩
      · intro e_ret hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v0, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            cases hr : lowerStmtsCFG bId (some j) true ρ s1 nextB v0 true
                none rest with
            | none => rw [hr] at h; simp at h
            | some Lr =>
                rw [hr] at h
                obtain rfl := Option.some.inj h
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.exprStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv (.exprStmt e :: rest)
                        (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => runHIRStmts fh henv rest (.value v)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                            hregE⟩ :=
                          lower_total.1 ρ supply e v0 ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        rw [hrE] at hrun
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        have hregE' : fenv1.env v0 = some wE := hww ▸ hregE
                        have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                        have hf1 : FreshAbove ρ s1 :=
                          FreshAbove.mono ρ supply s1 hs1 hfresh
                        have hlast1 : v0 < s1 :=
                          lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                        have hrel1 : RelEnv henv ρ fenv1.env :=
                          RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1
                            hrel hfresh hexec1
                        have hnp_ie : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                        have hexec_ie : execInstrsFullFromIn prog prev fenv ie
                            = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp_ie]
                          exact hexec1
                        have happ : execInstrsFullFromIn prog prev fenv
                            (ie ++ Lr.instrs) =
                            execInstrsFullFromIn prog prev fenv1 Lr.instrs := by
                          rw [execInstrsFullFromIn_append, hexec_ie]
                        have hbb : blockBound fuelB (.exprStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        cases F with
                        | zero =>
                            have h1 : blockBound fuelB rest ≥ 1 := by
                              rw [blockBound]; omega
                            omega
                        | succ F'' =>
                            have hLHS : execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, ie ++ Lr.instrs, Lr.term⟩ fenv =
                                execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, Lr.instrs, Lr.term⟩ fenv1 :=
                                execBlockFromIn_instrs_prefix prog F'' f prev bId ie
                                Lr.instrs Lr.term fenv fenv1 happ
                            have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                              rw [← hbb]; exact hg
                            have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                              fun b hb => hsub b hb
                            obtain ⟨w_e, hu_e, heq_rest⟩ :=((ih bId j ρ s1 nextB v0 true Lr hr hf1 hlast1 wE henv fenv1 hrel1 (fun hh => absurd hh (by simp)) hregE'
                                fh henv' out hrun prog f prev jblock (F'' + 1)
                                hsub' hnodf hfind fuelB C hg' u).2 e_ret hout)
                            exact ⟨w_e, hu_e, hLHS.trans heq_rest⟩
  | varDecl id τ init rest hstr _ hrs hfree ih =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply init with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨vb, ib, s1⟩ := p
            rw [he] at h
            simp only [] at h
            cases hr : lowerStmtsCFG bId (some j) true ((id, vb) :: ρ) s1
                nextB lastVal true none rest with
            | none => rw [hr] at h; simp at h
            | some Lr =>
                rw [hr] at h
                obtain rfl := Option.some.inj h
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.varDecl id τ init :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.varDecl id τ init :: rest) (.value (.lit accH)) =
                        (match evalHIR 256 henv init with
                          | none => (HFlow.stuck, henv)
                          | some v => runHIRStmts fh ((id, v) :: henv) rest
                              (.value (.lit accH))) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv init with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                            hregE⟩ :=
                          lower_total.1 ρ supply init vb ib s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        rw [hrE] at hrun
                        have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                        have hlast1 : lastVal < s1 :=
                          Nat.lt_of_lt_of_le hlast hs1
                        have hva : vb < s1 :=
                          lower_result_lt.1 ρ supply init vb ib s1 he hfresh
                        have hf1 : FreshAbove ((id, vb) :: ρ) s1 := by
                          intro j u hmem
                          rcases List.mem_cons.mp hmem with heq | hmem
                          · cases heq
                            exact hva
                          · exact Nat.lt_of_lt_of_le (hfresh j u hmem) hs1
                        have hrel1 : RelEnv henv ρ fenv1.env :=
                          RelEnv_exec henv ρ supply init vb ib s1 he fenv
                            fenv1 hrel hfresh hexec1
                        have hrel2 : RelEnv ((id, .lit wE) :: henv)
                            ((id, vb) :: ρ) fenv1.env := by
                          intro j u hlook
                          by_cases hid : id = j
                          · subst hid
                            have hu : u = vb := by
                              have hh : rhoLookup ((id, vb) :: ρ) id =
                                  some vb :=
                                rhoLookup_cons_head id vb ρ
                              rw [hh] at hlook
                              exact (Option.some.inj hlook).symm
                            subst hu
                            have hhead : lookupHEnv
                                ((id, .lit wE) :: henv) id =
                                some (.lit wE) := by
                              simp [lookupHEnv]
                            exact ⟨wE, hhead, hww ▸ hregE⟩
                          · have hlook' : rhoLookup ρ j = some u := by
                              rw [rhoLookup_cons_ne hid] at hlook
                              exact hlook
                            obtain ⟨w', hlookH, hregV⟩ :=
                              hrel1 j u hlook'
                            have hlookH' : lookupHEnv
                                ((id, .lit wE) :: henv) j =
                                some (.lit w') := by
                              rw [lookupHEnv_cons_ne hid]
                              exact hlookH
                            exact ⟨w', hlookH', hregV⟩
                        have hacc1 : fenv1.env lastVal = some accH := by
                          rw [lower_preserv_regs ρ supply init vb ib
                            s1 he fenv fenv1 hexec1 lastVal hlast]
                          exact hreg
                        have hnp : ∀ dst pred src,
                            .phi dst pred src ∉ ib := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                            rfl
                        have hexec : execInstrsFullFromIn prog prev
                            fenv ib = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
                          exact hexec1
                        have happ : execInstrsFullFromIn prog prev fenv
                            (ib ++ Lr.instrs) =
                            execInstrsFullFromIn prog prev fenv1 Lr.instrs := by
                          rw [execInstrsFullFromIn_append, hexec]
                        have hbb : blockBound fuelB (.varDecl id τ init :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        cases F with
                        | zero =>
                            have h1 : blockBound fuelB rest ≥ 1 := by
                              rw [blockBound]; omega
                            omega
                        | succ F'' =>
                            have hLHS : execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, ib ++ Lr.instrs, Lr.term⟩ fenv =
                                execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, Lr.instrs, Lr.term⟩ fenv1 :=
                                execBlockFromIn_instrs_prefix prog F'' f prev bId ib
                                Lr.instrs Lr.term fenv fenv1 happ
                            have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                              rw [← hbb]; exact hg
                            have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                              fun b hb => hsub b hb
                            obtain ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                                hrel_arr, hreg_arr⟩ :=
                              ((ih bId j ((id, vb) :: ρ) s1 nextB lastVal true
                                Lr hr hf1 hlast1 accH ((id, .lit wE) :: henv)
                                fenv1 hrel2 (fun hh => absurd hh (by simp))
                                hacc1 fh henv' out hrun prog f prev
                                jblock (F'' + 1) hsub' hnodf hfind fuelB C hg'
                                u).1 hout)
                            exact ⟨w_u, hu, F', fenv_arr, hle, hge,
                              hLHS.trans heq_rest, hrel_arr, hreg_arr⟩
      · intro e_ret hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply init with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨vb, ib, s1⟩ := p
            rw [he] at h
            simp only [] at h
            cases hr : lowerStmtsCFG bId (some j) true ((id, vb) :: ρ) s1
                nextB lastVal true none rest with
            | none => rw [hr] at h; simp at h
            | some Lr =>
                rw [hr] at h
                obtain rfl := Option.some.inj h
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.varDecl id τ init :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.varDecl id τ init :: rest) (.value (.lit accH)) =
                        (match evalHIR 256 henv init with
                          | none => (HFlow.stuck, henv)
                          | some v => runHIRStmts fh ((id, v) :: henv) rest
                              (.value (.lit accH))) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv init with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                            hregE⟩ :=
                          lower_total.1 ρ supply init vb ib s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        rw [hrE] at hrun
                        have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                        have hlast1 : lastVal < s1 :=
                          Nat.lt_of_lt_of_le hlast hs1
                        have hva : vb < s1 :=
                          lower_result_lt.1 ρ supply init vb ib s1 he hfresh
                        have hf1 : FreshAbove ((id, vb) :: ρ) s1 := by
                          intro j u hmem
                          rcases List.mem_cons.mp hmem with heq | hmem
                          · cases heq
                            exact hva
                          · exact Nat.lt_of_lt_of_le (hfresh j u hmem) hs1
                        have hrel1 : RelEnv henv ρ fenv1.env :=
                          RelEnv_exec henv ρ supply init vb ib s1 he fenv
                            fenv1 hrel hfresh hexec1
                        have hrel2 : RelEnv ((id, .lit wE) :: henv)
                            ((id, vb) :: ρ) fenv1.env := by
                          intro j u hlook
                          by_cases hid : id = j
                          · subst hid
                            have hu : u = vb := by
                              have hh : rhoLookup ((id, vb) :: ρ) id =
                                  some vb :=
                                rhoLookup_cons_head id vb ρ
                              rw [hh] at hlook
                              exact (Option.some.inj hlook).symm
                            subst hu
                            have hhead : lookupHEnv
                                ((id, .lit wE) :: henv) id =
                                some (.lit wE) := by
                              simp [lookupHEnv]
                            exact ⟨wE, hhead, hww ▸ hregE⟩
                          · have hlook' : rhoLookup ρ j = some u := by
                              rw [rhoLookup_cons_ne hid] at hlook
                              exact hlook
                            obtain ⟨w', hlookH, hregV⟩ :=
                              hrel1 j u hlook'
                            have hlookH' : lookupHEnv
                                ((id, .lit wE) :: henv) j =
                                some (.lit w') := by
                              rw [lookupHEnv_cons_ne hid]
                              exact hlookH
                            exact ⟨w', hlookH', hregV⟩
                        have hacc1 : fenv1.env lastVal = some accH := by
                          rw [lower_preserv_regs ρ supply init vb ib
                            s1 he fenv fenv1 hexec1 lastVal hlast]
                          exact hreg
                        have hnp : ∀ dst pred src,
                            .phi dst pred src ∉ ib := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                            rfl
                        have hexec : execInstrsFullFromIn prog prev
                            fenv ib = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
                          exact hexec1
                        have happ : execInstrsFullFromIn prog prev fenv
                            (ib ++ Lr.instrs) =
                            execInstrsFullFromIn prog prev fenv1 Lr.instrs := by
                          rw [execInstrsFullFromIn_append, hexec]
                        have hbb : blockBound fuelB (.varDecl id τ init :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        cases F with
                        | zero =>
                            have h1 : blockBound fuelB rest ≥ 1 := by
                              rw [blockBound]; omega
                            omega
                        | succ F'' =>
                            have hLHS : execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, ib ++ Lr.instrs, Lr.term⟩ fenv =
                                execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, Lr.instrs, Lr.term⟩ fenv1 :=
                                execBlockFromIn_instrs_prefix prog F'' f prev bId ib
                                Lr.instrs Lr.term fenv fenv1 happ
                            have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                              rw [← hbb]; exact hg
                            have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                              fun b hb => hsub b hb
                            obtain ⟨w_e, hu_e, heq_rest⟩ :=
                              ((ih bId j ((id, vb) :: ρ) s1 nextB lastVal true
                                Lr hr hf1 hlast1 accH ((id, .lit wE) :: henv)
                                fenv1 hrel2 (fun hh => absurd hh (by simp))
                                hacc1 fh henv' out hrun prog f prev
                                jblock (F'' + 1) hsub' hnodf hfind fuelB C hg'
                                u).2 e_ret hout)
                            exact ⟨w_e, hu_e, hLHS.trans heq_rest⟩
  | assign id e rest hstr _ hrs hfree ih =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v0, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            cases hr : lowerStmtsCFG bId (some j) true (updAssoc ρ id v0)
                s1 nextB lastVal true none rest with
            | none => rw [hr] at h; simp at h
            | some Lr =>
                rw [hr] at h
                obtain rfl := Option.some.inj h
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.assign id e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.assign id e :: rest)
                        (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => runHIRStmts fh
                              (updateHEnv henv id v) rest
                              (.value (.lit accH))) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                            hregE⟩ :=
                          lower_total.1 ρ supply e v0 ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        rw [hrE] at hrun
                        have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                        have hlast1 : lastVal < s1 :=
                          Nat.lt_of_lt_of_le hlast hs1
                        have hva : v0 < s1 :=
                          lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                        have hf1 : FreshAbove (updAssoc ρ id v0) s1 := by
                          intro j u hmem
                          rcases updAssoc_mem ρ id v0 j u hmem with ⟨-, hwu⟩ |
                            hmem
                          · rw [hwu]
                            exact hva
                          · exact Nat.lt_of_lt_of_le (hfresh j u hmem) hs1
                        have hrel1 : RelEnv henv ρ fenv1.env :=
                          RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1
                            hrel hfresh hexec1
                        have hrel2 : RelEnv
                            (updateHEnv henv id (.lit wE))
                            (updAssoc ρ id v0) fenv1.env :=
                          RelEnv_update ρ henv fenv1.env id v0 wE
                            hrel1 (hww ▸ hregE)
                        have hacc1 : fenv1.env lastVal = some accH := by
                          rw [lower_preserv_regs ρ supply e v0 ie s1
                            he fenv fenv1 hexec1 lastVal hlast]
                          exact hreg
                        have hnp : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                            rfl
                        have hexec : execInstrsFullFromIn prog prev
                            fenv ie = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
                          exact hexec1
                        have happ : execInstrsFullFromIn prog prev fenv
                            (ie ++ Lr.instrs) =
                            execInstrsFullFromIn prog prev fenv1 Lr.instrs := by
                          rw [execInstrsFullFromIn_append, hexec]
                        have hbb : blockBound fuelB (.assign id e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        cases F with
                        | zero =>
                            have h1 : blockBound fuelB rest ≥ 1 := by
                              rw [blockBound]; omega
                            omega
                        | succ F'' =>
                            have hLHS : execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, ie ++ Lr.instrs, Lr.term⟩ fenv =
                                execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, Lr.instrs, Lr.term⟩ fenv1 :=
                                execBlockFromIn_instrs_prefix prog F'' f prev bId ie
                                Lr.instrs Lr.term fenv fenv1 happ
                            have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                              rw [← hbb]; exact hg
                            have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                              fun b hb => hsub b hb
                            obtain ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                                hrel_arr, hreg_arr⟩ :=
                              ((ih bId j (updAssoc ρ id v0) s1 nextB lastVal
                                true Lr hr hf1 hlast1 accH
                                (updateHEnv henv id (.lit wE)) fenv1 hrel2
                                (fun hh => absurd hh (by simp)) hacc1
                                fh henv' out hrun prog f prev jblock (F'' + 1)
                                hsub' hnodf hfind fuelB C hg' u).1 hout)
                            exact ⟨w_u, hu, F', fenv_arr, hle, hge,
                              hLHS.trans heq_rest, hrel_arr, hreg_arr⟩
      · intro e_ret hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v0, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            cases hr : lowerStmtsCFG bId (some j) true (updAssoc ρ id v0)
                s1 nextB lastVal true none rest with
            | none => rw [hr] at h; simp at h
            | some Lr =>
                rw [hr] at h
                obtain rfl := Option.some.inj h
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.assign id e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.assign id e :: rest)
                        (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => runHIRStmts fh
                              (updateHEnv henv id v) rest
                              (.value (.lit accH))) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                            hregE⟩ :=
                          lower_total.1 ρ supply e v0 ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        rw [hrE] at hrun
                        have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                        have hlast1 : lastVal < s1 :=
                          Nat.lt_of_lt_of_le hlast hs1
                        have hva : v0 < s1 :=
                          lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                        have hf1 : FreshAbove (updAssoc ρ id v0) s1 := by
                          intro j u hmem
                          rcases updAssoc_mem ρ id v0 j u hmem with ⟨-, hwu⟩ |
                            hmem
                          · rw [hwu]
                            exact hva
                          · exact Nat.lt_of_lt_of_le (hfresh j u hmem) hs1
                        have hrel1 : RelEnv henv ρ fenv1.env :=
                          RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1
                            hrel hfresh hexec1
                        have hrel2 : RelEnv
                            (updateHEnv henv id (.lit wE))
                            (updAssoc ρ id v0) fenv1.env :=
                          RelEnv_update ρ henv fenv1.env id v0 wE
                            hrel1 (hww ▸ hregE)
                        have hacc1 : fenv1.env lastVal = some accH := by
                          rw [lower_preserv_regs ρ supply e v0 ie s1
                            he fenv fenv1 hexec1 lastVal hlast]
                          exact hreg
                        have hnp : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                            rfl
                        have hexec : execInstrsFullFromIn prog prev
                            fenv ie = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
                          exact hexec1
                        have happ : execInstrsFullFromIn prog prev fenv
                            (ie ++ Lr.instrs) =
                            execInstrsFullFromIn prog prev fenv1 Lr.instrs := by
                          rw [execInstrsFullFromIn_append, hexec]
                        have hbb : blockBound fuelB (.assign id e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        cases F with
                        | zero =>
                            have h1 : blockBound fuelB rest ≥ 1 := by
                              rw [blockBound]; omega
                            omega
                        | succ F'' =>
                            have hLHS : execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, ie ++ Lr.instrs, Lr.term⟩ fenv =
                                execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, Lr.instrs, Lr.term⟩ fenv1 :=
                                execBlockFromIn_instrs_prefix prog F'' f prev bId ie
                                Lr.instrs Lr.term fenv fenv1 happ
                            have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                              rw [← hbb]; exact hg
                            have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                              fun b hb => hsub b hb
                            obtain ⟨w_e, hu_e, heq_rest⟩ :=
                              ((ih bId j (updAssoc ρ id v0) s1 nextB lastVal
                                true Lr hr hf1 hlast1 accH
                                (updateHEnv henv id (.lit wE)) fenv1 hrel2
                                (fun hh => absurd hh (by simp)) hacc1
                                fh henv' out hrun prog f prev jblock (F'' + 1)
                                hsub' hnodf hfind fuelB C hg' u).2 e_ret hout)
                            exact ⟨w_e, hu_e, hLHS.trans heq_rest⟩
  | nop rest hrs ih =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG] at h
        cases hr : lowerStmtsCFG bId (some j) true ρ supply nextB lastVal
            hasVal none rest with
        | none => rw [hr] at h; simp at h
        | some Lr =>
            rw [hr] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv (.nop :: rest)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv (.nop :: rest)
                    (.value (.lit accH)) =
                    runHIRStmts fh henv rest (.value (.lit accH)) := rfl
                rw [hstep] at hrun
                have hbb : blockBound fuelB (.nop :: rest)
                    = blockBound fuelB rest := by
                  rw [blockBound, blockBound,
                    armBlockBound_cons_not_if fuelB
                      (fun c th el h => by cases h)
                      (fun c body h => by cases h)]
                have hg' : F ≥ blockBound fuelB rest + C := by
                  rw [← hbb]; exact hg
                obtain ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                    hrel_arr, hreg_arr⟩ :=
                  ((ih bId j ρ supply nextB lastVal hasVal Lr hr hfresh
                    hlast accH henv fenv hrel hval0 hreg fh henv' out hrun
                    prog f prev jblock F hsub hnodf hfind fuelB C hg'
                    u).1 hout)
                exact ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                  hrel_arr, hreg_arr⟩
      · intro e_ret hout
        simp only [lowerStmtsCFG] at h
        cases hr : lowerStmtsCFG bId (some j) true ρ supply nextB lastVal
            hasVal none rest with
        | none => rw [hr] at h; simp at h
        | some Lr =>
            rw [hr] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv (.nop :: rest)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv (.nop :: rest)
                    (.value (.lit accH)) =
                    runHIRStmts fh henv rest (.value (.lit accH)) := rfl
                rw [hstep] at hrun
                have hbb : blockBound fuelB (.nop :: rest)
                    = blockBound fuelB rest := by
                  rw [blockBound, blockBound,
                    armBlockBound_cons_not_if fuelB
                      (fun c th el h => by cases h)
                      (fun c body h => by cases h)]
                have hg' : F ≥ blockBound fuelB rest + C := by
                  rw [← hbb]; exact hg
                obtain ⟨w_e, hu_e, heq_rest⟩ :=
                  ((ih bId j ρ supply nextB lastVal hasVal Lr hr hfresh
                    hlast accH henv fenv hrel hval0 hreg fh henv' out hrun
                    prog f prev jblock F hsub hnodf hfind fuelB C hg'
                    u).2 e_ret hout)
                exact ⟨w_e, hu_e, heq_rest⟩
  | returnStmt e rest hstr _ =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv (.returnStmt e :: rest)
                    (.value (.lit accH)) =
                    (match evalHIR 256 henv e with
                      | none => (HFlow.stuck, henv)
                      | some v => (.returned v, henv)) := rfl
                rw [hstep] at hrun
                cases hev : evalHIR 256 henv e with
                | none =>
                    rw [hev] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | some r =>
                    rw [hev] at hrun
                    have hret : out = .returned r := (congrArg Prod.fst hrun).symm
                    rw [hret] at hout
                    exact absurd hout (by simp)
      · intro e_ret hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv (.returnStmt e :: rest)
                    (.value (.lit accH)) =
                    (match evalHIR 256 henv e with
                      | none => (HFlow.stuck, henv)
                      | some v => (.returned v, henv)) := rfl
                rw [hstep] at hrun
                cases hev : evalHIR 256 henv e with
                | none =>
                    rw [hev] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | some r =>
                    rw [hev] at hrun
                    have hret : out = .returned r := (congrArg Prod.fst hrun).symm
                    rw [hret] at hout
                    obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                        hregE⟩ :=
                      lower_total.1 ρ supply e v ie s1 he hstr hfresh
                        henv fenv hrel 256 r hev
                    have hrr : r = e_ret := HFlow.returned.inj hout
                    have heq : e_ret = .lit wE := hrr.symm ▸ hrE
                    have hnp : ∀ dst pred src,
                        .phi dst pred src ∉ ie := by
                      intro d p s hm
                      exact IsPure_not_phi
                        (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                    have hexec : execInstrsFullFromIn prog prev fenv ie
                        = some fenv1 := by
                      rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
                      exact hexec1
                    cases F with
                    | zero =>
                        have hbb : blockBound fuelB (.returnStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        have h1 : blockBound fuelB rest ≥ 1 := by
                          rw [blockBound]; omega
                        omega
                    | succ F' =>
                        refine ⟨wE, heq, ?_⟩
                        have hLHS : execBlockFromIn prog (F' + 1) f prev
                                ⟨bId, ie, .return_ v⟩ fenv =
                                fenv1.env v := by
                          have hret' : execBlockFromIn prog (F' + 1) f prev
                                ⟨bId, ie, .return_ v⟩ fenv =
                              (match execInstrsFullFromIn prog prev fenv ie with
                               | none => (none : Option Value)
                               | some g => g.env v) := rfl
                          rw [hret', hexec]
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        rw [hLHS, hww]
                        exact hregE
  | breakStmt rest _ =>
      simp only [lowerStmtsCFG] at h
      simp at h
  | continueStmt rest _ =>
      simp only [lowerStmtsCFG] at h
      simp at h
  | ifStmt c th el rest hstr _ hath hael hrs ihr =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
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
                  obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                    lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath
                  obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                    lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he hael
                  have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                  have hf1 : FreshAbove ρ s1 :=
                    FreshAbove.mono ρ supply s1 hs1 hfresh
                  have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
                  have hst : s1 ≤ lt.supply :=
                    (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht
                      hath).2.1
                  have hse : lt.supply ≤ le.supply :=
                    (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he
                      hael).2.1
                  have hfrρ : FreshAbove ρ le.supply :=
                    FreshAbove.mono ρ supply le.supply (Nat.le_trans hs1
                      (Nat.le_trans hst hse)) hfresh
                  have hbb_if : blockBound fuelB (.ifStmt c th el :: rest) =
                      1 + (3 + max (armBlockBound fuelB th)
                        (armBlockBound fuelB el) +
                        armBlockBound fuelB rest) := by
                    rw [blockBound, armBlockBound_if]
                  have hB1 : blockBound fuelB (.ifStmt c th el :: rest) ≥ 1 := by
                    rw [blockBound]; omega
                  have hne_pe : ((le.blocks.getLast?.map (fun b => b.id)).getD
                      (nextB + 1)) ≠
                      ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) := by
                    have hexitT : ((lt.blocks.getLast?.map (fun b => b.id)).getD
                        nextB) = nextB ∨
                        ∃ b ∈ lt.blocks,
                          ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) =
                            b.id := by
                      cases hgl : lt.blocks.getLast? with
                      | none =>
                          exact Or.inl (by simp)
                      | some b =>
                          have hm : b ∈ lt.blocks := getLast?_mem hgl
                          exact Or.inr ⟨b, hm, by simp⟩
                    have hexitE : ((le.blocks.getLast?.map (fun b => b.id)).getD
                        (nextB + 1)) = nextB + 1 ∨
                        ∃ b ∈ le.blocks,
                          ((le.blocks.getLast?.map (fun b => b.id)).getD
                            (nextB + 1)) = b.id := by
                      cases hgl : le.blocks.getLast? with
                      | none =>
                          exact Or.inl (by simp)
                      | some b =>
                          have hm : b ∈ le.blocks := getLast?_mem hgl
                          exact Or.inr ⟨b, hm, by simp⟩
                    rcases hexitT with hT | ⟨bt, hbt, hT⟩
                    · rcases hexitE with hE | ⟨be, hbe, hE⟩
                      · simp [hT, hE]
                      · obtain ⟨hlo, -⟩ := hbnde be hbe
                        rw [hE, hT]
                        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega)
                          (Nat.le_trans hmnt hlo))
                    · rcases hexitE with hE | ⟨be, hbe, hE⟩
                      · obtain ⟨hlo, -⟩ := hbndt bt hbt
                        rw [hE, hT]
                        exact Nat.ne_of_lt (Nat.le_trans (Nat.le_of_lt
                          (Nat.add_lt_add_left (by decide) nextB)) hlo)
                      · obtain ⟨-, hhi⟩ := hbndt bt hbt
                        obtain ⟨hlo, -⟩ := hbnde be hbe
                        rw [hE, hT]
                        exact Nat.ne_of_gt
                          (Nat.lt_of_lt_of_le hhi hlo)
                  have hgF : F ≥ 1 + (3 + max (armBlockBound fuelB th)
                      (armBlockBound fuelB el) + armBlockBound fuelB rest) + C := by
                    rw [← hbb_if]; exact hg
                  cases F with
                  | zero => omega
                  | succ F'' =>
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv
                              (.ifStmt c th el :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            simp [hst] at hout
                          · intro e hout
                            simp [hst] at hout
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.ifStmt c th el :: rest)
                              (.value (.lit accH)) =
                              (match evalHIR 256 henv c with
                                | some (.lit (.bool true)) =>
                                  match runHIRStmts fh henv th
                                      (HFlow.value (.lit .unit)) with
                                  | (HFlow.value u, env') =>
                                      runHIRStmts fh env' rest
                                        ((HFlow.value (.lit accH)).replace
                                          u)
                                  | (f, env') => (f, env')
                                | some (.lit (.bool false)) =>
                                  match runHIRStmts fh henv el
                                      (HFlow.value (.lit .unit)) with
                                  | (HFlow.value u, env') =>
                                      runHIRStmts fh env' rest
                                        ((HFlow.value (.lit accH)).replace
                                          u)
                                  | (f, env') => (f, env')
                                | _ => (.stuck, henv)) := rfl
                          rw [hstep] at hrun
                          cases hevC : evalHIR 256 henv c with
                          | none =>
                              rw [hevC] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout
                                simp [hst] at hout
                          | some r =>
                              rw [hevC] at hrun
                              obtain ⟨⟨w, hrw⟩, fenvC, hexecC, hstoreC,
                                  wC, hrC, hregC⟩ :=
                                lower_total.1 ρ supply c vc ic s1 heC hstr
                                  hfresh henv fenv hrel 256 r hevC
                              subst hrw
                              have hnp_ic : ∀ dst pred src,
                                  .phi dst pred src ∉ ic := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ heC _ hm)
                                  d p s rfl
                              have hexec_ic : execInstrsFullFromIn prog
                                  prev fenv ic = some fenvC := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp_ic]
                                exact hexecC
                              have hrelC : RelEnv henv ρ fenvC.env :=
                                RelEnv_exec henv ρ supply c vc ic s1 heC
                                  fenv fenvC hrel hfresh hexecC
                              have hsuffixW : ∀ (ρm : List
                                  (HIR.Id × ValId)) (s2 : Nat)
                                  (mphis : List Instr)
                                  (lr : Lowered),
                                  (hmk : mkMergePhis ρ lt.ρ
                                    le.ρ (le.supply + 1)
                                    ((lt.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    nextB)
                                    ((le.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    (nextB + 1))
                                    (mergeIds ρ lt.ρ le.ρ) =
                                    some (mphis, s2, ρm)) →
                                  (hr : lowerStmtsCFG
                                    (nextB + 2) (some j) true ρm
                                    s2 le.next le.supply true
                                    none rest = some lr) →
                                  (hsubR : ∀ b ∈ lt.blocks ++
                                    [⟨nextB, lt.instrs,
                                    lt.term⟩] ++ le.blocks ++
                                    [⟨nextB + 1, le.instrs,
                                    le.term⟩] ++ [⟨nextB + 2,
                                    [MIR.Instr.phi le.supply
                                    ((lt.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    nextB) lt.val,
                                    MIR.Instr.phi le.supply
                                    ((le.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    (nextB + 1)) le.val] ++
                                    mphis ++ lr.instrs,
                                    lr.term⟩] ++ lr.blocks,
                                    b ∈ f.blocks) →
                                  (armPrev : Option MIR.BlockId) →
                                  (armEntry : Block) →
                                  (armExit : MIR.BlockId) →
                                  (hentry : execBlockFromIn prog
                                    (F'' + 1) f prev
                                    ⟨bId, ic, .branch vc nextB
                                    (nextB + 1)⟩ fenv =
                                    execBlockFromIn prog F'' f
                                    armPrev armEntry fenvC) →
                                  (henvArm : HEnv) →
                                  (wArm : Value) →
                                  (henv' : HEnv) →
                                  (out : HFlow) →
                                  (hrunTail : runHIRStmts fh
                                    henvArm rest
                                    (.value (.lit wArm)) =
                                    (out, henv')) →
                                  (Cres : Nat) →
                                  (hCtge : Cres ≥ blockBound fuelB
                                    rest) →
                                  ∀ (fenvT : FullEnv)
                                  (F1' : Nat),
                                  F1' ≤ F'' →
                                  F1' ≥ Cres + C →
                                  (heq_arm : execBlockFromIn
                                  prog F'' f armPrev
                                  armEntry fenvC =
                                  execBlockFromIn prog F1' f
                                  (some armExit) ⟨nextB + 2,
                                  [MIR.Instr.phi le.supply
                                  ((lt.blocks.getLast?.map
                                  (fun b => b.id)).getD
                                  nextB) lt.val,
                                  MIR.Instr.phi le.supply
                                  ((le.blocks.getLast?.map
                                  (fun b => b.id)).getD
                                  (nextB + 1)) le.val] ++
                                  mphis ++ lr.instrs,
                                  lr.term⟩ fenvT) →
                                  (fenvJ : FullEnv) →
                                  (happJ : execInstrsFullFromIn prog
                                  (some armExit) fenvT
                                  (([MIR.Instr.phi le.supply
                                  ((lt.blocks.getLast?.map
                                  (fun b => b.id)).getD
                                  nextB) lt.val,
                                  MIR.Instr.phi le.supply
                                  ((le.blocks.getLast?.map
                                  (fun b => b.id)).getD
                                  (nextB + 1)) le.val] ++
                                  mphis) ++ lr.instrs) =
                                  execInstrsFullFromIn prog
                                  (some armExit) fenvJ lr.instrs) →
                                  (hrelJ : RelEnv henvArm ρm
                                    fenvJ.env) →
                                  (hvmJ : fenvJ.env le.supply =
                                  some wArm) →
                                  ∀ (u : HIR.Expr),
                                  (out = .value u →
                                  ∃ w_u, u = .lit w_u ∧
                                  ∃ F2 fenv2, F2 ≤ F'' + 1 ∧ F2 ≥ C ∧
                                    execBlockFromIn prog (F'' + 1) f prev
                                    ⟨bId, ic, .branch vc nextB
                                    (nextB + 1)⟩ fenv =
                                    execBlockFromIn prog F2 f
                                    (some ((lr.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    (nextB + 2))) jblock fenv2 ∧
                                    RelEnv henv' lr.ρ fenv2.env ∧
                                    fenv2.env lr.val = some w_u) ∧
                                  (∀ (e : HIR.Expr),
                                  out = .returned e →
                                  ∃ w_e, e = .lit w_e ∧
                                  execBlockFromIn prog (F'' + 1) f prev
                                  ⟨bId, ic, .branch vc nextB
                                  (nextB + 1)⟩ fenv =
                                  some w_e) := by
                                intro ρm s2 mphis lr hmk hr
                                  hsubR armPrev armEntry armExit
                                  hentry henvArm wArm henv'
                                  out hrunTail Cres hCtge
                                  fenvT F1' hle hge
                                  heq_arm fenvJ happJ hrelJ hvmJ
                                have hJmem : (⟨nextB + 2,
                                    [MIR.Instr.phi le.supply
                                    ((lt.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    nextB) lt.val,
                                    MIR.Instr.phi le.supply
                                    ((le.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    (nextB + 1)) le.val] ++
                                    mphis ++ lr.instrs,
                                    lr.term⟩ : Block) ∈
                                    f.blocks :=
                                  hsubR _ if_asm_mem_join
                                have hfindJ : findBlock f
                                    (nextB + 2) = some ⟨nextB + 2,
                                    [MIR.Instr.phi le.supply
                                    ((lt.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    nextB) lt.val,
                                    MIR.Instr.phi le.supply
                                    ((le.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    (nextB + 1)) le.val] ++
                                    mphis ++ lr.instrs,
                                    lr.term⟩ :=
                                  findBlock_of_nodup_mem hnodf
                                    hJmem
                                have hJeq : execBlockFromIn prog
                                    F1' f (some armExit)
                                    ⟨nextB + 2,
                                    [MIR.Instr.phi le.supply
                                    ((lt.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    nextB) lt.val,
                                    MIR.Instr.phi le.supply
                                    ((le.blocks.getLast?.map
                                    (fun b => b.id)).getD
                                    (nextB + 1)) le.val] ++
                                    mphis ++ lr.instrs,
                                    lr.term⟩ fenvT =
                                    execBlockFromIn prog F1'
                                    f (some armExit) ⟨nextB + 2,
                                    lr.instrs, lr.term⟩
                                    fenvJ := by
                                  cases F1' with
                                  | zero =>
                                      have hB1r : blockBound fuelB
                                          rest ≥ 1 := by
                                        rw [blockBound]; omega
                                      exact absurd hge (by omega)
                                  | succ G =>
                                      exact execBlockFromIn_instrs_prefix
                                        prog G f (some armExit)
                                        (nextB + 2)
                                        ([MIR.Instr.phi le.supply
                                        ((lt.blocks.getLast?.map
                                        (fun b => b.id)).getD
                                        nextB) lt.val,
                                        MIR.Instr.phi le.supply
                                        ((le.blocks.getLast?.map
                                        (fun b => b.id)).getD
                                        (nextB + 1)) le.val] ++
                                        mphis) lr.instrs lr.term
                                        fenvT fenvJ happJ
                                have hf_r : FreshAbove ρm s2 :=
                                  (mkMergePhis_growth_fresh
                                  (FreshAbove.mono ρ supply
                                  (le.supply + 1) (by omega)
                                  hfresh) hmk).2
                                have hlast_r : le.supply < s2 :=
                                  Nat.lt_of_lt_of_le
                                  (Nat.lt_succ_self _)
                                  (mkMergePhis_le hmk)
                                have hltB' : nextB + 2 < le.next := by
                                  have h1 : nextB + 3 ≤ lt.next :=
                                    hmnt
                                  have h2 : lt.next ≤ le.next :=
                                    hmne
                                  omega
                                have hsub_r : ∀ b ∈ lr.blocks,
                                    b ∈ f.blocks :=
                                  fun b hb => hsubR _
                                    (if_asm_mem_of_lr hb)
                                cases F1' with
                                | zero =>
                                    have hB1r : blockBound fuelB
                                        rest ≥ 1 := by
                                      rw [blockBound]; omega
                                    exact absurd hge (by omega)
                                | succ F1 =>
                                    have hg_r : F1 + 1 ≥
                                        blockBound fuelB rest + C :=
                                      Nat.le_trans (Nat.add_le_add_right hCtge C) hge
                                    have hihr :=
                                      ihr (nextB + 2) j ρm s2 le.next
                                      le.supply true lr hr hf_r
                                      hlast_r wArm henvArm fenvJ
                                      hrelJ (fun h => absurd h
                                      (by simp)) hvmJ fh
                                      henv' out hrunTail prog f
                                      (some armExit) jblock (F1 + 1)
                                      hsub_r hnodf hfind fuelB C
                                      hg_r
                                    intro u
                                    refine ⟨?_, ?_⟩
                                    · intro hout
                                      obtain ⟨w_u, hu, F2, fenv2,
                                          hle2, hge2, heq_rest,
                                          hrel_final,
                                          hreg_final⟩ :=
                                        (hihr u).1 hout
                                      exact ⟨w_u, hu, F2, fenv2,
                                        Nat.le_trans hle2
                                        (Nat.le_trans hle
                                        (Nat.le_succ _)),
                                        hge2,
                                        hentry.trans
                                        (heq_arm.trans
                                        (hJeq.trans
                                        heq_rest)),
                                        hrel_final,
                                        hreg_final⟩
                                    · intro e_ret hout2
                                      obtain ⟨w_e, hu_e,
                                          heq_rest⟩ :=
                                        (hihr e_ret).2 e_ret hout2
                                      exact ⟨w_e, hu_e,
                                        hentry.trans
                                        (heq_arm.trans
                                        (hJeq.trans
                                        heq_rest))⟩
                              cases w with
                              | bool b =>
                                  cases b with
                                  | true =>
                                      simp only [] at hrun
                                      cases har : runHIRStmts fh henv th
                                          (HFlow.value (.lit .unit)) with
                                      | mk out_arm env_arm =>
                                          rw [har] at hrun
                                          cases out_arm with
                                          | value u_arm =>
                                              simp only [] at hrun
                                              have hregCb : fenvC.env vc =
                                                  some (.bool true) := by
                                                have hww : (.bool true) =
                                                    wC :=
                                                  HIR.Expr.lit.inj hrC
                                                rw [hww]
                                                exact hregC
                                              have hbool : fenvC.boolOf vc =
                                                  some true :=
                                                boolOf_of_lit fenvC vc true
                                                  hregCb
                                              have hCtge : (2 + max
                                                  (armBlockBound fuelB th)
                                                  (armBlockBound fuelB el) +
                                                  armBlockBound fuelB rest -
                                                  armBlockBound fuelB th) ≥
                                                  blockBound fuelB rest := by
                                                have hBrest : blockBound
                                                    fuelB rest = 1 +
                                                    armBlockBound fuelB
                                                      rest := rfl
                                                omega
                                              have hg_t : F'' ≥ blockBound
                                                  fuelB th + (2 + max
                                                  (armBlockBound fuelB th)
                                                  (armBlockBound fuelB el) +
                                                  armBlockBound fuelB rest -
                                                  armBlockBound fuelB th + C) := by
                                                have hBth : blockBound
                                                    fuelB th = 1 +
                                                    armBlockBound fuelB
                                                      th := rfl
                                                omega
                                              have hfrT :=lowerStmtsCFG_arm_fresh budget _ _ _ _ _ _ _ _ _ _ ht hath hf1 hlast1
                                              have hfreshT : ∀ id srcT,
                                                  id ∈ mergeIds ρ lt.ρ le.ρ →
                                                  rhoLookup lt.ρ id =
                                                  some srcT →
                                                  srcT < le.supply + 1 := by
                                                intro id srcT hmem hlook
                                                have h1 : srcT < lt.supply :=
                                                  hfrT id srcT
                                                  (rhoLookup_some_mem lt.ρ id
                                                  srcT hlook)
                                                exact Nat.lt_of_lt_of_le h1
                                                  (Nat.le_trans hse
                                                    (Nat.le_succ _))
                                              have hne : ∀ id srcT,
                                                  id ∈ mergeIds ρ lt.ρ le.ρ →
                                                  rhoLookup lt.ρ id =
                                                  some srcT →
                                                  srcT ≠ le.supply := by
                                                intro id srcT hmem hlook
                                                have h1 : srcT < lt.supply :=
                                                  hfrT id srcT
                                                  (rhoLookup_some_mem lt.ρ id
                                                  srcT hlook)
                                                exact fun heq =>
                                                  (Nat.not_lt.mpr hse)
                                                    (heq.symm ▸ h1)
                                              cases hm : mergeIds ρ lt.ρ le.ρ with
                                              | nil =>
                                                  have hmk : mkMergePhis ρ lt.ρ
                                                      le.ρ (le.supply + 1)
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB)
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1))
                                                      (mergeIds ρ lt.ρ le.ρ) =
                                                      some ([], le.supply + 1,
                                                      ρ) := by
                                                    rw [hm]
                                                    rfl
                                                  rw [hm] at h
                                                  simp only [] at h
                                                  cases hr : lowerStmtsCFG
                                                      (nextB + 2) (some j) true ρ
                                                      (le.supply + 1) le.next
                                                      le.supply true none
                                                      rest with
                                                  | none => rw [hr] at h; simp at h
                                                  | some lr =>
                                                      rw [hr] at h
                                                      simp only [] at h
                                                      obtain rfl :=
                                                        Option.some.inj h
                                                      dsimp only at hsub ⊢
                                                      have hsub_t : ∀ b ∈ lt.blocks,
                                                          b ∈ f.blocks :=
                                                        fun b hb => hsub _
                                                          (if_asm_mem_of_lt hb)
                                                      have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                                          ∈ f.blocks :=
                                                        hsub _ if_asm_mem_then
                                                      have hfindT : findBlock f nextB =
                                                          some ⟨nextB, lt.instrs, lt.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf hTmem
                                                      have hfindJb : findBlock f
                                                          (nextB + 2) = some ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          lr.instrs,
                                                          lr.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_join)
                                                      obtain ⟨wArm, huArm, F1', fenvT,
                                                          hle, hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arm, _⟩ :=
                                                        ((lowerStmtsCFG_arm_total budget nextB (nextB + 2) ρ
                                                        s1 (nextB + 3) lastVal
                                                        false none th lt ht hath hf1 hlast1
                                                        .unit henv fenvC hrelC
                                                        (fun _ => rfl)
                                                        (fun h => absurd h
                                                        (by simp)) fh env_arm
                                                        (HFlow.value u_arm)
                                                        har prog f (some bId)
                                                        ⟨nextB + 2,
                                                        [MIR.Instr.phi le.supply
                                                        ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) lt.val,
                                                        MIR.Instr.phi le.supply
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) le.val] ++
                                                        lr.instrs,
                                                        lr.term⟩ F'' hsub_t
                                                        hnodf hfindJb fuelB
                                                        (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB th + C)
                                                        hg_t u_arm).1 rfl)
                                                      obtain ⟨fenvJ, happJ, hrelJ,
                                                          hvmJ, -⟩ :=
                                                        bindArm_join_exec prog hmk rfl
                                                          hne_pe hrel_arm hreg_arm
                                                          hfreshT hne
                                                          (Nat.lt_succ_self _) hfrρ
                                                      have hentry : execBlockFromIn prog
                                                          (F'' + 1) f prev
                                                          ⟨bId, ic, .branch vc nextB
                                                          (nextB + 1)⟩ fenv =
                                                          execBlockFromIn prog F'' f
                                                          (some bId)
                                                          ⟨nextB, lt.instrs,
                                                          lt.term⟩ fenvC :=
                                                        execBlockFromIn_branch_true
                                                          prog F'' f prev bId ic vc
                                                          nextB (nextB + 1) fenv
                                                          fenvC ⟨nextB, lt.instrs,
                                                          lt.term⟩ hexec_ic hbool
                                                          hfindT
                                                      have hsubR : ∀ b ∈ lt.blocks ++
                                                          [⟨nextB, lt.instrs,
                                                          lt.term⟩] ++ le.blocks ++
                                                          [⟨nextB + 1, le.instrs,
                                                          le.term⟩] ++ [⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          ([] : List Instr) ++
                                                          lr.instrs,
                                                          lr.term⟩] ++ lr.blocks,
                                                          b ∈ f.blocks :=
                                                        fun b hb => hsub _ hb
                                                      have hrep : ((HFlow.value
                                                          (.lit accH)).replace
                                                          (.lit wArm)) =
                                                          HFlow.value
                                                            (.lit wArm) := rfl
                                                      rw [huArm, hrep] at hrun
                                                      rw [if_assembly_exit rfl]
                                                      exact hsuffixW _ _ _ _ hmk hr
                                                        hsubR (some bId) ⟨nextB, lt.instrs,
                                                        lt.term⟩ ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) hentry env_arm wArm
                                                        henv' out hrun (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB th)
                                                        hCtge fenvT F1'
                                                        hle hge heq_arm
                                                        fenvJ happJ hrelJ hvmJ
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
                                                      cases hr : lowerStmtsCFG
                                                          (nextB + 2) (some j) true ρm
                                                          s2 le.next
                                                          le.supply true none
                                                          rest with
                                                      | none => rw [hr] at h; simp at h
                                                      | some lr =>
                                                          rw [hr] at h
                                                          simp only [] at h
                                                          obtain rfl :=
                                                            Option.some.inj h
                                                          dsimp only at hsub ⊢
                                                          have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                                              ∈ f.blocks :=
                                                            hsub _ if_asm_mem_then
                                                          have hfindT : findBlock f nextB =
                                                              some ⟨nextB, lt.instrs, lt.term⟩ :=
                                                            findBlock_of_nodup_mem hnodf hTmem
                                                          have hmk : mkMergePhis ρ lt.ρ
                                                              le.ρ (le.supply + 1)
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB)
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1))
                                                              (mergeIds ρ lt.ρ le.ρ) =
                                                              some (mphis, s2, ρm) := by
                                                            rw [hm]
                                                            exact hmphi
                                                          have hfindJb : findBlock f
                                                              (nextB + 2) = some ⟨nextB + 2,
                                                              [MIR.Instr.phi le.supply
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB) lt.val,
                                                              MIR.Instr.phi le.supply
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1)) le.val] ++
                                                              mphis ++ lr.instrs,
                                                              lr.term⟩ :=
                                                            findBlock_of_nodup_mem hnodf
                                                              (hsub _ if_asm_mem_join)
                                                          obtain ⟨wArm, huArm, F1', fenvT,
                                                              hle, hge, heq_arm,
                                                              hrel_arm,
                                                              hreg_arm, _⟩ :=
                                                            ((lowerStmtsCFG_arm_total budget nextB (nextB + 2) ρ
                                                            s1 (nextB + 3) lastVal
                                                            false none th lt ht hath hf1 hlast1
                                                            .unit henv fenvC hrelC
                                                            (fun _ => rfl)
                                                            (fun h => absurd h
                                                            (by simp)) fh env_arm
                                                            (HFlow.value u_arm)
                                                            har prog f (some bId)
                                                            ⟨nextB + 2,
                                                            [MIR.Instr.phi le.supply
                                                            ((lt.blocks.getLast?.map
                                                            (fun b => b.id)).getD
                                                            nextB) lt.val,
                                                            MIR.Instr.phi le.supply
                                                            ((le.blocks.getLast?.map
                                                            (fun b => b.id)).getD
                                                            (nextB + 1)) le.val] ++
                                                            mphis ++ lr.instrs,
                                                            lr.term⟩ F'' (fun b hb => hsub _ (if_asm_mem_of_lt hb))
                                                            hnodf hfindJb fuelB
                                                            (2 + max
                                                            (armBlockBound fuelB th)
                                                            (armBlockBound fuelB el) +
                                                            armBlockBound fuelB rest -
                                                            armBlockBound fuelB th + C)
                                                            hg_t u_arm).1 rfl)
                                                          obtain ⟨fenvJ, happJ, hrelJ,
                                                              hvmJ, -⟩ :=
                                                            bindArm_join_exec prog hmk rfl
                                                              hne_pe hrel_arm hreg_arm
                                                              hfreshT hne
                                                              (Nat.lt_succ_self _) hfrρ
                                                          have hentry : execBlockFromIn prog
                                                              (F'' + 1) f prev
                                                              ⟨bId, ic, .branch vc nextB
                                                              (nextB + 1)⟩ fenv =
                                                              execBlockFromIn prog F'' f
                                                              (some bId)
                                                              ⟨nextB, lt.instrs,
                                                              lt.term⟩ fenvC :=
                                                            execBlockFromIn_branch_true
                                                              prog F'' f prev bId ic vc
                                                              nextB (nextB + 1) fenv
                                                              fenvC ⟨nextB, lt.instrs,
                                                              lt.term⟩ hexec_ic hbool
                                                              hfindT
                                                          have hsubR : ∀ b ∈ lt.blocks ++
                                                              [⟨nextB, lt.instrs,
                                                              lt.term⟩] ++ le.blocks ++
                                                              [⟨nextB + 1, le.instrs,
                                                              le.term⟩] ++ [⟨nextB + 2,
                                                              [MIR.Instr.phi le.supply
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB) lt.val,
                                                              MIR.Instr.phi le.supply
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1)) le.val] ++
                                                              mphis ++ lr.instrs,
                                                              lr.term⟩] ++ lr.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _ hb
                                                          have hrep : ((HFlow.value
                                                              (.lit accH)).replace
                                                              (.lit wArm)) =
                                                              HFlow.value
                                                                (.lit wArm) := rfl
                                                          rw [huArm, hrep] at hrun
                                                          rw [if_assembly_exit rfl]
                                                          exact hsuffixW _ _ _ _ hmk hr
                                                            hsubR (some bId) ⟨nextB, lt.instrs,
                                                            lt.term⟩ ((lt.blocks.getLast?.map
                                                            (fun b => b.id)).getD
                                                            nextB) hentry env_arm wArm
                                                            henv' out hrun (2 + max
                                                            (armBlockBound fuelB th)
                                                            (armBlockBound fuelB el) +
                                                            armBlockBound fuelB rest -
                                                            armBlockBound fuelB th)
                                                            hCtge fenvT F1'
                                                            hle hge heq_arm
                                                            fenvJ happJ hrelJ hvmJ
                                          | returned e_arm =>
                                              simp only [] at hrun
                                              have hout_r : out =
                                                  .returned e_arm :=
                                                (congrArg Prod.fst
                                                  hrun).symm
                                              have hregCb_r : fenvC.env vc =
                                                  some (.bool true) := by
                                                have hww : (.bool true) =
                                                    wC :=
                                                  HIR.Expr.lit.inj hrC
                                                rw [hww]
                                                exact hregC
                                              have hbool_r : fenvC.boolOf vc =
                                                  some true :=
                                                boolOf_of_lit fenvC vc true
                                                  hregCb_r
                                              have hg_tr : F'' ≥ blockBound
                                                  fuelB th + (2 + max
                                                  (armBlockBound fuelB th)
                                                  (armBlockBound fuelB el) +
                                                  armBlockBound fuelB rest -
                                                  armBlockBound fuelB th) := by
                                                have hBth : blockBound
                                                    fuelB th = 1 +
                                                    armBlockBound fuelB
                                                      th := rfl
                                                omega
                                              cases hmR : mergeIds ρ lt.ρ le.ρ with
                                              | nil =>
                                                  rw [hmR] at h
                                                  simp only [] at h
                                                  cases hrR : lowerStmtsCFG
                                                      (nextB + 2) (some j) true ρ
                                                      (le.supply + 1) le.next
                                                      le.supply true none
                                                      rest with
                                                  | none =>
                                                      rw [hrR] at h
                                                      simp at h
                                                  | some lrR =>
                                                      rw [hrR] at h
                                                      simp only [] at h
                                                      obtain rfl :=
                                                        Option.some.inj h
                                                      have hfindT : findBlock f nextB =
                                                          some ⟨nextB, lt.instrs,
                                                          lt.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_then)
                                                      have hfindJb : findBlock f (nextB + 2) =
                                                          some ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          ([] : List Instr) ++
                                                          lrR.instrs,
                                                          lrR.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_join)
                                                      have hentry_r : execBlockFromIn prog
                                                          (F'' + 1) f prev
                                                          ⟨bId, ic, .branch vc nextB
                                                          (nextB + 1)⟩ fenv =
                                                          execBlockFromIn prog F'' f
                                                          (some bId)
                                                          ⟨nextB, lt.instrs,
                                                          lt.term⟩ fenvC :=
                                                        execBlockFromIn_branch_true
                                                          prog F'' f prev bId ic vc
                                                          nextB (nextB + 1) fenv
                                                          fenvC ⟨nextB, lt.instrs,
                                                          lt.term⟩ hexec_ic hbool_r
                                                          hfindT
                                                      intro u
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        simp [hout_r] at hout
                                                      · intro e hout2
                                                        have hret_e : e = e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                              hout2)).symm
                                                        obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                          ((lowerStmtsCFG_arm_total budget nextB (nextB + 2) ρ
                                                          s1 (nextB + 3) lastVal
                                                          false none th lt ht hath hf1 hlast1
                                                          .unit henv fenvC hrelC
                                                          (fun _ => rfl)
                                                          (fun h => absurd h
                                                          (by simp)) fh env_arm
                                                          (HFlow.returned e_arm)
                                                          har prog f (some bId)
                                                          ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          ([] : List Instr) ++
                                                          lrR.instrs,
                                                          lrR.term⟩ F'' (fun b hb => hsub _ (if_asm_mem_of_lt hb))
                                                          hnodf hfindJb fuelB
                                                          (2 + max
                                                          (armBlockBound fuelB th)
                                                          (armBlockBound fuelB el) +
                                                          armBlockBound fuelB rest -
                                                          armBlockBound fuelB th)
                                                          hg_tr e_arm).2 e_arm rfl)
                                                        exact ⟨w_e, hret_e.trans hu_e,
                                                          hentry_r.trans heq_e⟩
                                              | cons hdR tlR =>
                                                  rw [hmR] at h
                                                  simp only [] at h
                                                  cases hmphiR : mkMergePhis ρ lt.ρ le.ρ
                                                      (le.supply + 1)
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB)
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1))
                                                      (hdR :: tlR) with
                                                  | none =>
                                                      rw [hmphiR] at h
                                                      simp at h
                                                  | some qR =>
                                                      obtain ⟨mphisR, s2R,
                                                          ρmR⟩ := qR
                                                      rw [hmphiR] at h
                                                      simp only [] at h
                                                      cases hrR : lowerStmtsCFG
                                                          (nextB + 2) (some j) true
                                                          ρmR s2R le.next
                                                          le.supply true none
                                                          rest with
                                                      | none =>
                                                          rw [hrR] at h
                                                          simp at h
                                                      | some lrR =>
                                                          rw [hrR] at h
                                                          simp only [] at h
                                                          obtain rfl :=
                                                            Option.some.inj h
                                                          have hfindT : findBlock f nextB =
                                                              some ⟨nextB, lt.instrs,
                                                              lt.term⟩ :=
                                                            findBlock_of_nodup_mem hnodf
                                                              (hsub _ if_asm_mem_then)
                                                          have hfindJb : findBlock f (nextB + 2) =
                                                              some ⟨nextB + 2,
                                                              [MIR.Instr.phi le.supply
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB) lt.val,
                                                              MIR.Instr.phi le.supply
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1)) le.val] ++
                                                              mphisR ++
                                                              lrR.instrs,
                                                              lrR.term⟩ :=
                                                            findBlock_of_nodup_mem hnodf
                                                              (hsub _ if_asm_mem_join)
                                                          have hentry_r : execBlockFromIn prog
                                                              (F'' + 1) f prev
                                                              ⟨bId, ic, .branch vc nextB
                                                              (nextB + 1)⟩ fenv =
                                                              execBlockFromIn prog F'' f
                                                              (some bId)
                                                              ⟨nextB, lt.instrs,
                                                              lt.term⟩ fenvC :=
                                                            execBlockFromIn_branch_true
                                                              prog F'' f prev bId ic vc
                                                              nextB (nextB + 1) fenv
                                                              fenvC ⟨nextB, lt.instrs,
                                                              lt.term⟩ hexec_ic hbool_r
                                                              hfindT
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            simp [hout_r] at hout
                                                          · intro e hout2
                                                            have hret_e : e = e_arm :=
                                                              (HFlow.returned.inj
                                                                (hout_r.symm.trans
                                                                  hout2)).symm
                                                            obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                              ((lowerStmtsCFG_arm_total budget nextB (nextB + 2) ρ
                                                              s1 (nextB + 3) lastVal
                                                              false none th lt ht hath hf1 hlast1
                                                              .unit henv fenvC hrelC
                                                              (fun _ => rfl)
                                                              (fun h => absurd h
                                                              (by simp)) fh env_arm
                                                              (HFlow.returned e_arm)
                                                              har prog f (some bId)
                                                              ⟨nextB + 2,
                                                              [MIR.Instr.phi le.supply
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB) lt.val,
                                                              MIR.Instr.phi le.supply
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1)) le.val] ++
                                                              mphisR ++
                                                              lrR.instrs,
                                                              lrR.term⟩ F'' (fun b hb => hsub _ (if_asm_mem_of_lt hb))
                                                              hnodf hfindJb fuelB
                                                              (2 + max
                                                              (armBlockBound fuelB th)
                                                              (armBlockBound fuelB el) +
                                                              armBlockBound fuelB rest -
                                                              armBlockBound fuelB th)
                                                              hg_tr e_arm).2 e_arm rfl)
                                                            exact ⟨w_e, hret_e.trans hu_e,
                                                              hentry_r.trans heq_e⟩
                                          | broke =>
                                              simp only [] at hrun
                                              have hout_r : out = .broke :=
                                                (congrArg Prod.fst
                                                  hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hout_r] at hout
                                              · intro e hout2
                                                simp [hout_r] at hout2
                                          | continued =>
                                              simp only [] at hrun
                                              have hout_r : out = .continued :=
                                                (congrArg Prod.fst
                                                  hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hout_r] at hout
                                              · intro e hout2
                                                simp [hout_r] at hout2
                                          | stuck =>
                                              simp only [] at hrun
                                              have hout_r : out = .stuck :=
                                                (congrArg Prod.fst
                                                  hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hout_r] at hout
                                              · intro e hout2
                                                simp [hout_r] at hout2
                                  | false =>
                                      simp only [] at hrun
                                      cases har : runHIRStmts fh henv el
                                          (HFlow.value (.lit .unit)) with
                                      | mk out_arm env_arm =>
                                          rw [har] at hrun
                                          cases out_arm with
                                          | value u_arm =>
                                              simp only [] at hrun
                                              have hregCb : fenvC.env vc =
                                                  some (.bool false) := by
                                                have hww : (.bool false) =
                                                    wC :=
                                                  HIR.Expr.lit.inj hrC
                                                rw [hww]
                                                exact hregC
                                              have hbool : fenvC.boolOf vc =
                                                  some false :=
                                                boolOf_of_lit fenvC vc false
                                                  hregCb
                                              have hCtge' : (2 + max
                                                  (armBlockBound fuelB th)
                                                  (armBlockBound fuelB el) +
                                                  armBlockBound fuelB rest -
                                                  armBlockBound fuelB el) ≥
                                                  blockBound fuelB rest := by
                                                have hBrest : blockBound
                                                    fuelB rest = 1 +
                                                    armBlockBound fuelB
                                                      rest := rfl
                                                omega
                                              have hg_e : F'' ≥ blockBound
                                                  fuelB el + (2 + max
                                                  (armBlockBound fuelB th)
                                                  (armBlockBound fuelB el) +
                                                  armBlockBound fuelB rest -
                                                  armBlockBound fuelB el + C) := by
                                                have hBel : blockBound
                                                    fuelB el = 1 +
                                                    armBlockBound fuelB
                                                      el := rfl
                                                omega
                                              have hfE1 : FreshAbove ρ lt.supply :=
                                                FreshAbove.mono ρ supply lt.supply
                                                  (Nat.le_trans hs1 hst) hfresh
                                              have hlastE1 : lastVal < lt.supply :=
                                                Nat.lt_of_lt_of_le hlast1 hst
                                              have hfrE :=lowerStmtsCFG_arm_fresh budget _ _ _ _ _ _ _ _ _ _ he hael hfE1 hlastE1
                                              have hfreshE : ∀ id srcE,
                                                  id ∈ mergeIds ρ lt.ρ le.ρ →
                                                  rhoLookup le.ρ id =
                                                  some srcE →
                                                  srcE < le.supply + 1 := by
                                                intro id srcE hmem hlook
                                                have h1 : srcE < le.supply :=
                                                  hfrE id srcE
                                                  (rhoLookup_some_mem le.ρ id
                                                  srcE hlook)
                                                exact Nat.lt_of_lt_of_le h1
                                                  (Nat.le_succ _)
                                              have hneE : ∀ id srcE,
                                                  id ∈ mergeIds ρ lt.ρ le.ρ →
                                                  rhoLookup le.ρ id =
                                                  some srcE →
                                                  srcE ≠ le.supply := by
                                                intro id srcE hmem hlook
                                                have h1 : srcE < le.supply :=
                                                  hfrE id srcE
                                                  (rhoLookup_some_mem le.ρ id
                                                  srcE hlook)
                                                exact Nat.ne_of_lt h1
                                              cases hm : mergeIds ρ lt.ρ le.ρ with
                                              | nil =>
                                                  have hmk : mkMergePhis ρ lt.ρ
                                                      le.ρ (le.supply + 1)
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB)
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1))
                                                      (mergeIds ρ lt.ρ le.ρ) =
                                                      some ([], le.supply + 1,
                                                      ρ) := by
                                                    rw [hm]
                                                    rfl
                                                  rw [hm] at h
                                                  simp only [] at h
                                                  cases hr : lowerStmtsCFG
                                                      (nextB + 2) (some j) true ρ
                                                      (le.supply + 1) le.next
                                                      le.supply true none
                                                      rest with
                                                  | none => rw [hr] at h; simp at h
                                                  | some lr =>
                                                      rw [hr] at h
                                                      simp only [] at h
                                                      obtain rfl :=
                                                        Option.some.inj h
                                                      dsimp only at hsub ⊢
                                                      have hsub_e : ∀ b ∈ le.blocks,
                                                          b ∈ f.blocks :=
                                                        fun b hb => hsub _
                                                          (if_asm_mem_of_le hb)
                                                      have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ :
                                                          Block) ∈ f.blocks :=
                                                        hsub _ if_asm_mem_else
                                                      have hfindE : findBlock f (nextB + 1) =
                                                          some ⟨nextB + 1, le.instrs, le.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf hEmem
                                                      have hfindJb : findBlock f
                                                          (nextB + 2) = some ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          lr.instrs,
                                                          lr.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_join)
                                                      obtain ⟨wArm, huArm, F1', fenvT,
                                                          hle, hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arm, _⟩ :=
                                                        ((lowerStmtsCFG_arm_total budget (nextB + 1) (nextB + 2) ρ
                                                        lt.supply lt.next lastVal
                                                        false none el le he hael hfE1 hlastE1
                                                        .unit henv fenvC hrelC
                                                        (fun _ => rfl)
                                                        (fun h => absurd h
                                                        (by simp)) fh env_arm
                                                        (HFlow.value u_arm)
                                                        har prog f (some bId)
                                                        ⟨nextB + 2,
                                                        [MIR.Instr.phi le.supply
                                                        ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) lt.val,
                                                        MIR.Instr.phi le.supply
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) le.val] ++
                                                        lr.instrs,
                                                        lr.term⟩ F'' hsub_e
                                                        hnodf hfindJb fuelB
                                                        (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB el + C)
                                                        hg_e u_arm).1 rfl)
                                                      obtain ⟨fenvJ, happJ, hrelJ,
                                                          hvmJ, -⟩ :=
                                                        bindArm_join_execE prog hmk
                                                          (Ne.symm hne_pe) rfl
                                                          hrel_arm hreg_arm
                                                          hfreshE hneE
                                                          (Nat.lt_succ_self _) hfrρ
                                                      have hentry : execBlockFromIn prog
                                                          (F'' + 1) f prev
                                                          ⟨bId, ic, .branch vc nextB
                                                          (nextB + 1)⟩ fenv =
                                                          execBlockFromIn prog F'' f
                                                          (some bId)
                                                          ⟨nextB + 1, le.instrs,
                                                          le.term⟩ fenvC :=
                                                        execBlockFromIn_branch_false
                                                          prog F'' f prev bId ic vc
                                                          nextB (nextB + 1) fenv
                                                          fenvC ⟨nextB + 1, le.instrs,
                                                          le.term⟩ hexec_ic hbool
                                                          hfindE
                                                      have hsubR : ∀ b ∈ lt.blocks ++
                                                          [⟨nextB, lt.instrs,
                                                          lt.term⟩] ++ le.blocks ++
                                                          [⟨nextB + 1, le.instrs,
                                                          le.term⟩] ++ [⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          ([] : List Instr) ++
                                                          lr.instrs,
                                                          lr.term⟩] ++ lr.blocks,
                                                          b ∈ f.blocks :=
                                                        fun b hb => hsub _ hb
                                                      have hrep : ((HFlow.value
                                                          (.lit accH)).replace
                                                          (.lit wArm)) =
                                                          HFlow.value
                                                            (.lit wArm) := rfl
                                                      rw [huArm, hrep] at hrun
                                                      rw [if_assembly_exit rfl]
                                                      exact hsuffixW _ _ _ _ hmk hr
                                                        hsubR (some bId)
                                                        ⟨nextB + 1, le.instrs,
                                                        le.term⟩
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) hentry env_arm wArm
                                                        henv' out hrun (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB el)
                                                        hCtge' fenvT F1'
                                                        hle hge heq_arm
                                                        fenvJ happJ hrelJ hvmJ
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
                                                      cases hr : lowerStmtsCFG
                                                          (nextB + 2) (some j) true ρm
                                                          s2 le.next
                                                          le.supply true none
                                                          rest with
                                                      | none => rw [hr] at h; simp at h
                                                      | some lr =>
                                                          rw [hr] at h
                                                          simp only [] at h
                                                          obtain rfl :=
                                                            Option.some.inj h
                                                          dsimp only at hsub ⊢
                                                          have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ :
                                                              Block) ∈ f.blocks :=
                                                            hsub _ if_asm_mem_else
                                                          have hfindE : findBlock f (nextB + 1) =
                                                              some ⟨nextB + 1, le.instrs, le.term⟩ :=
                                                            findBlock_of_nodup_mem hnodf hEmem
                                                          have hmk : mkMergePhis ρ lt.ρ
                                                              le.ρ (le.supply + 1)
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB)
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1))
                                                              (mergeIds ρ lt.ρ le.ρ) =
                                                              some (mphis, s2, ρm) := by
                                                            rw [hm]
                                                            exact hmphi
                                                          have hfindJb : findBlock f
                                                              (nextB + 2) = some ⟨nextB + 2,
                                                              [MIR.Instr.phi le.supply
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB) lt.val,
                                                              MIR.Instr.phi le.supply
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1)) le.val] ++
                                                              mphis ++ lr.instrs,
                                                              lr.term⟩ :=
                                                            findBlock_of_nodup_mem hnodf
                                                              (hsub _ if_asm_mem_join)
                                                          obtain ⟨wArm, huArm, F1', fenvT,
                                                              hle, hge, heq_arm,
                                                              hrel_arm,
                                                              hreg_arm, _⟩ :=
                                                            ((lowerStmtsCFG_arm_total budget (nextB + 1) (nextB + 2) ρ
                                                            lt.supply lt.next lastVal
                                                            false none el le he hael hfE1 hlastE1
                                                            .unit henv fenvC hrelC
                                                            (fun _ => rfl)
                                                            (fun h => absurd h
                                                            (by simp)) fh env_arm
                                                            (HFlow.value u_arm)
                                                            har prog f (some bId)
                                                            ⟨nextB + 2,
                                                            [MIR.Instr.phi le.supply
                                                            ((lt.blocks.getLast?.map
                                                            (fun b => b.id)).getD
                                                            nextB) lt.val,
                                                            MIR.Instr.phi le.supply
                                                            ((le.blocks.getLast?.map
                                                            (fun b => b.id)).getD
                                                            (nextB + 1)) le.val] ++
                                                            mphis ++ lr.instrs,
                                                            lr.term⟩ F'' (fun b hb => hsub _ (if_asm_mem_of_le hb))
                                                            hnodf hfindJb fuelB
                                                            (2 + max
                                                            (armBlockBound fuelB th)
                                                            (armBlockBound fuelB el) +
                                                            armBlockBound fuelB rest -
                                                            armBlockBound fuelB el + C)
                                                            hg_e u_arm).1 rfl)
                                                          obtain ⟨fenvJ, happJ, hrelJ,
                                                              hvmJ, -⟩ :=
                                                            bindArm_join_execE prog hmk
                                                              (Ne.symm hne_pe) rfl
                                                              hrel_arm hreg_arm
                                                              hfreshE hneE
                                                              (Nat.lt_succ_self _) hfrρ
                                                          have hentry : execBlockFromIn prog
                                                              (F'' + 1) f prev
                                                              ⟨bId, ic, .branch vc nextB
                                                              (nextB + 1)⟩ fenv =
                                                              execBlockFromIn prog F'' f
                                                              (some bId)
                                                              ⟨nextB + 1, le.instrs,
                                                              le.term⟩ fenvC :=
                                                            execBlockFromIn_branch_false
                                                              prog F'' f prev bId ic vc
                                                              nextB (nextB + 1) fenv
                                                              fenvC ⟨nextB + 1, le.instrs,
                                                              le.term⟩ hexec_ic hbool
                                                              hfindE
                                                          have hsubR : ∀ b ∈ lt.blocks ++
                                                              [⟨nextB, lt.instrs,
                                                              lt.term⟩] ++ le.blocks ++
                                                              [⟨nextB + 1, le.instrs,
                                                              le.term⟩] ++ [⟨nextB + 2,
                                                              [MIR.Instr.phi le.supply
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB) lt.val,
                                                              MIR.Instr.phi le.supply
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1)) le.val] ++
                                                              mphis ++ lr.instrs,
                                                              lr.term⟩] ++ lr.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _ hb
                                                          have hrep : ((HFlow.value
                                                              (.lit accH)).replace
                                                              (.lit wArm)) =
                                                              HFlow.value
                                                                (.lit wArm) := rfl
                                                          rw [huArm, hrep] at hrun
                                                          rw [if_assembly_exit rfl]
                                                          exact hsuffixW _ _ _ _ hmk hr
                                                            hsubR (some bId)
                                                            ⟨nextB + 1, le.instrs,
                                                            le.term⟩
                                                            ((le.blocks.getLast?.map
                                                            (fun b => b.id)).getD
                                                            (nextB + 1)) hentry env_arm wArm
                                                            henv' out hrun (2 + max
                                                            (armBlockBound fuelB th)
                                                            (armBlockBound fuelB el) +
                                                            armBlockBound fuelB rest -
                                                            armBlockBound fuelB el)
                                                            hCtge' fenvT F1'
                                                            hle hge heq_arm
                                                            fenvJ happJ hrelJ hvmJ
                                          | returned e_arm =>
                                              simp only [] at hrun
                                              have hout_r : out =
                                                  .returned e_arm :=
                                                (congrArg Prod.fst
                                                  hrun).symm
                                              have hregCb_r : fenvC.env vc =
                                                  some (.bool false) := by
                                                have hww : (.bool false) =
                                                    wC :=
                                                  HIR.Expr.lit.inj hrC
                                                rw [hww]
                                                exact hregC
                                              have hbool_r : fenvC.boolOf vc =
                                                  some false :=
                                                boolOf_of_lit fenvC vc false
                                                  hregCb_r
                                              have hg_tr : F'' ≥ blockBound
                                                  fuelB el + (2 + max
                                                  (armBlockBound fuelB th)
                                                  (armBlockBound fuelB el) +
                                                  armBlockBound fuelB rest -
                                                  armBlockBound fuelB el) := by
                                                have hBel : blockBound
                                                    fuelB el = 1 +
                                                    armBlockBound fuelB
                                                      el := rfl
                                                omega
                                              cases hmR : mergeIds ρ lt.ρ le.ρ with
                                              | nil =>
                                                  rw [hmR] at h
                                                  simp only [] at h
                                                  cases hrR : lowerStmtsCFG
                                                      (nextB + 2) (some j) true ρ
                                                      (le.supply + 1) le.next
                                                      le.supply true none
                                                      rest with
                                                  | none =>
                                                      rw [hrR] at h
                                                      simp at h
                                                  | some lrR =>
                                                      rw [hrR] at h
                                                      simp only [] at h
                                                      obtain rfl :=
                                                        Option.some.inj h
                                                      have hfindE : findBlock f (nextB + 1) =
                                                          some ⟨nextB + 1, le.instrs,
                                                          le.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_else)
                                                      have hfindJb : findBlock f (nextB + 2) =
                                                          some ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          ([] : List Instr) ++
                                                          lrR.instrs,
                                                          lrR.term⟩ :=
                                                        findBlock_of_nodup_mem hnodf
                                                          (hsub _ if_asm_mem_join)
                                                      have hentry_r : execBlockFromIn prog
                                                          (F'' + 1) f prev
                                                          ⟨bId, ic, .branch vc nextB
                                                          (nextB + 1)⟩ fenv =
                                                          execBlockFromIn prog F'' f
                                                          (some bId)
                                                          ⟨nextB + 1, le.instrs,
                                                          le.term⟩ fenvC :=
                                                        execBlockFromIn_branch_false
                                                          prog F'' f prev bId ic vc
                                                          nextB (nextB + 1) fenv
                                                          fenvC ⟨nextB + 1, le.instrs,
                                                          le.term⟩ hexec_ic hbool_r
                                                          hfindE
                                                      have hlastE1 : lastVal < lt.supply := Nat.lt_of_lt_of_le hlast1 hst
                                                      have hfE1 : FreshAbove ρ lt.supply := FreshAbove.mono ρ supply lt.supply (Nat.le_trans hs1 hst) hfresh
                                                      intro u
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        simp [hout_r] at hout
                                                      · intro e hout2
                                                        have hret_e : e = e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                              hout2)).symm
                                                        obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                          ((lowerStmtsCFG_arm_total budget (nextB + 1) (nextB + 2) ρ
                                                          lt.supply lt.next lastVal
                                                          false none el le he hael hfE1 hlastE1
                                                          .unit henv fenvC hrelC
                                                          (fun _ => rfl)
                                                          (fun h => absurd h
                                                          (by simp)) fh env_arm
                                                          (HFlow.returned e_arm)
                                                          har prog f (some bId)
                                                          ⟨nextB + 2,
                                                          [MIR.Instr.phi le.supply
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) lt.val,
                                                          MIR.Instr.phi le.supply
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) le.val] ++
                                                          ([] : List Instr) ++
                                                          lrR.instrs,
                                                          lrR.term⟩ F'' (fun b hb => hsub _ (if_asm_mem_of_le hb))
                                                          hnodf hfindJb fuelB
                                                          (2 + max
                                                          (armBlockBound fuelB th)
                                                          (armBlockBound fuelB el) +
                                                          armBlockBound fuelB rest -
                                                          armBlockBound fuelB el)
                                                          hg_tr e_arm).2 e_arm rfl)
                                                        exact ⟨w_e, hret_e.trans hu_e,
                                                          hentry_r.trans heq_e⟩
                                              | cons hdR tlR =>
                                                  rw [hmR] at h
                                                  simp only [] at h
                                                  cases hmphiR : mkMergePhis ρ lt.ρ le.ρ
                                                      (le.supply + 1)
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB)
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1))
                                                      (hdR :: tlR) with
                                                  | none =>
                                                      rw [hmphiR] at h
                                                      simp at h
                                                  | some qR =>
                                                      obtain ⟨mphisR, s2R,
                                                          ρmR⟩ := qR
                                                      rw [hmphiR] at h
                                                      simp only [] at h
                                                      cases hrR : lowerStmtsCFG
                                                          (nextB + 2) (some j) true
                                                          ρmR s2R le.next
                                                          le.supply true none
                                                          rest with
                                                      | none =>
                                                          rw [hrR] at h
                                                          simp at h
                                                      | some lrR =>
                                                          rw [hrR] at h
                                                          simp only [] at h
                                                          obtain rfl :=
                                                            Option.some.inj h
                                                          have hfindE : findBlock f (nextB + 1) =
                                                              some ⟨nextB + 1, le.instrs,
                                                              le.term⟩ :=
                                                            findBlock_of_nodup_mem hnodf
                                                              (hsub _ if_asm_mem_else)
                                                          have hfindJb : findBlock f (nextB + 2) =
                                                              some ⟨nextB + 2,
                                                              [MIR.Instr.phi le.supply
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB) lt.val,
                                                              MIR.Instr.phi le.supply
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1)) le.val] ++
                                                              mphisR ++
                                                              lrR.instrs,
                                                              lrR.term⟩ :=
                                                            findBlock_of_nodup_mem hnodf
                                                              (hsub _ if_asm_mem_join)
                                                          have hentry_r : execBlockFromIn prog
                                                              (F'' + 1) f prev
                                                              ⟨bId, ic, .branch vc nextB
                                                              (nextB + 1)⟩ fenv =
                                                              execBlockFromIn prog F'' f
                                                              (some bId)
                                                              ⟨nextB + 1, le.instrs,
                                                              le.term⟩ fenvC :=
                                                            execBlockFromIn_branch_false
                                                              prog F'' f prev bId ic vc
                                                              nextB (nextB + 1) fenv
                                                              fenvC ⟨nextB + 1, le.instrs,
                                                              le.term⟩ hexec_ic hbool_r
                                                              hfindE
                                                          have hlastE1 : lastVal < lt.supply := Nat.lt_of_lt_of_le hlast1 hst
                                                          have hfE1 : FreshAbove ρ lt.supply := FreshAbove.mono ρ supply lt.supply (Nat.le_trans hs1 hst) hfresh
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            simp [hout_r] at hout
                                                          · intro e hout2
                                                            have hret_e : e = e_arm :=
                                                              (HFlow.returned.inj
                                                                (hout_r.symm.trans
                                                                  hout2)).symm
                                                            obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                              ((lowerStmtsCFG_arm_total budget (nextB + 1) (nextB + 2) ρ
                                                              lt.supply lt.next lastVal
                                                              false none el le he hael hfE1 hlastE1
                                                              .unit henv fenvC hrelC
                                                              (fun _ => rfl)
                                                              (fun h => absurd h
                                                              (by simp)) fh env_arm
                                                              (HFlow.returned e_arm)
                                                              har prog f (some bId)
                                                              ⟨nextB + 2,
                                                              [MIR.Instr.phi le.supply
                                                              ((lt.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              nextB) lt.val,
                                                              MIR.Instr.phi le.supply
                                                              ((le.blocks.getLast?.map
                                                              (fun b => b.id)).getD
                                                              (nextB + 1)) le.val] ++
                                                              mphisR ++
                                                              lrR.instrs,
                                                              lrR.term⟩ F'' (fun b hb => hsub _ (if_asm_mem_of_le hb))
                                                              hnodf hfindJb fuelB
                                                              (2 + max
                                                              (armBlockBound fuelB th)
                                                              (armBlockBound fuelB el) +
                                                              armBlockBound fuelB rest -
                                                              armBlockBound fuelB el)
                                                              hg_tr e_arm).2 e_arm rfl)
                                                            exact ⟨w_e, hret_e.trans hu_e,
                                                              hentry_r.trans heq_e⟩
                                          | broke =>
                                              simp only [] at hrun
                                              have hout_r : out = .broke :=
                                                (congrArg Prod.fst
                                                  hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hout_r] at hout
                                              · intro e hout2
                                                simp [hout_r] at hout2
                                          | continued =>
                                              simp only [] at hrun
                                              have hout_r : out = .continued :=
                                                (congrArg Prod.fst
                                                  hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hout_r] at hout
                                              · intro e hout2
                                                simp [hout_r] at hout2
                                          | stuck =>
                                              simp only [] at hrun
                                              have hout_r : out = .stuck :=
                                                (congrArg Prod.fst
                                                  hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hout_r] at hout
                                              · intro e hout2
                                                simp [hout_r] at hout2
                              | int _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | string _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | pointer _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | float _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | unit =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | undef =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | some _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | none =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | ok _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | err _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | tuple_ _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | array_ _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | loc _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2
                              | closure _ _ =>
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout2
                                    simp [hst] at hout2

end Morph.HIRToMIRCorrect
