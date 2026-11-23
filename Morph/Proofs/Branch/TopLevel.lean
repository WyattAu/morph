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
import Morph.Proofs.Branch.BindArm
import Morph.Proofs.Branch.LoopLookup
import Morph.Proofs.Branch.Spine
import Morph.Proofs.Branch.WhileLoop
import Morph.Proofs.Branch.Total
import Morph.Proofs.Branch.IfTotal

/-!
# Stage C capstone: closed wrappers and the program corollaries

Fourteenth proof leaf out of the `HIRToMIRBranch` monolith: the closed
top-level wrapper (`bindArm_if_closed`), the block-bound wrappers
(`total_bound`, `bindArm_if_closed_bound`), the top-level invariant
(`bindArm_if_top_inv`), and the two program corollaries
(`lowerProgramCFG_correct`, `lowerProgramCFG_bindArm_if_correct`)
(moved verbatim). The concrete programs below cite this leaf.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Closed top-level binding-arm `if` (C2c integration): `bindArm_if_total`
with both worker contracts discharged by `bindArm_total`. The then-arm rides
the cond's supply step; the else-arm's freshness is part of its contract. -/
theorem lowerStmtsCFG_bindArm_if_closed (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (c : HIR.Expr) (th el rest : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal none
        (.ifStmt c th el :: rest) = some L →
      IsStraight c → SLWeight c < budget →
      BindArmStmts budget th → BindArmStmts budget el →
      BranchStmts budget rest →
      FreshAbove ρ supply → lastVal < supply → bId < nextB →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      accH = .unit →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv (.ifStmt c th el :: rest) (.value (.lit accH)) =
        (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId)
        (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB : Nat), F ≥ blockBound fuelB (.ifStmt c th el :: rest) →
        fuelH ≤ fuelB →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_e) := by
  intro bId ρ supply nextB lastVal hasVal c th el rest L h hstr hlt hTh hEl
    hrs hfresh hlast hltB accH henv fenv hrel hacc haccU fuelH henv' out hrun
    prog f prev F hsub hnodf fuelB hg hfb u
  refine lowerStmtsCFG_bindArm_if_total budget bId ρ supply nextB lastVal
    hasVal c th el rest L h hstr hlt hTh hEl hrs hfresh hlast hltB accH henv
    fenv hrel hacc haccU fuelH henv' out hrun prog f prev F hsub hnodf fuelB
    hg hfb ?_ ?_ u
  · intro s1 lt exitT ht' hexit joinBlock hfindJb fenvC F1 C hrelC hg1 fh
      henvArm outArm hrunT hs1T hsubT hregT
    have hf1 : FreshAbove ρ s1 :=
      FreshAbove.mono ρ supply s1 hs1T hfresh
    have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1T
    have hT := lowerStmtsCFG_bindArm_total budget nextB (nextB + 2) ρ s1
      (nextB + 3) lastVal false th lt ht' hTh hf1 hlast1 .unit henv fenvC
      hrelC (fun _ => rfl) hregT fh henvArm outArm hrunT prog f (some bId)
      joinBlock F1 hsubT hnodf hfindJb fuelB C hg1
    refine ⟨fun uArm hout => ?_, fun e hout2 => (hT e).2 e hout2⟩
    obtain ⟨w, hu, F', fenvT, hle, hge, heq, hrelA, hval⟩ := (hT uArm).1 hout
    rw [hexit] at heq
    exact ⟨w, fenvT, F', hu, hle, hge, heq, hrelA, hval⟩
  · intro s1t ltE s1e le exitE he'T he'E hexitE joinBlock hfindJb fenvC F1 C hrelC
      hg1 fh henvArm outArm hrunE hsubE hfE hlE hregE
    have hE := lowerStmtsCFG_bindArm_total budget (nextB + 1) (nextB + 2) ρ
      s1e ltE.next lastVal false el le he'E hEl hfE hlE .unit henv fenvC hrelC
      (fun _ => rfl) hregE fh henvArm outArm hrunE prog f (some bId) joinBlock
      F1 hsubE hnodf hfindJb fuelB C hg1
    refine ⟨fun uArm hout => ?_, fun e hout2 => (hE e).2 e hout2⟩
    obtain ⟨w, hu, F', fenvT, hle, hge, heq, hrelA, hval⟩ := (hE uArm).1 hout
    rw [hexitE] at heq
    exact ⟨w, fenvT, F', hu, hle, hge, heq, hrelA, hval⟩

/-! ## §4.4: the fuel bound, and closed programs

Loop 180. The worker leaves `F` and `fuelB` free; the bridge only needs one
instantiation: `F := blockBound fuelH ss` with `fuelB := fuelH`, closed by
`Nat.le_refl`. C7 cites this corollary, never the worker. -/
theorem lowerStmtsCFG_total_bound (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal none ss = some L →
      BranchStmts budget ss →
      FreshAbove ρ supply → lastVal < supply → bId < nextB →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv ss (.value (.lit accH)) = (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog (blockBound fuelH ss) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog (blockBound fuelH ss) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_e) := by
  intro bId ρ supply nextB lastVal hasVal ss L h hss hfresh hlast hltB
    accH henv fenv hrel hacc fuelH henv' out hrun prog f prev hsub hnodf u
  exact lowerStmtsCFG_total budget bId ρ supply nextB lastVal hasVal ss L
    h hss hfresh hlast hltB accH henv fenv hrel hacc fuelH henv' out hrun prog f
    prev (blockBound fuelH ss) hsub hnodf fuelH
    (Nat.le_refl (blockBound fuelH ss)) (Nat.le_refl fuelH) u

/-- Binding `if` fuel closure (§4.4, C2c): `bindArm_if_closed` at
`F := blockBound fuelH` with `fuelB := fuelH`. C7 cites this, never the worker. -/
theorem lowerStmtsCFG_bindArm_if_closed_bound (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (c : HIR.Expr) (th el rest : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal none
        (.ifStmt c th el :: rest) = some L →
      IsStraight c → SLWeight c < budget →
      BindArmStmts budget th → BindArmStmts budget el →
      BranchStmts budget rest →
      FreshAbove ρ supply → lastVal < supply → bId < nextB →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      accH = .unit →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv (.ifStmt c th el :: rest) (.value (.lit accH)) =
        (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog (blockBound fuelH (.ifStmt c th el :: rest)) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog (blockBound fuelH (.ifStmt c th el :: rest)) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_e) := by
  intro bId ρ supply nextB lastVal hasVal c th el rest L h hstr hlt hTh hEl
    hrs hfresh hlast hltB accH henv fenv hrel hacc haccU fuelH henv' out hrun
    prog f prev hsub hnodf u
  exact lowerStmtsCFG_bindArm_if_closed budget bId ρ supply nextB lastVal
    hasVal c th el rest L h hstr hlt hTh hEl hrs hfresh hlast hltB accH henv
    fenv hrel hacc haccU fuelH henv' out hrun prog f prev
    (blockBound fuelH (.ifStmt c th el :: rest)) hsub hnodf fuelH
    (Nat.le_refl (blockBound fuelH (.ifStmt c th el :: rest)))
    (Nat.le_refl fuelH) u

/-- Static invariant for a top-level binding-arm `if` (C2c): the `bindArm_inv`
conclusion for the `.ifStmt c th el :: rest` shape at top level
(`cont = none`, `arm = false`). Arms ride `bindArm_inv`; the tail rides
`branch_inv` (empty merge) or `branch_inv` under the merged env (merge path,
supply via `mkMergePhis_le`). Block assembly is identical on both paths, so
bounds/nodup mirror `bindArm_inv`'s `if` case. The program-level binding-arm
corollary cites this for `hnodf`/`hbnd`. -/
theorem lowerStmtsCFG_bindArm_if_top_inv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (c : HIR.Expr) (th el rest : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal none
        (.ifStmt c th el :: rest) = some L →
      BindArmStmts budget th → BindArmStmts budget el →
      BranchStmts budget rest →
      nextB ≤ L.next ∧ supply ≤ L.supply ∧
        (∀ b ∈ L.blocks, nextB ≤ b.id ∧ b.id < L.next) ∧
        (L.blocks.map Block.id).Nodup := by
  intro bId ρ supply nextB lastVal hasVal c th el rest L h hTh hEl hrs
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
                lowerStmtsCFG_bindArm_inv budget _ _ _ _ _ _ _ _ _ ht hTh
              obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                lowerStmtsCFG_bindArm_inv budget _ _ _ _ _ _ _ _ _ he hEl
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
              cases hm : mergeIds ρ lt.ρ le.ρ with
              | nil =>
                  rw [hm] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) none false ρ
                      (le.supply + 1) le.next le.supply true none rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      dsimp only at ⊢
                      obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                        lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _ _ _
                          _ hr hrs
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
                      cases hr : lowerStmtsCFG (nextB + 2) none false ρm
                          s2 le.next le.supply true none rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          dsimp only at ⊢
                          have hle2 : le.supply + 1 ≤ s2 :=
                            mkMergePhis_le hmk
                          obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                            lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _ _ _
                              _ hr hrs
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

/-- Top corollary (C3 exit): a closed lowered program runs the oracle's value.
C7 cites this: HIR success (`runHIRProgram = value`) is MIR success
(`execFuncFrom = some`), with executor fuel `blockBound 1024`. The entry
block's `const 0 unit` prologue peels first (supply starts at 1, so register
0 is free); the worker then runs from `L.instrs`. Succeed-direction only:
C7 must not contrapose this for failure. -/
theorem lowerProgramCFG_correct (budget : Nat) (prog : HIR.Program)
    (f : Func) (progM : Program) (hlower : lowerProgramCFG prog = some f)
    (hss : BranchStmts budget prog.stmts) (w : Value)
    (hrun : runHIRProgram prog = .value (.lit w)) :
    execFuncFrom (blockBound 1024 prog.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some w := by
  unfold lowerProgramCFG at hlower
  cases hc : lowerStmtsCFG 0 none false [] 1 1 0 false none prog.stmts with
  | none =>
      simp [hc] at hlower
  | some L =>
      simp [hc] at hlower
      obtain rfl := hlower
      obtain ⟨hmn, hms, hbnd, hnodr⟩ :=
        lowerStmtsCFG_branch_inv budget 0 none [] 1 1 0 false none prog.stmts
          L hc hss
      have hsub : ∀ b ∈ L.blocks, b ∈ (⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks := by
        intro b hb
        exact List.Mem.tail _ (List.mem_reverse.mpr hb)
      have hrev : ∀ (l : List Block), (l.map Block.id).Nodup →
          (l.reverse.map Block.id).Nodup := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons b rest ih =>
            intro h
            rw [List.map_cons, List.nodup_cons] at h
            obtain ⟨hnotin, hnod⟩ := h
            have ihr := ih hnod
            rw [List.reverse_cons, List.map_append, List.map_singleton,
              List.nodup_append]
            refine ⟨ihr, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
            intro a ha x hx
            simp only [List.mem_singleton] at hx
            subst hx
            intro hcon
            have ha' : a ∈ rest.map Block.id := by
              obtain ⟨c, hc_mem, hc_id⟩ := List.mem_map.mp ha
              exact List.mem_map.mpr
                ⟨c, List.mem_reverse.mp hc_mem, hc_id⟩
            exact hnotin (hcon ▸ ha')
      have hmap0 : (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id) =
          0 :: L.blocks.reverse.map Block.id := rfl
      have hnodf : (((⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks).map
          Block.id).Nodup := by
        show (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id).Nodup
        rw [hmap0]
        refine List.nodup_cons.mpr ⟨?_, hrev _ hnodr⟩
        intro hm
        obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hm
        obtain ⟨hlo, -⟩ := hbnd b (List.mem_reverse.mp hb)
        rw [hbid] at hlo
        exact absurd hlo (by decide)
      have hmem_entry : (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ∈
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse :=
        List.Mem.head _
      have hfind_entry : findBlock
          ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ 0 =
          some (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) :=
        findBlock_of_nodup_mem hnodf hmem_entry
      cases hp : runHIRStmts 1024 [] prog.stmts (.value (.lit .unit)) with
      | mk out henv' =>
          have hout : out = .value (.lit w) := by
            have h1 : (runHIRStmts 1024 [] prog.stmts
                (.value (.lit .unit))).1 = .value (.lit w) := hrun
            rw [hp] at h1
            simp only [] at h1
            exact h1
          have hfresh : FreshAbove ([] : List (HIR.Id × ValId)) 1 := by
            intro j u hmem
            exact absurd hmem (by simp)
          have hrel : RelEnv ([] : HEnv) []
              (Env.update (fun _ => none) 0 .unit) := by
            intro id u hlook
            exact absurd hlook (by simp [rhoLookup])
          have hacc : Env.update (fun _ => none : Morph.MIR.Env) 0 .unit 0 =
              some .unit := by
            simp [Env.update]
          have hexec0 : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              [.const 0 .unit] =
              some (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                Store.empty⟩ : FullEnv) := rfl
          have happ : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              ([.const 0 .unit] ++ L.instrs) =
              execInstrsFullFromIn progM none
                (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                  Store.empty⟩ : FullEnv) L.instrs := by
            rw [execInstrsFullFromIn_append, hexec0]
          cases hF : blockBound 1024 prog.stmts with
          | zero =>
              have h1 : blockBound 1024 prog.stmts ≥ 1 := by
                rw [blockBound]; omega
              omega
          | succ F' =>
              have hpeel : execBlockFromIn progM (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none
                  (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    ⟨0, L.instrs, L.term⟩
                    (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                      Store.empty⟩ : FullEnv) :=
                execBlockFromIn_instrs_prefix progM F'
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none 0
                  [.const 0 .unit] L.instrs L.term _ _ happ
              have hrunF : execFuncFrom (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                    ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ := by
                rw [execFuncFrom_eq _ _ _ _ hfind_entry,
                  ← execBlockFromIn_eq]
              obtain ⟨w_u, hu, heq⟩ :=
                (lowerStmtsCFG_total_bound budget 0 [] 1 1 0 false prog.stmts
                  L hc hss hfresh (by decide) (by decide) .unit []
                  (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                    Store.empty⟩ : FullEnv) hrel hacc 1024 henv'
                  out hp progM _ none hsub hnodf (.lit w)).1 hout
              have hw : w = w_u := HIR.Expr.lit.inj hu
              subst hw
              rw [hF] at heq
              exact hrunF.trans (hpeel.trans heq)

/-! ## The lowered CFG runs -/
/-- Top program corollary for a binding-arm `if` head (C2c): a closed lowered
program whose statements are `.ifStmt c th el :: rest` with binding arms runs
the oracle's value. Mirrors `lowerProgramCFG_correct`, citing
`bindArm_if_top_inv` for `hbnd`/`hnodf` and `bindArm_if_closed_bound` for the
run. Succeed-direction only. -/
theorem lowerProgramCFG_bindArm_if_correct (budget : Nat) (prog : HIR.Program)
    (c : HIR.Expr) (th el rest : List HIR.Stmt)
    (hshape : prog.stmts = .ifStmt c th el :: rest)
    (f : Func) (progM : Program) (hlower : lowerProgramCFG prog = some f)
    (hstr : IsStraight c) (hlt : SLWeight c < budget)
    (hTh : BindArmStmts budget th) (hEl : BindArmStmts budget el)
    (hrs : BranchStmts budget rest) (w : Value)
    (hrun : runHIRProgram prog = .value (.lit w)) :
    execFuncFrom (blockBound 1024 prog.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some w := by
  unfold lowerProgramCFG at hlower
  rw [hshape] at hlower
  cases hc : lowerStmtsCFG 0 none false [] 1 1 0 false none
      (.ifStmt c th el :: rest) with
  | none =>
      simp [hc] at hlower
  | some L =>
      simp [hc] at hlower
      obtain rfl := hlower
      obtain ⟨hmn, hms, hbnd, hnodr⟩ :=
        lowerStmtsCFG_bindArm_if_top_inv budget 0 [] 1 1 0 false c th el
          rest L hc hTh hEl hrs
      have hsub : ∀ b ∈ L.blocks, b ∈ (⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks := by
        intro b hb
        exact List.Mem.tail _ (List.mem_reverse.mpr hb)
      have hrev : ∀ (l : List Block), (l.map Block.id).Nodup →
          (l.reverse.map Block.id).Nodup := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons b rest ih =>
            intro h
            rw [List.map_cons, List.nodup_cons] at h
            obtain ⟨hnotin, hnod⟩ := h
            have ihr := ih hnod
            rw [List.reverse_cons, List.map_append, List.map_singleton,
              List.nodup_append]
            refine ⟨ihr, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
            intro a ha x hx
            simp only [List.mem_singleton] at hx
            subst hx
            intro hcon
            have ha' : a ∈ rest.map Block.id := by
              obtain ⟨c, hc_mem, hc_id⟩ := List.mem_map.mp ha
              exact List.mem_map.mpr
                ⟨c, List.mem_reverse.mp hc_mem, hc_id⟩
            exact hnotin (hcon ▸ ha')
      have hmap0 : (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id) =
          0 :: L.blocks.reverse.map Block.id := rfl
      have hnodf : (((⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks).map
          Block.id).Nodup := by
        show (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id).Nodup
        rw [hmap0]
        refine List.nodup_cons.mpr ⟨?_, hrev _ hnodr⟩
        intro hm
        obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hm
        obtain ⟨hlo, -⟩ := hbnd b (List.mem_reverse.mp hb)
        rw [hbid] at hlo
        exact absurd hlo (by decide)
      have hmem_entry : (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ∈
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse :=
        List.Mem.head _
      have hfind_entry : findBlock
          ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ 0 =
          some (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) :=
        findBlock_of_nodup_mem hnodf hmem_entry
      cases hp : runHIRStmts 1024 [] prog.stmts (.value (.lit .unit)) with
      | mk out henv' =>
          rw [hshape] at hp
          have hout : out = .value (.lit w) := by
            have h1 : (runHIRStmts 1024 [] prog.stmts
                (.value (.lit .unit))).1 = .value (.lit w) := hrun
            rw [hshape] at h1
            rw [hp] at h1
            simp only [] at h1
            exact h1
          have hfresh : FreshAbove ([] : List (HIR.Id × ValId)) 1 := by
            intro j u hmem
            exact absurd hmem (by simp)
          have hrel : RelEnv ([] : HEnv) []
              (Env.update (fun _ => none) 0 .unit) := by
            intro id u hlook
            exact absurd hlook (by simp [rhoLookup])
          have hacc : Env.update (fun _ => none : Morph.MIR.Env) 0 .unit 0 =
              some .unit := by
            simp [Env.update]
          have hexec0 : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              [.const 0 .unit] =
              some (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                Store.empty⟩ : FullEnv) := rfl
          have happ : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              ([.const 0 .unit] ++ L.instrs) =
              execInstrsFullFromIn progM none
                (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                  Store.empty⟩ : FullEnv) L.instrs := by
            rw [execInstrsFullFromIn_append, hexec0]
          cases hF : blockBound 1024 (.ifStmt c th el :: rest) with
          | zero =>
              have h1 : blockBound 1024 (.ifStmt c th el :: rest) ≥ 1 := by
                rw [blockBound]; omega
              omega
          | succ F' =>
              have hpeel : execBlockFromIn progM (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none
                  (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    ⟨0, L.instrs, L.term⟩
                    (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                      Store.empty⟩ : FullEnv) :=
                execBlockFromIn_instrs_prefix progM F'
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none 0
                  [.const 0 .unit] L.instrs L.term _ _ happ
              have hrunF : execFuncFrom (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                    ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ := by
                rw [execFuncFrom_eq _ _ _ _ hfind_entry,
                  ← execBlockFromIn_eq]
              obtain ⟨w_u, hu, heq⟩ :=
                (lowerStmtsCFG_bindArm_if_closed_bound budget 0 [] 1 1 0
                  false c th el rest L hc hstr hlt hTh hEl hrs hfresh
                  (by decide) (by decide) .unit []
                  (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                    Store.empty⟩ : FullEnv) hrel hacc rfl 1024 henv'
                  out hp progM _ none hsub hnodf (.lit w)).1 hout
              have hw : w = w_u := HIR.Expr.lit.inj hu
              subst hw
              rw [hF] at heq
              rw [hshape, hF]
              exact hrunF.trans (hpeel.trans heq)

end Morph.HIRToMIRCorrect
