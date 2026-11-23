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

/-!
# Stage C binding-arm `if`: `lowerStmtsCFG_bindArm_if_total`

Thirteenth proof leaf out of the `HIRToMIRBranch` monolith: the
top-level binding-arm `if` case — `BindArmStmts` arms under
`arm = false`, `loop = none`. Arm executions arrive as worker contracts
in `arm_total`'s conclusion shape; the join goes through
`bindArm_join_exec`, and the tail invokes `lowerStmtsCFG_total` under
the merged env (moved verbatim, ~1.8k lines).
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Top-level binding-arm `if` case (C2c C3 integration): an `if` with
`BindArmStmts` arms at top level (`arm = false`, `loop = none`). The arm
executions come in as worker contracts (arrival equation plus arm-exit
`RelEnv`, value-register fact, and fuel threading, in `arm_total`'s
conclusion shape — the future arm worker discharges them); the HIR
inversion, entry stepping, and fuel splitting mirror `lowerStmtsCFG_total`.
The join goes through `bindArm_join_exec` uniformly on both merge paths
(the empty path is the merge path with no phis), and the tail invokes
`lowerStmtsCFG_total` itself under the merged env. -/
theorem lowerStmtsCFG_bindArm_if_total (budget : Nat) :
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
      ∀ (_harmT : ∀ (s1 : Nat) (lt : Lowered) (exitT : MIR.BlockId),
        lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3)
          lastVal false none th = some lt →
        ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) = exitT →
        ∀ (joinBlock : Block),
        findBlock f (nextB + 2) = some joinBlock →
        ∀ (fenvC : FullEnv) (F1 C : Nat),
        RelEnv henv ρ fenvC.env →
        F1 ≥ blockBound fuelB th + C →
        ∀ (fh : Nat) (henvArm : HEnv) (outArm : HFlow),
        runHIRStmts fh henv th (.value (.lit .unit)) = (outArm, henvArm) →
        ∀ (_hs1 : supply ≤ s1) (_hsubT : ∀ b ∈ lt.blocks, b ∈ f.blocks)
          (_hregT : fenvC.env lastVal = some .unit),
        (∀ (uArm : HIR.Expr), outArm = .value uArm →
          ∃ wArm fenvT F1', uArm = .lit wArm ∧ F1' ≤ F1 ∧ F1' ≥ C ∧
          execBlockFromIn prog F1 f (some bId) ⟨nextB, lt.instrs,
            lt.term⟩ fenvC =
            execBlockFromIn prog F1' f (some exitT) joinBlock fenvT ∧
          RelEnv henvArm lt.ρ fenvT.env ∧ fenvT.env lt.val = some wArm) ∧
        (∀ (e : HIR.Expr), outArm = .returned e →
          ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F1 f (some bId) ⟨nextB, lt.instrs,
            lt.term⟩ fenvC =
            some w_e)),
      ∀ (_harmE : ∀ (s1t : Nat) (ltE : Lowered) (s1e : Nat) (le : Lowered)
        (exitE : MIR.BlockId),
        lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1t (nextB + 3)
          lastVal false none th = some ltE →
        lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ s1e ltE.next
          lastVal false none el = some le →
        ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1)) = exitE →
        ∀ (joinBlock : Block),
        findBlock f (nextB + 2) = some joinBlock →
        ∀ (fenvC : FullEnv) (F1 C : Nat),
        RelEnv henv ρ fenvC.env →
        F1 ≥ blockBound fuelB el + C →
        ∀ (fh : Nat) (henvArm : HEnv) (outArm : HFlow),
        runHIRStmts fh henv el (.value (.lit .unit)) = (outArm, henvArm) →
        ∀ (_hsubE : ∀ b ∈ le.blocks, b ∈ f.blocks)
          (_hfE : FreshAbove ρ s1e) (_hlE : lastVal < s1e)
          (_hregE : fenvC.env lastVal = some .unit),
        (∀ (uArm : HIR.Expr), outArm = .value uArm →
          ∃ wArm fenvT F1', uArm = .lit wArm ∧ F1' ≤ F1 ∧ F1' ≥ C ∧
          execBlockFromIn prog F1 f (some bId) ⟨nextB + 1, le.instrs,
            le.term⟩ fenvC =
            execBlockFromIn prog F1' f (some exitE) joinBlock fenvT ∧
          RelEnv henvArm le.ρ fenvT.env ∧ fenvT.env le.val = some wArm) ∧
        (∀ (e : HIR.Expr), outArm = .returned e →
          ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F1 f (some bId) ⟨nextB + 1, le.instrs,
            le.term⟩ fenvC =
            some w_e)),
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
    prog f prev F hsub hnodf fuelB hg hfb harmT harmE u
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
              have hf1 : FreshAbove ρ s1 :=
                FreshAbove.mono ρ supply s1 hs1 hfresh
              have hlast1 : lastVal < s1 := Nat.lt_of_lt_of_le hlast hs1
              have hst : s1 ≤ lt.supply :=
                (lowerStmtsCFG_bindArm_inv budget _ _ _ _ _ _ _ _ _ ht
                  hTh).2.1
              have hse : lt.supply ≤ le.supply :=
                (lowerStmtsCFG_bindArm_inv budget _ _ _ _ _ _ _ _ _ he
                  hEl).2.1
              have hfrρ : FreshAbove ρ
                  le.supply :=
                FreshAbove.mono ρ supply
                  le.supply (Nat.le_trans hs1
                  (Nat.le_trans hst hse))
                  hfresh
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
                  (armBlockBound fuelB el) + armBlockBound fuelB rest) := by
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
                          have hentryC : fenvC.env lastVal = some .unit := by
                            have hp : fenvC.env lastVal = fenv.env lastVal :=
                              lower_preserv_regs ρ supply c vc ic s1 heC fenv
                                fenvC hexecC lastVal hlast
                            rw [hp, hacc, haccU]
                          have hsuffix : ∀ (ρm : List
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
                                (nextB + 2) none false ρm
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
                              (C : Nat) →
                              (hCtge : C ≥ blockBound fuelB
                                rest) →
                              ∀ (fenvT : FullEnv)
                              (F1' : Nat),
                              F1' ≤ F'' →
                              F1' ≥ C →
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
                              (out = .value u →
                              ∃ w_u, u = .lit w_u ∧
                              execBlockFromIn prog (F'' + 1) f
                              prev ⟨bId, ic, .branch vc
                              nextB (nextB + 1)⟩ fenv =
                              some w_u) ∧
                              (∀ (e : HIR.Expr),
                              out = .returned e →
                              ∃ w_e, e = .lit w_e ∧
                              execBlockFromIn prog (F'' + 1) f
                              prev ⟨bId, ic, .branch vc
                              nextB (nextB + 1)⟩ fenv =
                              some w_e) := by
                            intro ρm s2 mphis lr hmk hr
                              hsubR armPrev armEntry armExit
                              hentry henvArm wArm henv'
                              out hrunTail C hCtge
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
                                    blockBound fuelB rest :=
                                  Nat.le_trans hCtge hge
                                have hfb' : fh ≤ fuelB := by
                                  omega
                                have htail :=
                                  lowerStmtsCFG_total budget
                                  (nextB + 2) ρm s2 le.next
                                  le.supply true rest lr hr hrs
                                  hf_r hlast_r hltB' wArm
                                  henvArm fenvJ hrelJ hvmJ fh
                                  henv' out hrunTail prog f
                                  (some armExit) (F1 + 1) hsub_r
                                  hnodf fuelB hg_r hfb'
                                refine ⟨?_, ?_⟩
                                · intro hout
                                  obtain ⟨w_u, hu,
                                      heq_rest⟩ :=
                                    (htail u).1 hout
                                  exact ⟨w_u, hu,
                                    hentry.trans
                                    (heq_arm.trans
                                    (hJeq.trans
                                    heq_rest))⟩
                                · intro e_ret hout2
                                  obtain ⟨w_e, hu_e,
                                      heq_rest⟩ :=
                                    (htail u).2 e_ret hout2
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
                                              armBlockBound fuelB th) := by
                                            have hBth : blockBound
                                                fuelB th = 1 +
                                                armBlockBound fuelB
                                                  th := rfl
                                            omega
                                          have hfrT :=
                                            lowerStmtsCFG_bindArm_fresh
                                              budget _ _ _ _ _ _ _ _ _ ht
                                              hTh hf1 hlast1
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
                                                  (nextB + 2) none false ρ
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
                                                  have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                                      ∈ f.blocks :=
                                                    hsub _ if_asm_mem_then
                                                  have hfindT : findBlock f nextB =
                                                      some ⟨nextB, lt.instrs, lt.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf hTmem
                                                  have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                                                      ∈ f.blocks :=
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
                                                  obtain ⟨wArm, fenvT, F1',
                                                      huArm, hle, hge, heq_arm,
                                                      hrel_arm,
                                                      hreg_arm⟩ :=
                                                    ((harmT s1 lt
                                                    ((lt.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    nextB) ht rfl ⟨nextB + 2,
                                                    [MIR.Instr.phi le.supply
                                                    ((lt.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    nextB) lt.val,
                                                    MIR.Instr.phi le.supply
                                                    ((le.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    (nextB + 1)) le.val] ++
                                                    lr.instrs,
                                                    lr.term⟩ hfindJb fenvC F''
                                                    (2 + max
                                                    (armBlockBound fuelB th)
                                                    (armBlockBound fuelB el) +
                                                    armBlockBound fuelB rest -
                                                    armBlockBound fuelB th)
                                                    hrelC hg_t fh env_arm
                                                    (HFlow.value u_arm)
                                                    har hs1 (fun b hb => hsub _ (if_asm_mem_of_lt hb)) hentryC).1 u_arm rfl)
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
                                                  exact hsuffix _ _ _ _ hmk hr
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
                                                      (nextB + 2) none false ρm
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
                                                      have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                                                          ∈ f.blocks :=
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
                                                      obtain ⟨wArm, fenvT, F1',
                                                          huArm, hle, hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arm⟩ :=
                                                        ((harmT s1 lt
                                                        ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) ht rfl ⟨nextB + 2,
                                                        [MIR.Instr.phi le.supply
                                                        ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) lt.val,
                                                        MIR.Instr.phi le.supply
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) le.val] ++
                                                        mphis ++ lr.instrs,
                                                        lr.term⟩ hfindJb fenvC F''
                                                        (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB th)
                                                        hrelC hg_t fh env_arm
                                                        (HFlow.value u_arm)
                                                        har hs1 (fun b hb => hsub _ (if_asm_mem_of_lt hb)) hentryC).1 u_arm rfl)
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
                                                      exact hsuffix _ _ _ _ hmk hr
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
                                                  (nextB + 2) none false ρ
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
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    simp [hout_r] at hout
                                                  · intro e hout2
                                                    have hret_e : e = e_arm :=
                                                      (HFlow.returned.inj
                                                        (hout_r.symm.trans
                                                          hout2)).symm
                                                    obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                      ((harmT s1 lt
                                                      ((lt.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      nextB) ht rfl ⟨nextB + 2,
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
                                                      lrR.term⟩ hfindJb fenvC F''
                                                      (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB th)
                                                      hrelC hg_tr fh env_arm
                                                      (HFlow.returned e_arm)
                                                      har hs1 (fun b hb => hsub _ (if_asm_mem_of_lt hb)) hentryC).2 e_arm rfl)
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
                                                      (nextB + 2) none false
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
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        simp [hout_r] at hout
                                                      · intro e hout2
                                                        have hret_e : e = e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                              hout2)).symm
                                                        obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                          ((harmT s1 lt
                                                          ((lt.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          nextB) ht rfl ⟨nextB + 2,
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
                                                          lrR.term⟩ hfindJb fenvC F''
                                                          (2 + max
                                                          (armBlockBound fuelB th)
                                                          (armBlockBound fuelB el) +
                                                          armBlockBound fuelB rest -
                                                          armBlockBound fuelB th)
                                                          hrelC hg_tr fh env_arm
                                                          (HFlow.returned e_arm)
                                                          har hs1 (fun b hb => hsub _ (if_asm_mem_of_lt hb)) hentryC).2 e_arm rfl)
                                                        exact ⟨w_e, hret_e.trans hu_e,
                                                          hentry_r.trans heq_e⟩
                                      | broke =>
                                          simp only [] at hrun
                                          have hout_r : out = .broke :=
                                            (congrArg Prod.fst
                                              hrun).symm
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
                                              armBlockBound fuelB el) := by
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
                                          have hfrE :=
                                            lowerStmtsCFG_bindArm_fresh
                                              budget _ _ _ _ _ _ _ _ _ he
                                              hEl hfE1 hlastE1
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
                                                  (nextB + 2) none false ρ
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
                                                  have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                                      ∈ f.blocks :=
                                                    hsub _ if_asm_mem_then
                                                  have hfindT : findBlock f nextB =
                                                      some ⟨nextB, lt.instrs, lt.term⟩ :=
                                                    findBlock_of_nodup_mem hnodf hTmem
                                                  have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                                                      ∈ f.blocks :=
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
                                                  obtain ⟨wArm, fenvT, F1',
                                                      huArm, hle, hge, heq_arm,
                                                      hrel_arm,
                                                      hreg_arm⟩ :=
                                                    ((harmE s1 lt lt.supply le
                                                    ((le.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    (nextB + 1)) ht he rfl ⟨nextB + 2,
                                                    [MIR.Instr.phi le.supply
                                                    ((lt.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    nextB) lt.val,
                                                    MIR.Instr.phi le.supply
                                                    ((le.blocks.getLast?.map
                                                    (fun b => b.id)).getD
                                                    (nextB + 1)) le.val] ++
                                                    lr.instrs,
                                                    lr.term⟩ hfindJb fenvC F''
                                                    (2 + max
                                                    (armBlockBound fuelB th)
                                                    (armBlockBound fuelB el) +
                                                    armBlockBound fuelB rest -
                                                    armBlockBound fuelB el)
                                                    hrelC hg_e fh env_arm
                                                    (HFlow.value u_arm)
                                                    har (fun b hb => hsub _ (if_asm_mem_of_le hb)) hfE1 hlastE1 hentryC).1 u_arm rfl)
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
                                                  exact hsuffix _ _ _ _ hmk hr
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
                                                      (nextB + 2) none false ρm
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
                                                      have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                                                          ∈ f.blocks :=
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
                                                      obtain ⟨wArm, fenvT, F1',
                                                          huArm, hle, hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arm⟩ :=
                                                        ((harmE s1 lt lt.supply le
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) ht he rfl ⟨nextB + 2,
                                                        [MIR.Instr.phi le.supply
                                                        ((lt.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        nextB) lt.val,
                                                        MIR.Instr.phi le.supply
                                                        ((le.blocks.getLast?.map
                                                        (fun b => b.id)).getD
                                                        (nextB + 1)) le.val] ++
                                                        mphis ++ lr.instrs,
                                                        lr.term⟩ hfindJb fenvC F''
                                                        (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB el)
                                                        hrelC hg_e fh env_arm
                                                        (HFlow.value u_arm)
                                                        har (fun b hb => hsub _ (if_asm_mem_of_le hb)) hfE1 hlastE1 hentryC).1 u_arm rfl)
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
                                                      exact hsuffix _ _ _ _ hmk hr
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
                                          have hg_er : F'' ≥ blockBound
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
                                                  (nextB + 2) none false ρ
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
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    simp [hout_r] at hout
                                                  · intro e hout2
                                                    have hret_e : e = e_arm :=
                                                      (HFlow.returned.inj
                                                        (hout_r.symm.trans
                                                          hout2)).symm
                                                    obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                      ((harmE s1 lt lt.supply le
                                                      ((le.blocks.getLast?.map
                                                      (fun b => b.id)).getD
                                                      (nextB + 1)) ht he rfl ⟨nextB + 2,
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
                                                      lrR.term⟩ hfindJb fenvC F''
                                                      (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el)
                                                      hrelC hg_er fh env_arm
                                                      (HFlow.returned e_arm)
                                                      har (fun b hb => hsub _ (if_asm_mem_of_le hb)) (FreshAbove.mono ρ supply lt.supply (Nat.le_trans hs1 hst) hfresh) (Nat.lt_of_lt_of_le hlast1 hst) hentryC).2 e_arm rfl)
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
                                                      (nextB + 2) none false
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
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        simp [hout_r] at hout
                                                      · intro e hout2
                                                        have hret_e : e = e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                              hout2)).symm
                                                        obtain ⟨w_e, hu_e, heq_e⟩ :=
                                                          ((harmE s1 lt lt.supply le
                                                          ((le.blocks.getLast?.map
                                                          (fun b => b.id)).getD
                                                          (nextB + 1)) ht he rfl ⟨nextB + 2,
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
                                                          lrR.term⟩ hfindJb fenvC F''
                                                          (2 + max
                                                          (armBlockBound fuelB th)
                                                          (armBlockBound fuelB el) +
                                                          armBlockBound fuelB rest -
                                                          armBlockBound fuelB el)
                                                          hrelC hg_er fh env_arm
                                                          (HFlow.returned e_arm)
                                                          har (fun b hb => hsub _ (if_asm_mem_of_le hb)) (FreshAbove.mono ρ supply lt.supply (Nat.le_trans hs1 hst) hfresh) (Nat.lt_of_lt_of_le hlast1 hst) hentryC).2 e_arm rfl)
                                                        exact ⟨w_e, hret_e.trans hu_e,
                                                          hentry_r.trans heq_e⟩
                                      | broke =>
                                          simp only [] at hrun
                                          have hout_r : out = .broke :=
                                            (congrArg Prod.fst
                                              hrun).symm
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
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hout_r] at hout
                                          · intro e hout2
                                            simp [hout_r] at hout2
                          | int _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | string _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | pointer _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | float _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | unit =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | undef =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | some _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | none =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | ok _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | err _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | tuple_ _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | array_ _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | loc _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2
                          | closure _ _ =>
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout2
                                simp [hst] at hout2

end Morph.HIRToMIRCorrect
