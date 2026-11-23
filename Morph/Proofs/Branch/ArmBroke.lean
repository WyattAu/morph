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

/-!
# Stage C arm execution on `break`: `lowerStmtsCFG_arm_broke`

Third proof leaf out of the `HIRToMIRBranch` monolith: the arm-`break`
worker (moved verbatim). It cites the fallthrough worker from the
ArmTotal leaf for taken value arms; the `continued`/loop-body workers
left in the monolith cite this leaf for breaking arms.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Arm execution on `break`: when the HIR arm breaks, the MIR entry block
runs to the loop-exit block (looked up by the caller, who owns it) with a
related environment. Straight-line steps peel via `lower_total.1` exactly
as in `arm_total`; an `if` chains the taken arm through the join (citing
`arm_total` for a value arm) and the rest through the induction hypothesis;
a breaking arm chains directly to the exit. -/
theorem lowerStmtsCFG_arm_broke (budget : Nat) :
    ∀ (bId j : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (loop : Option LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId (some j) true ρ supply nextB lastVal hasVal loop ss =
        some L →
      ArmStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      (hasVal = false → accH = .unit) →
      (hasVal = true → fenv.env lastVal = some accH) →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv ss (.value (.lit accH)) = (out, henv') →
      out = .broke →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId) (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB C : Nat), F ≥ blockBound fuelB ss + C →
      ∀ (info : LoopInfo), loop = some info →
      CarriedExcl ρ info.carried →
      (∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ info.carried → (id₂, r₂) ∈ info.carried →
        r₁ = r₂ → id₁ = id₂) →
      ∀ (blk : Block), findBlock f info.exit = some blk →
      ∃ F' fenv_arr blkPrev, F' ≤ F ∧ F' ≥ C ∧
        execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
          execBlockFromIn prog F' f (some blkPrev) blk fenv_arr ∧
        RelEnv henv' L.ρ fenv_arr.env ∧
        (∀ id r w, (id, r) ∈ info.carried →
          lookupHEnv henv' id = some (.lit w) → fenv_arr.env r = some w) := by
  intro bId j ρ supply nextB lastVal hasVal loop ss L h hss hfresh hlast
  induction hss generalizing bId j ρ supply nextB lastVal hasVal loop L with
  | nil =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun hbroke prog f
        prev F hsub hnodf fuelB C hg info hlo hexcl hdist blk hfindE
      cases fuelH with
      | zero =>
          have hst : out = .stuck := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
              (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
          rw [hstep] at hrun
          have hacc : out = HFlow.value (.lit accH) :=
            (congrArg Prod.fst hrun).symm
          rw [hacc] at hbroke
          exact absurd hbroke (by simp)
  | exprStmt e rest hstr _ hrs ih =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun hbroke prog f
        prev F hsub hnodf fuelB C hg info hlo hexcl hdist blk hfindE
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId (some j) true ρ s1 nextB v0 true loop rest with
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
                  rw [hst] at hbroke
                  exact absurd hbroke (by simp)
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
                      have hst : out = .stuck :=
                        (congrArg Prod.fst hrun).symm
                      rw [hst] at hbroke
                      exact absurd hbroke (by simp)
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
                          obtain ⟨F', fenv_arr, blkPrev, hle, hge, heq_rest,
                              hrel_arr, hval_arr⟩ :=
                            ih bId j ρ s1 nextB v0 true loop Lr hr hf1
                              hlast1 wE henv fenv1 hrel1
                              (fun hh => absurd hh (by simp)) (fun _ => hregE')
                              fh henv' out hrun hbroke prog f prev (F'' + 1)
                              hsub' hnodf fuelB C hg' info hlo hexcl hdist blk hfindE
                          exact ⟨F', fenv_arr, blkPrev, hle, hge,
                            hLHS.trans heq_rest, hrel_arr, hval_arr⟩
  | nop rest hrs ih =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun hbroke prog f
        prev F hsub hnodf fuelB C hg info hlo hexcl hdist blk hfindE
      simp only [lowerStmtsCFG] at h
      cases hr : lowerStmtsCFG bId (some j) true ρ supply nextB lastVal
          hasVal loop rest with
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
              rw [hst] at hbroke
              exact absurd hbroke (by simp)
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
              cases F with
              | zero =>
                  have h1 : blockBound fuelB rest ≥ 1 := by
                    rw [blockBound]; omega
                  omega
              | succ F'' =>
                  have hLHS : execBlockFromIn prog (F'' + 1) f prev
                      ⟨bId, Lr.instrs, Lr.term⟩ fenv =
                      execBlockFromIn prog (F'' + 1) f prev
                      ⟨bId, Lr.instrs, Lr.term⟩ fenv := rfl
                  have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                    rw [← hbb]; exact hg
                  obtain ⟨F', fenv_arr, blkPrev, hle, hge, heq_rest,
                      hrel_arr, hval_arr⟩ :=
                    ih bId j ρ supply nextB lastVal hasVal loop Lr hr hfresh
                      hlast accH henv fenv hrel hval0 hreg
                      fh henv' out hrun hbroke prog f prev (F'' + 1)
                      hsub hnodf fuelB C hg' info hlo hexcl hdist blk hfindE
                  exact ⟨F', fenv_arr, blkPrev,
                    hle, hge,
                    hLHS.trans heq_rest, hrel_arr, hval_arr⟩
  | returnStmt e rest hstr _ =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun hbroke prog f
        prev F hsub hnodf fuelB C hg info hlo hexcl hdist blk hfindE
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          obtain rfl := Option.some.inj h
          cases fuelH with
          | zero =>
              have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                  (.value (.lit accH)) = (.stuck, henv) := rfl
              rw [hz] at hrun
              have hst : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hst] at hbroke
              exact absurd hbroke (by simp)
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
                  have hst : out = .stuck :=
                    (congrArg Prod.fst hrun).symm
                  rw [hst] at hbroke
                  exact absurd hbroke (by simp)
              | some r =>
                  rw [hev] at hrun
                  have hret : out = .returned r :=
                    (congrArg Prod.fst hrun).symm
                  rw [hret] at hbroke
                  exact absurd hbroke (by simp)
  | breakStmt rest _ =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun hbroke prog f
        prev F hsub hnodf fuelB C hg info hlo hexcl hdist blk hfindE
      subst hlo
      simp only [lowerStmtsCFG] at h
      cases hc : carryCopies ρ info.carried with
      | none => simp [hc] at h
      | some copies =>
          simp [hc] at h
          subst h
          cases fuelH with
          | zero =>
              have hz : runHIRStmts 0 henv (.break :: rest)
                  (.value (.lit accH)) = (.stuck, henv) := rfl
              rw [hz] at hrun
              have hst : out = .stuck := (congrArg Prod.fst hrun).symm
              rw [hst] at hbroke
              exact absurd hbroke (by simp)
          | succ fh =>
              have hstep : runHIRStmts (fh + 1) henv (.break :: rest)
                  (.value (.lit accH)) = (.broke, henv) := rfl
              rw [hstep] at hrun
              have h2 : henv = henv' := congrArg Prod.snd hrun
              cases F with
              | zero =>
                  have h1 : blockBound fuelB (.break :: rest) ≥ 1 := by
                    rw [blockBound]; omega
                  omega
              | succ F' =>
                  obtain ⟨fenv_arr, hexec_copies, hrel_arr, hval_arr, _⟩ :=
                    carryCopies_exec ρ info.carried copies hc prog prev fenv
                      henv hrel hexcl hdist
                  have heq : execBlockFromIn prog (F' + 1) f prev
                      ⟨bId, copies, .goto info.exit⟩ fenv =
                      execBlockFromIn prog F' f (some bId) blk fenv_arr :=
                    execBlockFromIn_goto prog F' f prev bId copies info.exit
                      fenv fenv_arr blk hexec_copies hfindE
                  have hge : F' ≥ C := by
                    have hbb : blockBound fuelB (.break :: rest) ≥ 1 := by
                      rw [blockBound]; omega
                    omega
                  refine ⟨F', fenv_arr, bId, Nat.le_succ _, hge, heq, ?_, ?_⟩
                  · rw [← h2]
                    exact hrel_arr
                  · rw [← h2]
                    exact hval_arr
  | continueStmt rest _ =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun hbroke prog f
        prev F hsub hnodf fuelB C hg info hlo hexcl hdist blk hfindE
      cases fuelH with
      | zero =>
          have hz : runHIRStmts 0 henv (.continue :: rest)
              (.value (.lit accH)) = (.stuck, henv) := rfl
          rw [hz] at hrun
          have hst : out = .stuck := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
      | succ fh =>
          have hstep : runHIRStmts (fh + 1) henv (.continue :: rest)
              (.value (.lit accH)) = (.continued, henv) := rfl
          rw [hstep] at hrun
          have hst : out = .continued := (congrArg Prod.fst hrun).symm
          rw [hst] at hbroke
          exact absurd hbroke (by simp)
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun hbroke prog f
        prev F hsub hnodf fuelB C hg info hlo hexcl hdist blk hlexit
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
                  cases hr : lowerStmtsCFG (nextB + 2) (some j) true ρ
                      (le.supply + 1) le.next le.supply true loop rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      dsimp only at hsub ⊢
                      generalize hTdef : ((lt.blocks.getLast?.map
                        (fun b => b.id)).getD nextB) = exitT
                      generalize hEdef : ((le.blocks.getLast?.map
                        (fun b => b.id)).getD (nextB + 1)) = exitE
                      rw [hTdef, hEdef] at hsub
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                      have hf1 : FreshAbove ρ s1 :=
                        FreshAbove.mono ρ supply s1 hs1 hfresh
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                        lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath
                      obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                        lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he hael
                      obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                        lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ hr hrs
                      have hrho_t : lt.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ ht hath
                      have hrho_e : le.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ he hael
                      have hrho_r : lr.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _ hr hrs
                      have hbb_if : blockBound fuelB (.ifStmt c th el :: rest) =
                          1 + (3 + max (armBlockBound fuelB th)
                            (armBlockBound fuelB el) +
                            armBlockBound fuelB rest) := by
                        rw [blockBound, armBlockBound_if]
                      have hB1 : blockBound fuelB (.ifStmt c th el :: rest)
                          ≥ 1 := by
                        rw [blockBound]; omega
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
                      have hJmem : (⟨nextB + 2,
                          [.phi le.supply exitT lt.val,
                           .phi le.supply exitE le.val] ++ lr.instrs,
                          lr.term⟩ : Block) ∈ f.blocks :=
                        hsub _ if_asm_mem_join
                      have hfindJ : findBlock f (nextB + 2) =
                          some ⟨nextB + 2,
                            [.phi le.supply exitT lt.val,
                             .phi le.supply exitE le.val] ++ lr.instrs,
                            lr.term⟩ :=
                        findBlock_of_nodup_mem hnodf hJmem
                      -- the two phi edges differ
                      have hne_pe : exitE ≠ exitT := by
                        have hexitT : exitT = nextB ∨
                            ∃ b ∈ lt.blocks, exitT = b.id := by
                          cases hgl : lt.blocks.getLast? with
                          | none =>
                              exact Or.inl (by simp [← hTdef, hgl])
                          | some b =>
                              have hm : b ∈ lt.blocks := getLast?_mem hgl
                              exact Or.inr ⟨b, hm, by simp [← hTdef, hgl]⟩
                        have hexitE : exitE = nextB + 1 ∨
                            ∃ b ∈ le.blocks, exitE = b.id := by
                          cases hgl : le.blocks.getLast? with
                          | none =>
                              exact Or.inl (by simp [← hEdef, hgl])
                          | some b =>
                              have hm : b ∈ le.blocks := getLast?_mem hgl
                              exact Or.inr ⟨b, hm, by simp [← hEdef, hgl]⟩
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
                            exact Nat.ne_of_lt (Nat.lt_of_le_of_lt
                              (Nat.add_le_add_left (by decide) nextB) hlo)
                          · obtain ⟨-, hhi⟩ := hbndt bt hbt
                            obtain ⟨hlo, -⟩ := hbnde be hbe
                            rw [hE, hT]
                            exact Nat.ne_of_gt
                              (Nat.lt_of_lt_of_le hhi hlo)
                      cases F with
                      | zero =>
                          have hbb : blockBound fuelB
                              (.ifStmt c th el :: rest) ≥ 1 := by
                            show 1 + _ ≥ 1
                            omega
                          omega
                      | succ F'' =>
                          cases fuelH with
                          | zero =>
                              have hz : runHIRStmts 0 henv
                                  (.ifStmt c th el :: rest)
                                  (.value (.lit accH)) = (.stuck, henv) := rfl
                              rw [hz] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              rw [hst] at hbroke
                              exact absurd hbroke (by simp)
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
                                  rw [hst] at hbroke
                                  exact absurd hbroke (by simp)
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
                                                  have hsub_t : ∀ b ∈ lt.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_lt hb)
                                                  have hC'ge : (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB th +
                                                      C) ≥ blockBound fuelB
                                                      rest + C := by
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
                                                      armBlockBound fuelB th +
                                                      C) := by
                                                    have hBth : blockBound
                                                        fuelB th = 1 +
                                                        armBlockBound fuelB
                                                          th := rfl
                                                    omega
                                                  obtain ⟨w_arm, hu_arm, F',
                                                      fenv_arr, hle, hge,
                                                      heq_arm, hrel_arm,
                                                      hreg_arr, _⟩ :=
                                                    ((lowerStmtsCFG_arm_total budget nextB (nextB + 2) ρ s1
                                                      (nextB + 3) lastVal false
                                                        loop th lt ht hath hf1 hlast1 .unit
                                                      henv fenvC hrelC
                                                      (fun _ => rfl)
                                                      (fun h => absurd h
                                                        (by simp))
                                                      fh env_arm
                                                      (HFlow.value u_arm) har prog f
                                                      (some bId) ⟨nextB + 2,
                                                        [.phi le.supply exitT
                                                          lt.val,
                                                         .phi le.supply exitE
                                                          le.val] ++ lr.instrs,
                                                        lr.term⟩ F'' hsub_t
                                                      hnodf hfindJ fuelB (2 +
                                                      max (armBlockBound
                                                      fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB th +
                                                      C) hg_t u_arm).1 rfl)
                                                  rw [hTdef] at heq_arm
                                                  rw [hrho_t] at hrel_arm
                                                  have hrep : ((HFlow.value
                                                      (.lit accH)).replace
                                                      (.lit w_arm)) =
                                                      HFlow.value
                                                        (.lit w_arm) := rfl
                                                  rw [hu_arm, hrep] at hrun
                                                  have hfrL : FreshAbove ρ
                                                      le.supply :=
                                                    FreshAbove.mono ρ supply
                                                      le.supply (Nat.le_trans
                                                      hs1 (Nat.le_trans hmst
                                                      hmse)) hfresh
                                                  have hrel_m : RelEnv env_arm ρ
                                                      (fenv_arr.env.update
                                                        le.supply
                                                        w_arm) := by
                                                    intro id u hlook
                                                    obtain ⟨w0, hlookH,
                                                      hreg0⟩ := hrel_arm id u
                                                      hlook
                                                    have hu : u < le.supply :=
                                                      hfrL id u
                                                        (rhoLookup_some_mem ρ
                                                          id u hlook)
                                                    have hne : u ≠ le.supply :=
                                                      Nat.ne_of_lt hu
                                                    refine ⟨w0, hlookH, ?_⟩
                                                    have hupd : (fenv_arr.env.update
                                                        le.supply w_arm) u =
                                                        fenv_arr.env u := by
                                                      simp [Env.update, hne]
                                                    show (fenv_arr.env.update
                                                        le.supply w_arm) u =
                                                      some w0
                                                    rw [hupd]
                                                    exact hreg0
                                                  have hreg_m : (⟨fenv_arr.env.update
                                                      le.supply w_arm,
                                                      fenv_arr.store⟩ :
                                                      FullEnv).env le.supply =
                                                      some w_arm := by
                                                    simp [Env.update]
                                                  have hf_r : FreshAbove ρ
                                                      (le.supply + 1) :=
                                                    FreshAbove.mono ρ supply
                                                      (le.supply + 1)
                                                      (Nat.le_trans hs1
                                                      (Nat.le_trans hmst
                                                      (Nat.le_trans hmse
                                                      (Nat.le_succ _))))
                                                      hfresh
                                                  have hlast_r : le.supply <
                                                      le.supply + 1 :=
                                                    Nat.lt_succ_self _
                                                  have hsub_r : ∀ b ∈ lr.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_lr hb)
                                                  cases F' with
                                                  | zero =>
                                                      have hB1r : blockBound
                                                          fuelB rest ≥ 1 := by
                                                        rw [blockBound]; omega
                                                      exact absurd hge (by omega)
                                                  | succ F1 =>
                                                      have happ_J : execInstrsFullFromIn
                                                          prog (some exitT)
                                                          fenv_arr
                                                          ([.phi le.supply
                                                            exitT lt.val,
                                                            .phi le.supply
                                                            exitE le.val] ++
                                                            lr.instrs) =
                                                          execInstrsFullFromIn
                                                            prog (some exitT)
                                                            ⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩
                                                            lr.instrs :=
                                                        execInstrsFullFromIn_phis_hit
                                                          prog exitT fenv_arr
                                                          le.supply exitT exitE
                                                          lt.val le.val
                                                          lr.instrs w_arm rfl
                                                          hne_pe hreg_arr
                                                      have hJeq : execBlockFromIn
                                                          prog (F1 + 1) f
                                                          (some exitT)
                                                          ⟨nextB + 2,
                                                            [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                            lr.term⟩ fenv_arr =
                                                          execBlockFromIn prog
                                                            (F1 + 1) f
                                                            (some exitT)
                                                            ⟨nextB + 2,
                                                              lr.instrs,
                                                              lr.term⟩
                                                            ⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :=
                                                        execBlockFromIn_instrs_prefix
                                                          prog F1 f (some exitT)
                                                          (nextB + 2)
                                                          [.phi le.supply
                                                            exitT lt.val,
                                                            .phi le.supply
                                                            exitE le.val]
                                                          lr.instrs lr.term
                                                          fenv_arr
                                                          ⟨fenv_arr.env.update
                                                            le.supply w_arm,
                                                            fenv_arr.store⟩
                                                          happ_J
                                                      have hg_r : F1 + 1 ≥
                                                          blockBound fuelB
                                                          rest + C :=
                                                        Nat.le_trans hC'ge hge
                                                      obtain ⟨F2, fenv_arr2, blkPrev2, hle2,
                                                          hge2, heq_rest, hrel_final,
                                                          hval_final⟩ :=
                                                        ihr (nextB + 2) j ρ (le.supply + 1)
                                                          le.next le.supply true loop lr hr
                                                          hf_r hlast_r w_arm env_arm
                                                          ⟨fenv_arr.env.update le.supply w_arm,
                                                            fenv_arr.store⟩
                                                          hrel_m (fun h => absurd h (by simp))
                                                          (fun _ => hreg_m) fh henv' out hrun
                                                          hbroke prog f (some exitT) (F1 + 1)
                                                          hsub_r hnodf fuelB C hg_r info hlo hexcl hdist
                                                          blk hlexit
                                                      -- goal is already the join exit
                                                      exact ⟨F2,
                                                          fenv_arr2, blkPrev2,
                                                          Nat.le_trans
                                                            (Nat.le_trans hle2
                                                            hle)
                                                            (Nat.le_succ _),
                                                          hge2,
                                                          hentry.trans
                                                            (heq_arm.trans
                                                            (hJeq.trans
                                                            heq_rest)),
                                                          hrel_final,
                                                          hval_final⟩
                                              | returned e_arm =>
                                                  simp only [] at hrun
                                                  have hc : out = _ := (congrArg Prod.fst hrun).symm
                                                  rw [hc] at hbroke
                                                  exact absurd hbroke (by simp)
                                              | stuck =>
                                                  simp only [] at hrun
                                                  have hc : out = _ := (congrArg Prod.fst hrun).symm
                                                  rw [hc] at hbroke
                                                  exact absurd hbroke (by simp)
                                              | broke =>
                                                  simp only [] at hrun
                                                  have henv_eq : env_arm = henv' :=
                                                  (congrArg Prod.snd hrun)
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
                                                  have hsub_t : ∀ b ∈ lt.blocks, b ∈ f.blocks :=
                                                    fun b hb => hsub _ (if_asm_mem_of_lt hb)
                                                  have hg_t : F'' ≥ blockBound
                                                      fuelB th + (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB th +
                                                      C) := by
                                                    have hBth : blockBound
                                                        fuelB th = 1 +
                                                        armBlockBound fuelB
                                                          th := rfl
                                                    omega
                                                  have hiht := ((iht nextB (nextB + 2) ρ s1 (nextB + 3) lastVal false loop lt ht hf1 hlast1 .unit
                                                      henv fenvC hrelC
                                                      (fun _ => rfl)
                                                      (fun h => absurd h
                                                        (by simp))
                                                      fh env_arm .broke har rfl prog f
                                                      (some bId) F'' hsub_t hnodf
                                                      fuelB (2 + max (armBlockBound fuelB th) (armBlockBound fuelB el) + armBlockBound fuelB rest - armBlockBound fuelB th + C) hg_t info hlo hexcl hdist blk hlexit))
                                                  obtain ⟨F2, fenv_arr2, blkPrev2, hle2,
                                                      hge2, heq_arm, hrel_final,
                                                      hval_final⟩ := hiht
                                                  rw [henv_eq] at hrel_final
                                                  rw [hrho_t, ← hrho_r] at hrel_final
                                                  rw [henv_eq] at hval_final
                                                  have hgeC : F2 ≥ C := by omega
                                                  exact ⟨F2, fenv_arr2, blkPrev2,
                                                    Nat.le_trans hle2 (Nat.le_succ _),
                                                    hgeC,
                                                    hentry.trans heq_arm,
                                                    hrel_final,
                                                    hval_final⟩
                                              | continued =>
                                                  simp only [] at hrun
                                                  have hc : out = _ := (congrArg Prod.fst hrun).symm
                                                  rw [hc] at hbroke
                                                  exact absurd hbroke (by simp)
                                      | false =>
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
                                          have hsub_e : ∀ b ∈ le.blocks,
                                              b ∈ f.blocks :=
                                            fun b hb => hsub _
                                              (if_asm_mem_of_le hb)
                                          have hf_e : FreshAbove ρ
                                              lt.supply :=
                                            FreshAbove.mono ρ s1 lt.supply
                                              hmst hf1
                                          have hlast_e : lastVal <
                                              lt.supply :=
                                            Nat.lt_of_lt_of_le hlast1 hmst
                                          have hC'ge : (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB el +
                                              C) ≥ blockBound fuelB
                                              rest + C := by
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
                                              armBlockBound fuelB el +
                                              C) := by
                                            have hBel : blockBound
                                                fuelB el = 1 +
                                                armBlockBound fuelB
                                                  el := rfl
                                            omega
                                          cases har : runHIRStmts fh henv el
                                              (HFlow.value (.lit .unit)) with
                                          | mk out_arm env_arm =>
                                              rw [har] at hrun
                                              cases out_arm with
                                              | value u_arm =>
                                                  simp only [] at hrun
                                                  obtain ⟨w_arm, hu_arm, F',
                                                      fenv_arr, hle, hge,
                                                      heq_arm, hrel_arm,
                                                      hreg_arr, _⟩ :=
                                                    ((lowerStmtsCFG_arm_total budget (nextB + 1)
                                                      (nextB + 2) ρ lt.supply
                                                      lt.next lastVal false
                                                        loop el le he hael hf_e hlast_e .unit
                                                      henv fenvC hrelC
                                                      (fun _ => rfl)
                                                      (fun h => absurd h
                                                        (by simp))
                                                      fh env_arm
                                                      (HFlow.value u_arm) har
                                                      prog f (some bId)
                                                      ⟨nextB + 2,
                                                        [.phi le.supply exitT
                                                          lt.val,
                                                         .phi le.supply exitE
                                                          le.val] ++ lr.instrs,
                                                        lr.term⟩ F'' hsub_e
                                                      hnodf hfindJ fuelB (2 +
                                                      max (armBlockBound
                                                      fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el +
                                                      C) hg_e u_arm).1 rfl)
                                                  rw [hEdef] at heq_arm
                                                  rw [hrho_e] at hrel_arm
                                                  have hrep : ((HFlow.value
                                                      (.lit accH)).replace
                                                      (.lit w_arm)) =
                                                      HFlow.value
                                                        (.lit w_arm) := rfl
                                                  rw [hu_arm, hrep] at hrun
                                                  have hfrL : FreshAbove ρ
                                                      le.supply :=
                                                    FreshAbove.mono ρ supply
                                                      le.supply (Nat.le_trans
                                                      hs1 (Nat.le_trans hmst
                                                      hmse)) hfresh
                                                  have hrel_m : RelEnv env_arm
                                                      ρ (fenv_arr.env.update
                                                        le.supply
                                                        w_arm) := by
                                                    intro id u hlook
                                                    obtain ⟨w0, hlookH,
                                                      hreg0⟩ := hrel_arm id u
                                                      hlook
                                                    have hu : u < le.supply :=
                                                      hfrL id u
                                                        (rhoLookup_some_mem ρ
                                                          id u hlook)
                                                    have hne : u ≠ le.supply :=
                                                      Nat.ne_of_lt hu
                                                    refine ⟨w0, hlookH, ?_⟩
                                                    have hupd : (fenv_arr.env.update
                                                        le.supply w_arm) u =
                                                        fenv_arr.env u := by
                                                      simp [Env.update, hne]
                                                    show (fenv_arr.env.update
                                                        le.supply w_arm) u =
                                                      some w0
                                                    rw [hupd]
                                                    exact hreg0
                                                  have hreg_m : (⟨fenv_arr.env.update
                                                      le.supply w_arm,
                                                      fenv_arr.store⟩ :
                                                      FullEnv).env le.supply =
                                                      some w_arm := by
                                                    simp [Env.update]
                                                  have hf_r : FreshAbove ρ
                                                      (le.supply + 1) :=
                                                    FreshAbove.mono ρ supply
                                                      (le.supply + 1)
                                                      (Nat.le_trans hs1
                                                      (Nat.le_trans hmst
                                                      (Nat.le_trans hmse
                                                      (Nat.le_succ _))))
                                                      hfresh
                                                  have hlast_r : le.supply <
                                                      le.supply + 1 :=
                                                    Nat.lt_succ_self _
                                                  have hsub_r : ∀ b ∈ lr.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_lr hb)
                                                  cases F' with
                                                  | zero =>
                                                      have hB1r : blockBound
                                                          fuelB rest ≥ 1 := by
                                                        rw [blockBound]; omega
                                                      exact absurd hge (by omega)
                                                  | succ F1 =>
                                                      have happ_J : execInstrsFullFromIn
                                                          prog (some exitE)
                                                          fenv_arr
                                                          ([.phi le.supply
                                                            exitT lt.val,
                                                            .phi le.supply
                                                            exitE le.val] ++
                                                            lr.instrs) =
                                                          execInstrsFullFromIn
                                                            prog (some exitE)
                                                            ⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩
                                                            lr.instrs := by
                                                        simp only
                                                          [List.cons_append,
                                                          List.nil_append]
                                                        rw [execInstrsFullFromIn_eq,
                                                          execInstrsFullFromIn_eq,
                                                          execInstrsFullFrom_phi_miss
                                                          _ _ _ _ _ _
                                                          (Ne.symm hne_pe),
                                                          execInstrsFullFrom_phi_hit
                                                          _ _ _ _ _ _ rfl,
                                                          hreg_arr]
                                                      have hJeq : execBlockFromIn
                                                          prog (F1 + 1) f
                                                          (some exitE)
                                                          ⟨nextB + 2,
                                                            [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                              lr.term⟩ fenv_arr =
                                                          execBlockFromIn prog
                                                            (F1 + 1) f
                                                            (some exitE)
                                                            ⟨nextB + 2,
                                                              lr.instrs,
                                                              lr.term⟩
                                                            ⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :=
                                                        execBlockFromIn_instrs_prefix
                                                          prog F1 f (some exitE)
                                                          (nextB + 2)
                                                          [.phi le.supply
                                                            exitT lt.val,
                                                            .phi le.supply
                                                            exitE le.val]
                                                          lr.instrs lr.term
                                                          fenv_arr
                                                          ⟨fenv_arr.env.update
                                                            le.supply w_arm,
                                                            fenv_arr.store⟩
                                                          happ_J
                                                      have hg_r : F1 + 1 ≥
                                                          blockBound fuelB
                                                          rest + C :=
                                                        Nat.le_trans hC'ge
                                                          hge
                                                      obtain ⟨F2, fenv_arr2, blkPrev2, hle2,
                                                          hge2, heq_rest, hrel_final,
                                                          hval_final⟩ :=
                                                        ihr (nextB + 2) j ρ (le.supply + 1)
                                                          le.next le.supply true loop lr hr
                                                          hf_r hlast_r w_arm env_arm
                                                          ⟨fenv_arr.env.update le.supply w_arm,
                                                            fenv_arr.store⟩
                                                          hrel_m (fun h => absurd h (by simp))
                                                          (fun _ => hreg_m) fh henv' out hrun
                                                          hbroke prog f (some exitE) (F1 + 1)
                                                          hsub_r hnodf fuelB C hg_r info hlo hexcl hdist
                                                          blk hlexit
                                                      exact ⟨F2,
                                                        fenv_arr2, blkPrev2,
                                                        Nat.le_trans
                                                          (Nat.le_trans hle2
                                                          hle)
                                                          (Nat.le_succ _),
                                                        hge2,
                                                        hentry.trans
                                                        (heq_arm.trans
                                                        (hJeq.trans
                                                        heq_rest)),
                                                        hrel_final,
                                                        hval_final⟩
                                              | returned e_arm =>
                                                  simp only [] at hrun
                                                  have hc : out = _ := (congrArg Prod.fst hrun).symm
                                                  rw [hc] at hbroke
                                                  exact absurd hbroke (by simp)
                                              | stuck =>
                                                  simp only [] at hrun
                                                  have hc : out = _ := (congrArg Prod.fst hrun).symm
                                                  rw [hc] at hbroke
                                                  exact absurd hbroke (by simp)
                                              | broke =>
                                                  simp only [] at hrun
                                                  have henv_eq : env_arm = henv' :=
                                                    (congrArg Prod.snd hrun)
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
                                                  have hg_t : F'' ≥ blockBound
                                                      fuelB el + (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el +
                                                      C) := by
                                                    have hBel : blockBound
                                                        fuelB el = 1 +
                                                        armBlockBound fuelB
                                                          el := rfl
                                                    omega
                                                  have hsub_e : ∀ b ∈ le.blocks, b ∈ f.blocks :=
                                                    fun b hb => hsub _ (if_asm_mem_of_le hb)
                                                  have hiht := ((ihe (nextB + 1) (nextB + 2) ρ lt.supply lt.next lastVal false loop le he hf_e hlast_e .unit
                                                      henv fenvC hrelC
                                                      (fun _ => rfl)
                                                      (fun h => absurd h
                                                        (by simp))
                                                      fh env_arm .broke har rfl prog f
                                                      (some bId) F'' hsub_e hnodf
                                                      fuelB (2 + max (armBlockBound fuelB th) (armBlockBound fuelB el) + armBlockBound fuelB rest - armBlockBound fuelB el + C) hg_t info hlo hexcl hdist blk hlexit))
                                                  obtain ⟨F2, fenv_arr2, blkPrev2, hle2,
                                                      hge2, heq_arm, hrel_final,
                                                      hval_final⟩ := hiht
                                                  rw [henv_eq] at hrel_final
                                                  rw [hrho_e, ← hrho_r] at hrel_final
                                                  rw [henv_eq] at hval_final
                                                  have hgeC : F2 ≥ C := by omega
                                                  exact ⟨F2, fenv_arr2, blkPrev2,
                                                    Nat.le_trans hle2 (Nat.le_succ _),
                                                    hgeC,
                                                    hentry.trans heq_arm,
                                                    hrel_final,
                                                    hval_final⟩
                                              | continued =>
                                                  simp only [] at hrun
                                                  have hc : out = _ := (congrArg Prod.fst hrun).symm
                                                  rw [hc] at hbroke
                                                  exact absurd hbroke (by simp)
                                  | int _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | string _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | pointer _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | float _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | unit =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | undef =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | some _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | none =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | ok _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | err _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | tuple_ _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | array_ _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | loc _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)
                                  | closure _ _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      rw [hst] at hbroke
                                      exact absurd hbroke (by simp)

end Morph.HIRToMIRCorrect
