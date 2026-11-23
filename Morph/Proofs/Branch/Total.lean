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

/-!
# Stage C body worker: `lowerStmtsCFG_total`

Twelfth proof leaf out of the `HIRToMIRBranch` monolith: the body
counterpart of the arm worker — closed bodies (`cont = none`) run to
the oracle's value. Straight-line steps peel via `lower_total.1`;
`if` reuses the arm worker for both arms; `whileStmt` cites
`whileLoop_correct` (moved verbatim, ~2.4k lines).
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-! ## The body worker: closed bodies run to the oracle's value

Loop 179. `lowerStmtsCFG_total` is the body counterpart of the arm worker:
with `cont = none` every path ends in `return_`, so both outcomes conclude
`entry-run = some w` and no join formula is needed. Straight-line steps peel
via `lower_total.1` and the instr-prefix bridge; `if` reuses the arm worker
for both arms and the list IH for the tail; `cont` is fixed to `none`
because only closed programs reach the bridge. -/
theorem lowerStmtsCFG_total (budget : Nat) :
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
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId)
        (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB : Nat), F ≥ blockBound fuelB ss → fuelH ≤ fuelB →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_e) := by
  intro bId ρ supply nextB lastVal hasVal ss
  induction ss generalizing bId ρ supply nextB lastVal hasVal with
  | nil =>
      intro L h hss hfresh hlast _hltB
      cases hss with
      | nil =>
          intro accH henv fenv hrel hacc fuelH henv' out hrun prog f prev F
            hsub hnodf fuelB hg hfb
          simp only [lowerStmtsCFG] at h
          obtain rfl := Option.some.inj h
          intro u
          refine ⟨?_, ?_⟩
          · intro hout
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
                have hu : u = .lit accH := by
                  have h1 : (.value (.lit accH)) = out :=
                    congrArg Prod.fst hrun
                  rw [← h1] at hout
                  exact (HFlow.value.inj hout).symm
                refine ⟨accH, hu, ?_⟩
                cases F with
                | zero =>
                    have hbb : blockBound fuelB ([] : List HIR.Stmt) = 1 := by
                      simp [blockBound]
                    omega
                | succ F' =>
                    have hLHS : execBlockFromIn prog (F' + 1) f prev
                        ⟨bId, [], .return_ lastVal⟩ fenv =
                        fenv.env lastVal := rfl
                    rw [hLHS]
                    exact hacc
          · intro e_ret hout2
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout2
                exact absurd hout2 (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                rw [← h1] at hout2
                exact absurd hout2 (by simp)
  | cons s rest ih =>
      intro L h hss hfresh hlast hltB
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
                  cases hr : lowerStmtsCFG bId none false ρ s1 nextB v true
                      none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg hfb
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      have hbb : blockBound fuelB (.exprStmt e :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)
                      (fun c body h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      have hf1 : FreshAbove ρ s1 :=
                        FreshAbove.mono ρ supply s1 hs1 hfresh
                      have hva : v < s1 :=
                        lower_result_lt.1 ρ supply e v ie s1 he hfresh
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv (.exprStmt e :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.exprStmt e :: rest) (.value (.lit accH)) =
                              (match evalHIR 256 henv e with
                                | none => (HFlow.stuck, henv)
                                | some v => runHIRStmts fh henv rest
                                    (.value v)) := rfl
                          rw [hstep] at hrun
                          cases hev : evalHIR 256 henv e with
                          | none =>
                              rw [hev] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply e v ie s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply e v ie s1 he fenv
                                  fenv1 hrel hfresh hexec1
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ie := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ie = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ie ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ie ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ie q.instrs q.term fenv fenv1
                                      happ
                                  have hww : wE = wE2 :=
                                    HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                                  intro u
                                  have hfb' : fh ≤ fuelB := by omega
                                  have hihr := ih bId ρ s1 nextB v true q hr
                                    hrs hf1 hva hltB wE henv fenv1 hrel1
                                    (hww ▸ hregE) fh henv' out hrun prog f
                                    prev (F' + 1) hsub hnodf fuelB hg' hfb' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | varDecl id τ init hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId none false ((id, vb) :: ρ) s1
                      nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg hfb
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
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
                      have hbb : blockBound fuelB (.varDecl id τ init :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)
                      (fun c body h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv
                              (.varDecl id τ init :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.varDecl id τ init :: rest)
                              (.value (.lit accH)) =
                              (match evalHIR 256 henv init with
                                | none => (HFlow.stuck, henv)
                                | some v => runHIRStmts fh ((id, v) :: henv)
                                    rest (.value (.lit accH))) := rfl
                          rw [hstep] at hrun
                          cases hev : evalHIR 256 henv init with
                          | none =>
                              rw [hev] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply init vb ib s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              have hww : wE = wE2 :=
                                HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply init vb ib s1 he
                                  fenv fenv1 hrel hfresh hexec1
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
                                  obtain ⟨w', hlookH, hreg⟩ :=
                                    hrel1 j u hlook'
                                  have hlookH' : lookupHEnv
                                      ((id, .lit wE) :: henv) j =
                                      some (.lit w') := by
                                    rw [lookupHEnv_cons_ne hid]
                                    exact hlookH
                                  exact ⟨w', hlookH', hreg⟩
                              have hacc1 : fenv1.env lastVal = some accH := by
                                rw [lower_preserv_regs ρ supply init vb ib
                                  s1 he fenv fenv1 hexec1 lastVal hlast]
                                exact hacc
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ib := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ib = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ib ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ib ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ib q.instrs q.term fenv fenv1
                                      happ
                                  intro u
                                  have hfb' : fh ≤ fuelB := by omega
                                  have hihr := ih bId ((id, vb) :: ρ) s1
                                    nextB lastVal true q hr hrs hf1 hlast1 hltB
                                    accH ((id, .lit wE) :: henv) fenv1 hrel2
                                    hacc1 fh henv' out hrun prog f prev
                                    (F' + 1) hsub hnodf fuelB hg' hfb' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | assign id e hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v0, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId none false (updAssoc ρ id v0)
                      s1 nextB lastVal true none rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg hfb
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
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
                      have hbb : blockBound fuelB (.assign id e :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)
                      (fun c body h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv (.assign id e :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
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
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply e v0 ie s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              have hww : wE = wE2 :=
                                HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply e v0 ie s1 he fenv
                                  fenv1 hrel hfresh hexec1
                              have hrel2 : RelEnv
                                  (updateHEnv henv id (.lit wE))
                                  (updAssoc ρ id v0) fenv1.env :=
                                RelEnv_update ρ henv fenv1.env id v0 wE
                                  hrel1 (hww ▸ hregE)
                              have hacc1 : fenv1.env lastVal = some accH := by
                                rw [lower_preserv_regs ρ supply e v0 ie s1
                                  he fenv fenv1 hexec1 lastVal hlast]
                                exact hacc
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ie := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ie = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ie ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ie ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ie q.instrs q.term fenv fenv1
                                      happ
                                  intro u
                                  have hfb' : fh ≤ fuelB := by omega
                                  have hihr := ih bId (updAssoc ρ id v0) s1
                                    nextB lastVal true q hr hrs hf1 hlast1 hltB
                                    accH (updateHEnv henv id (.lit wE))
                                    fenv1 hrel2 hacc1 fh henv' out hrun prog
                                    f prev (F' + 1) hsub hnodf fuelB hg' hfb' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | nop =>
              simp only [lowerStmtsCFG] at h
              intro accH henv fenv hrel hacc fuelH henv' out hrun prog f
                prev F hsub hnodf fuelB hg hfb
              have hbb : blockBound fuelB (Morph.HIR.Stmt.nop :: rest)
                  = blockBound fuelB rest := by
                rw [blockBound, blockBound,
                  armBlockBound_cons_not_if fuelB
                    (fun c th el h => by cases h)
                    (fun c body h => by cases h)]
              have hg' : F ≥ blockBound fuelB rest := by
                rw [← hbb]; exact hg
              cases fuelH with
              | zero =>
                  have hz : runHIRStmts 0 henv
                      (Morph.HIR.Stmt.nop :: rest)
                      (.value (.lit accH)) = (.stuck, henv) := rfl
                  rw [hz] at hrun
                  have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                  intro u
                  refine ⟨?_, ?_⟩
                  · intro hout
                    rw [hst] at hout
                    exact absurd hout (by simp)
                  · intro e_ret hout2
                    rw [hst] at hout2
                    exact absurd hout2 (by simp)
              | succ fh =>
                  have hstep : runHIRStmts (fh + 1) henv
                      (Morph.HIR.Stmt.nop :: rest) (.value (.lit accH)) =
                      runHIRStmts fh henv rest (.value (.lit accH)) := rfl
                  rw [hstep] at hrun
                  intro u
                  have hfb' : fh ≤ fuelB := by omega
                  exact ih bId ρ supply nextB lastVal hasVal L h hrs hfresh
                    hlast hltB accH henv fenv hrel hacc fh henv' out hrun prog f
                    prev F hsub hnodf fuelB hg' hfb' u
          | ifStmt c th el hstr _ hath hael =>
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
                      cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                          true ρ lt.supply lt.next lastVal false none el with
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
                          cases hr : lowerStmtsCFG (nextB + 2) none false ρ
                              (le.supply + 1) le.next le.supply true none rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              obtain rfl := Option.some.inj h
                              intro accH henv fenv hrel hacc fuelH henv' out
                                hrun prog f prev F hsub hnodf fuelB hg hfb
                              dsimp only at hsub ⊢
                              generalize hTdef : ((lt.blocks.getLast?.map
                                (fun b => b.id)).getD nextB) = exitT
                              generalize hEdef : ((le.blocks.getLast?.map
                                (fun b => b.id)).getD (nextB + 1)) = exitE
                              rw [hTdef, hEdef] at hsub
                              have hs1 : supply ≤ s1 :=
                                lower_mono.1 _ _ _ _ _ _ heC
                              have hf1 : FreshAbove ρ s1 :=
                                FreshAbove.mono ρ supply s1 hs1 hfresh
                              have hlast1 : lastVal < s1 :=
                                Nat.lt_of_lt_of_le hlast hs1
                              obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                                  ht hath
                              obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                                  he hael
                              obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                                lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _
                                  _ _ _ hr hrs
                              have hrho_t : lt.ρ = ρ :=
                                lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _
                                  _ ht hath
                              have hrho_e : le.ρ = ρ :=
                                lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _
                                  _ he hael
                              have hbb_if : blockBound fuelB
                                  (.ifStmt c th el :: rest) =
                                  1 + (3 + max (armBlockBound fuelB th)
                                    (armBlockBound fuelB el) +
                                    armBlockBound fuelB rest) := by
                                rw [blockBound, armBlockBound_if]
                              have hB1 : blockBound fuelB
                                  (.ifStmt c th el :: rest) ≥ 1 := by
                                rw [blockBound]; omega
                              have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                  ∈ f.blocks :=
                                hsub _ if_asm_mem_then
                              have hfindT : findBlock f nextB =
                                  some ⟨nextB, lt.instrs, lt.term⟩ :=
                                findBlock_of_nodup_mem hnodf hTmem
                              have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ :
                                  Block) ∈ f.blocks :=
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
                              have hne_pe : exitE ≠ exitT := by
                                have hexitT : exitT = nextB ∨
                                    ∃ b ∈ lt.blocks, exitT = b.id := by
                                  cases hgl : lt.blocks.getLast? with
                                  | none =>
                                      exact Or.inl (by simp [← hTdef, hgl])
                                  | some b =>
                                      have hm : b ∈ lt.blocks :=
                                        getLast?_mem hgl
                                      exact Or.inr ⟨b, hm, by simp [← hTdef, hgl]⟩
                                have hexitE : exitE = nextB + 1 ∨
                                    ∃ b ∈ le.blocks, exitE = b.id := by
                                  cases hgl : le.blocks.getLast? with
                                  | none =>
                                      exact Or.inl (by simp [← hEdef, hgl])
                                  | some b =>
                                      have hm : b ∈ le.blocks :=
                                        getLast?_mem hgl
                                      exact Or.inr ⟨b, hm, by simp [← hEdef, hgl]⟩
                                rcases hexitT with hT | ⟨bt, hbt, hT⟩
                                · rcases hexitE with hE | ⟨be, hbe, hE⟩
                                  · simp [hT, hE]
                                  · obtain ⟨hlo, -⟩ := hbnde be hbe
                                    rw [hE, hT]
                                    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le
                                      (by omega)
                                      (Nat.le_trans hmnt hlo))
                                · rcases hexitE with hE | ⟨be, hbe, hE⟩
                                  · obtain ⟨hlo, -⟩ := hbndt bt hbt
                                    rw [hE, hT]
                                    exact Nat.ne_of_lt (Nat.lt_of_le_of_lt
                                      (Nat.add_le_add_left (by decide) nextB)
                                      hlo)
                                  · obtain ⟨-, hhi⟩ := hbndt bt hbt
                                    obtain ⟨hlo, -⟩ := hbnde be hbe
                                    rw [hE, hT]
                                    exact Nat.ne_of_gt
                                      (Nat.lt_of_lt_of_le hhi hlo)
                              have hgF : F ≥ 1 + (3 + max (armBlockBound fuelB
                                  th) (armBlockBound fuelB el) +
                                  armBlockBound fuelB rest) := by
                                rw [← hbb_if]; exact hg
                              cases F with
                              | zero => omega
                              | succ F'' =>
                                  cases fuelH with
                                  | zero =>
                                      have hz : runHIRStmts 0 henv
                                          (.ifStmt c th el :: rest)
                                          (.value (.lit accH)) =
                                          (.stuck, henv) := rfl
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
                                                    ((HFlow.value
                                                      (.lit accH)).replace u)
                                              | (f, env') => (f, env')
                                            | some (.lit (.bool false)) =>
                                              match runHIRStmts fh henv el
                                                  (HFlow.value (.lit .unit)) with
                                              | (HFlow.value u, env') =>
                                                  runHIRStmts fh env' rest
                                                    ((HFlow.value
                                                      (.lit accH)).replace u)
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
                                          obtain ⟨⟨w, hrw⟩, fenvC, hexecC,
                                              hstoreC, wC, hrC, hregC⟩ :=
                                            lower_total.1 ρ supply c vc ic s1
                                              heC hstr hfresh henv fenv hrel
                                              256 r hevC
                                          subst hrw
                                          have hnp_ic : ∀ dst pred src,
                                              .phi dst pred src ∉ ic := by
                                            intro d p s hm
                                            exact IsPure_not_phi
                                              (lower_isPure.1 _ _ _ _ _ _ heC
                                                _ hm) d p s rfl
                                          have hexec_ic : execInstrsFullFromIn
                                              prog prev fenv ic =
                                              some fenvC := by
                                            rw [execInstrsFullFromIn_of_noPhi
                                              prog prev fenv _ hnp_ic]
                                            exact hexecC
                                          have hrelC : RelEnv henv ρ
                                              fenvC.env :=
                                            RelEnv_exec henv ρ supply c vc ic
                                              s1 heC fenv fenvC hrel hfresh
                                              hexecC
                                          cases w with
                                          | bool b =>
                                              cases b with
                                              | true =>
                                                  simp only [] at hrun
                                                  cases har : runHIRStmts fh
                                                      henv th (HFlow.value
                                                        (.lit .unit)) with
                                                  | mk out_arm env_arm =>
                                                      rw [har] at hrun
                                                      cases out_arm with
                                                      | value u_arm =>
                                                          simp only [] at hrun
                                                          have hregCb :
                                                              fenvC.env vc =
                                                              some
                                                              (.bool true) := by
                                                            have hww :
                                                                (.bool true) =
                                                                wC :=
                                                              HIR.Expr.lit.inj
                                                                hrC
                                                            rw [hww]
                                                            exact hregC
                                                          have hbool :
                                                              fenvC.boolOf vc =
                                                              some true :=
                                                            boolOf_of_lit fenvC
                                                              vc true hregCb
                                                          have hentry :
                                                              execBlockFromIn
                                                              prog (F'' + 1) f
                                                              prev ⟨bId, ic,
                                                              .branch vc nextB
                                                              (nextB + 1)⟩
                                                              fenv =
                                                              execBlockFromIn
                                                              prog F'' f
                                                              (some bId)
                                                              ⟨nextB, lt.instrs,
                                                              lt.term⟩ fenvC :=
                                                            execBlockFromIn_branch_true
                                                              prog F'' f prev
                                                              bId ic vc nextB
                                                              (nextB + 1) fenv
                                                              fenvC
                                                              ⟨nextB, lt.instrs,
                                                              lt.term⟩ hexec_ic
                                                              hbool hfindT
                                                          have hsub_t : ∀ b ∈
                                                              lt.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lt
                                                              hb)
                                                          have hCtge : (2 + max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) ≥
                                                              blockBound fuelB
                                                              rest := by
                                                            have hBrest :
                                                                blockBound fuelB
                                                                rest = 1 +
                                                                armBlockBound
                                                                fuelB rest :=
                                                              rfl
                                                            omega
                                                          have hg_t : F'' ≥
                                                              blockBound fuelB
                                                              th + (2 + max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) := by
                                                            have hBth :
                                                                blockBound fuelB
                                                                th = 1 +
                                                                armBlockBound
                                                                fuelB th := rfl
                                                            omega
                                                          obtain ⟨w_arm, hu_arm,
                                                              F', fenv_arr, hle,
                                                              hge, heq_arm,
                                                              hrel_arm,
                                                              hreg_arr, _⟩ :=
                                                            ((lowerStmtsCFG_arm_total
                                                              budget nextB
                                                              (nextB + 2) ρ s1
                                                              (nextB + 3)
                                                              lastVal false none th
                                                              lt ht hath hf1
                                                              hlast1 .unit henv
                                                              fenvC hrelC
                                                              (fun _ => rfl)
                                                              (fun h => absurd h
                                                              (by simp))
                                                              fh env_arm
                                                              (HFlow.value
                                                              u_arm) har prog f
                                                              (some bId)
                                                              ⟨nextB + 2,
                                                              [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                              lr.term⟩ F''
                                                              hsub_t hnodf
                                                              hfindJ fuelB (2 +
                                                              max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) hg_t
                                                              u_arm).1 rfl)
                                                          rw [hTdef] at heq_arm
                                                          rw [hrho_t] at hrel_arm
                                                          have hrep :
                                                              ((HFlow.value
                                                              (.lit accH)).replace
                                                              (.lit w_arm)) =
                                                              HFlow.value
                                                              (.lit w_arm) :=
                                                            rfl
                                                          rw [hu_arm, hrep] at hrun
                                                          have hfrL : FreshAbove
                                                              ρ le.supply :=
                                                            FreshAbove.mono ρ
                                                              supply le.supply
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              hmse)) hfresh
                                                          have hrel_m : RelEnv
                                                              env_arm ρ
                                                              (fenv_arr.env.update
                                                              le.supply
                                                              w_arm) := by
                                                            intro id u hlook
                                                            obtain ⟨w0, hlookH,
                                                              hreg0⟩ :=
                                                              hrel_arm id u
                                                              hlook
                                                            have hu : u <
                                                                le.supply :=
                                                              hfrL id u
                                                              (rhoLookup_some_mem
                                                              ρ id u hlook)
                                                            have hne : u ≠
                                                                le.supply :=
                                                              Nat.ne_of_lt hu
                                                            refine ⟨w0, hlookH,
                                                              ?_⟩
                                                            have hupd :
                                                                (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                                fenv_arr.env
                                                                u := by
                                                              simp [Env.update,
                                                                hne]
                                                            show (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                              some w0
                                                            rw [hupd]
                                                            exact hreg0
                                                          have hreg_m :
                                                              (⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :
                                                              FullEnv).env
                                                              le.supply =
                                                              some w_arm := by
                                                            simp [Env.update]
                                                          have hf_r : FreshAbove
                                                              ρ (le.supply +
                                                              1) :=
                                                            FreshAbove.mono ρ
                                                              supply
                                                              (le.supply + 1)
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              (Nat.le_trans hmse
                                                              (Nat.le_succ _))))
                                                              hfresh
                                                          have hlast_r :
                                                              le.supply <
                                                              le.supply + 1 :=
                                                            Nat.lt_succ_self _
                                                          have hsub_r : ∀ b ∈
                                                              lr.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lr
                                                              hb)
                                                          cases F' with
                                                          | zero =>
                                                              have hB1r :
                                                                  blockBound
                                                                  fuelB rest ≥
                                                                  1 := by
                                                                rw [blockBound]
                                                                omega
                                                              exact absurd hge
                                                                (by omega)
                                                          | succ F1 =>
                                                              have happ_J :
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitT)
                                                                  fenv_arr
                                                                  ([.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs) =
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitT)
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  lr.instrs :=
                                                                execInstrsFullFromIn_phis_hit
                                                                  prog exitT
                                                                  fenv_arr
                                                                  le.supply
                                                                  exitT exitE
                                                                  lt.val le.val
                                                                  lr.instrs
                                                                  w_arm rfl
                                                                  hne_pe
                                                                  hreg_arr
                                                              have hJeq :
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitT)
                                                                  ⟨nextB + 2,
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  fenv_arr =
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitT)
                                                                  ⟨nextB + 2,
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩ :=
                                                                execBlockFromIn_instrs_prefix
                                                                  prog F1 f
                                                                  (some exitT)
                                                                  (nextB + 2)
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val]
                                                                  lr.instrs
                                                                  lr.term
                                                                  fenv_arr
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  happ_J
                                                              have hg_r : F1 + 1 ≥
                                                                  blockBound
                                                                  fuelB rest :=
                                                                Nat.le_trans hCtge
                                                                  hge
                                                              intro u
                                                              have hfb' : fh ≤ fuelB := by omega
                                                              have hltB' : nextB + 2 < le.next := by
                                                                have h1 : nextB + 3 ≤ lt.next := hmnt
                                                                have h2 : lt.next ≤ le.next := hmne
                                                                omega
                                                              have hihr := ih
                                                                (nextB + 2) ρ
                                                                (le.supply + 1)
                                                                le.next
                                                                le.supply true
                                                                lr hr hrs hf_r
                                                                hlast_r hltB' w_arm
                                                                env_arm
                                                                ⟨fenv_arr.env.update
                                                                le.supply w_arm,
                                                                fenv_arr.store⟩
                                                                hrel_m hreg_m fh
                                                                henv' out hrun
                                                                prog f
                                                                (some exitT)
                                                                (F1 + 1) hsub_r
                                                                hnodf fuelB hg_r hfb'
                                                                u
                                                              refine ⟨?_, ?_⟩
                                                              · intro hout
                                                                obtain ⟨w_u, hu,
                                                                    heq_rest⟩ :=
                                                                  hihr.1 hout
                                                                exact ⟨w_u, hu,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                              · intro e_ret hout2
                                                                obtain ⟨w_e, hu_e,
                                                                    heq_rest⟩ :=
                                                                  hihr.2 e_ret
                                                                    hout2
                                                                exact ⟨w_e, hu_e,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                      | returned e_arm =>
                                                          simp only [] at hrun
                                                          have hout_r : out =
                                                              .returned e_arm :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_r] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            have hret_e : e_ret =
                                                                e_arm :=
                                                              (HFlow.returned.inj
                                                                (hout_r.symm.trans
                                                                hout2)).symm
                                                            have hregCb_r :
                                                                fenvC.env vc =
                                                                some
                                                                (.bool true) := by
                                                              have hww :
                                                                  (.bool true) =
                                                                  wC :=
                                                                HIR.Expr.lit.inj
                                                                  hrC
                                                              rw [hww]
                                                              exact hregC
                                                            have hbool_r :
                                                                fenvC.boolOf vc =
                                                                some true :=
                                                              boolOf_of_lit
                                                                fenvC vc true
                                                                hregCb_r
                                                            have hentry_r :
                                                                execBlockFromIn
                                                                prog (F'' + 1)
                                                                f prev ⟨bId, ic,
                                                                .branch vc
                                                                nextB
                                                                (nextB + 1)⟩
                                                                fenv =
                                                                execBlockFromIn
                                                                prog F'' f
                                                                (some bId)
                                                                ⟨nextB, lt.instrs,
                                                                lt.term⟩
                                                                fenvC :=
                                                              execBlockFromIn_branch_true
                                                                prog F'' f prev
                                                                bId ic vc nextB
                                                                (nextB + 1)
                                                                fenv fenvC
                                                                ⟨nextB,
                                                                lt.instrs,
                                                                lt.term⟩
                                                                hexec_ic
                                                                hbool_r hfindT
                                                            have hsub_tr : ∀ b ∈
                                                                lt.blocks,
                                                                b ∈ f.blocks :=
                                                              fun b hb => hsub _
                                                                (if_asm_mem_of_lt
                                                                hb)
                                                            have hCtge_r : (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) ≥
                                                                blockBound fuelB
                                                                rest := by
                                                              have hBrest :
                                                                  blockBound
                                                                  fuelB rest =
                                                                  1 +
                                                                  armBlockBound
                                                                  fuelB rest :=
                                                                rfl
                                                              omega
                                                            have hg_tr : F'' ≥
                                                                blockBound fuelB
                                                                th + (2 + max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) := by
                                                              have hBth :
                                                                  blockBound
                                                                  fuelB th = 1 +
                                                                  armBlockBound
                                                                  fuelB th :=
                                                                rfl
                                                              omega
                                                            obtain ⟨w_e, heq,
                                                                hexec_arm⟩ :=
                                                              ((lowerStmtsCFG_arm_total
                                                                budget nextB
                                                                (nextB + 2) ρ s1
                                                                (nextB + 3)
                                                                lastVal false none th
                                                                lt ht hath hf1
                                                                hlast1 .unit henv
                                                                fenvC hrelC
                                                                (fun _ => rfl)
                                                                (fun h => absurd h
                                                                (by simp))
                                                                fh env_arm
                                                                (HFlow.returned
                                                                e_arm)
                                                                har prog f
                                                                (some bId)
                                                                ⟨nextB + 2,
                                                                [.phi le.supply
                                                                exitT lt.val,
                                                                .phi le.supply
                                                                exitE le.val] ++
                                                                lr.instrs,
                                                                lr.term⟩ F''
                                                                hsub_tr hnodf
                                                                hfindJ fuelB (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) hg_tr
                                                                (.lit .unit)).2
                                                                e_arm rfl)
                                                            exact ⟨w_e,
                                                              hret_e.trans heq,
                                                              hentry_r.trans
                                                              hexec_arm⟩
                                                      | stuck =>
                                                          simp only [] at hrun
                                                          have hout_s : out =
                                                              .stuck :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_s] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_s] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | broke =>
                                                          simp only [] at hrun
                                                          have hout_b : out =
                                                              .broke :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_b] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_b] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | continued =>
                                                          simp only [] at hrun
                                                          have hout_c : out =
                                                              .continued :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_c] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_c] at hout2
                                                            exact absurd hout2
                                                              (by simp)
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
                                                  have hentry : execBlockFromIn
                                                      prog (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc
                                                      nextB (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog F'' f
                                                        (some bId)
                                                        ⟨nextB + 1, le.instrs,
                                                        le.term⟩ fenvC :=
                                                    execBlockFromIn_branch_false
                                                      prog F'' f prev bId ic vc
                                                      nextB (nextB + 1) fenv
                                                      fenvC
                                                      ⟨nextB + 1, le.instrs,
                                                      le.term⟩ hexec_ic hbool
                                                      hfindE
                                                  have hsub_e : ∀ b ∈ le.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_le hb)
                                                  have hf_e : FreshAbove ρ
                                                      lt.supply :=
                                                    FreshAbove.mono ρ s1
                                                      lt.supply hmst hf1
                                                  have hlast_e : lastVal <
                                                      lt.supply :=
                                                    Nat.lt_of_lt_of_le hlast1
                                                      hmst
                                                  have hCege : (2 + max
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
                                                  cases har : runHIRStmts fh
                                                      henv el (HFlow.value
                                                        (.lit .unit)) with
                                                  | mk out_arm env_arm =>
                                                      rw [har] at hrun
                                                      cases out_arm with
                                                      | value u_arm =>
                                                          simp only [] at hrun
                                                          obtain ⟨w_arm, hu_arm,
                                                              F', fenv_arr, hle,
                                                              hge, heq_arm,
                                                              hrel_arm,
                                                              hreg_arr, _⟩ :=
                                                            ((lowerStmtsCFG_arm_total
                                                              budget (nextB + 1)
                                                              (nextB + 2) ρ
                                                              lt.supply lt.next
                                                              lastVal false none el
                                                              le he hael hf_e
                                                              hlast_e .unit henv
                                                              fenvC hrelC
                                                              (fun _ => rfl)
                                                              (fun h => absurd h
                                                              (by simp))
                                                              fh env_arm
                                                              (HFlow.value
                                                              u_arm) har prog f
                                                              (some bId)
                                                              ⟨nextB + 2,
                                                              [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                              lr.term⟩ F''
                                                              hsub_e hnodf
                                                              hfindJ fuelB (2 +
                                                              max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB el) hg_e
                                                              u_arm).1 rfl)
                                                          rw [hEdef] at heq_arm
                                                          rw [hrho_e] at hrel_arm
                                                          have hrep :
                                                              ((HFlow.value
                                                              (.lit accH)).replace
                                                              (.lit w_arm)) =
                                                              HFlow.value
                                                              (.lit w_arm) :=
                                                            rfl
                                                          rw [hu_arm, hrep] at hrun
                                                          have hfrL : FreshAbove
                                                              ρ le.supply :=
                                                            FreshAbove.mono ρ
                                                              supply le.supply
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              hmse)) hfresh
                                                          have hrel_m : RelEnv
                                                              env_arm ρ
                                                              (fenv_arr.env.update
                                                              le.supply
                                                              w_arm) := by
                                                            intro id u hlook
                                                            obtain ⟨w0, hlookH,
                                                              hreg0⟩ :=
                                                              hrel_arm id u
                                                              hlook
                                                            have hu : u <
                                                                le.supply :=
                                                              hfrL id u
                                                              (rhoLookup_some_mem
                                                              ρ id u hlook)
                                                            have hne : u ≠
                                                                le.supply :=
                                                              Nat.ne_of_lt hu
                                                            refine ⟨w0, hlookH,
                                                              ?_⟩
                                                            have hupd :
                                                                (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                                fenv_arr.env
                                                                u := by
                                                              simp [Env.update,
                                                                hne]
                                                            show (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                              some w0
                                                            rw [hupd]
                                                            exact hreg0
                                                          have hreg_m :
                                                              (⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :
                                                              FullEnv).env
                                                              le.supply =
                                                              some w_arm := by
                                                            simp [Env.update]
                                                          have hf_r : FreshAbove
                                                              ρ (le.supply +
                                                              1) :=
                                                            FreshAbove.mono ρ
                                                              supply
                                                              (le.supply + 1)
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              (Nat.le_trans hmse
                                                              (Nat.le_succ _))))
                                                              hfresh
                                                          have hlast_r :
                                                              le.supply <
                                                              le.supply + 1 :=
                                                            Nat.lt_succ_self _
                                                          have hsub_r : ∀ b ∈
                                                              lr.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lr
                                                              hb)
                                                          cases F' with
                                                          | zero =>
                                                              have hB1r :
                                                                  blockBound
                                                                  fuelB rest ≥
                                                                  1 := by
                                                                rw [blockBound]
                                                                omega
                                                              exact absurd hge
                                                                (by omega)
                                                          | succ F1 =>
                                                              have happ_J :
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitE)
                                                                  fenv_arr
                                                                  ([.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs) =
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitE)
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  lr.instrs := by
                                                                simp only
                                                                  [List.cons_append,
                                                                  List.nil_append]
                                                                rw [execInstrsFullFromIn_eq,
                                                                  execInstrsFullFromIn_eq,
                                                                  execInstrsFullFrom_phi_miss
                                                                  _ _ _ _ _ _
                                                                  (Ne.symm
                                                                  hne_pe),
                                                                  execInstrsFullFrom_phi_hit
                                                                  _ _ _ _ _ _
                                                                  rfl,
                                                                  hreg_arr]
                                                              have hJeq :
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitE)
                                                                  ⟨nextB + 2,
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  fenv_arr =
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitE)
                                                                  ⟨nextB + 2,
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩ :=
                                                                execBlockFromIn_instrs_prefix
                                                                  prog F1 f
                                                                  (some exitE)
                                                                  (nextB + 2)
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val]
                                                                  lr.instrs
                                                                  lr.term
                                                                  fenv_arr
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  happ_J
                                                              have hg_r : F1 + 1 ≥
                                                                  blockBound
                                                                  fuelB rest :=
                                                                Nat.le_trans hCege
                                                                  hge
                                                              intro u
                                                              have hfb' : fh ≤ fuelB := by omega
                                                              have hltB' : nextB + 2 < le.next := by
                                                                have h1 : nextB + 3 ≤ lt.next := hmnt
                                                                have h2 : lt.next ≤ le.next := hmne
                                                                omega
                                                              have hihr := ih
                                                                (nextB + 2) ρ
                                                                (le.supply + 1)
                                                                le.next
                                                                le.supply true
                                                                lr hr hrs hf_r
                                                                hlast_r hltB' w_arm
                                                                env_arm
                                                                ⟨fenv_arr.env.update
                                                                le.supply w_arm,
                                                                fenv_arr.store⟩
                                                                hrel_m hreg_m fh
                                                                henv' out hrun
                                                                prog f
                                                                (some exitE)
                                                                (F1 + 1) hsub_r
                                                                hnodf fuelB hg_r hfb'
                                                                u
                                                              refine ⟨?_, ?_⟩
                                                              · intro hout
                                                                obtain ⟨w_u, hu,
                                                                    heq_rest⟩ :=
                                                                  hihr.1 hout
                                                                exact ⟨w_u, hu,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                              · intro e_ret hout2
                                                                obtain ⟨w_e, hu_e,
                                                                    heq_rest⟩ :=
                                                                  hihr.2 e_ret
                                                                    hout2
                                                                exact ⟨w_e, hu_e,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                      | returned e_arm =>
                                                          simp only [] at hrun
                                                          have hout_r : out =
                                                              .returned e_arm :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_r] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            have hret_e : e_ret =
                                                                e_arm :=
                                                              (HFlow.returned.inj
                                                                (hout_r.symm.trans
                                                                hout2)).symm
                                                            have hregCb_r :
                                                                fenvC.env vc =
                                                                some
                                                                (.bool false) := by
                                                              have hww :
                                                                  (.bool false) =
                                                                  wC :=
                                                                HIR.Expr.lit.inj
                                                                  hrC
                                                              rw [hww]
                                                              exact hregC
                                                            have hbool_r :
                                                                fenvC.boolOf vc =
                                                                some false :=
                                                              boolOf_of_lit
                                                                fenvC vc false
                                                                hregCb_r
                                                            have hentry_r :
                                                                execBlockFromIn
                                                                prog (F'' + 1)
                                                                f prev ⟨bId, ic,
                                                                .branch vc
                                                                nextB
                                                                (nextB + 1)⟩
                                                                fenv =
                                                                execBlockFromIn
                                                                prog F'' f
                                                                (some bId)
                                                                ⟨nextB + 1,
                                                                le.instrs,
                                                                le.term⟩
                                                                fenvC :=
                                                              execBlockFromIn_branch_false
                                                                prog F'' f prev
                                                                bId ic vc nextB
                                                                (nextB + 1)
                                                                fenv fenvC
                                                                ⟨nextB + 1,
                                                                le.instrs,
                                                                le.term⟩
                                                                hexec_ic
                                                                hbool_r hfindE
                                                            have hsub_er : ∀ b ∈
                                                                le.blocks,
                                                                b ∈ f.blocks :=
                                                              fun b hb => hsub _
                                                                (if_asm_mem_of_le
                                                                hb)
                                                            have hCege_r : (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) ≥
                                                                blockBound fuelB
                                                                rest := by
                                                              have hBrest :
                                                                  blockBound
                                                                  fuelB rest =
                                                                  1 +
                                                                  armBlockBound
                                                                  fuelB rest :=
                                                                rfl
                                                              omega
                                                            have hg_er : F'' ≥
                                                                blockBound fuelB
                                                                el + (2 + max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) := by
                                                              have hBel :
                                                                  blockBound
                                                                  fuelB el = 1 +
                                                                  armBlockBound
                                                                  fuelB el :=
                                                                rfl
                                                              omega
                                                            obtain ⟨w_e, heq,
                                                                hexec_arm⟩ :=
                                                              ((lowerStmtsCFG_arm_total
                                                                budget (nextB + 1)
                                                                (nextB + 2) ρ
                                                                lt.supply lt.next
                                                                lastVal false none el
                                                                le he hael hf_e
                                                                hlast_e .unit
                                                                henv fenvC hrelC
                                                                (fun _ => rfl)
                                                                (fun h => absurd h
                                                                (by simp))
                                                                fh env_arm
                                                                (HFlow.returned
                                                                e_arm)
                                                                har prog f
                                                                (some bId)
                                                                ⟨nextB + 2,
                                                                [.phi le.supply
                                                                exitT lt.val,
                                                                .phi le.supply
                                                                exitE le.val] ++
                                                                lr.instrs,
                                                                lr.term⟩ F''
                                                                hsub_er hnodf
                                                                hfindJ fuelB (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) hg_er
                                                                (.lit .unit)).2
                                                                e_arm rfl)
                                                            exact ⟨w_e,
                                                              hret_e.trans heq,
                                                              hentry_r.trans
                                                              hexec_arm⟩
                                                      | stuck =>
                                                          simp only [] at hrun
                                                          have hout_s : out =
                                                              .stuck :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_s] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_s] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | broke =>
                                                          simp only [] at hrun
                                                          have hout_b : out =
                                                              .broke :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_b] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_b] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | continued =>
                                                          simp only [] at hrun
                                                          have hout_c : out =
                                                              .continued :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_c] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_c] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                          | int _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | string _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | pointer _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | float _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | unit =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | undef =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | some _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | none =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | ok _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | err _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | tuple_ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | array_ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | loc _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | closure _ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
          | breakStmt =>
              simp only [lowerStmtsCFG] at h
              intro accH henv fenv hrel hacc fuelH henv' out hrun prog f
                prev F hsub hnodf fuelB hg hfb u
              refine ⟨?_, ?_⟩
              · intro hout
                simp at h
              · intro e_ret hout2
                simp at h
          | continueStmt =>
              simp only [lowerStmtsCFG] at h
              intro accH henv fenv hrel hacc fuelH henv' out hrun prog f
                prev F hsub hnodf fuelB hg hfb u
              refine ⟨?_, ?_⟩
              · intro hout
                simp at h
              · intro e_ret hout2
                simp at h
          | whileStmt c body hstr hlt hbody =>
              simp only [lowerStmtsCFG] at h
              cases hm : mkCarried ρ supply
                  ((dedupIds (assignedIds body)).filterMap
                    (fun id => (rhoLookup ρ id).map (fun _ => id))) with
              | none => rw [hm] at h; simp at h
              | some p =>
                  obtain ⟨carried, sA, ρb⟩ := p
                  rw [hm] at h
                  simp only [] at h
                  cases hc : lowerExpr ρb sA c with
                  | none => rw [hc] at h; simp at h
                  | some q =>
                      obtain ⟨vc, ic, s1⟩ := q
                      rw [hc] at h
                      simp only [] at h
                      cases hb : lowerStmtsCFG (nextB + 2) (some nextB) false
                          ρb (s1 + 1) (nextB + 3) s1 true
                          (loop := some ⟨nextB, nextB + 1, carried⟩)
                          body with
                      | none => rw [hb] at h; simp at h
                      | some lb =>
                          rw [hb] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 1) none false
                              ρb (lb.supply + 1) lb.next lb.supply true none
                              rest with
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
                                  obtain rfl := Option.some.inj h
                                  intro accH henv fenv hrel hacc fuelH henv'
                                    out hrun prog f prev F hsub hnodf fuelB
                                    hg hfb u
                                  have hbb : blockBound fuelB
                                      (.whileLoop c body :: rest) =
                                      1 + ((2 + armBlockBound fuelB body) *
                                        (fuelB + 1) +
                                        armBlockBound fuelB rest) := by
                                    rw [blockBound, armBlockBound_while]
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    cases fuelH with
                                    | zero =>
                                        have hz : runHIRStmts 0 henv
                                            (.whileLoop c body :: rest)
                                            (.value (.lit accH)) =
                                            (.stuck, henv) := rfl
                                        rw [hz] at hrun
                                        have hst : out = .stuck :=
                                          (congrArg Prod.fst hrun).symm
                                        rw [hst] at hout
                                        exact absurd hout (by simp)
                                    | succ fh =>
                                        have hstep : runHIRStmts (fh + 1)
                                            henv
                                            (.whileLoop c body :: rest)
                                            (.value (.lit accH)) =
                                            (match runHIRWhile fh henv c body with
                                             | (HFlow.value uu, env'') =>
                                                 runHIRStmts fh env'' rest
                                                   (HFlow.replace
                                                     (HFlow.value
                                                     (.lit accH)) uu)
                                             | (ff, env'') =>
                                                 (ff, env'')) := rfl
                                        rw [hstep] at hrun
                                        cases hw : runHIRWhile fh henv c
                                            body with
                                        | mk res envL =>
                                            rw [hw] at hrun
                                            cases res with
                                            | value v =>
                                                simp only [] at hrun
                                                have hv : v = .lit .unit :=
                                                  runHIRWhile_value_unit fh
                                                    henv c body v envL hw
                                                rw [hv] at hrun hw
                                                simp only
                                                  [HFlow.replace] at hrun
                                                have hfle : fh ≤ fuelB := by
                                                  omega
                                                have hF : F ≥ 1 +
                                                    ((2 + armBlockBound
                                                      fuelB body) *
                                                      (fh + 1) +
                                                      armBlockBound fuelB
                                                      rest) := by
                                                  have h1 : fh + 1 ≤
                                                      fuelB + 1 := by omega
                                                  have h2 : (2 +
                                                      armBlockBound fuelB
                                                      body) * (fh + 1) ≤
                                                      (2 + armBlockBound
                                                      fuelB body) *
                                                      (fuelB + 1) :=
                                                    Nat.mul_le_mul_left
                                                      _ h1
                                                  omega
                                                obtain ⟨hfrX, hloopV,
                                                    hloopR⟩ :=
                                                  whileLoop_correct budget
                                                    bId nextB ρ supply c body
                                                    rest carried sA ρb vc ic
                                                    s1 lb lr phis hm hc hb hr
                                                    hp hbody hrs hstr hlt hfresh hltB fh henv fenv hrel
                                                    (HFlow.value (.lit .unit)) envL hw prog f prev F
                                                    hsub hnodf fuelB hF
                                                obtain ⟨F', fenvX, hleF, hgeF,
                                                    hexit, hrelX, haccX⟩ :=
                                                  hloopV rfl
                                                have hfb'' : fh ≤ fuelB := by
                                                  omega
                                                have hsub_r : ∀ b ∈ lr.blocks,
                                                    b ∈ f.blocks :=
                                                  fun b hb => hsub _
                                                    (List.mem_append_right _
                                                      hb)
                                                have hg'_r : F' ≥ blockBound
                                                    fuelB rest := by
                                                  have hbr : blockBound fuelB
                                                      rest =
                                                      1 + armBlockBound
                                                      fuelB rest := by
                                                    rw [blockBound]
                                                  omega
                                                have hmnb : nextB + 3 ≤ lb.next :=
                                                  (lowerStmtsCFG_loopBody_inv budget _ _ _ _ _ _ _ _ _ _ hb hbody).1
                                                have hltB' : nextB + 1 < lb.next := by omega
                                                obtain ⟨w_u, hu, heq_rest⟩ :=
                                                  (ih (nextB + 1) ρb
                                                    (lb.supply + 1) lb.next
                                                    lb.supply true lr hr hrs
                                                    hfrX
                                                    (Nat.lt_succ_self _)
                                                    hltB'
                                                    .unit envL fenvX hrelX haccX fh
                                                    henv' out hrun prog f
                                                    (some (nextB + 1)) F'
                                                    hsub_r hnodf fuelB hg'_r
                                                    hfb'' u).1 hout
                                                refine ⟨w_u, hu, ?_⟩
                                                exact hexit.trans heq_rest
                                            | returned e =>
                                                simp only [] at hrun
                                                have hret : out =
                                                    .returned e :=
                                                  (congrArg Prod.fst
                                                    hrun).symm
                                                rw [hret] at hout
                                                exact absurd hout (by simp)
                                            | broke =>
                                                exact ((runHIRWhile_outcome fh
                                                  henv c body (.broke) envL
                                                  hw).1 rfl).elim
                                            | continued =>
                                                exact ((runHIRWhile_outcome fh
                                                  henv c body (.continued) envL
                                                  hw).2 rfl).elim
                                            | stuck =>
                                                simp only [] at hrun
                                                have hst : out = .stuck :=
                                                  (congrArg Prod.fst
                                                    hrun).symm
                                                rw [hst] at hout
                                                exact absurd hout (by simp)
                                  · intro e_ret hout2
                                    cases fuelH with
                                    | zero =>
                                        have hz : runHIRStmts 0 henv
                                            (.whileLoop c body :: rest)
                                            (.value (.lit accH)) =
                                            (.stuck, henv) := rfl
                                        rw [hz] at hrun
                                        have hst : out = .stuck :=
                                          (congrArg Prod.fst hrun).symm
                                        rw [hst] at hout2
                                        exact absurd hout2 (by simp)
                                    | succ fh =>
                                        have hstep : runHIRStmts (fh + 1)
                                            henv
                                            (.whileLoop c body :: rest)
                                            (.value (.lit accH)) =
                                            (match runHIRWhile fh henv c body with
                                             | (HFlow.value uu, env'') =>
                                                 runHIRStmts fh env'' rest
                                                   (HFlow.replace
                                                     (HFlow.value
                                                     (.lit accH)) uu)
                                             | (ff, env'') =>
                                                 (ff, env'')) := rfl
                                        rw [hstep] at hrun
                                        cases hw : runHIRWhile fh henv c
                                            body with
                                        | mk res envL =>
                                            rw [hw] at hrun
                                            cases res with
                                            | value v =>
                                                simp only [] at hrun
                                                have hv : v = .lit .unit :=
                                                  runHIRWhile_value_unit fh
                                                    henv c body v envL hw
                                                rw [hv] at hrun hw
                                                simp only
                                                  [HFlow.replace] at hrun
                                                have hfle : fh ≤ fuelB := by
                                                  omega
                                                have hF : F ≥ 1 +
                                                    ((2 + armBlockBound
                                                      fuelB body) *
                                                      (fh + 1) +
                                                      armBlockBound fuelB
                                                      rest) := by
                                                  have h1 : fh + 1 ≤
                                                      fuelB + 1 := by omega
                                                  have h2 : (2 +
                                                      armBlockBound fuelB
                                                      body) * (fh + 1) ≤
                                                      (2 + armBlockBound
                                                      fuelB body) *
                                                      (fuelB + 1) :=
                                                    Nat.mul_le_mul_left
                                                      _ h1
                                                  omega
                                                obtain ⟨hfrX, hloopV,
                                                    hloopR⟩ :=
                                                  whileLoop_correct budget
                                                    bId nextB ρ supply c body
                                                    rest carried sA ρb vc ic
                                                    s1 lb lr phis hm hc hb hr
                                                    hp hbody hrs hstr hlt hfresh hltB fh henv fenv hrel
                                                    (HFlow.value (.lit .unit)) envL hw prog f prev F
                                                    hsub hnodf fuelB hF
                                                obtain ⟨F', fenvX, hleF, hgeF,
                                                    hexit, hrelX, haccX⟩ :=
                                                  hloopV rfl
                                                have hfb'' : fh ≤ fuelB := by
                                                  omega
                                                have hsub_r : ∀ b ∈ lr.blocks,
                                                    b ∈ f.blocks :=
                                                  fun b hb => hsub _
                                                    (List.mem_append_right _
                                                      hb)
                                                have hg'_r : F' ≥ blockBound
                                                    fuelB rest := by
                                                  have hbr : blockBound fuelB
                                                      rest =
                                                      1 + armBlockBound
                                                      fuelB rest := by
                                                    rw [blockBound]
                                                  omega
                                                have hmnb : nextB + 3 ≤ lb.next :=
                                                  (lowerStmtsCFG_loopBody_inv budget _ _ _ _ _ _ _ _ _ _ hb hbody).1
                                                have hltB' : nextB + 1 < lb.next := by omega
                                                obtain ⟨w_e, heq, heq_rest⟩ :=
                                                  (ih (nextB + 1) ρb
                                                    (lb.supply + 1) lb.next
                                                    lb.supply true lr hr hrs
                                                    hfrX
                                                    (Nat.lt_succ_self _)
                                                    hltB'
                                                    .unit envL fenvX hrelX haccX fh
                                                    henv' out hrun prog f
                                                    (some (nextB + 1)) F'
                                                    hsub_r hnodf fuelB hg'_r
                                                    hfb'' u).2 e_ret hout2
                                                refine ⟨w_e, heq, ?_⟩
                                                exact hexit.trans heq_rest
                                            | returned e =>
                                                simp only [] at hrun
                                                have hret : out =
                                                    .returned e :=
                                                  (congrArg Prod.fst
                                                    hrun).symm
                                                rw [hret] at hout2
                                                have hee : e = e_ret :=
                                                  HFlow.returned.inj hout2
                                                have hfle_r : fh ≤ fuelB := by
                                                  omega
                                                have hF_r : F ≥ 1 +
                                                    ((2 + armBlockBound
                                                      fuelB body) *
                                                      (fh + 1) +
                                                      armBlockBound fuelB
                                                      rest) := by
                                                  have h1 : fh + 1 ≤
                                                      fuelB + 1 := by omega
                                                  have h2 : (2 +
                                                      armBlockBound fuelB
                                                      body) * (fh + 1) ≤
                                                      (2 + armBlockBound
                                                      fuelB body) *
                                                      (fuelB + 1) :=
                                                    Nat.mul_le_mul_left
                                                      _ h1
                                                  omega
                                                obtain ⟨hfrX, hloopV,
                                                    hloopR⟩ :=
                                                  whileLoop_correct budget
                                                    bId nextB ρ supply c body
                                                    rest carried sA ρb vc ic
                                                    s1 lb lr phis hm hc hb hr
                                                    hp hbody hrs hstr hlt hfresh hltB fh henv fenv hrel
                                                    (HFlow.returned e) envL hw prog f prev F
                                                    hsub hnodf fuelB hF_r
                                                obtain ⟨w_e, heq, hexec⟩ :=
                                                  hloopR e rfl
                                                rw [hee] at heq
                                                exact ⟨w_e, heq, hexec⟩
                                            | broke =>
                                                exact ((runHIRWhile_outcome fh
                                                  henv c body (.broke) envL
                                                  hw).1 rfl).elim
                                            | continued =>
                                                exact ((runHIRWhile_outcome fh
                                                  henv c body (.continued) envL
                                                  hw).2 rfl).elim
                                            | stuck =>
                                                simp only [] at hrun
                                                have hst : out = .stuck :=
                                                  (congrArg Prod.fst
                                                    hrun).symm
                                                rw [hst] at hout2
                                                exact absurd hout2 (by simp)
      | returnStmt e rest hstr _ =>
          intro accH henv fenv hrel hacc fuelH henv' out hrun prog f prev F
            hsub hnodf fuelB hg hfb
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              intro u
              refine ⟨?_, ?_⟩
              · intro hout
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.returnStmt e :: rest) (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => (.returned v, henv)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck :=
                          (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        have hret : out = .returned r :=
                          (congrArg Prod.fst hrun).symm
                        rw [hret] at hout
                        exact absurd hout (by simp)
              · intro e_ret hout2
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout2
                    exact absurd hout2 (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.returnStmt e :: rest) (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => (.returned v, henv)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck :=
                          (congrArg Prod.fst hrun).symm
                        rw [hst] at hout2
                        exact absurd hout2 (by simp)
                    | some r =>
                        rw [hev] at hrun
                        have hret : out = .returned r :=
                          (congrArg Prod.fst hrun).symm
                        rw [hret] at hout2
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2,
                            hrE2, hregE⟩ :=
                          lower_total.1 ρ supply e v ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        have hrr : r = e_ret := HFlow.returned.inj hout2
                        have heq : e_ret = .lit wE := hrr.symm ▸ hrE
                        have hnp : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                        have hexec : execInstrsFullFromIn prog prev fenv ie
                            = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _
                            hnp]
                          exact hexec1
                        have hbb : blockBound fuelB (.returnStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)
                              (fun c body h => by cases h)]
                        have h1 : blockBound fuelB rest ≥ 1 := by
                          rw [blockBound]; omega
                        cases F with
                        | zero => omega
                        | succ F' =>
                            refine ⟨wE, heq, ?_⟩
                            have hLHS : execBlockFromIn prog (F' + 1) f prev
                                    ⟨bId, ie, .return_ v⟩ fenv =
                                    fenv1.env v := by
                              have hret' : execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, ie, .return_ v⟩ fenv =
                                  (match execInstrsFullFromIn prog prev fenv
                                      ie with
                                   | none => (none : Option Value)
                                   | some g => g.env v) := rfl
                              rw [hret', hexec]
                            have hww : wE = wE2 :=
                              HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                            rw [hLHS, hww]
                            exact hregE

end Morph.HIRToMIRCorrect
