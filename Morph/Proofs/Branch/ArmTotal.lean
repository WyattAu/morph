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

/-!
# Stage C arm worker: `lowerStmtsCFG_arm_total` and its executor groundwork

Second proof leaf out of the `HIRToMIRBranch` monolith: the fallthrough arm
worker plus the carried-register / header-phi executor lemmas the later
`broke`/`continued`/`loopBody_run` workers cite (`lowerExpr_result_ge`,
`lowerBlock_result_ge`, the `mkCarried_*` family, `lowerStmtsCFG_loopBody_excl`,
`mkHeaderPhis_*`, `trampPhis_exec_miss`, the `headerGroup`/`headerPhis`
family, `carryCopies_exec`). Moved verbatim; the monolith imports this back.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Arm worker: executing an arm segment's entry block runs the HIR arm. On
fallthrough the run arrives at the join block with the arm's value in its
register and both environments related; on `return` the entry block itself
returns the value. The conclusion is equational (arrival state
existential, fuel squeezed between the remaining budget and the caller's
`C`) so the caller — the body worker's `if` case — can chain it into the
rest segment without any continuation hypothesis: the join's phis and the
rest are the caller's business, discharged with the exit formula below.

The HIR run is over the arm alone (arms always run from `unit`), so no
append-composition lemma is needed: the caller already inverts the whole
run into arm-run and rest-run. The two `hasVal` premises say exactly when
the register file is known to hold the accumulator: a produced value is
present, and a valueless arm runs from `unit` (loop 176 — this is what
makes the empty-arm equation close). -/
theorem lowerStmtsCFG_arm_total (budget : Nat) :
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
          RelEnv henv' L.ρ fenv_arr.env ∧ fenv_arr.env L.val = some w_u ∧
          (∀ r, r < supply → fenv_arr.env r = fenv.env r)) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
        execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
          some w_e) := by
  intro bId j ρ supply nextB lastVal hasVal loop ss L h hss hfresh hlast
  induction hss generalizing bId j ρ supply nextB lastVal hasVal loop L with
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
            have hbb : blockBound fuelB ([] : List HIR.Stmt) = 1 := by
              simp [blockBound]
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
                | zero => omega
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
                      Nat.le_succ _, ?_, ?_, ?_, ?_, ?_⟩
                    · omega
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
                    · intro r hr
                      simp [Env.update, Nat.ne_of_lt hr]
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
                        ?_, ?_, ?_⟩
                      · have hbb : blockBound fuelB ([] : List HIR.Stmt)
                            = 1 := by simp [blockBound]
                        omega
                      · dsimp only
                        exact execBlockFromIn_goto prog F' f prev bId [] j
                          fenv fenv jblock rfl hfind
                      · rw [← h2]; exact hrel
                      · exact hreg hv
                      · intro r _; rfl
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
                            have hpl : ∀ r, r < supply → fenv1.env r = fenv.env r :=
                              fun r hr => lower_preserv_regs ρ supply e v0 ie s1
                                he fenv fenv1 hexec1 r hr
                            obtain ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                                hrel_arr, hreg_arr, hpres_arr⟩ :=
                              ((ih bId j ρ s1 nextB v0 true loop Lr hr hf1
                                hlast1 wE henv fenv1 hrel1
                                (fun hh => absurd hh (by simp)) (fun _ => hregE')
                                fh henv' out hrun prog f prev jblock (F'' + 1)
                                hsub' hnodf hfind fuelB C hg' u).1 hout)
                            refine ⟨w_u, hu, F', fenv_arr, hle, hge,
                              hLHS.trans heq_rest, hrel_arr, hreg_arr, ?_⟩
                            intro r hr
                            rw [hpres_arr r (Nat.lt_of_lt_of_le hr hs1)]
                            exact hpl r hr
      · intro e_ret hout
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
                            obtain ⟨w_e, hu_e, heq_rest⟩ :=
                              ((ih bId j ρ s1 nextB v0 true loop Lr hr hf1
                                hlast1 wE henv fenv1 hrel1
                                (fun hh => absurd hh (by simp)) (fun _ => hregE')
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
                    hrel_arr, hreg_arr, hpres_arr⟩ :=
                  ((ih bId j ρ supply nextB lastVal hasVal loop Lr hr hfresh
                    hlast accH henv fenv hrel hval0 hreg fh henv' out hrun
                    prog f prev jblock F hsub hnodf hfind fuelB C hg'
                    u).1 hout)
                exact ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                  hrel_arr, hreg_arr, hpres_arr⟩
      · intro e_ret hout
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
                  ((ih bId j ρ supply nextB lastVal hasVal loop Lr hr hfresh
                    hlast accH henv fenv hrel hval0 hreg fh henv' out hrun
                    prog f prev jblock F hsub hnodf hfind fuelB C hg'
                    u).2 e_ret hout)
                exact ⟨w_e, hu_e, heq_rest⟩
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
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
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            omega
                          · intro e hout
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
                                                      hreg_arr, hpres_arm⟩ :=
                                                    ((iht nextB (nextB + 2) ρ s1 (nextB + 3) lastVal false loop lt ht hf1 hlast1 .unit
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
                                                      intro u
                                                      have hihr := ihr
                                                        (nextB + 2) j ρ
                                                        (le.supply + 1) le.next
                                                        le.supply true loop lr hr
                                                        hf_r hlast_r w_arm
                                                        env_arm
                                                        ⟨fenv_arr.env.update
                                                          le.supply w_arm,
                                                          fenv_arr.store⟩
                                                        hrel_m
                                                        (fun h => absurd h
                                                          (by simp))
                                                        (fun _ => hreg_m) fh
                                                        henv' out hrun prog f
                                                        (some exitT) jblock
                                                        (F1 + 1) hsub_r hnodf
                                                        hfind fuelB C hg_r u
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        obtain ⟨w_u, hu, F2,
                                                            fenv_arr2, hle2,
                                                            hge2, heq_rest,
                                                            hrel_final,
                                                            hreg_final,
                                                            hpres_tail⟩ :=
                                                          (hihr.1 hout)
                                                        rw [if_assembly_exit
                                                          rfl]
                                                        refine ⟨w_u, hu, F2,
                                                          fenv_arr2,
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
                                                          hreg_final, ?_⟩
                                                        have hpc : ∀ r, r < supply →
                                                            fenvC.env r = fenv.env r :=
                                                          fun r hr =>
                                                            lower_preserv_regs ρ supply c vc ic s1 heC
                                                              fenv fenvC hexecC r hr
                                                        have hle_sup : supply ≤ le.supply :=
                                                          Nat.le_trans hs1
                                                            (Nat.le_trans hmst hmse)
                                                        intro r hr
                                                        have e1 : fenvC.env r = fenv.env r :=
                                                          hpc r hr
                                                        have e2 : fenv_arr.env r = fenvC.env r :=
                                                          hpres_arm r
                                                            (Nat.lt_of_lt_of_le hr hs1)
                                                        have e3 : (fenv_arr.env.update le.supply
                                                            w_arm) r = fenv_arr.env r := by
                                                          simp [Env.update,
                                                            Nat.ne_of_lt
                                                              (Nat.lt_of_lt_of_le hr hle_sup)]
                                                        have e4 : fenv_arr2.env r =
                                                            (fenv_arr.env.update le.supply
                                                            w_arm) r :=
                                                          hpres_tail r
                                                            (Nat.lt_of_lt_of_le hr
                                                            (Nat.le_trans hle_sup
                                                            (Nat.le_succ _)))
                                                        exact e4.trans (e3.trans (e2.trans e1))
                                                      · intro e_ret hout2
                                                        obtain ⟨w_e, hu_e,
                                                            heq_rest⟩ :=
                                                          (hihr.2 e_ret hout2)
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
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    have hret_e : e_ret =
                                                        e_arm :=
                                                      (HFlow.returned.inj
                                                        (hout_r.symm.trans
                                                          hout2)).symm
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
                                                    have hentry_r : execBlockFromIn
                                                        prog (F'' + 1) f prev
                                                        ⟨bId, ic, .branch vc
                                                          nextB
                                                          (nextB + 1)⟩ fenv =
                                                        execBlockFromIn prog F''
                                                          f (some bId)
                                                          ⟨nextB, lt.instrs,
                                                            lt.term⟩ fenvC :=
                                                      execBlockFromIn_branch_true
                                                        prog F'' f prev bId ic
                                                        vc nextB (nextB + 1)
                                                        fenv fenvC
                                                        ⟨nextB, lt.instrs,
                                                          lt.term⟩ hexec_ic
                                                        hbool_r hfindT
                                                    have hsub_tr : ∀ b ∈ lt.blocks,
                                                        b ∈ f.blocks :=
                                                      fun b hb => hsub _
                                                        (if_asm_mem_of_lt hb)
                                                    have hC'ge_r : (2 + max
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
                                                    have hg_tr : F'' ≥ blockBound
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
                                                    obtain ⟨w_e, heq,
                                                        hexec_arm⟩ :=((iht nextB (nextB + 2) ρ s1 (nextB + 3) lastVal false loop lt ht hf1 hlast1 .unit henv
                                                        fenvC hrelC
                                                        (fun _ => rfl)
                                                        (fun h => absurd h
                                                          (by simp))
                                                        fh env_arm
                                                        (HFlow.returned e_arm)
                                                        har prog f (some bId)
                                                        ⟨nextB + 2,
                                                          [.phi le.supply exitT
                                                            lt.val,
                                                           .phi le.supply exitE
                                                            le.val] ++
                                                          lr.instrs,
                                                          lr.term⟩ F'' hsub_tr
                                                        hnodf hfindJ fuelB (2 +
                                                        max (armBlockBound
                                                        fuelB th)
                                                        (armBlockBound
                                                          fuelB el) +
                                                        armBlockBound fuelB
                                                          rest -
                                                        armBlockBound fuelB th +
                                                        C) hg_tr
                                                        (.lit .unit)).2 e_arm
                                                        rfl)
                                                    exact ⟨w_e, hret_e.trans
                                                      heq, hentry_r.trans
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
                                                    exact absurd hout (by simp)
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
                                                    exact absurd hout (by simp)
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
                                                    exact absurd hout (by simp)
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
                                                      hreg_arr, hpres_arm⟩ :=
                                                    ((ihe (nextB + 1) (nextB + 2) ρ lt.supply lt.next lastVal false loop le he hf_e hlast_e .unit
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
                                                      intro u
                                                      have hihr := ihr
                                                        (nextB + 2) j ρ
                                                        (le.supply + 1) le.next
                                                        le.supply true loop lr hr
                                                        hf_r hlast_r w_arm
                                                        env_arm
                                                        ⟨fenv_arr.env.update
                                                          le.supply w_arm,
                                                          fenv_arr.store⟩
                                                        hrel_m
                                                        (fun h => absurd h
                                                          (by simp))
                                                        (fun _ => hreg_m) fh
                                                        henv' out hrun prog f
                                                        (some exitE) jblock
                                                        (F1 + 1) hsub_r hnodf
                                                        hfind fuelB C hg_r u
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        obtain ⟨w_u, hu, F2,
                                                            fenv_arr2, hle2,
                                                            hge2, heq_rest,
                                                            hrel_final,
                                                            hreg_final,
                                                            hpres_tail⟩ :=
                                                          (hihr.1 hout)
                                                        rw [if_assembly_exit
                                                          rfl]
                                                        refine ⟨w_u, hu, F2,
                                                          fenv_arr2,
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
                                                          hreg_final, ?_⟩
                                                        have hpc : ∀ r, r < supply →
                                                            fenvC.env r = fenv.env r :=
                                                          fun r hr =>
                                                            lower_preserv_regs ρ supply c vc ic s1 heC
                                                              fenv fenvC hexecC r hr
                                                        have hle_sup : supply ≤ le.supply :=
                                                          Nat.le_trans hs1
                                                            (Nat.le_trans hmst hmse)
                                                        intro r hr
                                                        have e1 : fenvC.env r = fenv.env r :=
                                                          hpc r hr
                                                        have e2 : fenv_arr.env r = fenvC.env r :=
                                                          hpres_arm r
                                                            (Nat.lt_of_lt_of_le hr (Nat.le_trans hs1 hmst))
                                                        have e3 : (fenv_arr.env.update le.supply
                                                            w_arm) r = fenv_arr.env r := by
                                                          simp [Env.update,
                                                            Nat.ne_of_lt
                                                              (Nat.lt_of_lt_of_le hr hle_sup)]
                                                        have e4 : fenv_arr2.env r =
                                                            (fenv_arr.env.update le.supply
                                                            w_arm) r :=
                                                          hpres_tail r
                                                            (Nat.lt_of_lt_of_le hr
                                                            (Nat.le_trans hle_sup
                                                            (Nat.le_succ _)))
                                                        exact e4.trans (e3.trans (e2.trans e1))
                                                      · intro e_ret hout2
                                                        obtain ⟨w_e, hu_e,
                                                            heq_rest⟩ :=
                                                          (hihr.2 e_ret hout2)
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
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    have hret_e : e_ret =
                                                        e_arm :=
                                                      (HFlow.returned.inj
                                                        (hout_r.symm.trans
                                                          hout2)).symm
                                                    have hregCb_r : fenvC.env
                                                        vc =
                                                        some
                                                        (.bool false) := by
                                                      have hww : (.bool false) =
                                                          wC :=
                                                        HIR.Expr.lit.inj hrC
                                                      rw [hww]
                                                      exact hregC
                                                    have hbool_r : fenvC.boolOf
                                                        vc = some false :=
                                                      boolOf_of_lit fenvC vc
                                                        false hregCb_r
                                                    have hentry_r : execBlockFromIn
                                                        prog (F'' + 1) f prev
                                                        ⟨bId, ic, .branch vc
                                                          nextB
                                                          (nextB + 1)⟩ fenv =
                                                        execBlockFromIn prog F''
                                                          f (some bId)
                                                          ⟨nextB + 1,
                                                            le.instrs,
                                                            le.term⟩ fenvC :=
                                                      execBlockFromIn_branch_false
                                                        prog F'' f prev bId ic
                                                        vc nextB (nextB + 1)
                                                        fenv fenvC
                                                        ⟨nextB + 1, le.instrs,
                                                          le.term⟩ hexec_ic
                                                        hbool_r hfindE
                                                    have hC'ge_r : (2 + max
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
                                                    have hg_er : F'' ≥ blockBound
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
                                                    obtain ⟨w_e, heq,
                                                        hexec_arm⟩ :=
                                                      ((ihe (nextB + 1)
                                                        (nextB + 2) ρ lt.supply
                                                        lt.next lastVal false
                                                        loop le he hf_e hlast_e
                                                        .unit henv fenvC hrelC
                                                        (fun _ => rfl)
                                                        (fun h => absurd h
                                                          (by simp))
                                                        fh env_arm
                                                        (HFlow.returned e_arm)
                                                        har prog f (some bId)
                                                        ⟨nextB + 2,
                                                          [.phi le.supply exitT
                                                            lt.val,
                                                           .phi le.supply exitE
                                                            le.val] ++
                                                          lr.instrs,
                                                          lr.term⟩ F'' hsub_e
                                                        hnodf hfindJ fuelB (2 +
                                                        max (armBlockBound
                                                        fuelB th)
                                                        (armBlockBound
                                                          fuelB el) +
                                                        armBlockBound fuelB
                                                          rest -
                                                        armBlockBound fuelB el +
                                                        C) hg_er
                                                        (.lit .unit)).2 e_arm
                                                        rfl)
                                                    exact ⟨w_e, hret_e.trans
                                                      heq, hentry_r.trans
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
                                                    exact absurd hout (by simp)
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
                                                    exact absurd hout (by simp)
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
                                                    exact absurd hout (by simp)
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
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        cases fuelH with
        | zero =>
            have hz : runHIRStmts 0 henv (.break :: rest)
                (.value (.lit accH)) = (.stuck, henv) := rfl
            rw [hz] at hrun
            have hst : out = .stuck := (congrArg Prod.fst hrun).symm
            rw [hst] at hout
            exact absurd hout (by simp)
        | succ fh =>
            have hstep : runHIRStmts (fh + 1) henv (.break :: rest)
                (.value (.lit accH)) = (.broke, henv) := rfl
            rw [hstep] at hrun
            have hst : out = .broke := (congrArg Prod.fst hrun).symm
            rw [hst] at hout
            exact absurd hout (by simp)
      · intro e_ret hout
        cases fuelH with
        | zero =>
            have hz : runHIRStmts 0 henv (.break :: rest)
                (.value (.lit accH)) = (.stuck, henv) := rfl
            rw [hz] at hrun
            have hst : out = .stuck := (congrArg Prod.fst hrun).symm
            rw [hst] at hout
            exact absurd hout (by simp)
        | succ fh =>
            have hstep : runHIRStmts (fh + 1) henv (.break :: rest)
                (.value (.lit accH)) = (.broke, henv) := rfl
            rw [hstep] at hrun
            have hst : out = .broke := (congrArg Prod.fst hrun).symm
            rw [hst] at hout
            exact absurd hout (by simp)
  | continueStmt rest _ =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        cases fuelH with
        | zero =>
            have hz : runHIRStmts 0 henv (.continue :: rest)
                (.value (.lit accH)) = (.stuck, henv) := rfl
            rw [hz] at hrun
            have hst : out = .stuck := (congrArg Prod.fst hrun).symm
            rw [hst] at hout
            exact absurd hout (by simp)
        | succ fh =>
            have hstep : runHIRStmts (fh + 1) henv (.continue :: rest)
                (.value (.lit accH)) = (.continued, henv) := rfl
            rw [hstep] at hrun
            have hst : out = .continued := (congrArg Prod.fst hrun).symm
            rw [hst] at hout
            exact absurd hout (by simp)
      · intro e_ret hout
        cases fuelH with
        | zero =>
            have hz : runHIRStmts 0 henv (.continue :: rest)
                (.value (.lit accH)) = (.stuck, henv) := rfl
            rw [hz] at hrun
            have hst : out = .stuck := (congrArg Prod.fst hrun).symm
            rw [hst] at hout
            exact absurd hout (by simp)
        | succ fh =>
            have hstep : runHIRStmts (fh + 1) henv (.continue :: rest)
                (.value (.lit accH)) = (.continued, henv) := rfl
            rw [hstep] at hrun
            have hst : out = .continued := (congrArg Prod.fst hrun).symm
            rw [hst] at hout
            exact absurd hout (by simp)


/-- Non-variable expressions allocate at or above the incoming supply:
literals take the supply itself, operations allocate above it. Variables read
below-supply registers, so `VarFree` excludes exactly the aliasing case.
Induction on `IsStraight`; the `block` case runs a nested list induction
using the outer IH for heads and the inner IH for tails. -/
theorem lowerExpr_result_ge (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (e : HIR.Expr) (v : ValId) (is : List Instr) (s' : Nat)
    (hstr : IsStraight e) (hvf : VarFree e)
    (h : lowerExpr ρ supply e = some (v, is, s')) : supply ≤ v := by
  induction hstr generalizing ρ supply v is s' with
  | var id =>
      cases hvf
  | lit val =>
      simp only [lowerExpr] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Nat.le_refl _
  | unop op e _ _ _ih =>
      simp only [lowerExpr] at h
      cases hto : toUnOp op with
      | none => rw [hto] at h; simp at h
      | some u =>
          cases he : lowerExpr ρ supply e with
          | none => rw [he, hto] at h; simp at h
          | some p =>
              obtain ⟨ve, ie, s⟩ := p
              rw [he] at h
              rw [hto] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact lower_mono.1 _ _ _ _ _ _ he
  | binop op a b _ _ _ _iha _ihb =>
      simp only [lowerExpr] at h
      cases hto : toBinOp op with
      | none => rw [hto] at h; simp at h
      | some bo =>
          cases he1 : lowerExpr ρ supply a with
          | none => rw [he1] at h; simp at h
          | some p =>
              obtain ⟨va, ia, s1⟩ := p
              rw [he1] at h
              cases he2 : lowerExpr ρ s1 b with
              | none => simp only [he2, hto] at h; cases h
              | some q =>
                  obtain ⟨vb, ib, s2⟩ := q
                  simp only [he2, hto] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact Nat.le_trans (lower_mono.1 _ _ _ _ _ _ he1)
                    (lower_mono.1 _ _ _ _ _ _ he2)
  | let_ id init body _ _ _ihinit ihbody =>
      simp only [lowerExpr] at h
      cases he1 : lowerExpr ρ supply init with
      | none => rw [he1] at h; simp at h
      | some p =>
          obtain ⟨va, ia, s1⟩ := p
          rw [he1] at h
          cases he2 : lowerExpr ((id, va) :: ρ) s1 body with
          | none => simp only [he2] at h; cases h
          | some q =>
              obtain ⟨vb, ib, s2⟩ := q
              simp only [he2] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              cases hvf with
              | let_ _ _ _ hvi hvb =>
                  have hle1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he1
                  have hle2 : s1 ≤ v := ihbody _ _ _ _ _ hvb he2
                  exact Nat.le_trans hle1 hle2
  | block es hall ih =>
      simp only [lowerExpr] at h
      cases hvf with
      | block _ hallv =>
          have nest : ∀ (ρ : List (HIR.Id × ValId)) (supply : Nat)
              (l : List HIR.Expr) (v : ValId) (is : List Instr) (s' : Nat),
              (∀ e ∈ l, IsStraight e) → (∀ e ∈ l, VarFree e) →
              (∀ e ∈ l, ∀ (ρ' : List (HIR.Id × ValId)) (supply' : Nat)
                (v' : ValId) (is' : List Instr) (s'' : Nat), VarFree e →
                lowerExpr ρ' supply' e = some (v', is', s'') → supply' ≤ v') →
              lowerBlock ρ supply l = some (v, is, s') → supply ≤ v := by
            intro ρ supply l v is s' halll hvfl single h
            induction l generalizing ρ supply v is s' with
            | nil =>
                simp only [lowerBlock] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact Nat.le_refl _
            | cons e l inner =>
                cases l with
                | nil =>
                    simp only [lowerBlock] at h
                    exact single e (List.mem_cons.mpr (Or.inl rfl)) _ _ _ _ _
                      (hvfl e (List.mem_cons.mpr (Or.inl rfl))) h
                | cons e2 l2 =>
                    simp only [lowerBlock] at h
                    cases he : lowerExpr ρ supply e with
                    | none => rw [he] at h; simp at h
                    | some p =>
                        obtain ⟨ve, ie, s1⟩ := p
                        rw [he] at h
                        cases ht : lowerBlock ρ s1 (e2 :: l2) with
                        | none => simp only [ht] at h; cases h
                        | some q =>
                            obtain ⟨v', ibe', s2'⟩ := q
                            simp only [ht] at h
                            have hmem : ∀ e' ∈ e2 :: l2, IsStraight e' := by
                              intro e' hm
                              exact halll e' (List.mem_cons_of_mem _ hm)
                            have hmemv : ∀ e' ∈ e2 :: l2, VarFree e' := by
                              intro e' hm
                              exact hvfl e' (List.mem_cons_of_mem _ hm)
                            have hsingle : ∀ e ∈ e2 :: l2,
                                ∀ (ρ' : List (HIR.Id × ValId)) (supply' : Nat)
                                (v' : ValId) (is' : List Instr) (s'' : Nat),
                                VarFree e →
                                lowerExpr ρ' supply' e = some (v', is', s'') →
                                supply' ≤ v' := by
                              intro e' hm
                              exact single e' (List.mem_cons_of_mem _ hm)
                            have hle1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                            have hle2 : s1 ≤ v' := inner _ _ _ _ _ hmem hmemv hsingle ht
                            obtain ⟨rfl, rfl, rfl⟩ := h
                            exact Nat.le_trans hle1 hle2
          exact nest _ _ _ _ _ _ hall hallv (fun e hmem => ih e hmem) h

/-- `lowerBlock` results also sit at or above the incoming supply. Induction on
the list (the head threads the supply into the tail); the singleton case cites
the expression lemma above. -/
theorem lowerBlock_result_ge (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (es : List HIR.Expr) (v : ValId) (is : List Instr) (s' : Nat)
    (hall : ∀ e ∈ es, IsStraight e) (hvf : ∀ e ∈ es, VarFree e)
    (h : lowerBlock ρ supply es = some (v, is, s')) : supply ≤ v := by
  induction es generalizing ρ supply v is s' with
  | nil =>
      simp only [lowerBlock] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Nat.le_refl _
  | cons e es ih =>
      cases es with
      | nil =>
          simp only [lowerBlock] at h
          exact lowerExpr_result_ge _ _ _ _ _ _
            (hall e (by simp)) (hvf e (by simp)) h
      | cons e2 es2 =>
          simp only [lowerBlock] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨ve, ie, s1⟩ := p
              rw [he] at h
              cases ht : lowerBlock ρ s1 (e2 :: es2) with
              | none => simp only [ht] at h; cases h
              | some q =>
                  obtain ⟨v', ibe', s2'⟩ := q
                  simp only [ht] at h
                  have hmem : ∀ e' ∈ e2 :: es2, IsStraight e' := by
                    intro e' hm
                    exact hall e' (List.mem_cons_of_mem _ hm)
                  have hmemv : ∀ e' ∈ e2 :: es2, VarFree e' := by
                    intro e' hm
                    exact hvf e' (List.mem_cons_of_mem _ hm)
                  have hle1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  have hle2 : s1 ≤ v' := ih _ _ _ _ _ hmem hmemv ht
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact Nat.le_trans hle1 hle2



/-- Carried registers sit at or above the allocation supply: `mkCarried`
hands out `s, s + 1, …` in order. -/
theorem mkCarried_mem_lo {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} {id : HIR.Id} {r : ValId}
    (h : mkCarried ρ s ids = some (cs, s', ρ')) (hmem : (id, r) ∈ cs) :
    s ≤ r := by
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp at hmem
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
              simp only [List.mem_cons] at hmem
              rcases hmem with hmem | hmem
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
                exact Nat.le_refl _
              · exact Nat.le_trans (Nat.le_succ _) (ih hrec hmem)

/-- Carried registers sit strictly below the final supply. -/
theorem mkCarried_mem_hi {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} {id : HIR.Id} {r : ValId}
    (h : mkCarried ρ s ids = some (cs, s', ρ')) (hmem : (id, r) ∈ cs) :
    r < s' := by
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp at hmem
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
              simp only [List.mem_cons] at hmem
              rcases hmem with hmem | hmem
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
                  (mkCarried_le hrec)
              · exact ih hrec hmem

/-- Allocation order makes carried registers injective: the same register
means the same allocation step, hence the same id. -/
theorem mkCarried_reg_inj {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} {id₁ id₂ : HIR.Id} {r : ValId}
    (h : mkCarried ρ s ids = some (cs, s', ρ'))
    (h₁ : (id₁, r) ∈ cs) (h₂ : (id₂, r) ∈ cs) : id₁ = id₂ := by
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp at h₁
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
              simp only [List.mem_cons] at h₁ h₂
              rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
              · exact (Prod.mk.inj h₁).1.trans ((Prod.mk.inj h₂).1).symm
              · obtain ⟨-, hr⟩ := Prod.mk.inj h₁
                have hle : s + 1 ≤ r := mkCarried_mem_lo hrec h₂
                rw [hr] at hle
                exact absurd hle (Nat.not_succ_le_self s)
              · obtain ⟨-, hr⟩ := Prod.mk.inj h₂
                have hle : s + 1 ≤ r := mkCarried_mem_lo hrec h₁
                rw [hr] at hle
                exact absurd hle (Nat.not_succ_le_self s)
              · exact ih hrec h₁ h₂

/-- A `mkCarried` environment resolves every id either to its carried pair
or to the pre-loop environment: the update chain only remaps. -/
theorem mkCarried_lookup {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} {id' : HIR.Id} {u' : ValId}
    (h : mkCarried ρ s ids = some (cs, s', ρ'))
    (hlook : rhoLookup ρ' id' = some u') :
    (∃ id r, (id, r) ∈ cs ∧ id' = id ∧ u' = r) ∨
      rhoLookup ρ id' = some u' := by
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr hlook
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
              rcases ih hrec hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
              · exact Or.inl ⟨i, rr, List.mem_cons_of_mem _ hmem, hid, hu⟩
              · by_cases heq : id' = hd
                · have hss : u' = s := by
                    have hupd : rhoLookup (updAssoc ρ hd s) hd = some s := by
                      rw [rhoLookup_updAssoc_id ρ hd s, hρ]
                      rfl
                    rw [heq, hupd] at hbase
                    exact (Option.some.inj hbase).symm
                  exact Or.inl ⟨hd, s, List.mem_cons_self .., heq, hss⟩
                · rw [rhoLookup_updAssoc_ne (fun hh => heq hh.symm) ρ] at hbase
                  exact Or.inr hbase

/-- Carried exclusivity: every carried register is its id's exclusive effective
register. A `continue` snapshot writes each carried register from its id's
current register; exclusivity is what keeps those writes from clobbering
another id's register (aliasing through variable reads is excluded by
`VarFree`, fresh allocations never hit carried registers, and shadowing puts
the newest mapping first). Threaded through the loop-body worker. -/
def CarriedExcl (ρ : List (HIR.Id × ValId))
    (carried : List (HIR.Id × ValId)) : Prop :=
  ∀ id r, (id, r) ∈ carried → ∀ id' u',
    rhoLookup ρ id' = some u' → u' = r → id' = id

/-- `mkCarried` environments are exclusive over the carried set: a carried
register is fresh (at or above the pre-loop supply), so any id resolving to
it through the carried env must name a carried pair with that register —
and allocation order makes the id unique. Otherwise the id resolved through
the pre-loop env, whose registers sit below the supply: contradiction. -/
theorem mkCarried_excl {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)}
    (hf : FreshAbove ρ s)
    (h : mkCarried ρ s ids = some (cs, s', ρ')) :
    CarriedExcl ρ' cs := by
  intro id r hmem id' u' hlook heq
  rcases mkCarried_lookup h hlook with ⟨i, rr, hmem2, rfl, hu⟩ | hbase
  · have hrr : rr = r := hu.symm.trans heq
    rw [hrr] at hmem2
    exact (mkCarried_reg_inj h hmem hmem2).symm
  · have hlt : u' < s := hf _ _ (rhoLookup_some_mem _ _ _ hbase)
    have hle : s ≤ r := mkCarried_mem_lo h hmem
    rw [heq] at hlt
    exact absurd hle (Nat.not_le_of_gt hlt)

/-- A high register in a `mkCarried` environment is carried: anything
resolving through the pre-loop env sits below the supply. The header-phi
chaining uses this to classify back-edge sources. -/
theorem mkCarried_lookup_high {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)}
    (hf : FreshAbove ρ s)
    (h : mkCarried ρ s ids = some (cs, s', ρ'))
    {id : HIR.Id} {r : ValId}
    (hlook : rhoLookup ρ' id = some r) (hle : s ≤ r) :
    (id, r) ∈ cs := by
  rcases mkCarried_lookup h hlook with ⟨i, rr, hmem, rfl, rfl⟩ | hbase
  · exact hmem
  · exfalso
    have hlt : r < s := hf _ _ (rhoLookup_some_mem _ _ _ hbase)
    exact absurd hle (Nat.not_le_of_gt hlt)

/-- Carried registers are fresh for the pre-loop env too: every `ρ` register
sits below the supply, hence below every carried register. The entry-edge
phi chaining uses this for its frame argument. -/
theorem mkCarried_excl_pre {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)}
    (hf : FreshAbove ρ s)
    (h : mkCarried ρ s ids = some (cs, s', ρ')) :
    CarriedExcl ρ cs := by
  intro id r hmem id' u' hlook heq
  have hlt : u' < s := hf _ _ (rhoLookup_some_mem _ _ _ hlook)
  have hle : s ≤ r := mkCarried_mem_lo h hmem
  rw [heq] at hlt
  exact absurd hle (Nat.not_le_of_gt hlt)

/-- Loop bodies preserve carried exclusivity: straight-line steps only bind
fresh registers (at or above the supply, hence above every carried
register), `varDecl` is refused under `loop = some`, arms preserve the env
(`arm_rho`), and `break`/`continue`/`return` leave it unchanged. The spine
needs this for the back edge: body-exit registers resolve carried ids
without aliasing, so sequential back-phi writes never clobber a later
source. -/
theorem lowerStmtsCFG_loopBody_excl (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered) (carried : List (HIR.Id × ValId)),
      loop = some info →
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop ss = some L →
      LoopStmts budget ss →
      CarriedExcl ρ carried →
      (∀ id r, (id, r) ∈ carried → r < supply) →
      CarriedExcl L.ρ carried := by
  intro bId cont ρ supply nextB lastVal hasVal loop info ss
  induction ss generalizing bId cont ρ supply nextB lastVal hasVal loop with
  | nil =>
      intro L carried hlo h hss hexcl hsup
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          simp at h
          subst h
          exact hexcl
  | cons s rest ih =>
      intro L carried hlo h hss hexcl hsup
      cases hss with
      | exprStmt e rest hstr _ hrs =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId cont false ρ s1 nextB v0 true
                  loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  have hsup1 : ∀ id r, (id, r) ∈ carried → r < s1 :=
                    fun id r hmem =>
                      Nat.lt_of_lt_of_le (hsup _ _ hmem) hs1
                  exact ih bId cont ρ s1 nextB v0 true loop q carried hlo hr
                    hrs hexcl hsup1
      | varDecl id τ init rest hstr _ hrs _ =>
          cases hlo' : loop with
          | some _ => simp [hlo'] at h
          | none => rw [hlo] at hlo'; simp at hlo'
      | assign id e rest hstr _ hrs hvf =>
          simp at h
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
                  obtain rfl := Option.some.inj h
                  have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                  have hsup1 : ∀ id0 r0, (id0, r0) ∈ carried → r0 < s1 :=
                    fun id0 r0 hmem =>
                      Nat.lt_of_lt_of_le (hsup _ _ hmem) hs1
                  have hexcl' : CarriedExcl (updAssoc ρ id v) carried := by
                    intro id0 r0 hmem id' u' hlook heq
                    by_cases heq' : id' = id
                    · rw [heq'] at hlook
                      have huv : u' = v := by
                        have h1 := rhoLookup_updAssoc_id ρ id v
                        rw [h1] at hlook
                        cases hρ : rhoLookup ρ id with
                        | none => simp [hρ] at hlook
                        | some _ =>
                            simp [hρ] at hlook
                            exact hlook.symm
                      have hrS : r0 < supply := hsup _ _ hmem
                      have hge : supply ≤ v :=
                        lowerExpr_result_ge _ _ _ _ _ _ hstr hvf he
                      have hlt : r0 < v := Nat.lt_of_lt_of_le hrS hge
                      rw [← huv, heq] at hlt
                      exact absurd hlt (Nat.lt_irrefl _)
                    · have hlook' : rhoLookup ρ id' = some u' := by
                        have hrr := rhoLookup_updAssoc_ne
                          (fun hh => heq' hh.symm) (v := v) ρ
                        rw [hrr] at hlook
                        exact hlook
                      exact hexcl id0 r0 hmem id' u' hlook' heq
                  exact ih bId cont (updAssoc ρ id v) s1 nextB lastVal true
                    loop q carried hlo hr hrs hexcl' hsup1
      | nop rest hrs =>
          simp only [lowerStmtsCFG] at h
          exact ih bId cont ρ supply nextB lastVal hasVal loop L carried hlo
            h hrs hexcl hsup
      | ifStmt c th el rest hstr _ hath hael hrs =>
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
                          obtain rfl := Option.some.inj h
                          have hs1 : supply ≤ s1 :=
                            lower_mono.1 _ _ _ _ _ _ heC
                          obtain ⟨hmnt, hmst, -, -⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              ht hath
                          obtain ⟨hmne, hmse, -, -⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              he hael
                          have hle : supply ≤ le.supply :=
                            Nat.le_trans hs1 (Nat.le_trans hmst hmse)
                          have hsupR : ∀ id r, (id, r) ∈ carried →
                              r < le.supply + 1 :=
                            fun id r hmem => Nat.lt_of_lt_of_le
                              (hsup _ _ hmem)
                              (Nat.le_trans hle (Nat.le_succ _))
                          exact ih (nextB + 2) cont ρ (le.supply + 1) le.next
                            le.supply true loop lr carried hlo hr hrs hexcl
                            hsupR
      | ifStmtBreak c th el rest hstr _ hath hael hrs _ =>
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
                          obtain rfl := Option.some.inj h
                          have hs1 : supply ≤ s1 :=
                            lower_mono.1 _ _ _ _ _ _ heC
                          obtain ⟨hmnt, hmst, -, -⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              ht hath
                          obtain ⟨hmne, hmse, -, -⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              he hael
                          have hle : supply ≤ le.supply :=
                            Nat.le_trans hs1 (Nat.le_trans hmst hmse)
                          have hsupR : ∀ id r, (id, r) ∈ carried →
                              r < le.supply + 1 :=
                            fun id r hmem => Nat.lt_of_lt_of_le
                              (hsup _ _ hmem)
                              (Nat.le_trans hle (Nat.le_succ _))
                          exact ih (nextB + 2) cont ρ (le.supply + 1) le.next
                            le.supply true loop lr carried hlo hr hrs hexcl
                            hsupR
      | returnStmt e rest hstr _ =>
          simp at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              exact hexcl
      | breakStmt rest _ =>
          cases hloop : loop with
          | some j =>
              simp only [lowerStmtsCFG, hloop] at h
              cases hc : carryCopies ρ j.carried with
              | none => simp [hc] at h
              | some copies =>
                  simp [hc] at h
                  subst h
                  exact hexcl
          | none => rw [hlo] at hloop; simp at hloop
      | continueStmt rest _ =>
          cases hloop : loop with
          | some j =>
              simp only [lowerStmtsCFG, hloop] at h
              cases hc : carryCopies ρ j.carried with
              | none => simp [hc] at h
              | some copies =>
                  simp [hc] at h
                  subst h
                  exact hexcl
          | none => rw [hlo] at hloop; simp at hloop

/-- The header-phi fold maps `none` to `none`: a failed accumulator never
recovers, so a successful fold had every lookup succeed. -/
theorem mkHeaderPhis_foldl_none (ρ : List (HIR.Id × ValId))
    (entryPred : MIR.BlockId) (fallEnd : MIR.BlockId)
    (ρout : List (HIR.Id × ValId)) (tramps : List MIR.BlockId) :
    ∀ (l : List (HIR.Id × ValId)),
    l.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
      match a with
      | none => none
      | some ps =>
          match rhoLookup ρ p.1, rhoLookup ρout p.1 with
          | some entrySrc, some backSrc =>
              some (ps ++ [.phi p.2 entryPred entrySrc, .phi p.2 fallEnd backSrc] ++
                tramps.map (.phi p.2 · p.2))
          | _, _ => none) none = none := by
  intro l
  induction l with
  | nil => rfl
  | cons _ rest ih =>
      simp only [List.foldl]
      exact ih

/-- The header-phi fold builds one phi group per carried pair: an entry phi
(`pred = entryPred`, source in the pre-loop env), a back-edge phi
(`pred = fallEnd`, source in the body's exit env), and one self-copy per
`continue` trampoline. The fold appends left-to-right, so the result is the
concatenation of the per-pair groups. The header-chaining lemmas execute
the groups one by one (each entry/back phi fires on exactly one edge),
which needs the group structure, not just membership. -/
theorem mkHeaderPhis_flatMap (ρ : List (HIR.Id × ValId))
    (entryPred : MIR.BlockId) (fallEnd : MIR.BlockId)
    (ρout : List (HIR.Id × ValId)) (tramps : List MIR.BlockId) :
    ∀ (l : List (HIR.Id × ValId)) (acc phis : List Instr),
    l.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
      match a with
      | none => none
      | some ps =>
          match rhoLookup ρ p.1, rhoLookup ρout p.1 with
          | some entrySrc, some backSrc =>
              some (ps ++ [.phi p.2 entryPred entrySrc, .phi p.2 fallEnd backSrc] ++
                tramps.map (.phi p.2 · p.2))
          | _, _ => none) (some acc) = some phis →
    ∃ f : HIR.Id × ValId → List Instr,
      (∀ q ∈ l, ∃ esrc bsrc, rhoLookup ρ q.1 = some esrc ∧
        rhoLookup ρout q.1 = some bsrc ∧
        f q = ([.phi q.2 entryPred esrc, .phi q.2 fallEnd bsrc] ++
          tramps.map (.phi q.2 · q.2))) ∧
      phis = acc ++ (l.map f).flatten := by
  intro l acc phis h
  revert acc phis h
  induction l with
  | nil =>
      intro acc phis h
      simp only [List.foldl] at h
      obtain rfl := Option.some.inj h
      exact ⟨fun _ => [], by simp, by simp⟩
  | cons p rest ih =>
      intro acc phis h
      simp only [List.foldl] at h
      cases he1 : rhoLookup ρ p.1 with
      | none =>
          have hnone := mkHeaderPhis_foldl_none ρ entryPred fallEnd ρout
            tramps rest
          simp only [he1] at h
          rw [hnone] at h
          simp at h
      | some esrc =>
          cases he2 : rhoLookup ρout p.1 with
          | none =>
              have hnone := mkHeaderPhis_foldl_none ρ entryPred fallEnd ρout
                tramps rest
              simp only [he1, he2] at h
              rw [hnone] at h
              simp at h
          | some bsrc =>
              simp only [he1, he2] at h
              obtain ⟨f', hf', hflat⟩ := ih _ _ h
              refine ⟨fun q => if q = p then ([.phi p.2 entryPred esrc,
                .phi p.2 fallEnd bsrc] ++
                tramps.map (.phi p.2 · p.2)) else f' q, ?_, ?_⟩
              · intro q hq
                rw [List.mem_cons] at hq
                cases hq with
                | inl heq =>
                    subst heq
                    exact ⟨esrc, bsrc, he1, he2, by simp⟩
                | inr hmem =>
                    obtain ⟨e, b, he1q, he2q, hfq⟩ := hf' q hmem
                    by_cases heq : q = p
                    · subst heq
                      obtain rfl := Option.some.inj (he1.symm.trans he1q)
                      obtain rfl := Option.some.inj (he2.symm.trans he2q)
                      exact ⟨esrc, bsrc, he1, he2, by simp⟩
                    · exact ⟨e, b, he1q, he2q, by simp [heq, hfq]⟩
              · have hmap : (rest.map fun q =>
                    if q = p then ([.phi p.2 entryPred esrc,
                      .phi p.2 fallEnd bsrc] ++
                      tramps.map (.phi p.2 · p.2)) else f' q) =
                    rest.map f' := by
                  apply List.map_congr_left
                  intro q hq
                  by_cases heq : q = p
                  · subst heq
                    obtain ⟨e, b, he1q, he2q, hfq⟩ := hf' q hq
                    obtain rfl := Option.some.inj (he1.symm.trans he1q)
                    obtain rfl := Option.some.inj (he2.symm.trans he2q)
                    simp [hfq]
                  · simp [heq]
                simp only [List.map_cons, hmap, List.flatten_cons, hflat,
                  List.append_assoc]
                simp

/-- Trampoline self-copies all miss on a non-tramp edge, so the group tail
is a no-op. By induction on the trampoline list. -/
theorem trampPhis_exec_miss (prog : Program) (e : MIR.BlockId)
    (tramps : List MIR.BlockId) (r : ValId) (fenv : FullEnv)
    (h : ∀ t ∈ tramps, t ≠ e) :
    execInstrsFullFromIn prog (some e) fenv (tramps.map (.phi r · r)) =
      some fenv := by
  induction tramps generalizing fenv with
  | nil => simp [List.map_nil, execInstrsFullFromIn_eq, execInstrsFullFrom]
  | cons t ts ih =>
      have hhead : t ≠ e := h t (List.mem_cons_self ..)
      have htail : ∀ t' ∈ ts, t' ≠ e :=
        fun t' hm => h t' (List.mem_cons_of_mem _ hm)
      simp only [List.map_cons]
      rw [execInstrsFullFromIn_eq,
        execInstrsFullFrom_phi_miss _ _ _ _ _ _ hhead,
        ← execInstrsFullFromIn_eq]
      exact ih fenv htail

/-- One header group on the entry edge: the entry phi hits (its source reads
through the pre-loop relation), the back phi and every trampoline self-copy
miss, and the tail runs from the updated environment. -/
theorem headerGroup_exec_entry (entryPred fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) (r esrc backSrc : ValId) (fenv : FullEnv)
    (w : Value) (hfall : fallEnd ≠ entryPred)
    (hsrc : fenv.env esrc = some w) :
    execInstrsFullFrom (some entryPred) fenv
        ([.phi r entryPred esrc, .phi r fallEnd backSrc] ++
          tramps.map (.phi r · r)) =
      execInstrsFullFrom (some entryPred) ⟨fenv.env.update r w, fenv.store⟩
        (tramps.map (.phi r · r)) := by
  simp only [List.cons_append, List.nil_append,
    execInstrsFullFrom_phi_hit _ _ _ _ _ _ rfl, hsrc,
    execInstrsFullFrom_phi_miss _ _ _ _ _ _ hfall]

/-- One header group on the back edge: the back phi hits (its source reads
through the body-exit relation), the entry phi and every trampoline
self-copy miss, and the tail runs from the updated environment. -/
theorem headerGroup_exec_back (entryPred fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) (r entrySrc backSrc : ValId) (fenv : FullEnv)
    (w : Value) (hentry : entryPred ≠ fallEnd)
    (hsrc : fenv.env backSrc = some w) :
    execInstrsFullFrom (some fallEnd) fenv
        ([.phi r entryPred entrySrc, .phi r fallEnd backSrc] ++
          tramps.map (.phi r · r)) =
      execInstrsFullFrom (some fallEnd) ⟨fenv.env.update r w, fenv.store⟩
        (tramps.map (.phi r · r)) := by
  simp only [List.cons_append, List.nil_append,
    execInstrsFullFrom_phi_miss _ _ _ _ _ _ hentry,
    execInstrsFullFrom_phi_hit _ _ _ _ _ _ rfl, hsrc]

/-- Header phis on the back edge preserve the body-exit relation and thread
values through: each carried register ends holding its id's HIR value, and
registers outside the carried set are untouched. A back-edge source may
itself be a carried register (self-copy or body aliasing), but exclusivity
says it then names the same id, so the overwrite agrees with the relation —
the same argument as `carryCopies_exec`. Duplicate pairs rewrite the same
value. -/
theorem headerPhis_exec_back (ρout : List (HIR.Id × ValId))
    (entryPred fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) :
    ∀ (l : List (HIR.Id × ValId)) (f : HIR.Id × ValId → List Instr),
    (∀ q ∈ l, ∃ entrySrc backSrc, rhoLookup ρout q.1 = some backSrc ∧
      f q = ([.phi q.2 entryPred entrySrc, .phi q.2 fallEnd backSrc] ++
        tramps.map (.phi q.2 · q.2))) →
    entryPred ≠ fallEnd → (∀ t ∈ tramps, t ≠ fallEnd) →
    CarriedExcl ρout l →
    (∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ l → (id₂, r₂) ∈ l → r₁ = r₂ → id₁ = id₂) →
    ∀ (prog : Program) (fenv : FullEnv) (henv : HEnv),
    RelEnv henv ρout fenv.env →
    ∃ fenv_arr, execInstrsFullFromIn prog (some fallEnd) fenv
        ((l.map f).flatten) = some fenv_arr ∧
      RelEnv henv ρout fenv_arr.env ∧
      (∀ id r w, (id, r) ∈ l → lookupHEnv henv id = some (.lit w) →
        fenv_arr.env r = some w) ∧
      (∀ r', (∀ id, (id, r') ∉ l) → fenv_arr.env r' = fenv.env r') := by
  intro l f hf hentry htr hexcl hdist prog fenv henv hrel
  revert hf hentry htr hexcl hdist fenv hrel
  induction l with
  | nil =>
      intro hf hentry htr hexcl hdist fenv hrel
      refine ⟨fenv, by simp [execInstrsFullFromIn_eq], hrel, ?_, ?_⟩
      · intro id r w hmem
        simp at hmem
      · intro r' _
        rfl
  | cons p rest ih =>
      obtain ⟨id₀, r₀⟩ := p
      intro hf hentry htr hexcl hdist fenv hrel
      have hfhead : ∃ entrySrc backSrc, rhoLookup ρout id₀ = some backSrc ∧
          f (id₀, r₀) = ([.phi r₀ entryPred entrySrc,
            .phi r₀ fallEnd backSrc] ++
            tramps.map (.phi r₀ · r₀)) :=
        hf _ (List.mem_cons_self ..)
      obtain ⟨entrySrc, backSrc, he2, hfp⟩ := hfhead
      have hf_rest : ∀ q ∈ rest, ∃ entrySrc backSrc,
          rhoLookup ρout q.1 = some backSrc ∧
          f q = ([.phi q.2 entryPred entrySrc, .phi q.2 fallEnd backSrc] ++
            tramps.map (.phi q.2 · q.2)) :=
        fun q hq => hf q (List.mem_cons_of_mem _ hq)
      have hexcl_rest : CarriedExcl ρout rest := by
        intro id r hmem id' u' hlook heq
        exact hexcl id r (List.mem_cons_of_mem _ hmem) id' u' hlook heq
      have hdist_rest : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ rest →
          (id₂, r₂) ∈ rest → r₁ = r₂ → id₁ = id₂ := by
        intro id₁ r₁ id₂ r₂ h₁ h₂ heq
        exact hdist id₁ r₁ id₂ r₂ (List.mem_cons_of_mem _ h₁)
          (List.mem_cons_of_mem _ h₂) heq
      obtain ⟨w, hlookH, hreg⟩ := hrel id₀ backSrc he2
      have hexec1 : execInstrsFullFrom (some fallEnd) fenv (f (id₀, r₀)) =
          execInstrsFullFrom (some fallEnd)
            ⟨fenv.env.update r₀ w, fenv.store⟩
            (tramps.map (.phi r₀ · r₀)) := by
        rw [hfp]
        exact headerGroup_exec_back entryPred fallEnd tramps r₀ entrySrc
          backSrc fenv w hentry hreg
      have hexecT : execInstrsFullFrom (some fallEnd)
          ⟨fenv.env.update r₀ w, fenv.store⟩ (tramps.map (.phi r₀ · r₀)) =
          some ⟨fenv.env.update r₀ w, fenv.store⟩ := by
        rw [← execInstrsFullFromIn_eq]
        exact trampPhis_exec_miss prog fallEnd tramps r₀ _ htr
      have hrel1 : RelEnv henv ρout
          (⟨fenv.env.update r₀ w, fenv.store⟩ : FullEnv).env := by
        intro id' u' hlook
        by_cases heq : u' = r₀
        · have hid : id' = id₀ := hexcl id₀ r₀
            (List.mem_cons.mpr (Or.inl rfl)) id' u' hlook heq
          refine ⟨w, ?_, ?_⟩
          · rwa [hid]
          · rw [heq]
            simp [Env.update]
        · have hbeq : ¬ (u' == r₀) := by simpa using heq
          obtain ⟨w0, h1, h2⟩ := hrel id' u' hlook
          exact ⟨w0, h1, by simp [Env.update, hbeq, h2]⟩
      obtain ⟨fenv_arr, hexec_rest, hrel_arr, hval_arr, hframe_arr⟩ :=
        ih hf_rest hentry htr hexcl_rest hdist_rest
          ⟨fenv.env.update r₀ w, fenv.store⟩ hrel1
      have happ : execInstrsFullFromIn prog (some fallEnd) fenv
          (f (id₀, r₀) ++ (rest.map f).flatten) =
          execInstrsFullFromIn prog (some fallEnd)
            ⟨fenv.env.update r₀ w, fenv.store⟩ (rest.map f).flatten := by
        rw [execInstrsFullFromIn_eq, execInstrsFullFromIn_eq,
          execInstrsFullFrom_append, hexec1, hexecT]
      refine ⟨fenv_arr, ?_, hrel_arr, ?_, ?_⟩
      · show execInstrsFullFromIn prog (some fallEnd) fenv
            (f (id₀, r₀) ++ (rest.map f).flatten) = some fenv_arr
        rw [happ]
        exact hexec_rest
      · intro id r w' hmem hlookH'
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · obtain ⟨hid, hr⟩ := Prod.mk.inj hmem
          rw [hid] at hlookH'
          rw [hr]
          have hw_eq : w' = w := by
            have h1 := hlookH
            rw [hlookH'] at h1
            exact HIR.Expr.lit.inj (Option.some.inj h1)
          subst hw_eq
          by_cases hdup : (id₀, r₀) ∈ rest
          · exact hval_arr id₀ r₀ w' hdup hlookH
          · have hnotin : ∀ idx, (idx, r₀) ∉ rest := by
              intro idx hcon
              exact hdup (hdist idx r₀ id₀ r₀ (List.mem_cons_of_mem _ hcon)
                (List.mem_cons.mpr (Or.inl rfl)) rfl ▸ hcon)
            rw [hframe_arr r₀ hnotin]
            simp [Env.update]
        · exact hval_arr id r w' hmem hlookH'
      · intro r' hnotin
        have hne : r' ≠ r₀ := by
          intro heq
          subst heq
          exact hnotin id₀ (List.mem_cons.mpr (Or.inl rfl))
        have h1 : fenv_arr.env r' =
              (fenv.env.update r₀ w) r' :=
          hframe_arr r' (by
            intro idx hcon
            exact hnotin idx (List.mem_cons_of_mem _ hcon))
        have hne_b : ¬ (r' == r₀) := by simpa using hne
        simp only [Env.update, if_neg hne_b] at h1
        exact h1

/-- Rewriting a register with its current value is a no-op. Trampoline
self-copies hit exactly on their own edge, so each one reduces to this. -/
theorem Env.update_eq_self (env : Morph.MIR.Env) (dst : ValId) (v : Value)
    (h : env dst = some v) : env.update dst v = env := by
  funext x
  by_cases heq : x = dst
  · subst heq
    simp [Env.update, h]
  · simp [Env.update, heq]

/-- Trampoline self-copies on any edge leave the environment unchanged: a
miss skips, and a hit rewrites the register with its current value. No
membership or duplicate-freedom needed — every case is a no-op. -/
theorem trampSelf_exec (t : MIR.BlockId) (r : ValId)
    (ts : List MIR.BlockId) (fenv : FullEnv) (w₀ : Value)
    (hreg : fenv.env r = some w₀) :
    execInstrsFullFrom (some t) fenv (ts.map (.phi r · r)) = some fenv := by
  induction ts generalizing fenv with
  | nil => simp [List.map_nil]
  | cons t' ts' ih =>
      by_cases heq : t' = t
      · subst heq
        simp only [List.map_cons,
          execInstrsFullFrom_phi_hit _ _ _ _ _ _ rfl, hreg]
        rw [Env.update_eq_self _ _ _ hreg]
        exact ih _ hreg
      · simp only [List.map_cons,
          execInstrsFullFrom_phi_miss _ _ _ _ _ _ heq]
        exact ih _ hreg

/-- One header group on a trampoline edge: both edge phis miss and every
self-copy is a no-op, so the group runs to the unchanged environment. -/
theorem headerGroup_exec_tramp (t entryPred fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) (r entrySrc backSrc : ValId) (fenv : FullEnv)
    (w₀ : Value) (hentry : entryPred ≠ t) (hfall : fallEnd ≠ t)
    (hreg : fenv.env r = some w₀) :
    execInstrsFullFrom (some t) fenv
        ([.phi r entryPred entrySrc, .phi r fallEnd backSrc] ++
          tramps.map (.phi r · r)) = some fenv := by
  simp only [List.cons_append, List.nil_append,
    execInstrsFullFrom_phi_miss _ _ _ _ _ _ hentry,
    execInstrsFullFrom_phi_miss _ _ _ _ _ _ hfall]
  exact trampSelf_exec t r tramps fenv w₀ hreg

/-- Header phis on a trampoline edge preserve the environment outright:
self-copies rewrite carried registers with their current values, so the
whole fold is a no-op. The value invariant (every carried register already
holds its HIR value — established by the trampoline's snapshot copies) and
the relation pass straight through. -/
theorem headerPhis_exec_tramp (ρout : List (HIR.Id × ValId))
    (entryPred fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) :
    ∀ (l : List (HIR.Id × ValId)) (f : HIR.Id × ValId → List Instr),
    (∀ q ∈ l, ∃ entrySrc backSrc, rhoLookup ρout q.1 = some backSrc ∧
      f q = ([.phi q.2 entryPred entrySrc, .phi q.2 fallEnd backSrc] ++
        tramps.map (.phi q.2 · q.2))) →
    ∀ (t : MIR.BlockId), t ∈ tramps →
    entryPred ≠ t → fallEnd ≠ t →
    (∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ l → (id₂, r₂) ∈ l → r₁ = r₂ → id₁ = id₂) →
    ∀ (prog : Program) (fenv : FullEnv) (henv : HEnv),
    RelEnv henv ρout fenv.env →
    (∀ id r, (id, r) ∈ l → ∃ w, lookupHEnv henv id = some (.lit w) ∧
      fenv.env r = some w) →
    ∃ fenv_arr, execInstrsFullFromIn prog (some t) fenv
        ((l.map f).flatten) = some fenv_arr ∧
      RelEnv henv ρout fenv_arr.env ∧
      (∀ id r w, (id, r) ∈ l → lookupHEnv henv id = some (.lit w) →
        fenv_arr.env r = some w) ∧
      (∀ r', (∀ id, (id, r') ∉ l) → fenv_arr.env r' = fenv.env r') := by
  intro l f hf t htmem hentry hfall hdist prog fenv henv hrel hval
  revert hf hentry hfall hdist fenv hrel hval
  induction l with
  | nil =>
      intro hf hentry hfall hdist fenv hrel hval
      refine ⟨fenv, by simp [execInstrsFullFromIn_eq], hrel, ?_, ?_⟩
      · intro id r w hmem
        simp at hmem
      · intro r' _
        rfl
  | cons p rest ih =>
      obtain ⟨id₀, r₀⟩ := p
      intro hf hentry hfall hdist fenv hrel hval
      have hfhead : ∃ entrySrc backSrc, rhoLookup ρout id₀ = some backSrc ∧
          f (id₀, r₀) = ([.phi r₀ entryPred entrySrc,
            .phi r₀ fallEnd backSrc] ++
            tramps.map (.phi r₀ · r₀)) :=
        hf _ (List.mem_cons_self ..)
      obtain ⟨entrySrc, backSrc, he2, hfp⟩ := hfhead
      have hf_rest : ∀ q ∈ rest, ∃ entrySrc backSrc,
          rhoLookup ρout q.1 = some backSrc ∧
          f q = ([.phi q.2 entryPred entrySrc, .phi q.2 fallEnd backSrc] ++
            tramps.map (.phi q.2 · q.2)) :=
        fun q hq => hf q (List.mem_cons_of_mem _ hq)
      have hval_rest : ∀ id r, (id, r) ∈ rest → ∃ w,
          lookupHEnv henv id = some (.lit w) ∧ fenv.env r = some w :=
        fun id r hmem => hval id r (List.mem_cons_of_mem _ hmem)
      obtain ⟨w₀, hlookH, hreg0⟩ := hval id₀ r₀ (List.mem_cons_self ..)
      have hexec1 : execInstrsFullFrom (some t) fenv (f (id₀, r₀)) =
          some fenv := by
        rw [hfp]
        exact headerGroup_exec_tramp t entryPred fallEnd tramps r₀ entrySrc
          backSrc fenv w₀ hentry hfall hreg0
      have hdist_rest : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ rest →
          (id₂, r₂) ∈ rest → r₁ = r₂ → id₁ = id₂ := by
        intro id₁ r₁ id₂ r₂ h₁ h₂ heq
        exact hdist id₁ r₁ id₂ r₂ (List.mem_cons_of_mem _ h₁)
          (List.mem_cons_of_mem _ h₂) heq
      obtain ⟨fenv_arr, hexec_rest, hrel_arr, hval_arr, hframe_arr⟩ :=
        ih hf_rest hentry hfall hdist_rest fenv hrel hval_rest
      have happ : execInstrsFullFromIn prog (some t) fenv
          (f (id₀, r₀) ++ (rest.map f).flatten) =
          execInstrsFullFromIn prog (some t) fenv (rest.map f).flatten := by
        rw [execInstrsFullFromIn_eq, execInstrsFullFromIn_eq,
          execInstrsFullFrom_append, hexec1]
      refine ⟨fenv_arr, ?_, hrel_arr, ?_, ?_⟩
      · show execInstrsFullFromIn prog (some t) fenv
            (f (id₀, r₀) ++ (rest.map f).flatten) = some fenv_arr
        rw [happ]
        exact hexec_rest
      · intro id r w' hmem hlookH'
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · obtain ⟨hid, hr⟩ := Prod.mk.inj hmem
          rw [hid] at hlookH'
          rw [hr]
          have hw_eq : w' = w₀ := by
            have h1 := hlookH
            rw [hlookH'] at h1
            exact HIR.Expr.lit.inj (Option.some.inj h1)
          rw [hw_eq] at hlookH' ⊢
          by_cases hdup : (id₀, r₀) ∈ rest
          · exact hval_arr id₀ r₀ w₀ hdup hlookH
          · have hnotin : ∀ idx, (idx, r₀) ∉ rest := by
              intro idx hcon
              exact hdup (hdist idx r₀ id₀ r₀ (List.mem_cons_of_mem _ hcon)
                (List.mem_cons.mpr (Or.inl rfl)) rfl ▸ hcon)
            rw [hframe_arr r₀ hnotin]
            exact hreg0
        · exact hval_arr id r w' hmem hlookH'
      · intro r' hnotin
        exact hframe_arr r' (by
          intro idx hcon
          exact hnotin idx (List.mem_cons_of_mem _ hcon))

/-- Header phis on the entry edge preserve the pre-loop relation and thread
values through: each carried register ends holding its id's HIR value, and
registers outside the carried set are untouched. Entry sources sit below the
supply (freshness), so entry writes never clobber a later source; duplicate
pairs rewrite the same value. By induction on the carried list, mirroring
`carryCopies_exec`. -/
theorem headerPhis_exec_entry (ρ : List (HIR.Id × ValId))
    (entryPred fallEnd : MIR.BlockId) (ρout : List (HIR.Id × ValId))
    (tramps : List MIR.BlockId) :
    ∀ (l : List (HIR.Id × ValId)) (f : HIR.Id × ValId → List Instr),
    (∀ q ∈ l, ∃ esrc backSrc, rhoLookup ρ q.1 = some esrc ∧
      rhoLookup ρout q.1 = some backSrc ∧
      f q = ([.phi q.2 entryPred esrc, .phi q.2 fallEnd backSrc] ++
        tramps.map (.phi q.2 · q.2))) →
    fallEnd ≠ entryPred → (∀ t ∈ tramps, t ≠ entryPred) →
    ∀ (supply : Nat), FreshAbove ρ supply → (∀ q ∈ l, supply ≤ q.2) →
    (∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ l → (id₂, r₂) ∈ l → r₁ = r₂ → id₁ = id₂) →
    ∀ (prog : Program) (fenv : FullEnv) (henv : HEnv),
    RelEnv henv ρ fenv.env →
    ∃ fenv_arr, execInstrsFullFromIn prog (some entryPred) fenv
        ((l.map f).flatten) = some fenv_arr ∧
      RelEnv henv ρ fenv_arr.env ∧
      (∀ id r w, (id, r) ∈ l → lookupHEnv henv id = some (.lit w) →
        fenv_arr.env r = some w) ∧
      (∀ r', (∀ id, (id, r') ∉ l) → fenv_arr.env r' = fenv.env r') := by
  intro l f hf hfall htr supply hfresh hs hdist prog fenv henv hrel
  revert hf hfall htr hs hdist fenv hrel
  induction l with
  | nil =>
      intro hf hfall htr hs hdist fenv hrel
      refine ⟨fenv, by simp [execInstrsFullFromIn_eq], hrel, ?_, ?_⟩
      · intro id r w hmem
        simp at hmem
      · intro r' _
        rfl
  | cons p rest ih =>
      obtain ⟨id₀, r₀⟩ := p
      intro hf hfall htr hs hdist fenv hrel
      have hfhead : ∃ esrc backSrc, rhoLookup ρ id₀ = some esrc ∧
          rhoLookup ρout id₀ = some backSrc ∧
          f (id₀, r₀) = ([.phi r₀ entryPred esrc, .phi r₀ fallEnd backSrc] ++
            tramps.map (.phi r₀ · r₀)) :=
        hf _ (List.mem_cons_self ..)
      obtain ⟨esrc, backSrc, he1, he2, hfp⟩ := hfhead
      have hfresh_rest : FreshAbove ρ supply := hfresh
      have hs_rest : ∀ q ∈ rest, supply ≤ q.2 :=
        fun q hq => hs q (List.mem_cons_of_mem _ hq)
      have hf_rest : ∀ q ∈ rest, ∃ esrc backSrc, rhoLookup ρ q.1 = some esrc ∧
          rhoLookup ρout q.1 = some backSrc ∧
          f q = ([.phi q.2 entryPred esrc, .phi q.2 fallEnd backSrc] ++
            tramps.map (.phi q.2 · q.2)) :=
        fun q hq => hf q (List.mem_cons_of_mem _ hq)
      have hdist_rest : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ rest →
          (id₂, r₂) ∈ rest → r₁ = r₂ → id₁ = id₂ := by
        intro id₁ r₁ id₂ r₂ h₁ h₂ heq
        exact hdist id₁ r₁ id₂ r₂ (List.mem_cons_of_mem _ h₁)
          (List.mem_cons_of_mem _ h₂) heq
      obtain ⟨w, hlookH, hreg⟩ := hrel id₀ esrc he1
      have hsup : supply ≤ r₀ := hs _ (List.mem_cons_self ..)
      have hexec1 : execInstrsFullFrom (some entryPred) fenv (f (id₀, r₀)) =
          execInstrsFullFrom (some entryPred)
            ⟨fenv.env.update r₀ w, fenv.store⟩
            (tramps.map (.phi r₀ · r₀)) := by
        rw [hfp]
        exact headerGroup_exec_entry entryPred fallEnd tramps r₀ esrc
          backSrc fenv w hfall hreg
      have hexecT : execInstrsFullFrom (some entryPred)
          ⟨fenv.env.update r₀ w, fenv.store⟩ (tramps.map (.phi r₀ · r₀)) =
          some ⟨fenv.env.update r₀ w, fenv.store⟩ := by
        rw [← execInstrsFullFromIn_eq]
        exact trampPhis_exec_miss prog entryPred tramps r₀ _ htr
      have hrel1 : RelEnv henv ρ
          (⟨fenv.env.update r₀ w, fenv.store⟩ : FullEnv).env := by
        intro id' u' hlook
        have hlt : u' < supply := hfresh _ _ (rhoLookup_some_mem _ _ _ hlook)
        have hne : u' ≠ r₀ := Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt hsup)
        have hbeq : ¬ (u' == r₀) := by simpa using hne
        obtain ⟨w0, h1, h2⟩ := hrel id' u' hlook
        exact ⟨w0, h1, by simp [Env.update, hbeq, h2]⟩
      obtain ⟨fenv_arr, hexec_rest, hrel_arr, hval_arr, hframe_arr⟩ :=
        ih hf_rest hfall htr hs_rest hdist_rest
          ⟨fenv.env.update r₀ w, fenv.store⟩ hrel1
      have happ : execInstrsFullFromIn prog (some entryPred) fenv
          (f (id₀, r₀) ++ (rest.map f).flatten) =
          execInstrsFullFromIn prog (some entryPred)
            ⟨fenv.env.update r₀ w, fenv.store⟩ (rest.map f).flatten := by
        rw [execInstrsFullFromIn_eq, execInstrsFullFromIn_eq,
          execInstrsFullFrom_append, hexec1, hexecT]
      refine ⟨fenv_arr, ?_, hrel_arr, ?_, ?_⟩
      · show execInstrsFullFromIn prog (some entryPred) fenv
            (f (id₀, r₀) ++ (rest.map f).flatten) = some fenv_arr
        rw [happ]
        exact hexec_rest
      · intro id r w' hmem hlookH'
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · obtain ⟨hid, hr⟩ := Prod.mk.inj hmem
          rw [hid] at hlookH'
          rw [hr]
          have hw_eq : w' = w := by
            have h1 := hlookH
            rw [hlookH'] at h1
            exact HIR.Expr.lit.inj (Option.some.inj h1)
          subst hw_eq
          by_cases hdup : (id₀, r₀) ∈ rest
          · exact hval_arr id₀ r₀ w' hdup hlookH
          · have hnotin : ∀ idx, (idx, r₀) ∉ rest := by
              intro idx hcon
              exact hdup (hdist idx r₀ id₀ r₀ (List.mem_cons_of_mem _ hcon)
                (List.mem_cons.mpr (Or.inl rfl)) rfl ▸ hcon)
            rw [hframe_arr r₀ hnotin]
            simp [Env.update]
        · exact hval_arr id r w' hmem hlookH'
      · intro r' hnotin
        have hne : r' ≠ r₀ := by
          intro heq
          subst heq
          exact hnotin id₀ (List.mem_cons.mpr (Or.inl rfl))
        have h1 : fenv_arr.env r' =
              (fenv.env.update r₀ w) r' :=
          hframe_arr r' (by
            intro idx hcon
            exact hnotin idx (List.mem_cons_of_mem _ hcon))
        have hne_b : ¬ (r' == r₀) := by simpa using hne
        simp only [Env.update, if_neg hne_b] at h1
        exact h1

/-- `continue` snapshots preserve the environment relation: copies only write
carried registers, and exclusivity says no other id reads those registers,
so every id's register still holds its value. The value invariant says each
carried register ends holding its id's HIR value (duplicate pairs rewrite
the same value); the frame says registers outside the carried set are
untouched (used for a duplicate-free head register). By induction on the
carried list; each copy's source reads correctly because any earlier
overwrite of that source would itself be an exclusivity violation. -/
theorem carryCopies_exec (ρ : List (HIR.Id × ValId))
    (carried : List (HIR.Id × ValId)) :
    ∀ (copies : List Instr), carryCopies ρ carried = some copies →
    ∀ (prog : Program) (prev : Option MIR.BlockId) (fenv : FullEnv)
      (henv : HEnv),
      RelEnv henv ρ fenv.env → CarriedExcl ρ carried →
      (∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried →
        r₁ = r₂ → id₁ = id₂) →
      ∃ fenv_arr, execInstrsFullFromIn prog prev fenv copies = some fenv_arr ∧
        RelEnv henv ρ fenv_arr.env ∧
        (∀ id r w, (id, r) ∈ carried →
          lookupHEnv henv id = some (.lit w) → fenv_arr.env r = some w) ∧
        (∀ r', (∀ id, (id, r') ∉ carried) →
          fenv_arr.env r' = fenv.env r') := by
  induction carried generalizing ρ with
  | nil =>
      intro copies hc prog prev fenv henv hrel _ _
      simp only [carryCopies] at hc
      obtain rfl := Option.some.inj hc
      refine ⟨fenv, rfl, hrel, ?_, ?_⟩
      · intro id r w hmem
        simp at hmem
      · intro r' _
        rfl
  | cons pr rest ih =>
      obtain ⟨id₀, r₀⟩ := pr
      intro copies hc prog prev fenv henv hrel hexcl hdist
      simp only [carryCopies] at hc
      cases hρ : rhoLookup ρ id₀ with
      | none => rw [hρ] at hc; simp at hc
      | some s =>
          rw [hρ] at hc
          simp only [] at hc
          cases hrec : carryCopies ρ rest with
          | none => simp [hrec] at hc
          | some copies' =>
              rw [hrec] at hc
              simp only [Option.map_some] at hc
              obtain rfl := Option.some.inj hc
              obtain ⟨w, hlookH, hreg⟩ := hrel id₀ s hρ
              have hexec1 : execInstrsFullFromIn prog prev fenv
                  [.copy r₀ s] =
                  some ⟨fenv.env.update r₀ w, fenv.store⟩ := by
                simp [execInstrsFullFromIn, evalInstrFull, hreg]
              have hrel1 : RelEnv henv ρ
                  (⟨fenv.env.update r₀ w, fenv.store⟩ : FullEnv).env := by
                intro id' u' hlook
                by_cases heq : u' = r₀
                · have hid : id' = id₀ := hexcl id₀ r₀
                    (List.mem_cons.mpr (Or.inl rfl)) id' u' hlook heq
                  refine ⟨w, ?_, ?_⟩
                  · rwa [hid]
                  · rw [heq]
                    simp [Env.update]
                · have hbeq : ¬ (u' == r₀) := by simpa using heq
                  obtain ⟨w0, h1, h2⟩ := hrel id' u' hlook
                  exact ⟨w0, h1, by simp [Env.update, hbeq, h2]⟩
              have hexcl_rest : CarriedExcl ρ rest := by
                intro id r hmem id' u' hlook heq
                exact hexcl id r (List.mem_cons_of_mem _ hmem) id' u'
                  hlook heq
              have hdist_rest : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ rest →
                  (id₂, r₂) ∈ rest → r₁ = r₂ → id₁ = id₂ := by
                intro id₁ r₁ id₂ r₂ h₁ h₂ heq
                exact hdist id₁ r₁ id₂ r₂ (List.mem_cons_of_mem _ h₁)
                  (List.mem_cons_of_mem _ h₂) heq
              obtain ⟨fenv_arr, hexec_rest, hrel_arr, hval_arr, hframe_arr⟩ :=
                ih ρ copies' hrec prog prev ⟨fenv.env.update r₀ w, fenv.store⟩ henv hrel1 hexcl_rest hdist_rest
              have happ : execInstrsFullFromIn prog prev fenv
                  ([.copy r₀ s] ++ copies') =
                  execInstrsFullFromIn prog prev
                    ⟨fenv.env.update r₀ w, fenv.store⟩ copies' := by
                rw [execInstrsFullFromIn_append, hexec1]
              refine ⟨fenv_arr, ?_, hrel_arr, ?_, ?_⟩
              · show execInstrsFullFromIn prog prev fenv
                      ([.copy r₀ s] ++ copies') = some fenv_arr
                rw [happ]
                exact hexec_rest
              · intro id r w' hmem hlookH'
                simp only [List.mem_cons] at hmem
                rcases hmem with hmem | hmem
                · obtain ⟨hid, hr⟩ := Prod.mk.inj hmem
                  rw [hid] at hlookH'
                  rw [hr]
                  have hw_eq : w' = w := by
                    have h1 := hlookH
                    rw [hlookH'] at h1
                    exact HIR.Expr.lit.inj (Option.some.inj h1)
                  subst hw_eq
                  by_cases hdup : (id₀, r₀) ∈ rest
                  · exact hval_arr id₀ r₀ w' hdup hlookH
                  · have hnotin : ∀ idx, (idx, r₀) ∉ rest := by
                      intro idx hcon
                      exact hdup (hdist idx r₀ id₀ r₀ (List.mem_cons_of_mem _ hcon)
                        (List.mem_cons.mpr (Or.inl rfl)) rfl ▸ hcon)
                    rw [hframe_arr r₀ hnotin]
                    simp [Env.update]
                · exact hval_arr id r w' hmem hlookH'
              · intro r' hnotin
                have hne : r' ≠ r₀ := by
                  intro heq
                  subst heq
                  exact hnotin id₀ (List.mem_cons.mpr (Or.inl rfl))
                have h1 : fenv_arr.env r' =
                      (fenv.env.update r₀ w) r' :=
                  hframe_arr r' (by
                    intro idx hcon
                    exact hnotin idx (List.mem_cons_of_mem _ hcon))
                have hne_b : ¬ (r' == r₀) := by simpa using hne
                simp only [Env.update, if_neg hne_b] at h1
                exact h1

end Morph.HIRToMIRCorrect
