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

/-!
# Stage C loop-body execution: `lowerStmtsCFG_loopBody_run`

Fifth proof leaf out of the `HIRToMIRBranch` monolith: the C7 spine
worker (moved verbatim, ~4.4k lines — the largest single theorem).
It cites the `arm_total` / `arm_broke` / `arm_continued` workers from
the Arm leaves; everything downstream (oracle lemmas, `whileLoop_correct`,
the totals, the program corollaries) cites this leaf.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Loop-body execution (C7 spine worker): a closed body run from unit
reaches the header on fall-through (back edge, with the body's exit env),
the loop exit on `break`, the header on `continue` (trampoline edge, with
carried values snapshotted), or returns its value; anything else is
vacuous. Straight-line steps peel via `lower_total.1` exactly as in
`arm_total`; `varDecl` is refused under `loop = some` so that case is
vacuous by computation; an `if` chains the taken arm (citing `arm_total` /
`arm_broke` / `arm_continued`) through the join and the rest through the
induction hypothesis. No accumulator hypothesis: arms always run from unit
and `nil` never reads `lastVal` on a `goto` continuation. -/
theorem lowerStmtsCFG_loopBody_run (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (contB : MIR.BlockId) (lastVal : ValId)
      (loop : Option LoopInfo) (info : LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered),
      loop = some info →
      lowerStmtsCFG bId (some contB) false ρ supply nextB lastVal true loop ss =
        some L →
      LoopStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      ∀ (forbid : MIR.BlockId), forbid < nextB → forbid < bId →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv ss (.value (.lit accH)) = (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId) (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB C : Nat), F ≥ blockBound fuelB ss + C →
      CarriedExcl ρ info.carried →
      (∀ id r, (id, r) ∈ info.carried → r < supply) →
      (∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ info.carried → (id₂, r₂) ∈ info.carried →
        r₁ = r₂ → id₁ = id₂) →
      ∀ (hblk : Block) (eblk : Block) (hdr : Block),
      findBlock f contB = some hblk →
      findBlock f info.exit = some eblk →
      findBlock f info.header = some hdr →
      (∀ (u : HIR.Expr), out = .value u →
        ∃ F' fenv_arr, F' ≤ F ∧ F' ≥ C ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            execBlockFromIn prog F' f
              (some ((L.blocks.getLast?.map (fun b => b.id)).getD bId))
              hblk fenv_arr ∧
          RelEnv henv' L.ρ fenv_arr.env) ∧
      (out = .broke →
        ∃ F' fenv_arr blkPrev, F' ≤ F ∧ F' ≥ C ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            execBlockFromIn prog F' f (some blkPrev) eblk fenv_arr ∧
          RelEnv henv' L.ρ fenv_arr.env ∧
          (∀ id r w, (id, r) ∈ info.carried →
            lookupHEnv henv' id = some (.lit w) → fenv_arr.env r = some w)) ∧
      (out = .continued →
        ∃ F' fenv_arr blkPrev, F' ≤ F ∧ F' ≥ C ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            execBlockFromIn prog F' f (some blkPrev) hdr fenv_arr ∧
          (∀ id r w, (id, r) ∈ info.carried →
            lookupHEnv henv' id = some (.lit w) → fenv_arr.env r = some w) ∧
          (∀ r, r < supply → (∀ id, (id, r) ∉ info.carried) →
            fenv_arr.env r = fenv.env r) ∧
          forbid < blkPrev ∧
          (blkPrev = (L.blocks.getLast?.map fun b => b.id).getD bId →
            RelEnv henv' L.ρ fenv_arr.env)) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_e) := by
  intro bId ρ supply nextB contB lastVal loop info ss L hlo h hss hfresh hlast
    forbid hfN hfB
  induction ss generalizing bId ρ supply nextB contB lastVal loop L
    forbid hfN hfB with
  | nil =>
      intro accH henv fenv hrel hacc fuelH henv' out hrun prog f prev F
        hsub hnodf fuelB C hg hexcl hsup hdist hblk eblk hdr hfindC hfindE
        hfindHdr
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          obtain rfl := Option.some.inj h
          cases fuelH with
          | zero =>
              have hst : out = .stuck := (congrArg Prod.fst hrun).symm
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro u hout
                rw [hst] at hout
                exact absurd hout (by simp)
              · intro hbroke
                rw [hst] at hbroke
                exact absurd hbroke (by simp)
              · intro hcont
                rw [hst] at hcont
                exact absurd hcont (by simp)
              · intro e_ret hout
                rw [hst] at hout
                exact absurd hout (by simp)
          | succ fh =>
              have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                  (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
              rw [hstep] at hrun
              have hacc : out = HFlow.value (.lit accH) :=
                (congrArg Prod.fst hrun).symm
              have henv_eq : henv = henv' := congrArg Prod.snd hrun
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro u _hout
                cases F with
                | zero =>
                    have h1 : blockBound fuelB ([] : List HIR.Stmt) ≥ 1 := by
                      rw [blockBound]; omega
                    omega
                | succ F' =>
                    have heq : execBlockFromIn prog (F' + 1) f prev
                        ⟨bId, [], .goto contB⟩ fenv =
                        execBlockFromIn prog F' f (some bId) hblk fenv :=
                      execBlockFromIn_goto prog F' f prev bId [] contB
                        fenv fenv hblk rfl hfindC
                    refine ⟨F', fenv, Nat.le_succ _, ?_, ?_, ?_⟩
                    · have hbb : blockBound fuelB ([] : List HIR.Stmt)
                          ≥ 1 := by
                        rw [blockBound]; omega
                      omega
                    · have hlastB : (([] : List Block).getLast?.map
                        (fun b => b.id)).getD bId = bId := by simp
                      rw [hlastB]
                      exact heq
                    · rw [← henv_eq]
                      exact hrel
              · intro hbroke
                rw [hacc] at hbroke
                exact absurd hbroke (by simp)
              · intro hcont
                rw [hacc] at hcont
                exact absurd hcont (by simp)
              · intro e_ret hout
                rw [hacc] at hout
                exact absurd hout (by simp)
  | cons s rest ih =>
      intro accH henv fenv hrel hacc fuelH henv' out hrun prog f prev F
        hsub hnodf fuelB C hg hexcl hsup hdist hblk eblk hdr hfindC hfindE
        hfindHdr
      cases hss with
      | exprStmt e rest hstr _ hrs =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId (some contB) false ρ s1 nextB v0
                  true loop rest with
              | none => rw [hr] at h; simp at h
              | some Lr =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  cases fuelH with
                  | zero =>
                      have hz : runHIRStmts 0 henv (.exprStmt e :: rest)
                          (.value (.lit accH)) = (.stuck, henv) := rfl
                      rw [hz] at hrun
                      have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · intro u hout
                        rw [hst] at hout
                        exact absurd hout (by simp)
                      · intro hbroke
                        rw [hst] at hbroke
                        exact absurd hbroke (by simp)
                      · intro hcont
                        rw [hst] at hcont
                        exact absurd hcont (by simp)
                      · intro e_ret hout
                        rw [hst] at hout
                        exact absurd hout (by simp)
                  | succ fh =>
                      have hstep : runHIRStmts (fh + 1) henv
                          (.exprStmt e :: rest) (.value (.lit accH)) =
                          (match evalHIR 256 henv e with
                            | none => (HFlow.stuck, henv)
                            | some v => runHIRStmts fh henv rest (.value v)) := rfl
                      rw [hstep] at hrun
                      cases hev : evalHIR 256 henv e with
                      | none =>
                          rw [hev] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          refine ⟨?_, ?_, ?_, ?_⟩
                          · intro u hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro hbroke
                            rw [hst] at hbroke
                            exact absurd hbroke (by simp)
                          · intro hcont
                            rw [hst] at hcont
                            exact absurd hcont (by simp)
                          · intro e_ret hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                      | some r =>
                          rw [hev] at hrun
                          obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2,
                              hrE2, hregE⟩ :=
                            lower_total.1 ρ supply e v0 ie s1 he hstr hfresh
                              henv fenv hrel 256 r hev
                          rw [hrE] at hrun
                          simp only [] at hrun
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
                          have hsup1 : ∀ id r, (id, r) ∈ info.carried →
                              r < s1 :=
                            fun id r hmem =>
                              Nat.lt_of_lt_of_le (hsup _ _ hmem) hs1
                          have hnp_ie : ∀ dst pred src,
                              .phi dst pred src ∉ ie := by
                            intro d p s hm
                            exact IsPure_not_phi
                              (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                          have hexec_ie : execInstrsFullFromIn prog prev fenv
                              ie = some fenv1 := by
                            rw [execInstrsFullFromIn_of_noPhi prog prev fenv
                              _ hnp_ie]
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
                              obtain ⟨ihV, ihB, ihC, ihR⟩ :=
                                ih bId ρ s1 nextB contB v0 loop Lr hlo hr hrs hf1 hlast1 forbid hfN hfB wE henv fenv1 hrel1 hregE' fh henv' out
                                  hrun prog f prev (F'' + 1) hsub' hnodf fuelB
                                  C hg' hexcl hsup1 hdist hblk eblk hdr hfindC
                                  hfindE hfindHdr
                              refine ⟨?_, ?_, ?_, ?_⟩
                              · intro u hout
                                obtain ⟨F', fenv_arr, hle, hge,
                                    heq_rest, hrel_arr⟩ := ihV u hout
                                exact ⟨F', fenv_arr, hle, hge,
                                  hLHS.trans heq_rest, hrel_arr⟩
                              · intro hbroke
                                obtain ⟨F', fenv_arr, blkPrev, hle, hge,
                                    heq_rest, hrel_arr, hval_arr⟩ := ihB hbroke
                                exact ⟨F', fenv_arr, blkPrev, hle, hge,
                                  hLHS.trans heq_rest, hrel_arr, hval_arr⟩
                              · intro hcont
                                obtain ⟨F', fenv_arr, blkPrev, hle, hge,
                                    heq_rest, hcarried, hpreserv, hforbid⟩ := ihC hcont
                                refine ⟨F', fenv_arr, blkPrev, hle, hge,
                                  hLHS.trans heq_rest, hcarried, ?_, hforbid⟩
                                intro r hr hnc
                                exact (hpreserv r (Nat.lt_of_lt_of_le hr hs1) hnc).trans
                                  (lower_preserv_regs ρ supply e v0 ie s1 he fenv fenv1 hexec1 r hr)
                              · intro e_ret hout
                                obtain ⟨w_e, hu_e, heq_rest⟩ := ihR e_ret hout
                                exact ⟨w_e, hu_e, hLHS.trans heq_rest⟩
      | varDecl id τ init rest hstr _ hrs _ =>
          subst hlo
          simp only [lowerStmtsCFG] at h
          simp at h
      | assign id e rest hstr _ hrs hvf =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId (some contB) false
                  (updAssoc ρ id v0) s1 nextB lastVal true loop rest with
              | none => rw [hr] at h; simp at h
              | some Lr =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  have hs1 : supply ≤ s1 :=
                    lower_mono.1 _ _ _ _ _ _ he
                  have hlast1 : lastVal < s1 :=
                    Nat.lt_of_lt_of_le hlast hs1
                  have hva : v0 < s1 :=
                    lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                  have hf1 : FreshAbove (updAssoc ρ id v0) s1 := by
                    intro j u hmem
                    rcases updAssoc_mem ρ id v0 j u hmem with ⟨-, hwu⟩ |
                      hmem'
                    · rw [hwu]
                      exact hva
                    · exact Nat.lt_of_lt_of_le (hfresh j u hmem') hs1
                  have hsup1 : ∀ id0 r0, (id0, r0) ∈ info.carried →
                      r0 < s1 :=
                    fun id0 r0 hmem =>
                      Nat.lt_of_lt_of_le (hsup _ _ hmem) hs1
                  have hexcl' : CarriedExcl (updAssoc ρ id v0)
                      info.carried := by
                    intro id0 r0 hmem id' u' hlook heq
                    by_cases heq' : id' = id
                    · rw [heq'] at hlook
                      have huv : u' = v0 := by
                        have h1 := rhoLookup_updAssoc_id ρ id v0
                        rw [h1] at hlook
                        cases hρ : rhoLookup ρ id with
                        | none => simp [hρ] at hlook
                        | some _ =>
                            simp [hρ] at hlook
                            exact hlook.symm
                      have hrS : r0 < supply := hsup _ _ hmem
                      have hge : supply ≤ v0 :=
                        lowerExpr_result_ge _ _ _ _ _ _ hstr hvf he
                      have hlt : r0 < v0 :=
                        Nat.lt_of_lt_of_le hrS hge
                      rw [← huv, heq] at hlt
                      exact absurd hlt (Nat.lt_irrefl _)
                    · have hlook' : rhoLookup ρ id' = some u' := by
                        have hrr := rhoLookup_updAssoc_ne
                          (fun hh => heq' hh.symm) (v := v0) ρ
                        rw [hrr] at hlook
                        exact hlook
                      exact hexcl id0 r0 hmem id' u' hlook' heq
                  have hbb : blockBound fuelB (.assign id e :: rest)
                      = blockBound fuelB rest := by
                    rw [blockBound, blockBound,
                      armBlockBound_cons_not_if fuelB
                        (fun c th el h => by cases h)
                        (fun c body h => by cases h)]
                  have hg0 : F ≥ blockBound fuelB rest + C := by
                    rw [← hbb]; exact hg
                  cases fuelH with
                  | zero =>
                      have hz : runHIRStmts 0 henv (.assign id e :: rest)
                          (.value (.lit accH)) = (.stuck, henv) := rfl
                      rw [hz] at hrun
                      have hst : out = .stuck :=
                        (congrArg Prod.fst hrun).symm
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · intro u hout
                        rw [hst] at hout
                        exact absurd hout (by simp)
                      · intro hbroke
                        rw [hst] at hbroke
                        exact absurd hbroke (by simp)
                      · intro hcont
                        rw [hst] at hcont
                        exact absurd hcont (by simp)
                      · intro e_ret hout
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
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          refine ⟨?_, ?_, ?_, ?_⟩
                          · intro u hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro hbroke
                            rw [hst] at hbroke
                            exact absurd hbroke (by simp)
                          · intro hcont
                            rw [hst] at hcont
                            exact absurd hcont (by simp)
                          · intro e_ret hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
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
                              fenv (ie ++ Lr.instrs) =
                              execInstrsFullFromIn prog prev fenv1
                                Lr.instrs := by
                            rw [execInstrsFullFromIn_append, hexec]
                          cases F with
                          | zero =>
                              have h1 : blockBound fuelB rest ≥ 1 := by
                                rw [blockBound]; omega
                              omega
                          | succ F' =>
                              have hpeel : execBlockFromIn prog (F' + 1)
                                  f prev ⟨bId, ie ++ Lr.instrs, Lr.term⟩
                                  fenv = execBlockFromIn prog (F' + 1) f
                                  prev ⟨bId, Lr.instrs, Lr.term⟩
                                  fenv1 :=
                                execBlockFromIn_instrs_prefix prog F' f
                                  prev bId ie Lr.instrs Lr.term fenv fenv1
                                  happ
                              have hg' : F' + 1 ≥ blockBound fuelB rest + C := by
                                rw [← hbb]; exact hg
                              have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                                fun b hb => hsub b hb
                              obtain ⟨ihV, ihB, ihC, ihR⟩ :=
                                ih bId (updAssoc ρ id v0) s1 nextB contB lastVal
                                  loop Lr hlo hr hrs hf1 hlast1 forbid hfN hfB accH
                                  (updateHEnv henv id (.lit wE))
                                  fenv1 hrel2 hacc1 fh henv' out hrun prog f
                                  prev (F' + 1) hsub' hnodf fuelB C hg'
                                  hexcl' hsup1 hdist hblk eblk hdr hfindC
                                  hfindE hfindHdr
                              refine ⟨?_, ?_, ?_, ?_⟩
                              · intro u hout
                                obtain ⟨F', fenv_arr, hle, hge,
                                    heq_rest, hrel_arr⟩ := ihV u hout
                                exact ⟨F', fenv_arr, hle, hge,
                                  hpeel.trans heq_rest, hrel_arr⟩
                              · intro hbroke
                                obtain ⟨F', fenv_arr, blkPrev, hle, hge,
                                    heq_rest, hrel_arr, hval_arr⟩ := ihB hbroke
                                exact ⟨F', fenv_arr, blkPrev, hle, hge,
                                  hpeel.trans heq_rest, hrel_arr, hval_arr⟩
                              · intro hcont
                                obtain ⟨F', fenv_arr, blkPrev, hle, hge,
                                    heq_rest, hcarried, hpreserv, hforbid⟩ :=
                                  ihC hcont
                                refine ⟨F', fenv_arr, blkPrev, hle, hge,
                                  hpeel.trans heq_rest, hcarried, ?_, hforbid⟩
                                intro r hr hnc
                                exact (hpreserv r (Nat.lt_of_lt_of_le hr hs1) hnc).trans
                                  (lower_preserv_regs ρ supply e v0 ie s1 he fenv fenv1 hexec1 r hr)
                              · intro e_ret hout
                                obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                  ihR e_ret hout
                                exact ⟨w_e, hu_e,
                                  hpeel.trans heq_rest⟩
      | nop rest hrs =>
          simp only [lowerStmtsCFG] at h
          have hbb : blockBound fuelB (Morph.HIR.Stmt.nop :: rest)
              = blockBound fuelB rest := by
            rw [blockBound, blockBound,
              armBlockBound_cons_not_if fuelB
                (fun c th el h => by cases h)
                (fun c body h => by cases h)]
          have hg' : F ≥ blockBound fuelB rest + C := by
            rw [← hbb]; exact hg
          cases fuelH with
          | zero =>
              have hz : runHIRStmts 0 henv
                  (Morph.HIR.Stmt.nop :: rest)
                  (.value (.lit accH)) = (.stuck, henv) := rfl
              rw [hz] at hrun
              have hst : out = .stuck := (congrArg Prod.fst hrun).symm
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro u hout
                rw [hst] at hout
                exact absurd hout (by simp)
              · intro hbroke
                rw [hst] at hbroke
                exact absurd hbroke (by simp)
              · intro hcont
                rw [hst] at hcont
                exact absurd hcont (by simp)
              · intro e_ret hout
                rw [hst] at hout
                exact absurd hout (by simp)
          | succ fh =>
              have hstep : runHIRStmts (fh + 1) henv
                  (Morph.HIR.Stmt.nop :: rest) (.value (.lit accH)) =
                  runHIRStmts fh henv rest (.value (.lit accH)) := rfl
              rw [hstep] at hrun
              exact ih bId ρ supply nextB contB lastVal loop L hlo h hrs hfresh
                hlast forbid hfN hfB accH henv fenv hrel hacc fh henv' out hrun prog f
                prev F hsub hnodf fuelB C hg' hexcl hsup hdist hblk eblk hdr
                hfindC hfindE hfindHdr
      | ifStmt c th el rest hstr _ hath hael hrs hnb_t hnb_e =>
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
                      cases hr : lowerStmtsCFG (nextB + 2) (some contB) false
                          ρ (le.supply + 1) le.next le.supply true loop
                          rest with
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
                          have hs1 : supply ≤ s1 :=
                            lower_mono.1 _ _ _ _ _ _ heC
                          have hf1 : FreshAbove ρ s1 :=
                            FreshAbove.mono ρ supply s1 hs1 hfresh
                          have hlast1 : lastVal < s1 :=
                            Nat.lt_of_lt_of_le hlast hs1
                          have hsup1 : ∀ id r, (id, r) ∈ info.carried →
                              r < s1 :=
                            fun id r hmem =>
                              Nat.lt_of_lt_of_le (hsup _ _ hmem) hs1
                          obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              ht hath
                          obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              he hael
                          obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                            lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _ _
                              _ _ hr (LoopStmts_to_BranchStmts hrs)
                          have hrho_t : lt.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _
                              ht hath
                          have hrho_e : le.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _
                              he hael
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
                          have hfindEl : findBlock f (nextB + 1) =
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
                                      (.value (.lit accH)) = (.stuck, henv) :=
                                    rfl
                                  rw [hz] at hrun
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  refine ⟨?_, ?_, ?_, ?_⟩
                                  · intro u hout
                                    rw [hst] at hout
                                    exact absurd hout (by simp)
                                  · intro hbroke
                                    rw [hst] at hbroke
                                    exact absurd hbroke (by simp)
                                  · intro hcont
                                    rw [hst] at hcont
                                    exact absurd hcont (by simp)
                                  · intro e_ret hout
                                    rw [hst] at hout
                                    exact absurd hout (by simp)
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
                                                (((HFlow.value
                                                  (.lit accH))).replace u)
                                          | (f, env') => (f, env')
                                        | some (.lit (.bool false)) =>
                                          match runHIRStmts fh henv el
                                              (HFlow.value (.lit .unit)) with
                                          | (HFlow.value u, env') =>
                                              runHIRStmts fh env' rest
                                                (((HFlow.value
                                                  (.lit accH))).replace u)
                                          | (f, env') => (f, env')
                                        | _ => (.stuck, henv)) := rfl
                                  rw [hstep] at hrun
                                  cases hevC : evalHIR 256 henv c with
                                  | none =>
                                      rw [hevC] at hrun
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      refine ⟨?_, ?_, ?_, ?_⟩
                                      · intro u hout
                                        rw [hst] at hout
                                        exact absurd hout (by simp)
                                      · intro hbroke
                                        rw [hst] at hbroke
                                        exact absurd hbroke (by simp)
                                      · intro hcont
                                        rw [hst] at hcont
                                        exact absurd hcont (by simp)
                                      · intro e_ret hout
                                        rw [hst] at hout
                                        exact absurd hout (by simp)
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
                                          (lower_isPure.1 _ _ _ _ _ _ heC _
                                            hm) d p s rfl
                                      have hexec_ic : execInstrsFullFromIn
                                          prog prev fenv ic = some fenvC := by
                                        rw [execInstrsFullFromIn_of_noPhi prog
                                          prev fenv _ hnp_ic]
                                        exact hexecC
                                      have hrelC : RelEnv henv ρ fenvC.env :=
                                        RelEnv_exec henv ρ supply c vc ic s1
                                          heC fenv fenvC hrel hfresh hexecC
                                      cases w with
                                      | bool b =>
                                          cases b with
                                          | true =>
                                              simp only [] at hrun
                                              cases har : runHIRStmts fh henv
                                                  th
                                                  (HFlow.value
                                                    (.lit .unit)) with
                                              | mk out_arm env_arm =>
                                                  rw [har] at hrun
                                                  have hregCb : fenvC.env
                                                      vc =
                                                      some (.bool true) := by
                                                    have hww : (.bool true) =
                                                        wC :=
                                                      HIR.Expr.lit.inj hrC
                                                    rw [hww]
                                                    exact hregC
                                                  have hbool : fenvC.boolOf
                                                      vc = some true :=
                                                    boolOf_of_lit fenvC vc
                                                      true hregCb
                                                  have hentry :
                                                      execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc
                                                        nextB
                                                        (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog
                                                        F'' f (some bId)
                                                        ⟨nextB, lt.instrs,
                                                          lt.term⟩ fenvC :=
                                                    execBlockFromIn_branch_true
                                                      prog F'' f prev bId ic
                                                      vc nextB (nextB + 1)
                                                      fenv fenvC
                                                      ⟨nextB, lt.instrs,
                                                        lt.term⟩ hexec_ic
                                                      hbool hfindT
                                                  have hsub_t : ∀ b ∈
                                                      lt.blocks, b ∈
                                                      f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_lt hb)
                                                  have hC'ge : (2 + max
                                                      (armBlockBound
                                                        fuelB th)
                                                      (armBlockBound
                                                        fuelB el) +
                                                      armBlockBound fuelB
                                                        rest -
                                                      armBlockBound fuelB
                                                        th + C) ≥
                                                      blockBound fuelB
                                                        rest + C := by
                                                    have hBrest : blockBound
                                                        fuelB rest = 1 +
                                                        armBlockBound
                                                          fuelB rest := rfl
                                                    omega
                                                  have hg_t : F'' ≥
                                                      blockBound fuelB th +
                                                      (2 + max
                                                      (armBlockBound
                                                        fuelB th)
                                                      (armBlockBound
                                                        fuelB el) +
                                                      armBlockBound fuelB
                                                        rest -
                                                      armBlockBound fuelB
                                                        th + C) := by
                                                    have hBth : blockBound
                                                        fuelB th = 1 +
                                                        armBlockBound
                                                          fuelB th := rfl
                                                    omega
                                                  cases out_arm with
                                                  | value u_arm =>
                                                      simp only [] at hrun
                                                      obtain ⟨w_arm, hu_arm,
                                                          F', fenv_arr, hle,
                                                          hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arr, hpres_arm⟩ :=
                                                        ((lowerStmtsCFG_arm_total
                                                          budget nextB
                                                          (nextB + 2) ρ s1
                                                          (nextB + 3)
                                                          lastVal false
                                                          loop th lt ht hath
                                                          hf1 hlast1 .unit
                                                          henv fenvC hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm
                                                          (HFlow.value
                                                            u_arm) har
                                                          prog f (some bId)
                                                          ⟨nextB + 2,
                                                          [.phi le.supply
                                                            exitT lt.val,
                                                           .phi le.supply
                                                            exitE le.val] ++
                                                            lr.instrs,
                                                          lr.term⟩ F''
                                                          hsub_t hnodf
                                                          hfindJ fuelB
                                                          (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB th + C)
                                                          hg_t u_arm).1
                                                          rfl)
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
                                                      have hfrL : FreshAbove ρ
                                                          le.supply :=
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
                                                          le.supply w_arm)
                                                            u = some w0
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
                                                      have hf_r : FreshAbove ρ
                                                          (le.supply + 1) :=
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
                                                      have hsup_r : ∀ id r,
                                                          (id, r) ∈
                                                          info.carried →
                                                          r < le.supply +
                                                            1 :=
                                                        fun id r hmem =>
                                                          Nat.lt_of_lt_of_le
                                                            (hsup _ _ hmem)
                                                            (Nat.le_trans
                                                              hs1
                                                              (Nat.le_trans
                                                              hmst
                                                              (Nat.le_trans
                                                              hmse
                                                              (Nat.le_succ
                                                              _))))
                                                      have hsub_r : ∀ b ∈
                                                          lr.blocks, b ∈
                                                          f.blocks :=
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
                                                              .phi
                                                              le.supply
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
                                                              lr.instrs w_arm
                                                              rfl hne_pe
                                                              hreg_arr
                                                          have hJeq :
                                                              execBlockFromIn
                                                              prog (F1 + 1)
                                                              f (some exitT)
                                                              ⟨nextB + 2,
                                                              [.phi
                                                              le.supply
                                                              exitT lt.val,
                                                              .phi
                                                              le.supply
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
                                                              .phi
                                                              le.supply
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
                                                              fuelB rest +
                                                              C :=
                                                            Nat.le_trans
                                                              hC'ge hge
                                                          obtain ⟨ihV, ihB,
                                                              ihC, ihR⟩ :=
                                                            ih (nextB + 2) ρ
                                                              (le.supply + 1)
                                                              le.next contB
                                                              le.supply
                                                              loop lr hlo hr
                                                              hrs hf_r
                                                              hlast_r forbid
                                                              (Nat.lt_of_lt_of_le hfN
                                                                (Nat.le_trans (Nat.le_add_right nextB 3)
                                                                  (Nat.le_trans hmnt hmne)))
                                                              (Nat.lt_of_lt_of_le hfN
                                                                (Nat.le_add_right nextB 2)) w_arm
                                                              env_arm
                                                              ⟨fenv_arr.env.update
                                                              le.supply
                                                              w_arm,
                                                              fenv_arr.store⟩
                                                              hrel_m hreg_m
                                                              fh henv' out
                                                              hrun prog f
                                                              (some exitT)
                                                              (F1 + 1)
                                                              hsub_r hnodf
                                                              fuelB C hg_r
                                                              hexcl hsup_r
                                                              hdist hblk eblk
                                                              hdr hfindC
                                                              hfindE
                                                              hfindHdr
                                                          refine ⟨?_, ?_, ?_,
                                                              ?_⟩
                                                          · intro u hout
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hrel_final⟩ :=
                                                              ihV u hout
                                                            rw
                                                              [if_assembly_exit
                                                              rfl]
                                                            exact ⟨F2,
                                                              fenv_arr2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hrel_final⟩
                                                          · intro hbroke
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hrel_final,
                                                              hval_final⟩ :=
                                                              ihB hbroke
                                                            exact ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hrel_final,
                                                              hval_final⟩
                                                          · intro hcont
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hcarried, hpreserv, hforbid⟩ :=
                                                              ihC hcont
                                                            refine ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hcarried, ?_, ⟨hforbid.1, fun hEq => hforbid.2 (hEq.trans (if_assembly_exit rfl))⟩⟩
                                                            intro r hr hnc
                                                            have hle_sup : supply ≤ le.supply :=
                                                              Nat.le_trans hs1
                                                                (Nat.le_trans hmst hmse)
                                                            have e1 : fenv_arr2.env r =
                                                                (fenv_arr.env.update le.supply w_arm) r :=
                                                              hpreserv r
                                                                (Nat.lt_of_lt_of_le hr
                                                                  (Nat.le_trans hle_sup (Nat.le_succ _))) hnc
                                                            have e2 : (fenv_arr.env.update le.supply
                                                                w_arm) r = fenv_arr.env r := by
                                                              simp [Env.update,
                                                                Nat.ne_of_lt
                                                                  (Nat.lt_of_lt_of_le hr hle_sup)]
                                                            have e3 : fenv_arr.env r = fenvC.env r :=
                                                              hpres_arm r
                                                                (Nat.lt_of_lt_of_le hr hs1)
                                                            have e4 : fenvC.env r = fenv.env r :=
                                                              lower_preserv_regs ρ supply c vc ic s1 heC
                                                                fenv fenvC hexecC r hr
                                                            exact e1.trans (e2.trans (e3.trans e4))
                                                          · intro e_ret hout
                                                            obtain ⟨w_e, hu_e,
                                                              heq_rest⟩ :=
                                                              ihR e_ret hout
                                                            exact ⟨w_e, hu_e,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest))⟩
                                                  | broke =>
                                                      simp only [] at hrun
                                                      have hfalse : False :=
                                                        ArmNoBreak_run hnb_t
                                                          fh henv env_arm
                                                          _ _ (by simp) har
                                                          rfl
                                                      exact hfalse.elim
                                                  | continued =>
                                                      simp only [] at hrun
                                                      have hout_c : out =
                                                          .continued :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      have henv_eq : env_arm =
                                                          henv' :=
                                                        congrArg Prod.snd
                                                          hrun
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_c] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hout_c] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        obtain ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2, hle2,
                                                          hge2, heq_arm, _,
                                                          hcarried, hpreserv, hforbid⟩ :=
                                                          lowerStmtsCFG_arm_continued
                                                          budget nextB
                                                          (nextB + 2) ρ s1
                                                          (nextB + 3)
                                                          lastVal false
                                                          loop th lt ht
                                                          hath hf1 hlast1 forbid
                                                          (Nat.lt_of_lt_of_le hfN
                                                            (Nat.le_add_right nextB 3)) hfN
                                                          .unit henv fenvC
                                                          hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm
                                                          .continued har
                                                          rfl prog f
                                                          (some bId) F''
                                                          hsub_t hnodf
                                                          fuelB (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB th + C)
                                                          hg_t info hlo
                                                          hexcl hdist hdr
                                                          hfindHdr
                                                        rw [henv_eq] at hcarried
                                                        have hgeC : F2 ≥ C :=
                                                          by omega
                                                        refine ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2,
                                                          Nat.le_trans
                                                          hle2
                                                          (Nat.le_succ _),
                                                          hgeC,
                                                          hentry.trans
                                                          heq_arm,
                                                          hcarried, ?_,
                                                          hforbid.1, ?_⟩
                                                        intro r hr hnc
                                                        have e1 : fenv_arr2.env r = fenvC.env r :=
                                                          hpreserv r
                                                            (Nat.lt_of_lt_of_le hr hs1) hnc
                                                        have e2 : fenvC.env r = fenv.env r :=
                                                          lower_preserv_regs ρ supply c vc ic s1 heC
                                                            fenv fenvC hexecC r hr
                                                        exact e1.trans e2
                                                        have hne_entry : nextB ≠ nextB + 2 := by omega
                                                        have hexit_lt : nextB + 2 < nextB + 3 := by omega
                                                        have he2Rest : nextB + 1 + 1 ≤ le.next := by omega
                                                        intro hEq
                                                        exact absurd (hEq.trans (if_assembly_exit rfl))
                                                          (arrNe_restExit hforbid.2 (fun b hb => hbndt b hb)
                                                            (fun b hb => (hbndr b hb).1) hne_entry
                                                            hexit_lt he2Rest hmne)
                                                      · intro e_ret hout
                                                        rw [hout_c] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                  | returned e_arm =>
                                                      simp only [] at hrun
                                                      have hout_r : out =
                                                          .returned e_arm :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_r] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hout_r] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        rw [hout_r] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout2
                                                        have hret_e : e_ret =
                                                            e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                            hout2)).symm
                                                        obtain ⟨w_e, hu_e,
                                                            heq_arm⟩ :=
                                                          ((lowerStmtsCFG_arm_total
                                                            budget nextB
                                                            (nextB + 2) ρ
                                                            s1 (nextB + 3)
                                                            lastVal false
                                                            loop th lt ht
                                                            hath hf1 hlast1
                                                            .unit henv
                                                            fenvC hrelC
                                                            (fun _ => rfl)
                                                            (fun h =>
                                                              absurd h
                                                              (by simp))
                                                            fh env_arm
                                                            (HFlow.returned
                                                              e_arm) har
                                                            prog f
                                                            (some bId)
                                                            ⟨nextB + 2,
                                                            [.phi le.supply
                                                              exitT lt.val,
                                                            .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                            lr.term⟩ F''
                                                            hsub_t hnodf
                                                            hfindJ fuelB
                                                            (2 + max
                                                            (armBlockBound
                                                            fuelB th)
                                                            (armBlockBound
                                                            fuelB el) +
                                                            armBlockBound
                                                            fuelB rest -
                                                            armBlockBound
                                                            fuelB th + C)
                                                            hg_t e_arm).2
                                                            e_arm rfl)
                                                        rw [hret_e]
                                                        exact ⟨w_e, hu_e,
                                                          hentry.trans
                                                          heq_arm⟩
                                                  | stuck =>
                                                      simp only [] at hrun
                                                      have hst : out =
                                                          .stuck :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hst] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hst] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        rw [hst] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout
                                                        rw [hst] at hout
                                                        exact absurd hout
                                                          (by simp)
                                          | false =>
                                              simp only [] at hrun
                                              cases har : runHIRStmts fh
                                                  henv el
                                                  (HFlow.value
                                                    (.lit .unit)) with
                                              | mk out_arm env_arm =>
                                                  rw [har] at hrun
                                                  have hregCb : fenvC.env
                                                      vc =
                                                      some (.bool false) :=
                                                    by
                                                    have hww :
                                                        (.bool false) = wC :=
                                                      HIR.Expr.lit.inj hrC
                                                    rw [hww]
                                                    exact hregC
                                                  have hbool : fenvC.boolOf
                                                      vc = some false :=
                                                    boolOf_of_lit fenvC vc
                                                      false hregCb
                                                  have hentry :
                                                      execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc
                                                        nextB
                                                        (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog
                                                        F'' f (some bId)
                                                        ⟨nextB + 1,
                                                          le.instrs,
                                                          le.term⟩ fenvC :=
                                                    execBlockFromIn_branch_false
                                                      prog F'' f prev bId ic
                                                      vc nextB (nextB + 1)
                                                      fenv fenvC
                                                      ⟨nextB + 1,
                                                        le.instrs,
                                                        le.term⟩ hexec_ic
                                                      hbool hfindEl
                                                  have hsub_e : ∀ b ∈
                                                      le.blocks, b ∈
                                                      f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_le hb)
                                                  have hf_e : FreshAbove ρ
                                                      lt.supply :=
                                                    FreshAbove.mono ρ s1
                                                      lt.supply hmst hf1
                                                  have hlast_e : lastVal <
                                                      lt.supply :=
                                                    Nat.lt_of_lt_of_le
                                                      hlast1 hmst
                                                  have hC'ge : (2 + max
                                                      (armBlockBound
                                                        fuelB th)
                                                      (armBlockBound
                                                        fuelB el) +
                                                      armBlockBound fuelB
                                                        rest -
                                                      armBlockBound fuelB
                                                        el + C) ≥
                                                      blockBound fuelB
                                                        rest + C := by
                                                    have hBrest : blockBound
                                                        fuelB rest = 1 +
                                                        armBlockBound
                                                          fuelB rest := rfl
                                                    omega
                                                  have hg_e : F'' ≥
                                                      blockBound fuelB el +
                                                      (2 + max
                                                      (armBlockBound
                                                        fuelB th)
                                                      (armBlockBound
                                                        fuelB el) +
                                                      armBlockBound fuelB
                                                        rest -
                                                      armBlockBound fuelB
                                                        el + C) := by
                                                    have hBel : blockBound
                                                        fuelB el = 1 +
                                                        armBlockBound
                                                          fuelB el := rfl
                                                    omega
                                                  cases out_arm with
                                                  | value u_arm =>
                                                      simp only [] at hrun
                                                      obtain ⟨w_arm, hu_arm,
                                                          F', fenv_arr, hle,
                                                          hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arr, hpres_arm⟩ :=
                                                        ((lowerStmtsCFG_arm_total
                                                          budget (nextB + 1)
                                                          (nextB + 2) ρ
                                                          lt.supply lt.next
                                                          lastVal false
                                                          loop el le he hael
                                                          hf_e hlast_e .unit
                                                          henv fenvC hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm
                                                          (HFlow.value
                                                            u_arm) har
                                                          prog f (some bId)
                                                          ⟨nextB + 2,
                                                          [.phi le.supply
                                                            exitT lt.val,
                                                           .phi le.supply
                                                            exitE le.val] ++
                                                            lr.instrs,
                                                          lr.term⟩ F''
                                                          hsub_e hnodf
                                                          hfindJ fuelB
                                                          (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB el + C)
                                                          hg_e u_arm).1
                                                          rfl)
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
                                                      have hfrL : FreshAbove ρ
                                                          le.supply :=
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
                                                          le.supply w_arm)
                                                            u = some w0
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
                                                      have hf_r : FreshAbove ρ
                                                          (le.supply + 1) :=
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
                                                      have hsup_r : ∀ id r,
                                                          (id, r) ∈
                                                          info.carried →
                                                          r < le.supply +
                                                            1 :=
                                                        fun id r hmem =>
                                                          Nat.lt_of_lt_of_le
                                                            (hsup _ _ hmem)
                                                            (Nat.le_trans
                                                              hs1
                                                              (Nat.le_trans
                                                              hmst
                                                              (Nat.le_trans
                                                              hmse
                                                              (Nat.le_succ
                                                              _))))
                                                      have hsub_r : ∀ b ∈
                                                          lr.blocks, b ∈
                                                          f.blocks :=
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
                                                              .phi
                                                              le.supply
                                                              exitE le.val] ++
                                                              lr.instrs) =
                                                              execInstrsFullFromIn
                                                              prog
                                                              (some exitE)
                                                              ⟨fenv_arr.env.update
                                                              le.supply
                                                              w_arm,
                                                              fenv_arr.store⟩
                                                              lr.instrs :=
                                                            by
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
                                                              .phi
                                                              le.supply
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
                                                              .phi
                                                              le.supply
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
                                                              fuelB rest +
                                                              C :=
                                                            Nat.le_trans
                                                              hC'ge hge
                                                          obtain ⟨ihV, ihB,
                                                              ihC, ihR⟩ :=
                                                            ih (nextB + 2) ρ
                                                              (le.supply + 1)
                                                              le.next contB
                                                              le.supply
                                                              loop lr hlo hr
                                                              hrs hf_r
                                                              hlast_r forbid
                                                              (Nat.lt_of_lt_of_le hfN
                                                                (Nat.le_trans (Nat.le_add_right nextB 3)
                                                                  (Nat.le_trans hmnt hmne)))
                                                              (Nat.lt_of_lt_of_le hfN
                                                                (Nat.le_add_right nextB 2)) w_arm
                                                              env_arm
                                                              ⟨fenv_arr.env.update
                                                              le.supply
                                                              w_arm,
                                                              fenv_arr.store⟩
                                                              hrel_m hreg_m
                                                              fh henv' out
                                                              hrun prog f
                                                              (some exitE)
                                                              (F1 + 1)
                                                              hsub_r hnodf
                                                              fuelB C hg_r
                                                              hexcl hsup_r
                                                              hdist hblk eblk
                                                              hdr hfindC
                                                              hfindE
                                                              hfindHdr
                                                          refine ⟨?_, ?_, ?_,
                                                              ?_⟩
                                                          · intro u hout
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hrel_final⟩ :=
                                                              ihV u hout
                                                            rw
                                                              [if_assembly_exit
                                                              rfl]
                                                            exact ⟨F2,
                                                              fenv_arr2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hrel_final⟩
                                                          · intro hbroke
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hrel_final,
                                                              hval_final⟩ :=
                                                              ihB hbroke
                                                            exact ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hrel_final,
                                                              hval_final⟩
                                                          · intro hcont
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hcarried, hpreserv, hforbid⟩ :=
                                                              ihC hcont
                                                            refine ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hcarried, ?_, ⟨hforbid.1, fun hEq => hforbid.2 (hEq.trans (if_assembly_exit rfl))⟩⟩
                                                            intro r hr hnc
                                                            have hle_sup : supply ≤ le.supply :=
                                                              Nat.le_trans hs1
                                                                (Nat.le_trans hmst hmse)
                                                            have e1 : fenv_arr2.env r =
                                                                (fenv_arr.env.update le.supply w_arm) r :=
                                                              hpreserv r
                                                                (Nat.lt_of_lt_of_le hr
                                                                  (Nat.le_trans hle_sup (Nat.le_succ _))) hnc
                                                            have e2 : (fenv_arr.env.update le.supply
                                                                w_arm) r = fenv_arr.env r := by
                                                              simp [Env.update,
                                                                Nat.ne_of_lt
                                                                  (Nat.lt_of_lt_of_le hr hle_sup)]
                                                            have e3 : fenv_arr.env r = fenvC.env r :=
                                                              hpres_arm r
                                                                (Nat.lt_of_lt_of_le hr (Nat.le_trans hs1 hmst))
                                                            have e4 : fenvC.env r = fenv.env r :=
                                                              lower_preserv_regs ρ supply c vc ic s1 heC
                                                                fenv fenvC hexecC r hr
                                                            exact e1.trans (e2.trans (e3.trans e4))
                                                          · intro e_ret hout
                                                            obtain ⟨w_e, hu_e,
                                                              heq_rest⟩ :=
                                                              ihR e_ret hout
                                                            exact ⟨w_e, hu_e,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest))⟩
                                                  | broke =>
                                                      simp only [] at hrun
                                                      have hfalse : False :=
                                                        ArmNoBreak_run hnb_e
                                                          fh henv env_arm
                                                          _ _ (by simp) har
                                                          rfl
                                                      exact hfalse.elim
                                                  | continued =>
                                                      simp only [] at hrun
                                                      have hout_c : out =
                                                          .continued :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      have henv_eq : env_arm =
                                                          henv' :=
                                                        congrArg Prod.snd
                                                          hrun
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_c] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hout_c] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        obtain ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2, hle2,
                                                          hge2, heq_arm, _,
                                                          hcarried, hpreserv, hforbid⟩ :=
                                                          lowerStmtsCFG_arm_continued
                                                          budget
                                                          (nextB + 1)
                                                          (nextB + 2) ρ
                                                          lt.supply lt.next
                                                          lastVal false
                                                          loop el le he
                                                          hael hf_e hlast_e forbid
                                                          (Nat.lt_of_lt_of_le hfN
                                                            (Nat.le_trans (Nat.le_add_right nextB 3) hmnt))
                                                          (Nat.lt_of_lt_of_le hfN
                                                            (Nat.le_add_right nextB 1))
                                                          .unit henv fenvC
                                                          hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm
                                                          .continued har
                                                          rfl prog f
                                                          (some bId) F''
                                                          hsub_e hnodf
                                                          fuelB (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB el + C)
                                                          hg_e info hlo
                                                          hexcl hdist hdr
                                                          hfindHdr
                                                        rw [henv_eq] at hcarried
                                                        have hgeC : F2 ≥ C :=
                                                          by omega
                                                        refine ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2,
                                                          Nat.le_trans
                                                          hle2
                                                          (Nat.le_succ _),
                                                          hgeC,
                                                          hentry.trans
                                                          heq_arm,
                                                          hcarried, ?_,
                                                          hforbid.1, ?_⟩
                                                        intro r hr hnc
                                                        have e1 : fenv_arr2.env r = fenvC.env r :=
                                                          hpreserv r
                                                            (Nat.lt_of_lt_of_le hr (Nat.le_trans hs1 hmst)) hnc
                                                        have e2 : fenvC.env r = fenv.env r :=
                                                          lower_preserv_regs ρ supply c vc ic s1 heC
                                                            fenv fenvC hexecC r hr
                                                        exact e1.trans e2
                                                        have hne_entry : nextB + 1 ≠ nextB + 2 := by omega
                                                        have hexit_lt : nextB + 2 < lt.next := by omega
                                                        have he2Rest : nextB + 1 + 1 + 1 ≤ le.next := by omega
                                                        intro hEq
                                                        exact absurd (hEq.trans (if_assembly_exit rfl))
                                                          (arrNe_restExit hforbid.2 (fun b hb => hbnde b hb)
                                                            (fun b hb => (hbndr b hb).1) hne_entry
                                                            hexit_lt he2Rest (Nat.le_refl _))
                                                      · intro e_ret hout
                                                        rw [hout_c] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                  | returned e_arm =>
                                                      simp only [] at hrun
                                                      have hout_r : out =
                                                          .returned e_arm :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_r] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hout_r] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        rw [hout_r] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout2
                                                        have hret_e : e_ret =
                                                            e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                            hout2)).symm
                                                        obtain ⟨w_e, hu_e,
                                                            heq_arm⟩ :=
                                                          ((lowerStmtsCFG_arm_total
                                                            budget
                                                            (nextB + 1)
                                                            (nextB + 2) ρ
                                                            lt.supply
                                                            lt.next lastVal
                                                            false loop el le
                                                            he hael hf_e
                                                            hlast_e .unit
                                                            henv fenvC hrelC
                                                            (fun _ => rfl)
                                                            (fun h =>
                                                              absurd h
                                                              (by simp))
                                                            fh env_arm
                                                            (HFlow.returned
                                                              e_arm) har
                                                            prog f
                                                            (some bId)
                                                            ⟨nextB + 2,
                                                            [.phi le.supply
                                                              exitT lt.val,
                                                            .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                            lr.term⟩ F''
                                                            hsub_e hnodf
                                                            hfindJ fuelB
                                                            (2 + max
                                                            (armBlockBound
                                                            fuelB th)
                                                            (armBlockBound
                                                            fuelB el) +
                                                            armBlockBound
                                                            fuelB rest -
                                                            armBlockBound
                                                            fuelB el + C)
                                                            hg_e e_arm).2
                                                            e_arm rfl)
                                                        rw [hret_e]
                                                        exact ⟨w_e, hu_e,
                                                          hentry.trans
                                                          heq_arm⟩
                                                  | stuck =>
                                                      simp only [] at hrun
                                                      have hst : out =
                                                          .stuck :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hst] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hst] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        rw [hst] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout
                                                        rw [hst] at hout
                                                        exact absurd hout
                                                          (by simp)
                                      | int _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | string _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | pointer _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | float _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | unit =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | undef =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | some _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | none =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | ok _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | err _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | tuple_ _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | array_ _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | loc _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | closure _ _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
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
                      cases hr : lowerStmtsCFG (nextB + 2) (some contB) false
                          ρ (le.supply + 1) le.next le.supply true loop
                          rest with
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
                          have hs1 : supply ≤ s1 :=
                            lower_mono.1 _ _ _ _ _ _ heC
                          have hf1 : FreshAbove ρ s1 :=
                            FreshAbove.mono ρ supply s1 hs1 hfresh
                          have hlast1 : lastVal < s1 :=
                            Nat.lt_of_lt_of_le hlast hs1
                          have hsup1 : ∀ id r, (id, r) ∈ info.carried →
                              r < s1 :=
                            fun id r hmem =>
                              Nat.lt_of_lt_of_le (hsup _ _ hmem) hs1
                          obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              ht hath
                          obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                            lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _
                              he hael
                          obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                            lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _ _
                              _ _ hr (LoopStmts_to_BranchStmts hrs)
                          have hrho_t : lt.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _
                              ht hath
                          have hrho_e : le.ρ = ρ :=
                            lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ _
                              he hael
                          have hrho_r : lr.ρ = ρ :=
                            lowerStmtsCFG_branchArm_rho budget (nextB + 2)
                              (some contB) ρ (le.supply + 1) le.next
                              le.supply true loop rest lr hr harm
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
                          have hfindEl : findBlock f (nextB + 1) =
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
                                      (.value (.lit accH)) = (.stuck, henv) :=
                                    rfl
                                  rw [hz] at hrun
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  refine ⟨?_, ?_, ?_, ?_⟩
                                  · intro u hout
                                    rw [hst] at hout
                                    exact absurd hout (by simp)
                                  · intro hbroke
                                    rw [hst] at hbroke
                                    exact absurd hbroke (by simp)
                                  · intro hcont
                                    rw [hst] at hcont
                                    exact absurd hcont (by simp)
                                  · intro e_ret hout
                                    rw [hst] at hout
                                    exact absurd hout (by simp)
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
                                                (((HFlow.value
                                                  (.lit accH))).replace u)
                                          | (f, env') => (f, env')
                                        | some (.lit (.bool false)) =>
                                          match runHIRStmts fh henv el
                                              (HFlow.value (.lit .unit)) with
                                          | (HFlow.value u, env') =>
                                              runHIRStmts fh env' rest
                                                (((HFlow.value
                                                  (.lit accH))).replace u)
                                          | (f, env') => (f, env')
                                        | _ => (.stuck, henv)) := rfl
                                  rw [hstep] at hrun
                                  cases hevC : evalHIR 256 henv c with
                                  | none =>
                                      rw [hevC] at hrun
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      refine ⟨?_, ?_, ?_, ?_⟩
                                      · intro u hout
                                        rw [hst] at hout
                                        exact absurd hout (by simp)
                                      · intro hbroke
                                        rw [hst] at hbroke
                                        exact absurd hbroke (by simp)
                                      · intro hcont
                                        rw [hst] at hcont
                                        exact absurd hcont (by simp)
                                      · intro e_ret hout
                                        rw [hst] at hout
                                        exact absurd hout (by simp)
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
                                          (lower_isPure.1 _ _ _ _ _ _ heC _
                                            hm) d p s rfl
                                      have hexec_ic : execInstrsFullFromIn
                                          prog prev fenv ic = some fenvC := by
                                        rw [execInstrsFullFromIn_of_noPhi prog
                                          prev fenv _ hnp_ic]
                                        exact hexecC
                                      have hrelC : RelEnv henv ρ fenvC.env :=
                                        RelEnv_exec henv ρ supply c vc ic s1
                                          heC fenv fenvC hrel hfresh hexecC
                                      cases w with
                                      | bool b =>
                                          cases b with
                                          | true =>
                                              simp only [] at hrun
                                              cases har : runHIRStmts fh henv
                                                  th
                                                  (HFlow.value
                                                    (.lit .unit)) with
                                              | mk out_arm env_arm =>
                                                  rw [har] at hrun
                                                  have hregCb : fenvC.env
                                                      vc =
                                                      some (.bool true) := by
                                                    have hww : (.bool true) =
                                                        wC :=
                                                      HIR.Expr.lit.inj hrC
                                                    rw [hww]
                                                    exact hregC
                                                  have hbool : fenvC.boolOf
                                                      vc = some true :=
                                                    boolOf_of_lit fenvC vc
                                                      true hregCb
                                                  have hentry :
                                                      execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc
                                                        nextB
                                                        (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog
                                                        F'' f (some bId)
                                                        ⟨nextB, lt.instrs,
                                                          lt.term⟩ fenvC :=
                                                    execBlockFromIn_branch_true
                                                      prog F'' f prev bId ic
                                                      vc nextB (nextB + 1)
                                                      fenv fenvC
                                                      ⟨nextB, lt.instrs,
                                                        lt.term⟩ hexec_ic
                                                      hbool hfindT
                                                  have hsub_t : ∀ b ∈
                                                      lt.blocks, b ∈
                                                      f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_lt hb)
                                                  have hC'ge : (2 + max
                                                      (armBlockBound
                                                        fuelB th)
                                                      (armBlockBound
                                                        fuelB el) +
                                                      armBlockBound fuelB
                                                        rest -
                                                      armBlockBound fuelB
                                                        th + C) ≥
                                                      blockBound fuelB
                                                        rest + C := by
                                                    have hBrest : blockBound
                                                        fuelB rest = 1 +
                                                        armBlockBound
                                                          fuelB rest := rfl
                                                    omega
                                                  have hg_t : F'' ≥
                                                      blockBound fuelB th +
                                                      (2 + max
                                                      (armBlockBound
                                                        fuelB th)
                                                      (armBlockBound
                                                        fuelB el) +
                                                      armBlockBound fuelB
                                                        rest -
                                                      armBlockBound fuelB
                                                        th + C) := by
                                                    have hBth : blockBound
                                                        fuelB th = 1 +
                                                        armBlockBound
                                                          fuelB th := rfl
                                                    omega
                                                  cases out_arm with
                                                  | value u_arm =>
                                                      simp only [] at hrun
                                                      obtain ⟨w_arm, hu_arm,
                                                          F', fenv_arr, hle,
                                                          hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arr, hpres_arm⟩ :=
                                                        ((lowerStmtsCFG_arm_total
                                                          budget nextB
                                                          (nextB + 2) ρ s1
                                                          (nextB + 3)
                                                          lastVal false
                                                          loop th lt ht hath
                                                          hf1 hlast1 .unit
                                                          henv fenvC hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm
                                                          (HFlow.value
                                                            u_arm) har
                                                          prog f (some bId)
                                                          ⟨nextB + 2,
                                                          [.phi le.supply
                                                            exitT lt.val,
                                                           .phi le.supply
                                                            exitE le.val] ++
                                                            lr.instrs,
                                                          lr.term⟩ F''
                                                          hsub_t hnodf
                                                          hfindJ fuelB
                                                          (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB th + C)
                                                          hg_t u_arm).1
                                                          rfl)
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
                                                      have hfrL : FreshAbove ρ
                                                          le.supply :=
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
                                                          le.supply w_arm)
                                                            u = some w0
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
                                                      have hf_r : FreshAbove ρ
                                                          (le.supply + 1) :=
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
                                                      have hsup_r : ∀ id r,
                                                          (id, r) ∈
                                                          info.carried →
                                                          r < le.supply +
                                                            1 :=
                                                        fun id r hmem =>
                                                          Nat.lt_of_lt_of_le
                                                            (hsup _ _ hmem)
                                                            (Nat.le_trans
                                                              hs1
                                                              (Nat.le_trans
                                                              hmst
                                                              (Nat.le_trans
                                                              hmse
                                                              (Nat.le_succ
                                                              _))))
                                                      have hsub_r : ∀ b ∈
                                                          lr.blocks, b ∈
                                                          f.blocks :=
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
                                                              .phi
                                                              le.supply
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
                                                              lr.instrs w_arm
                                                              rfl hne_pe
                                                              hreg_arr
                                                          have hJeq :
                                                              execBlockFromIn
                                                              prog (F1 + 1)
                                                              f (some exitT)
                                                              ⟨nextB + 2,
                                                              [.phi
                                                              le.supply
                                                              exitT lt.val,
                                                              .phi
                                                              le.supply
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
                                                              .phi
                                                              le.supply
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
                                                              fuelB rest +
                                                              C :=
                                                            Nat.le_trans
                                                              hC'ge hge
                                                          obtain ⟨ihV, ihB,
                                                              ihC, ihR⟩ :=
                                                            ih (nextB + 2) ρ
                                                              (le.supply + 1)
                                                              le.next contB
                                                              le.supply
                                                              loop lr hlo hr
                                                              hrs hf_r
                                                              hlast_r forbid
                                                              (Nat.lt_of_lt_of_le hfN
                                                                (Nat.le_trans (Nat.le_add_right nextB 3)
                                                                  (Nat.le_trans hmnt hmne)))
                                                              (Nat.lt_of_lt_of_le hfN
                                                                (Nat.le_add_right nextB 2)) w_arm
                                                              env_arm
                                                              ⟨fenv_arr.env.update
                                                              le.supply
                                                              w_arm,
                                                              fenv_arr.store⟩
                                                              hrel_m hreg_m
                                                              fh henv' out
                                                              hrun prog f
                                                              (some exitT)
                                                              (F1 + 1)
                                                              hsub_r hnodf
                                                              fuelB C hg_r
                                                              hexcl hsup_r
                                                              hdist hblk eblk
                                                              hdr hfindC
                                                              hfindE
                                                              hfindHdr
                                                          refine ⟨?_, ?_, ?_,
                                                              ?_⟩
                                                          · intro u hout
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hrel_final⟩ :=
                                                              ihV u hout
                                                            rw
                                                              [if_assembly_exit
                                                              rfl]
                                                            exact ⟨F2,
                                                              fenv_arr2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hrel_final⟩
                                                          · intro hbroke
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hrel_final,
                                                              hval_final⟩ :=
                                                              ihB hbroke
                                                            exact ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hrel_final,
                                                              hval_final⟩
                                                          · intro hcont
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hcarried, hpreserv, hforbid⟩ :=
                                                              ihC hcont
                                                            refine ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hcarried, ?_, ⟨hforbid.1, fun hEq => hforbid.2 (hEq.trans (if_assembly_exit rfl))⟩⟩
                                                            intro r hr hnc
                                                            have hle_sup : supply ≤ le.supply :=
                                                              Nat.le_trans hs1
                                                                (Nat.le_trans hmst hmse)
                                                            have e1 : fenv_arr2.env r =
                                                                (fenv_arr.env.update le.supply w_arm) r :=
                                                              hpreserv r
                                                                (Nat.lt_of_lt_of_le hr
                                                                  (Nat.le_trans hle_sup (Nat.le_succ _))) hnc
                                                            have e2 : (fenv_arr.env.update le.supply
                                                                w_arm) r = fenv_arr.env r := by
                                                              simp [Env.update,
                                                                Nat.ne_of_lt
                                                                  (Nat.lt_of_lt_of_le hr hle_sup)]
                                                            have e3 : fenv_arr.env r = fenvC.env r :=
                                                              hpres_arm r
                                                                (Nat.lt_of_lt_of_le hr hs1)
                                                            have e4 : fenvC.env r = fenv.env r :=
                                                              lower_preserv_regs ρ supply c vc ic s1 heC
                                                                fenv fenvC hexecC r hr
                                                            exact e1.trans (e2.trans (e3.trans e4))
                                                          · intro e_ret hout
                                                            obtain ⟨w_e, hu_e,
                                                              heq_rest⟩ :=
                                                              ihR e_ret hout
                                                            exact ⟨w_e, hu_e,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest))⟩
                                                  | broke =>
                                                      simp only [] at hrun
                                                      have hout_b : out =
                                                          .broke :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      have henv_eq : env_arm =
                                                          henv' :=
                                                        congrArg Prod.snd
                                                          hrun
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_b] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        obtain ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2, hle2,
                                                          hge2, heq_arm,
                                                          hrel_final,
                                                          hval_final⟩ :=
                                                          lowerStmtsCFG_arm_broke
                                                          budget nextB
                                                          (nextB + 2) ρ s1
                                                          (nextB + 3)
                                                          lastVal false
                                                          loop th lt ht
                                                          hath hf1 hlast1
                                                          .unit henv fenvC
                                                          hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm .broke
                                                          har rfl prog f
                                                          (some bId) F''
                                                          hsub_t hnodf
                                                          fuelB (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB th + C)
                                                          hg_t info hlo
                                                          hexcl hdist eblk
                                                          hfindE
                                                        rw [henv_eq, hrho_t,
                                                          ← hrho_r] at hrel_final
                                                        rw [henv_eq] at hval_final
                                                        have hgeC : F2 ≥ C :=
                                                          by omega
                                                        exact ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2,
                                                          Nat.le_trans
                                                          hle2
                                                          (Nat.le_succ _),
                                                          hgeC,
                                                          hentry.trans
                                                          heq_arm,
                                                          hrel_final,
                                                          hval_final⟩
                                                      · intro hcont
                                                        rw [hout_b] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout
                                                        rw [hout_b] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                  | continued =>
                                                      simp only [] at hrun
                                                      have hout_c : out =
                                                          .continued :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      have henv_eq : env_arm =
                                                          henv' :=
                                                        congrArg Prod.snd
                                                          hrun
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_c] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hout_c] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        obtain ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2, hle2,
                                                          hge2, heq_arm, _,
                                                          hcarried, hpreserv, hforbid⟩ :=
                                                          lowerStmtsCFG_arm_continued
                                                          budget nextB
                                                          (nextB + 2) ρ s1
                                                          (nextB + 3)
                                                          lastVal false
                                                          loop th lt ht
                                                          hath hf1 hlast1 forbid
                                                          (Nat.lt_of_lt_of_le hfN
                                                            (Nat.le_add_right nextB 3)) hfN
                                                          .unit henv fenvC
                                                          hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm
                                                          .continued har
                                                          rfl prog f
                                                          (some bId) F''
                                                          hsub_t hnodf
                                                          fuelB (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB th + C)
                                                          hg_t info hlo
                                                          hexcl hdist hdr
                                                          hfindHdr
                                                        rw [henv_eq] at hcarried
                                                        have hgeC : F2 ≥ C :=
                                                          by omega
                                                        refine ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2,
                                                          Nat.le_trans
                                                          hle2
                                                          (Nat.le_succ _),
                                                          hgeC,
                                                          hentry.trans
                                                          heq_arm,
                                                          hcarried, ?_,
                                                          hforbid.1, ?_⟩
                                                        intro r hr hnc
                                                        have e1 : fenv_arr2.env r = fenvC.env r :=
                                                          hpreserv r
                                                            (Nat.lt_of_lt_of_le hr hs1) hnc
                                                        have e2 : fenvC.env r = fenv.env r :=
                                                          lower_preserv_regs ρ supply c vc ic s1 heC
                                                            fenv fenvC hexecC r hr
                                                        exact e1.trans e2
                                                        have hne_entry : nextB ≠ nextB + 2 := by omega
                                                        have hexit_lt : nextB + 2 < nextB + 3 := by omega
                                                        have he2Rest : nextB + 1 + 1 ≤ le.next := by omega
                                                        intro hEq
                                                        exact absurd (hEq.trans (if_assembly_exit rfl))
                                                          (arrNe_restExit hforbid.2 (fun b hb => hbndt b hb)
                                                            (fun b hb => (hbndr b hb).1) hne_entry
                                                            hexit_lt he2Rest hmne)
                                                      · intro e_ret hout
                                                        rw [hout_c] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                  | returned e_arm =>
                                                      simp only [] at hrun
                                                      have hout_r : out =
                                                          .returned e_arm :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_r] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hout_r] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        rw [hout_r] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout2
                                                        have hret_e : e_ret =
                                                            e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                            hout2)).symm
                                                        obtain ⟨w_e, hu_e,
                                                            heq_arm⟩ :=
                                                          ((lowerStmtsCFG_arm_total
                                                            budget nextB
                                                            (nextB + 2) ρ
                                                            s1 (nextB + 3)
                                                            lastVal false
                                                            loop th lt ht
                                                            hath hf1 hlast1
                                                            .unit henv
                                                            fenvC hrelC
                                                            (fun _ => rfl)
                                                            (fun h =>
                                                              absurd h
                                                              (by simp))
                                                            fh env_arm
                                                            (HFlow.returned
                                                              e_arm) har
                                                            prog f
                                                            (some bId)
                                                            ⟨nextB + 2,
                                                            [.phi le.supply
                                                              exitT lt.val,
                                                            .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                            lr.term⟩ F''
                                                            hsub_t hnodf
                                                            hfindJ fuelB
                                                            (2 + max
                                                            (armBlockBound
                                                            fuelB th)
                                                            (armBlockBound
                                                            fuelB el) +
                                                            armBlockBound
                                                            fuelB rest -
                                                            armBlockBound
                                                            fuelB th + C)
                                                            hg_t e_arm).2
                                                            e_arm rfl)
                                                        rw [hret_e]
                                                        exact ⟨w_e, hu_e,
                                                          hentry.trans
                                                          heq_arm⟩
                                                  | stuck =>
                                                      simp only [] at hrun
                                                      have hst : out =
                                                          .stuck :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hst] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hst] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        rw [hst] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout
                                                        rw [hst] at hout
                                                        exact absurd hout
                                                          (by simp)
                                          | false =>
                                              simp only [] at hrun
                                              cases har : runHIRStmts fh henv
                                                  el
                                                  (HFlow.value
                                                    (.lit .unit)) with
                                              | mk out_arm env_arm =>
                                                  rw [har] at hrun
                                                  have hregCb : fenvC.env
                                                      vc =
                                                      some (.bool false) :=
                                                    by
                                                    have hww :
                                                        (.bool false) = wC :=
                                                      HIR.Expr.lit.inj hrC
                                                    rw [hww]
                                                    exact hregC
                                                  have hbool : fenvC.boolOf
                                                      vc = some false :=
                                                    boolOf_of_lit fenvC vc
                                                      false hregCb
                                                  have hentry :
                                                      execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc
                                                        nextB
                                                        (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog
                                                        F'' f (some bId)
                                                        ⟨nextB + 1,
                                                          le.instrs,
                                                          le.term⟩ fenvC :=
                                                    execBlockFromIn_branch_false
                                                      prog F'' f prev bId ic
                                                      vc nextB (nextB + 1)
                                                      fenv fenvC
                                                      ⟨nextB + 1,
                                                        le.instrs,
                                                        le.term⟩ hexec_ic
                                                      hbool hfindEl
                                                  have hsub_e : ∀ b ∈
                                                      le.blocks, b ∈
                                                      f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_le hb)
                                                  have hf_e : FreshAbove ρ
                                                      lt.supply :=
                                                    FreshAbove.mono ρ s1
                                                      lt.supply hmst hf1
                                                  have hlast_e : lastVal <
                                                      lt.supply :=
                                                    Nat.lt_of_lt_of_le
                                                      hlast1 hmst
                                                  have hC'ge : (2 + max
                                                      (armBlockBound
                                                        fuelB th)
                                                      (armBlockBound
                                                        fuelB el) +
                                                      armBlockBound fuelB
                                                        rest -
                                                      armBlockBound fuelB
                                                        el + C) ≥
                                                      blockBound fuelB
                                                        rest + C := by
                                                    have hBrest : blockBound
                                                        fuelB rest = 1 +
                                                        armBlockBound
                                                          fuelB rest := rfl
                                                    omega
                                                  have hg_e : F'' ≥
                                                      blockBound fuelB el +
                                                      (2 + max
                                                      (armBlockBound
                                                        fuelB th)
                                                      (armBlockBound
                                                        fuelB el) +
                                                      armBlockBound fuelB
                                                        rest -
                                                      armBlockBound fuelB
                                                        el + C) := by
                                                    have hBel : blockBound
                                                        fuelB el = 1 +
                                                        armBlockBound
                                                          fuelB el := rfl
                                                    omega
                                                  cases out_arm with
                                                  | value u_arm =>
                                                      simp only [] at hrun
                                                      obtain ⟨w_arm, hu_arm,
                                                          F', fenv_arr, hle,
                                                          hge, heq_arm,
                                                          hrel_arm,
                                                          hreg_arr, hpres_arm⟩ :=
                                                        ((lowerStmtsCFG_arm_total
                                                          budget (nextB + 1)
                                                          (nextB + 2) ρ
                                                          lt.supply lt.next
                                                          lastVal false
                                                          loop el le he hael
                                                          hf_e hlast_e .unit
                                                          henv fenvC hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm
                                                          (HFlow.value
                                                            u_arm) har
                                                          prog f (some bId)
                                                          ⟨nextB + 2,
                                                          [.phi le.supply
                                                            exitT lt.val,
                                                           .phi le.supply
                                                            exitE le.val] ++
                                                            lr.instrs,
                                                          lr.term⟩ F''
                                                          hsub_e hnodf
                                                          hfindJ fuelB
                                                          (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB el + C)
                                                          hg_e u_arm).1
                                                          rfl)
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
                                                      have hfrL : FreshAbove ρ
                                                          le.supply :=
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
                                                          le.supply w_arm)
                                                            u = some w0
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
                                                      have hf_r : FreshAbove ρ
                                                          (le.supply + 1) :=
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
                                                      have hsup_r : ∀ id r,
                                                          (id, r) ∈
                                                          info.carried →
                                                          r < le.supply +
                                                            1 :=
                                                        fun id r hmem =>
                                                          Nat.lt_of_lt_of_le
                                                            (hsup _ _ hmem)
                                                            (Nat.le_trans
                                                              hs1
                                                              (Nat.le_trans
                                                              hmst
                                                              (Nat.le_trans
                                                              hmse
                                                              (Nat.le_succ
                                                              _))))
                                                      have hsub_r : ∀ b ∈
                                                          lr.blocks, b ∈
                                                          f.blocks :=
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
                                                              .phi
                                                              le.supply
                                                              exitE le.val] ++
                                                              lr.instrs) =
                                                              execInstrsFullFromIn
                                                              prog
                                                              (some exitE)
                                                              ⟨fenv_arr.env.update
                                                              le.supply
                                                              w_arm,
                                                              fenv_arr.store⟩
                                                              lr.instrs :=
                                                            by
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
                                                              .phi
                                                              le.supply
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
                                                              .phi
                                                              le.supply
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
                                                              fuelB rest +
                                                              C :=
                                                            Nat.le_trans
                                                              hC'ge hge
                                                          obtain ⟨ihV, ihB,
                                                              ihC, ihR⟩ :=
                                                            ih (nextB + 2) ρ
                                                              (le.supply + 1)
                                                              le.next contB
                                                              le.supply
                                                              loop lr hlo hr
                                                              hrs hf_r
                                                              hlast_r forbid
                                                              (Nat.lt_of_lt_of_le hfN
                                                                (Nat.le_trans (Nat.le_add_right nextB 3)
                                                                  (Nat.le_trans hmnt hmne)))
                                                              (Nat.lt_of_lt_of_le hfN
                                                                (Nat.le_add_right nextB 2)) w_arm
                                                              env_arm
                                                              ⟨fenv_arr.env.update
                                                              le.supply
                                                              w_arm,
                                                              fenv_arr.store⟩
                                                              hrel_m hreg_m
                                                              fh henv' out
                                                              hrun prog f
                                                              (some exitE)
                                                              (F1 + 1)
                                                              hsub_r hnodf
                                                              fuelB C hg_r
                                                              hexcl hsup_r
                                                              hdist hblk eblk
                                                              hdr hfindC
                                                              hfindE
                                                              hfindHdr
                                                          refine ⟨?_, ?_, ?_,
                                                              ?_⟩
                                                          · intro u hout
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hrel_final⟩ :=
                                                              ihV u hout
                                                            rw
                                                              [if_assembly_exit
                                                              rfl]
                                                            exact ⟨F2,
                                                              fenv_arr2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hrel_final⟩
                                                          · intro hbroke
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hrel_final,
                                                              hval_final⟩ :=
                                                              ihB hbroke
                                                            exact ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hrel_final,
                                                              hval_final⟩
                                                          · intro hcont
                                                            obtain ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              hle2, hge2,
                                                              heq_rest,
                                                              hcarried, hpreserv, hforbid⟩ :=
                                                              ihC hcont
                                                            refine ⟨F2,
                                                              fenv_arr2,
                                                              blkPrev2,
                                                              Nat.le_trans
                                                              (Nat.le_trans
                                                              hle2 hle)
                                                              (Nat.le_succ _),
                                                              hge2,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest)),
                                                              hcarried, ?_, ⟨hforbid.1, fun hEq => hforbid.2 (hEq.trans (if_assembly_exit rfl))⟩⟩
                                                            intro r hr hnc
                                                            have hle_sup : supply ≤ le.supply :=
                                                              Nat.le_trans hs1
                                                                (Nat.le_trans hmst hmse)
                                                            have e1 : fenv_arr2.env r =
                                                                (fenv_arr.env.update le.supply w_arm) r :=
                                                              hpreserv r
                                                                (Nat.lt_of_lt_of_le hr
                                                                  (Nat.le_trans hle_sup (Nat.le_succ _))) hnc
                                                            have e2 : (fenv_arr.env.update le.supply
                                                                w_arm) r = fenv_arr.env r := by
                                                              simp [Env.update,
                                                                Nat.ne_of_lt
                                                                  (Nat.lt_of_lt_of_le hr hle_sup)]
                                                            have e3 : fenv_arr.env r = fenvC.env r :=
                                                              hpres_arm r
                                                                (Nat.lt_of_lt_of_le hr (Nat.le_trans hs1 hmst))
                                                            have e4 : fenvC.env r = fenv.env r :=
                                                              lower_preserv_regs ρ supply c vc ic s1 heC
                                                                fenv fenvC hexecC r hr
                                                            exact e1.trans (e2.trans (e3.trans e4))
                                                          · intro e_ret hout
                                                            obtain ⟨w_e, hu_e,
                                                              heq_rest⟩ :=
                                                              ihR e_ret hout
                                                            exact ⟨w_e, hu_e,
                                                              hentry.trans
                                                              (heq_arm.trans
                                                              (hJeq.trans
                                                              heq_rest))⟩
                                                  | broke =>
                                                      simp only [] at hrun
                                                      have hout_b : out =
                                                          .broke :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      have henv_eq : env_arm =
                                                          henv' :=
                                                        congrArg Prod.snd
                                                          hrun
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_b] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        obtain ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2, hle2,
                                                          hge2, heq_arm,
                                                          hrel_final,
                                                          hval_final⟩ :=
                                                          lowerStmtsCFG_arm_broke
                                                          budget
                                                          (nextB + 1)
                                                          (nextB + 2) ρ
                                                          lt.supply lt.next
                                                          lastVal false
                                                          loop el le he
                                                          hael hf_e hlast_e
                                                          .unit henv fenvC
                                                          hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm .broke
                                                          har rfl prog f
                                                          (some bId) F''
                                                          hsub_e hnodf
                                                          fuelB (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB el + C)
                                                          hg_e info hlo
                                                          hexcl hdist eblk
                                                          hfindE
                                                        rw [henv_eq, hrho_e,
                                                          ← hrho_r] at hrel_final
                                                        rw [henv_eq] at hval_final
                                                        have hgeC : F2 ≥ C :=
                                                          by omega
                                                        exact ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2,
                                                          Nat.le_trans
                                                          hle2
                                                          (Nat.le_succ _),
                                                          hgeC,
                                                          hentry.trans
                                                          heq_arm,
                                                          hrel_final,
                                                          hval_final⟩
                                                      · intro hcont
                                                        rw [hout_b] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout
                                                        rw [hout_b] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                  | continued =>
                                                      simp only [] at hrun
                                                      have hout_c : out =
                                                          .continued :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      have henv_eq : env_arm =
                                                          henv' :=
                                                        congrArg Prod.snd
                                                          hrun
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_c] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hout_c] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        obtain ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2, hle2,
                                                          hge2, heq_arm, _,
                                                          hcarried, hpreserv, hforbid⟩ :=
                                                          lowerStmtsCFG_arm_continued
                                                          budget
                                                          (nextB + 1)
                                                          (nextB + 2) ρ
                                                          lt.supply lt.next
                                                          lastVal false
                                                          loop el le he
                                                          hael hf_e hlast_e forbid
                                                          (Nat.lt_of_lt_of_le hfN
                                                            (Nat.le_trans (Nat.le_add_right nextB 3) hmnt))
                                                          (Nat.lt_of_lt_of_le hfN
                                                            (Nat.le_add_right nextB 1))
                                                          .unit henv fenvC
                                                          hrelC
                                                          (fun _ => rfl)
                                                          (fun h =>
                                                            absurd h
                                                              (by simp))
                                                          fh env_arm
                                                          .continued har
                                                          rfl prog f
                                                          (some bId) F''
                                                          hsub_e hnodf
                                                          fuelB (2 + max
                                                          (armBlockBound
                                                          fuelB th)
                                                          (armBlockBound
                                                          fuelB el) +
                                                          armBlockBound
                                                          fuelB rest -
                                                          armBlockBound
                                                          fuelB el + C)
                                                          hg_e info hlo
                                                          hexcl hdist hdr
                                                          hfindHdr
                                                        rw [henv_eq] at hcarried
                                                        have hgeC : F2 ≥ C :=
                                                          by omega
                                                        refine ⟨F2,
                                                          fenv_arr2,
                                                          blkPrev2,
                                                          Nat.le_trans
                                                          hle2
                                                          (Nat.le_succ _),
                                                          hgeC,
                                                          hentry.trans
                                                          heq_arm,
                                                          hcarried, ?_,
                                                          hforbid.1, ?_⟩
                                                        intro r hr hnc
                                                        have e1 : fenv_arr2.env r = fenvC.env r :=
                                                          hpreserv r
                                                            (Nat.lt_of_lt_of_le hr (Nat.le_trans hs1 hmst)) hnc
                                                        have e2 : fenvC.env r = fenv.env r :=
                                                          lower_preserv_regs ρ supply c vc ic s1 heC
                                                            fenv fenvC hexecC r hr
                                                        exact e1.trans e2
                                                        have hne_entry : nextB + 1 ≠ nextB + 2 := by omega
                                                        have hexit_lt : nextB + 2 < lt.next := by omega
                                                        have he2Rest : nextB + 1 + 1 + 1 ≤ le.next := by omega
                                                        intro hEq
                                                        exact absurd (hEq.trans (if_assembly_exit rfl))
                                                          (arrNe_restExit hforbid.2 (fun b hb => hbnde b hb)
                                                            (fun b hb => (hbndr b hb).1) hne_entry
                                                            hexit_lt he2Rest (Nat.le_refl _))
                                                      · intro e_ret hout
                                                        rw [hout_c] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                  | returned e_arm =>
                                                      simp only [] at hrun
                                                      have hout_r : out =
                                                          .returned e_arm :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hout_r] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hout_r] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        rw [hout_r] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout2
                                                        have hret_e : e_ret =
                                                            e_arm :=
                                                          (HFlow.returned.inj
                                                            (hout_r.symm.trans
                                                            hout2)).symm
                                                        obtain ⟨w_e, hu_e,
                                                            heq_arm⟩ :=
                                                          ((lowerStmtsCFG_arm_total
                                                            budget
                                                            (nextB + 1)
                                                            (nextB + 2) ρ
                                                            lt.supply
                                                            lt.next lastVal
                                                            false loop el le
                                                            he hael hf_e
                                                            hlast_e .unit
                                                            henv fenvC hrelC
                                                            (fun _ => rfl)
                                                            (fun h =>
                                                              absurd h
                                                              (by simp))
                                                            fh env_arm
                                                            (HFlow.returned
                                                              e_arm) har
                                                            prog f
                                                            (some bId)
                                                            ⟨nextB + 2,
                                                            [.phi le.supply
                                                              exitT lt.val,
                                                            .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                            lr.term⟩ F''
                                                            hsub_e hnodf
                                                            hfindJ fuelB
                                                            (2 + max
                                                            (armBlockBound
                                                            fuelB th)
                                                            (armBlockBound
                                                            fuelB el) +
                                                            armBlockBound
                                                            fuelB rest -
                                                            armBlockBound
                                                            fuelB el + C)
                                                            hg_e e_arm).2
                                                            e_arm rfl)
                                                        rw [hret_e]
                                                        exact ⟨w_e, hu_e,
                                                          hentry.trans
                                                          heq_arm⟩
                                                  | stuck =>
                                                      simp only [] at hrun
                                                      have hst : out =
                                                          .stuck :=
                                                        (congrArg Prod.fst
                                                          hrun).symm
                                                      refine ⟨?_, ?_, ?_, ?_⟩
                                                      · intro u hout
                                                        rw [hst] at hout
                                                        exact absurd hout
                                                          (by simp)
                                                      · intro hbroke
                                                        rw [hst] at hbroke
                                                        exact absurd hbroke
                                                          (by simp)
                                                      · intro hcont
                                                        rw [hst] at hcont
                                                        exact absurd hcont
                                                          (by simp)
                                                      · intro e_ret hout
                                                        rw [hst] at hout
                                                        exact absurd hout
                                                          (by simp)
                                      | int _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | string _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | pointer _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | float _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | unit =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | undef =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | some _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | none =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | ok _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | err _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | tuple_ _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | array_ _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | loc _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                      | closure _ _ =>
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          refine ⟨?_, ?_, ?_, ?_⟩
                                          · intro u hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
                                          · intro hbroke
                                            rw [hst] at hbroke
                                            exact absurd hbroke (by simp)
                                          · intro hcont
                                            rw [hst] at hcont
                                            exact absurd hcont (by simp)
                                          · intro e_ret hout
                                            rw [hst] at hout
                                            exact absurd hout (by simp)
      | returnStmt e rest hstr _ =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro u hout
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck :=
                      (congrArg Prod.fst hrun).symm
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
              · intro hbroke
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck :=
                      (congrArg Prod.fst hrun).symm
                    rw [hst] at hbroke
                    exact absurd hbroke (by simp)
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
                        rw [hst] at hbroke
                        exact absurd hbroke (by simp)
                    | some r =>
                        rw [hev] at hrun
                        have hret : out = .returned r :=
                          (congrArg Prod.fst hrun).symm
                        rw [hret] at hbroke
                        exact absurd hbroke (by simp)
              · intro hcont
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck :=
                      (congrArg Prod.fst hrun).symm
                    rw [hst] at hcont
                    exact absurd hcont (by simp)
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
                        rw [hst] at hcont
                        exact absurd hcont (by simp)
                    | some r =>
                        rw [hev] at hrun
                        have hret : out = .returned r :=
                          (congrArg Prod.fst hrun).symm
                        rw [hret] at hcont
                        exact absurd hcont (by simp)
              · intro e_ret hout2
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck :=
                      (congrArg Prod.fst hrun).symm
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
                          lower_total.1 ρ supply e v0 ie s1 he hstr hfresh
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
                                    ⟨bId, ie, .return_ v0⟩ fenv =
                                    fenv1.env v0 := by
                              have hret' : execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, ie, .return_ v0⟩ fenv =
                                  (match execInstrsFullFromIn prog prev fenv
                                      ie with
                                   | none => (none : Option Value)
                                   | some g => g.env v0) := rfl
                              rw [hret', hexec]
                            have hww : wE = wE2 :=
                              HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                            rw [hLHS, hww]
                            exact hregE
      | breakStmt rest _ =>
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
                  have hst : out = .stuck :=
                    (congrArg Prod.fst hrun).symm
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · intro u hout
                    rw [hst] at hout
                    exact absurd hout (by simp)
                  · intro hbroke
                    rw [hst] at hbroke
                    exact absurd hbroke (by simp)
                  · intro hcont
                    rw [hst] at hcont
                    exact absurd hcont (by simp)
                  · intro e_ret hout
                    rw [hst] at hout
                    exact absurd hout (by simp)
              | succ fh =>
                  have hstep : runHIRStmts (fh + 1) henv (.break :: rest)
                      (.value (.lit accH)) = (.broke, henv) := rfl
                  rw [hstep] at hrun
                  have hout_b : out = .broke :=
                    (congrArg Prod.fst hrun).symm
                  have h2 : henv = henv' := congrArg Prod.snd hrun
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · intro u hout
                    rw [hout_b] at hout
                    exact absurd hout (by simp)
                  · intro hbroke
                    cases F with
                    | zero =>
                        have h1 : blockBound fuelB (.break :: rest) ≥ 1 := by
                          rw [blockBound]; omega
                        omega
                    | succ F' =>
                        obtain ⟨fenv_arr, hexec_copies, hrel_arr, hval_arr, _⟩ :=
                          carryCopies_exec ρ info.carried copies hc prog prev
                            fenv henv hrel hexcl hdist
                        have heq : execBlockFromIn prog (F' + 1) f prev
                            ⟨bId, copies, .goto info.exit⟩ fenv =
                            execBlockFromIn prog F' f (some bId) eblk
                              fenv_arr :=
                          execBlockFromIn_goto prog F' f prev bId copies
                            info.exit fenv fenv_arr eblk hexec_copies hfindE
                        have hge : F' ≥ C := by
                          have hbb : blockBound fuelB (.break :: rest) ≥ 1 := by
                            rw [blockBound]; omega
                          omega
                        refine ⟨F', fenv_arr, bId, Nat.le_succ _, hge, heq,
                          ?_, ?_⟩
                        · rw [← h2]
                          exact hrel_arr
                        · rw [← h2]
                          exact hval_arr
                  · intro hcont
                    rw [hout_b] at hcont
                    exact absurd hcont (by simp)
                  · intro e_ret hout
                    rw [hout_b] at hout
                    exact absurd hout (by simp)
      | continueStmt rest _ =>
          subst hlo
          simp only [lowerStmtsCFG] at h
          cases hc : carryCopies ρ info.carried with
          | none => simp [hc] at h
          | some copies =>
              simp [hc] at h
              subst h
              cases fuelH with
              | zero =>
                  have hz : runHIRStmts 0 henv (.continue :: rest)
                      (.value (.lit accH)) = (.stuck, henv) := rfl
                  rw [hz] at hrun
                  have hst : out = .stuck :=
                    (congrArg Prod.fst hrun).symm
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · intro u hout
                    rw [hst] at hout
                    exact absurd hout (by simp)
                  · intro hbroke
                    rw [hst] at hbroke
                    exact absurd hbroke (by simp)
                  · intro hcont
                    rw [hst] at hcont
                    exact absurd hcont (by simp)
                  · intro e_ret hout
                    rw [hst] at hout
                    exact absurd hout (by simp)
              | succ fh =>
                  have hstep : runHIRStmts (fh + 1) henv (.continue :: rest)
                      (.value (.lit accH)) = (.continued, henv) := rfl
                  rw [hstep] at hrun
                  have hout_c : out = .continued :=
                    (congrArg Prod.fst hrun).symm
                  have h2 : henv = henv' := congrArg Prod.snd hrun
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · intro u hout
                    rw [hout_c] at hout
                    exact absurd hout (by simp)
                  · intro hbroke
                    rw [hout_c] at hbroke
                    exact absurd hbroke (by simp)
                  · intro hcont
                    cases F with
                    | zero =>
                        have h1 : blockBound fuelB (.continue :: rest) ≥ 1 :=
                          by
                          rw [blockBound]; omega
                        omega
                    | succ F' =>
                        obtain ⟨fenv_arr, hexec_copies, hrel_arr, hval_arr,
                            hpres_copies⟩ :=
                          carryCopies_exec ρ info.carried copies hc prog prev
                            fenv henv hrel hexcl hdist
                        have heq : execBlockFromIn prog (F' + 1) f prev
                            ⟨bId, copies, .goto info.header⟩ fenv =
                            execBlockFromIn prog F' f (some bId) hdr
                              fenv_arr :=
                          execBlockFromIn_goto prog F' f prev bId copies
                            info.header fenv fenv_arr hdr hexec_copies
                            hfindHdr
                        have hge : F' ≥ C := by
                          have hbb : blockBound fuelB (.continue :: rest) ≥
                              1 := by
                            rw [blockBound]; omega
                          omega
                        have hfallRel : bId =
                            ((([] : List Block).getLast?.map fun b => b.id)).getD bId →
                            RelEnv henv ρ fenv_arr.env := by
                          intro _
                          exact hrel_arr
                        refine ⟨F', fenv_arr, bId, Nat.le_succ _, hge, heq,
                          ?_⟩
                        rw [← h2]
                        exact ⟨hval_arr,
                          fun r _ hnc => hpres_copies r hnc, hfB, hfallRel⟩
                  · intro e_ret hout
                    rw [hout_c] at hout
                    exact absurd hout (by simp)

end Morph.HIRToMIRCorrect
