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

/-!
# Stage C spine: `spine_P` through `header_loop_correct`

Ninth proof leaf out of the `HIRToMIRBranch` monolith: `spine_P`,
`tramp_post_RelEnv`, the `mkCarried_domain_mono` / `mkCarried_mem_domain`
pair, the header-group/phi tramp/miss/fall executors,
`headerPhis_all_identity`, `cont_post_RelEnv`, `conv_backRelEnv`, and
`header_loop_correct` (moved verbatim). `whileLoop_correct` cites this leaf.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Spine lit-preservation (pure HIR, fuel induction): if every carried id
binds a literal in the pre-body env, it still does after running a `LoopStmts`
body (to any outcome). Assigns store closed-straight eval results (literals
by `evalHIR_straight_varfree_lit`); `varDecl` pushes the same; arms bind
nothing (`runHIRStmts_arm_lookup`); everything else leaves the env alone.
`cases hss` is safe here (fuel, not `ss`, is the induction target). -/
theorem spine_P (budget : Nat) (carried : List (HIR.Id × ValId)) :
    ∀ (fuel : Nat) (henv henv' : HEnv) (ss : List HIR.Stmt)
      (_hss : LoopStmts budget ss) (acc out : HFlow),
      runHIRStmts fuel henv ss acc = (out, henv') →
      (∀ id r, (id, r) ∈ carried → ∃ w, lookupHEnv henv id = some (.lit w)) →
      (∀ id r, (id, r) ∈ carried → ∃ w, lookupHEnv henv' id = some (.lit w)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro henv henv' ss hss acc out hrun hP id r hmem
      have hz : runHIRStmts 0 henv ss acc = (.stuck, henv) := rfl
      rw [hz] at hrun
      obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
      subst henvEq
      exact hP id r hmem
  | succ fh ih =>
      intro henv henv' ss hss acc out hrun hP
      cases hss with
      | nil =>
          simp only [runHIRStmts] at hrun
          obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
          subst henvEq
          exact hP
      | exprStmt e rest hstr _ hrest =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
              subst henvEq
              exact hP
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              exact ih henv henv' rest hrest _ _ hrun hP
      | varDecl id τ init rest hstr _ hrest hvf =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv init with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
              subst henvEq
              exact hP
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨w, hv⟩ := evalHIR_straight_varfree_lit init hvf hstr 256 henv v hev
              subst hv
              have hP' : ∀ idr rr, (idr, rr) ∈ carried →
                  ∃ w0, lookupHEnv ((id, .lit w) :: henv) idr = some (.lit w0) := by
                intro idr rr hmem
                by_cases heq : idr = id
                · subst heq
                  exact ⟨w, lookupHEnv_cons_head _ _ _⟩
                · have hne : id ≠ idr := fun h => heq h.symm
                  obtain ⟨w0, h0⟩ := hP idr rr hmem
                  exact ⟨w0, by rw [lookupHEnv_cons_ne hne]; exact h0⟩
              exact ih _ _ _ hrest _ _ hrun hP'
      | assign id e rest hstr _ hrest hvf =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
              subst henvEq
              exact hP
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨w, hv⟩ := evalHIR_straight_varfree_lit e hvf hstr 256 henv v hev
              subst hv
              have hP' : ∀ idr rr, (idr, rr) ∈ carried →
                  ∃ w0, lookupHEnv (updateHEnv henv id (.lit w)) idr = some (.lit w0) := by
                intro idr rr hmem
                by_cases heq : idr = id
                · subst idr
                  obtain ⟨w0, h0⟩ := hP id rr hmem
                  have hbd : lookupHEnv henv id ≠ none := by
                    rw [h0]; simp
                  exact ⟨w, lookupHEnv_updateHEnv_id hbd⟩
                · have hne : id ≠ idr := fun h => heq h.symm
                  obtain ⟨w0, h0⟩ := hP idr rr hmem
                  exact ⟨w0, by rw [lookupHEnv_updateHEnv_ne hne]; exact h0⟩
              exact ih _ _ _ hrest _ _ hrun hP'
      | nop rest hrest =>
          simp only [runHIRStmts] at hrun
          exact ih _ _ _ hrest _ _ hrun hP
      | ifStmt c th el rest hstr _ hath hael hrest _ _ =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv c with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
              subst henvEq
              exact hP
          | some v =>
              rw [hev] at hrun
              split at hrun
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : v = HIR.Expr.lit (.bool true) := by simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv th (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have hPa : ∀ id r, (id, r) ∈ carried →
                            ∃ w, lookupHEnv envA id = some (.lit w) := by
                          intro idr rr hmem
                          obtain ⟨w0, h0⟩ := hP idr rr hmem
                          have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                            runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                          rw [hlook]
                          exact ⟨w0, h0⟩
                        exact ih _ _ _ hrest _ _ hrun hPa
                    | broke =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | continued =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | returned e =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | stuck =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : v = HIR.Expr.lit (.bool false) := by simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv el (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have hPa : ∀ id r, (id, r) ∈ carried →
                            ∃ w, lookupHEnv envA id = some (.lit w) := by
                          intro idr rr hmem
                          obtain ⟨w0, h0⟩ := hP idr rr hmem
                          have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                            runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                          rw [hlook]
                          exact ⟨w0, h0⟩
                        exact ih _ _ _ hrest _ _ hrun hPa
                    | broke =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | continued =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | returned e =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | stuck =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
              · obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                subst henvEq
                exact hP
      | ifStmtBreak c th el rest hstr _ hath hael hrest _ =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv c with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
              subst henvEq
              exact hP
          | some v =>
              rw [hev] at hrun
              split at hrun
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : v = HIR.Expr.lit (.bool true) := by simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv th (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have hPa : ∀ id r, (id, r) ∈ carried →
                            ∃ w, lookupHEnv envA id = some (.lit w) := by
                          intro idr rr hmem
                          obtain ⟨w0, h0⟩ := hP idr rr hmem
                          have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                            runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                          rw [hlook]
                          exact ⟨w0, h0⟩
                        have hPr : ∀ id r, (id, r) ∈ carried →
                            ∃ w, lookupHEnv henv id = some (.lit w) := hP
                        exact ih _ _ _ hrest _ _ hrun hPa
                    | broke =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | continued =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | returned e =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | stuck =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hath fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
              · rename_i heq
                rw [Option.some.injEq] at heq
                have heq2 : v = HIR.Expr.lit (.bool false) := by simpa using heq
                subst heq2
                cases har : runHIRStmts fh henv el (.value (.lit .unit)) with
                | mk outA envA =>
                    rw [har] at hrun
                    cases outA with
                    | value u =>
                        simp only [] at hrun
                        have hPa : ∀ id r, (id, r) ∈ carried →
                            ∃ w, lookupHEnv envA id = some (.lit w) := by
                          intro idr rr hmem
                          obtain ⟨w0, h0⟩ := hP idr rr hmem
                          have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                            runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                          rw [hlook]
                          exact ⟨w0, h0⟩
                        exact ih _ _ _ hrest _ _ hrun hPa
                    | broke =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | continued =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | returned e =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
                    | stuck =>
                        simp only [] at hrun
                        obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                        subst henvEq
                        intro idr rr hmem
                        obtain ⟨w0, h0⟩ := hP idr rr hmem
                        have hlook : lookupHEnv envA idr = lookupHEnv henv idr :=
                          runHIRStmts_arm_lookup budget hael fh henv envA _ _ idr har
                        rw [hlook]
                        exact ⟨w0, h0⟩
              · obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
                subst henvEq
                exact hP
      | returnStmt e rest hstr _ =>
          simp only [runHIRStmts] at hrun
          cases hev : evalHIR 256 henv e with
          | none =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
              subst henvEq
              exact hP
          | some v =>
              rw [hev] at hrun
              simp only [] at hrun
              obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
              subst henvEq
              exact hP
      | breakStmt rest hrest =>
          simp only [runHIRStmts] at hrun
          obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
          subst henvEq
          exact hP
      | continueStmt rest hrest =>
          simp only [runHIRStmts] at hrun
          obtain ⟨_, henvEq⟩ := Prod.mk.inj hrun
          subst henvEq
          exact hP

/-- Trampoline post-phi relation (direct back-edge alternative for `continue`):
executing the header's trampoline phis (prev `t`) leaves the env unchanged
(self-copies + misses, via `headerGroup_exec_tramp`), and the pre-phi env is
already `RelEnv`-related under `ρb`. Carried ids use the HIR-lit fact plus the
worker's carried-bind; assigned-but-not-carried resolve through `carried`;
unassigned ids use HIR lookup preservation plus the pre-body `RelEnv` and the
worker's below-supply frame. No `RelEnv` under `lb.ρ` is needed. -/
theorem tramp_post_RelEnv (budget : Nat)
    (nextB : MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (body : List HIR.Stmt) (carried : List (HIR.Id × ValId)) (sA : Nat)
    (ρb : List (HIR.Id × ValId)) (s1 : Nat) (lb : Lowered)
    (hmk : mkCarried ρ supply
      ((dedupIds (assignedIds body)).filterMap
        (fun id => (rhoLookup ρ id).map (fun _ => id))) =
      some (carried, sA, ρb))
    (_hbody : lowerStmtsCFG (nextB + 2) (some nextB) false ρb (s1 + 1)
      (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body = some lb)
    (_hloop : LoopStmts budget body)
    (hfresh : FreshAbove ρ supply)
    (bId fallEnd : MIR.BlockId) (tramps : List MIR.BlockId)
    (phif : HIR.Id × ValId → List MIR.Instr)
    (hphif : ∀ q ∈ carried, ∃ entrySrc backSrc,
      rhoLookup ρ q.1 = some entrySrc ∧
      phif q = ([MIR.Instr.phi q.2 bId entrySrc,
        MIR.Instr.phi q.2 fallEnd backSrc] ++
        tramps.map (MIR.Instr.phi q.2 · q.2)))
    (_hfallNe : fallEnd ≠ bId)
    (_htrNe : ∀ t ∈ tramps, t ≠ bId)
    (hdistC : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried →
      r₁ = r₂ → id₁ = id₂)
    (envB : HEnv) (henv : HEnv) (fenv fenvArr : FullEnv)
    (hrelB0 : RelEnv henv ρb fenv.env)
    (hBIND : ∀ id r w, (id, r) ∈ carried →
      lookupHEnv envB id = some (.lit w) → fenvArr.env r = some w)
    (hP : ∀ id r, (id, r) ∈ carried → ∃ w, lookupHEnv envB id = some (.lit w))
    (hpres : ∀ r, r < supply → (∀ idx, (idx, r) ∉ carried) →
      fenvArr.env r = fenv.env r)
    (hlookB : ∀ id, id ∉ assignedIds body →
      lookupHEnv envB id = lookupHEnv henv id)
    (t : MIR.BlockId) (_htmem : t ∈ tramps) (hfallt : fallEnd ≠ t)
    (hbIdt : bId ≠ t) (prog : Program) :
    ∃ fenv', execInstrsFullFromIn prog (some t) fenvArr
        ((carried.map phif).flatten) = some fenv' ∧
      RelEnv envB ρb fenv'.env ∧
      (∀ id r w, (id, r) ∈ carried →
        lookupHEnv envB id = some (.lit w) → fenv'.env r = some w) ∧
      (∀ r', (∀ idx, (idx, r') ∉ carried) → fenv'.env r' = fenvArr.env r') := by
  -- Per-carried HIR-lit plus worker bind: every carried reg is bound.
  have hval : ∀ id r, (id, r) ∈ carried → ∃ w,
      lookupHEnv envB id = some (.lit w) ∧ fenvArr.env r = some w := by
    intro idr rr hmem
    obtain ⟨w, hlookH⟩ := hP idr rr hmem
    exact ⟨w, hlookH, hBIND idr rr w hmem hlookH⟩
  -- (i) Executing all tramp groups leaves the env unchanged.
  have hexec : execInstrsFullFromIn prog (some t) fenvArr
      ((carried.map phif).flatten) = some fenvArr := by
    have genFrom : ∀ (cs : List (HIR.Id × ValId)),
        (∀ q ∈ cs, ∃ entrySrc backSrc, rhoLookup ρ q.1 = some entrySrc ∧
          phif q = ([MIR.Instr.phi q.2 bId entrySrc,
            MIR.Instr.phi q.2 fallEnd backSrc] ++
            tramps.map (MIR.Instr.phi q.2 · q.2))) →
        (∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ cs → (id₂, r₂) ∈ cs →
          r₁ = r₂ → id₁ = id₂) →
        (∀ id r, (id, r) ∈ cs → ∃ w,
          lookupHEnv envB id = some (.lit w) ∧ fenvArr.env r = some w) →
        execInstrsFullFrom (some t) fenvArr
          ((cs.map phif).flatten) = some fenvArr := by
      intro cs hphif_cs hdist_cs hval_cs
      induction cs with
      | nil =>
          simp
      | cons p rest ih =>
          obtain ⟨id₀, r₀⟩ := p
          have hfhead : ∃ entrySrc backSrc, rhoLookup ρ id₀ = some entrySrc ∧
              phif (id₀, r₀) = ([MIR.Instr.phi r₀ bId entrySrc,
                MIR.Instr.phi r₀ fallEnd backSrc] ++
                tramps.map (MIR.Instr.phi r₀ · r₀)) := by
            have h := hphif_cs (id₀, r₀) (List.mem_cons_self ..)
            obtain ⟨esrc, bsrc, he1, he2⟩ := h
            exact ⟨esrc, bsrc, he1, he2⟩
          obtain ⟨entrySrc, backSrc, he1, hfp⟩ := hfhead
          have hval_rest : ∀ id r, (id, r) ∈ rest → ∃ w,
              lookupHEnv envB id = some (.lit w) ∧ fenvArr.env r = some w := by
            intro idr rr hmem
            exact hval_cs idr rr (List.mem_cons_of_mem _ hmem)
          have hphif_rest : ∀ q ∈ rest, ∃ entrySrc backSrc,
              rhoLookup ρ q.1 = some entrySrc ∧
              phif q = ([MIR.Instr.phi q.2 bId entrySrc,
                MIR.Instr.phi q.2 fallEnd backSrc] ++
                tramps.map (MIR.Instr.phi q.2 · q.2)) := by
            intro q hq
            exact hphif_cs q (List.mem_cons_of_mem _ hq)
          have hdist_rest : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ rest → (id₂, r₂) ∈ rest →
              r₁ = r₂ → id₁ = id₂ := by
            intro a b c d h1 h2 heq
            exact hdist_cs a b c d (List.mem_cons_of_mem _ h1)
              (List.mem_cons_of_mem _ h2) heq
          obtain ⟨w₀, hlookH, hreg0⟩ := hval_cs id₀ r₀ (List.mem_cons_self ..)
          have hexec1 : execInstrsFullFrom (some t) fenvArr (phif (id₀, r₀)) =
              some fenvArr := by
            rw [hfp]
            exact headerGroup_exec_tramp t bId fallEnd tramps r₀ entrySrc
              backSrc fenvArr w₀ hbIdt hfallt hreg0
          have hrest := ih hphif_rest hdist_rest hval_rest
          have happ : execInstrsFullFrom (some t) fenvArr
              (phif (id₀, r₀) ++ (rest.map phif).flatten) = some fenvArr := by
            rw [execInstrsFullFrom_append, hexec1]
            exact hrest
          simpa using happ
    rw [execInstrsFullFromIn_eq]
    exact genFrom carried hphif hdistC hval
  refine ⟨fenvArr, hexec, ?_, ?_, ?_⟩
  · -- (ii) RelEnv under ρb.
    intro id u hlook
    rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
    · subst hid
      subst hu
      obtain ⟨w, hlookH, hreg⟩ := hval id u hmem
      exact ⟨w, hlookH, hreg⟩
    · by_cases hass : id ∈ assignedIds body
      · have hmemIds : id ∈ (dedupIds (assignedIds body)).filterMap
          (fun id => (rhoLookup ρ id).map (fun _ => id)) := by
          rw [List.mem_filterMap]
          exact ⟨id, dedupIds_mem hass, by simp [hbase]⟩
        obtain ⟨r, hlookB', hmemC⟩ := mkCarried_mem_lookup hmemIds hmk
        have hur : r = u := Option.some.inj (hlookB'.symm.trans hlook)
        subst hur
        obtain ⟨w, hlookH, hreg⟩ := hval id r hmemC
        exact ⟨w, hlookH, hreg⟩
      · have hEq : lookupHEnv envB id = lookupHEnv henv id := hlookB id hass
        obtain ⟨w, hlookH0, hreg0⟩ := hrelB0 id u hlook
        refine ⟨w, ?_, ?_⟩
        · rw [hEq]; exact hlookH0
        · have hnotin : ∀ idx, (idx, u) ∉ carried := by
            intro idx hcon
            have hle := mkCarried_mem_lo hmk hcon
            have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
            exact absurd hle (Nat.not_le_of_gt hlt)
          rw [hpres u (hfresh id u (rhoLookup_some_mem _ _ _ hbase)) hnotin]
          exact hreg0
  · intro id r w hmem hlookH
    obtain ⟨w', hlookH', hreg⟩ := hval id r hmem
    have h1 : HIR.Expr.lit w' = HIR.Expr.lit w := Option.some.inj (by
        have h := hlookH
        rw [hlookH'] at h
        exact h)
    have hw : w = w' := (HIR.Expr.lit.inj h1).symm
    subst hw
    exact hreg
  · intro r' hnotin
    rfl

/-- `mkCarried` never drops a binding: an id bound in the entry env stays
bound (at some register) in the exit env. `updAssoc` only conses, and a
`none` allocation aborts the whole fold, so the induction just transports
the lookup across each update. Feeds `mkCarried_mem_domain`. -/
theorem mkCarried_domain_mono {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} {id : HIR.Id} {u : ValId}
    (h : mkCarried ρ s ids = some (cs, s', ρ'))
    (hlook : rhoLookup ρ id = some u) :
    ∃ u', rhoLookup ρ' id = some u' := by
  induction ids generalizing ρ s cs s' ρ' u with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      exact ⟨u, hlook⟩
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
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              by_cases heq : id = hd
              · have hUs : rhoLookup (updAssoc ρ hd s) hd = some s := by
                  have e1 := rhoLookup_updAssoc_id ρ hd s
                  rw [hρ] at e1
                  exact e1
                subst heq
                obtain ⟨u', hu'⟩ := ih hrec hUs
                exact ⟨u', hu'⟩
              · have hlook' : rhoLookup (updAssoc ρ hd s) id =
                    rhoLookup ρ id :=
                  rhoLookup_updAssoc_ne (fun hh => heq hh.symm) ρ
                have hlookU : rhoLookup (updAssoc ρ hd s) id = some u := by
                  rw [hlook']
                  exact hlook
                exact ih hrec hlookU

/-- Every carried pair's id resolves in the exit env (at some register).
The nil case is vacuous; the cons head case allocates (then stays bound by
`mkCarried_domain_mono`); the tail case is the induction hypothesis. Gives
the pre-body HIR-lit fact for `cont_post_RelEnv` without any uniqueness
hypothesis. -/
theorem mkCarried_mem_domain {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} {id : HIR.Id} {r : ValId}
    (h : mkCarried ρ s ids = some (cs, s', ρ'))
    (hmem : (id, r) ∈ cs) :
    ∃ u, rhoLookup ρ' id = some u := by
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
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
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              rcases List.mem_cons.mp hmem with hmem | hmem
              · have hUs : rhoLookup (updAssoc ρ hd s) hd = some s := by
                  have e1 := rhoLookup_updAssoc_id ρ hd s
                  rw [hρ] at e1
                  exact e1
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
                exact mkCarried_domain_mono hrec hUs
              · exact ih hrec hmem

/-- Header phis on a trampoline edge are identity: the entry and back phis
miss (predecessor is neither), and the hitting self-copy rewrites the
register with its current value (`headerGroup_exec_tramp`). Needs only
reg-boundness per carried pair — no `RelEnv`. -/
theorem headerPhis_tramp_hit_exec (t bId fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) (l : List (HIR.Id × ValId))
    (f : HIR.Id × ValId → List MIR.Instr)
    (hf : ∀ q ∈ l, ∃ entrySrc backSrc,
      f q = ([MIR.Instr.phi q.2 bId entrySrc,
        MIR.Instr.phi q.2 fallEnd backSrc] ++
        tramps.map (MIR.Instr.phi q.2 · q.2)))
    (_htmem : t ∈ tramps) (hnt : bId ≠ t) (hnf : fallEnd ≠ t)
    (prog : Program) (fenv : FullEnv)
    (hval : ∀ id r, (id, r) ∈ l → ∃ w, fenv.env r = some w) :
    execInstrsFullFromIn prog (some t) fenv ((l.map f).flatten) =
      some fenv := by
  have gen : ∀ (cs : List (HIR.Id × ValId)),
      (∀ q ∈ cs, ∃ entrySrc backSrc,
        f q = ([MIR.Instr.phi q.2 bId entrySrc,
          MIR.Instr.phi q.2 fallEnd backSrc] ++
          tramps.map (MIR.Instr.phi q.2 · q.2))) →
      (∀ id r, (id, r) ∈ cs → ∃ w, fenv.env r = some w) →
      execInstrsFullFromIn prog (some t) fenv ((cs.map f).flatten) =
        some fenv := by
    intro cs hcs hval_cs
    induction cs with
    | nil => simp [List.map_nil, execInstrsFullFromIn_eq, execInstrsFullFrom]
    | cons p rest ih =>
        obtain ⟨id₀, r₀⟩ := p
        have hfhead : ∃ entrySrc backSrc,
            f (id₀, r₀) = ([MIR.Instr.phi r₀ bId entrySrc,
              MIR.Instr.phi r₀ fallEnd backSrc] ++
              tramps.map (MIR.Instr.phi r₀ · r₀)) :=
          hcs _ (List.mem_cons_self ..)
        obtain ⟨entrySrc, backSrc, hfp⟩ := hfhead
        have hval_rest : ∀ id r, (id, r) ∈ rest → ∃ w,
            fenv.env r = some w := by
          intro idr rr hmem
          exact hval_cs idr rr (List.mem_cons_of_mem _ hmem)
        have hcs_rest : ∀ q ∈ rest, ∃ entrySrc backSrc,
            f q = ([MIR.Instr.phi q.2 bId entrySrc,
              MIR.Instr.phi q.2 fallEnd backSrc] ++
              tramps.map (MIR.Instr.phi q.2 · q.2)) := by
          intro q hq
          exact hcs q (List.mem_cons_of_mem _ hq)
        obtain ⟨w₀, hreg0⟩ := hval_cs id₀ r₀ (List.mem_cons_self ..)
        have hexec1 : execInstrsFullFrom (some t) fenv (f (id₀, r₀)) =
            some fenv := by
          rw [hfp]
          exact headerGroup_exec_tramp t bId fallEnd tramps r₀ entrySrc
            backSrc fenv w₀ hnt hnf hreg0
        have hrest := ih hcs_rest hval_rest
        have happ : execInstrsFullFromIn prog (some t) fenv
            (f (id₀, r₀) ++ (rest.map f).flatten) =
            execInstrsFullFromIn prog (some t) fenv (rest.map f).flatten := by
          rw [execInstrsFullFromIn_eq, execInstrsFullFromIn_eq,
            execInstrsFullFrom_append, hexec1]
        have hflat : (((id₀, r₀) :: rest).map f).flatten =
            f (id₀, r₀) ++ (rest.map f).flatten := by simp
        rw [hflat, happ]
        exact hrest
  exact gen l hf hval

/-- One header group with a foreign predecessor is identity: the entry and
back phis miss and every trampoline self-copy misses
(`trampPhis_exec_miss`). -/
theorem headerGroup_exec_miss (pred bId fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) (r entrySrc backSrc : ValId)
    (fenv : FullEnv)
    (hnb : bId ≠ pred) (hnf : fallEnd ≠ pred)
    (hnm : ∀ t ∈ tramps, t ≠ pred) (prog : Program) :
    execInstrsFullFromIn prog (some pred) fenv
      ([MIR.Instr.phi r bId entrySrc, MIR.Instr.phi r fallEnd backSrc] ++
        tramps.map (MIR.Instr.phi r · r)) = some fenv := by
  rw [execInstrsFullFromIn_eq]
  simp only [List.cons_append, List.nil_append,
    execInstrsFullFrom_phi_miss _ _ _ _ _ _ hnb,
    execInstrsFullFrom_phi_miss _ _ _ _ _ _ hnf]
  rw [← execInstrsFullFromIn_eq]
  exact trampPhis_exec_miss prog pred tramps r fenv hnm

/-- Header phis with a foreign predecessor are identity: entry, back, and
every trampoline self-copy miss. Needs only predecessor inequality facts —
no values at all. -/
theorem headerPhis_miss_exec (pred bId fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) (l : List (HIR.Id × ValId))
    (f : HIR.Id × ValId → List MIR.Instr)
    (hf : ∀ q ∈ l, ∃ entrySrc backSrc,
      f q = ([MIR.Instr.phi q.2 bId entrySrc,
        MIR.Instr.phi q.2 fallEnd backSrc] ++
        tramps.map (MIR.Instr.phi q.2 · q.2)))
    (hnb : bId ≠ pred) (hnf : fallEnd ≠ pred)
    (hnm : ∀ t ∈ tramps, t ≠ pred)
    (prog : Program) (fenv : FullEnv) :
    execInstrsFullFromIn prog (some pred) fenv ((l.map f).flatten) =
      some fenv := by
  have gen : ∀ (cs : List (HIR.Id × ValId)),
      (∀ q ∈ cs, ∃ entrySrc backSrc,
        f q = ([MIR.Instr.phi q.2 bId entrySrc,
          MIR.Instr.phi q.2 fallEnd backSrc] ++
          tramps.map (MIR.Instr.phi q.2 · q.2))) →
      execInstrsFullFromIn prog (some pred) fenv ((cs.map f).flatten) =
        some fenv := by
    intro cs hcs
    induction cs with
    | nil => simp [List.map_nil, execInstrsFullFromIn_eq, execInstrsFullFrom]
    | cons p rest ih =>
        obtain ⟨id₀, r₀⟩ := p
        obtain ⟨entrySrc, backSrc, hfp⟩ := hcs _ (List.mem_cons_self ..)
        have hcs_rest : ∀ q ∈ rest, ∃ entrySrc backSrc,
            f q = ([MIR.Instr.phi q.2 bId entrySrc,
              MIR.Instr.phi q.2 fallEnd backSrc] ++
              tramps.map (MIR.Instr.phi q.2 · q.2)) := by
          intro q hq
          exact hcs q (List.mem_cons_of_mem _ hq)
        have hexec1 : execInstrsFullFromIn prog (some pred) fenv
            (f (id₀, r₀)) = some fenv := by
          rw [hfp]
          exact headerGroup_exec_miss pred bId fallEnd tramps r₀ entrySrc
            backSrc fenv hnb hnf hnm prog
        have hrest := ih hcs_rest
        have happ : execInstrsFullFromIn prog (some pred) fenv
            (f (id₀, r₀) ++ (rest.map f).flatten) =
            execInstrsFullFromIn prog (some pred) fenv (rest.map f).flatten := by
          simp only [execInstrsFullFromIn_append, hexec1]
        have hflat : (((id₀, r₀) :: rest).map f).flatten =
            f (id₀, r₀) ++ (rest.map f).flatten := by simp
        rw [hflat, happ]
        exact hrest
  exact gen l hf

/-- One header group on the fall edge is identity when both sources agree:
the entry phi misses, the fall phi rewrites the register with its current
value (a no-op via `Env.update_eq_self`), and trampoline self-copies are
no-ops (`trampSelf_exec`). -/
theorem headerGroup_exec_fall (entryPred fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) (r entrySrc backSrc : ValId) (fenv : FullEnv)
    (w : Value) (hentry : entryPred ≠ fallEnd)
    (hreg : fenv.env r = some w) (hsrc : fenv.env backSrc = some w) :
    execInstrsFullFrom (some fallEnd) fenv
        ([.phi r entryPred entrySrc, .phi r fallEnd backSrc] ++
          tramps.map (.phi r · r)) = some fenv := by
  have h1 : execInstrsFullFrom (some fallEnd) fenv
      ([.phi r entryPred entrySrc, .phi r fallEnd backSrc] ++
        tramps.map (.phi r · r)) =
      execInstrsFullFrom (some fallEnd) ⟨fenv.env.update r w, fenv.store⟩
        (tramps.map (.phi r · r)) := by
    simp only [List.cons_append, List.nil_append,
      execInstrsFullFrom_phi_miss _ _ _ _ _ _ hentry,
      execInstrsFullFrom_phi_hit _ _ _ _ _ _ rfl, hsrc]
  rw [h1, Env.update_eq_self _ _ _ hreg]
  exact trampSelf_exec fallEnd r tramps fenv w hreg

/-- Header phis on the fall edge are identity when every carried register
and its back-edge source already hold the same value: each entry phi
misses, each fall phi is a no-op rewrite, and trampoline self-copies are
no-ops. Needs value agreement, not just shape — the caller derives it from
the fall-gated arrival relation. -/
theorem headerPhis_exec_fall (fallEnd entryPred : MIR.BlockId)
    (tramps : List MIR.BlockId) (l : List (HIR.Id × ValId))
    (f : HIR.Id × ValId → List MIR.Instr)
    (prog : Program) (fenv : FullEnv)
    (hf : ∀ q ∈ l, ∃ entrySrc backSrc w, fenv.env q.2 = some w ∧
      fenv.env backSrc = some w ∧
      f q = ([MIR.Instr.phi q.2 entryPred entrySrc,
        MIR.Instr.phi q.2 fallEnd backSrc] ++
        tramps.map (MIR.Instr.phi q.2 · q.2)))
    (hentry : entryPred ≠ fallEnd) :
    execInstrsFullFromIn prog (some fallEnd) fenv ((l.map f).flatten) =
      some fenv := by
  have gen : ∀ (cs : List (HIR.Id × ValId)),
      (∀ q ∈ cs, ∃ entrySrc backSrc w, fenv.env q.2 = some w ∧
        fenv.env backSrc = some w ∧
        f q = ([MIR.Instr.phi q.2 entryPred entrySrc,
          MIR.Instr.phi q.2 fallEnd backSrc] ++
          tramps.map (MIR.Instr.phi q.2 · q.2))) →
      execInstrsFullFromIn prog (some fallEnd) fenv ((cs.map f).flatten) =
        some fenv := by
    intro cs hcs
    induction cs with
    | nil => simp [List.map_nil, execInstrsFullFromIn_eq, execInstrsFullFrom]
    | cons p rest ih =>
        obtain ⟨id₀, r₀⟩ := p
        obtain ⟨entrySrc, backSrc, w, hreg, hsrc, hfp⟩ :=
          hcs _ (List.mem_cons_self ..)
        have hcs_rest : ∀ q ∈ rest, ∃ entrySrc backSrc w,
            fenv.env q.2 = some w ∧ fenv.env backSrc = some w ∧
            f q = ([MIR.Instr.phi q.2 entryPred entrySrc,
              MIR.Instr.phi q.2 fallEnd backSrc] ++
              tramps.map (MIR.Instr.phi q.2 · q.2)) := by
          intro q hq
          exact hcs q (List.mem_cons_of_mem _ hq)
        have hexec1 : execInstrsFullFromIn prog (some fallEnd) fenv
            (f (id₀, r₀)) = some fenv := by
          rw [hfp, execInstrsFullFromIn_eq]
          exact headerGroup_exec_fall entryPred fallEnd tramps r₀ entrySrc
            backSrc fenv w hentry hreg hsrc
        have hrest := ih hcs_rest
        have happ : execInstrsFullFromIn prog (some fallEnd) fenv
            (f (id₀, r₀) ++ (rest.map f).flatten) =
            execInstrsFullFromIn prog (some fallEnd) fenv (rest.map f).flatten := by
          simp only [execInstrsFullFromIn_append, hexec1]
        have hflat : (((id₀, r₀) :: rest).map f).flatten =
            f (id₀, r₀) ++ (rest.map f).flatten := by simp
        rw [hflat, happ]
        exact hrest
  exact gen l hf

/-- Header phis from any predecessor are identity: on the fall edge the
back phis rewrite carried registers with their current values
(`headerPhis_exec_fall`, with value agreement supplied only there); off
the fall edge the arrival is a trampoline hit or a clean miss. The
predecessor split lives inside this lemma, so callers stay split-free and
their downstream proof needs no duplication. -/
theorem headerPhis_all_identity (entryPred fallEnd : MIR.BlockId)
    (tramps : List MIR.BlockId) (l : List (HIR.Id × ValId))
    (f : HIR.Id × ValId → List MIR.Instr)
    (pred : MIR.BlockId) (prog : Program) (fenv : FullEnv)
    (hfval : (pred = fallEnd) → ∀ q ∈ l, ∃ entrySrc backSrc w,
      fenv.env q.2 = some w ∧ fenv.env backSrc = some w ∧
      f q = ([MIR.Instr.phi q.2 entryPred entrySrc,
        MIR.Instr.phi q.2 fallEnd backSrc] ++
        tramps.map (MIR.Instr.phi q.2 · q.2)))
    (hshape : ∀ q ∈ l, ∃ entrySrc backSrc,
      f q = ([MIR.Instr.phi q.2 entryPred entrySrc,
        MIR.Instr.phi q.2 fallEnd backSrc] ++
        tramps.map (MIR.Instr.phi q.2 · q.2)))
    (hval : ∀ id r, (id, r) ∈ l → ∃ w, fenv.env r = some w)
    (hneB : entryPred ≠ pred)
    (hfallNe : fallEnd ≠ entryPred)
    (_htrFall : ∀ t ∈ tramps, t ≠ fallEnd) :
    execInstrsFullFromIn prog (some pred) fenv ((l.map f).flatten) = some fenv := by
  by_cases hfall : pred = fallEnd
  · rw [hfall]
    exact headerPhis_exec_fall fallEnd entryPred tramps l f prog fenv
      (hfval hfall) (Ne.symm hfallNe)
  · by_cases hmem : pred ∈ tramps
    · exact headerPhis_tramp_hit_exec pred entryPred fallEnd tramps l f hshape
        hmem hneB (Ne.symm hfall) prog fenv hval
    · exact headerPhis_miss_exec pred entryPred fallEnd tramps l f hshape hneB
        (Ne.symm hfall) (fun t ht heq => hmem (heq ▸ ht)) prog fenv

/-- Post-body relation for `continue` arrivals (trampoline/miss alternative
to `conv_backRelEnv`): the continued selector gives carried binds plus a
below-supply frame but no `RelEnv` under `lb.ρ` — and none is needed.
Carried ids use the post-body HIR-lit fact (`spine_P` from pre-body
binding) plus the worker's bind; assigned-but-not-carried resolve through
`carried`; unassigned ids use HIR lookup preservation plus the pre-body
`RelEnv` and the frame. -/
theorem cont_post_RelEnv (_budget : Nat)
    (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (body : List HIR.Stmt) (carried : List (HIR.Id × ValId)) (sA : Nat)
    (ρb : List (HIR.Id × ValId))
    (hmk : mkCarried ρ supply
      ((dedupIds (assignedIds body)).filterMap
        (fun id => (rhoLookup ρ id).map (fun _ => id))) =
      some (carried, sA, ρb))
    (hfresh : FreshAbove ρ supply)
    (s1hi : Nat) (hle : supply ≤ s1hi)
    (envB : HEnv) (henv : HEnv) (fenv fenvArr : FullEnv)
    (hrelB0 : RelEnv henv ρb fenv.env)
    (hBIND : ∀ id r w, (id, r) ∈ carried →
      lookupHEnv envB id = some (.lit w) → fenvArr.env r = some w)
    (hP : ∀ id r, (id, r) ∈ carried → ∃ w,
      lookupHEnv envB id = some (.lit w))
    (hframe : ∀ r, r < s1hi → (∀ idx, (idx, r) ∉ carried) →
      fenvArr.env r = fenv.env r)
    (hlookB : ∀ id, id ∉ assignedIds body →
      lookupHEnv envB id = lookupHEnv henv id) :
    RelEnv envB ρb fenvArr.env := by
  have hval : ∀ id r, (id, r) ∈ carried → ∃ w,
      lookupHEnv envB id = some (.lit w) ∧ fenvArr.env r = some w := by
    intro idr rr hmem
    obtain ⟨w, hlookH⟩ := hP idr rr hmem
    exact ⟨w, hlookH, hBIND idr rr w hmem hlookH⟩
  intro id u hlook
  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
  · subst hid
    subst hu
    obtain ⟨w, hlookH, hreg⟩ := hval id u hmem
    exact ⟨w, hlookH, hreg⟩
  · by_cases hass : id ∈ assignedIds body
    · have hmemIds : id ∈ (dedupIds (assignedIds body)).filterMap
        (fun id => (rhoLookup ρ id).map (fun _ => id)) := by
        rw [List.mem_filterMap]
        exact ⟨id, dedupIds_mem hass, by simp [hbase]⟩
      obtain ⟨r, hlookC, hmemC⟩ := mkCarried_mem_lookup hmemIds hmk
      have hur : r = u := Option.some.inj (hlookC.symm.trans hlook)
      subst hur
      obtain ⟨w, hlookH, hreg⟩ := hval id r hmemC
      exact ⟨w, hlookH, hreg⟩
    · have hEq : lookupHEnv envB id = lookupHEnv henv id := hlookB id hass
      obtain ⟨w, hlookH0, hreg0⟩ := hrelB0 id u hlook
      refine ⟨w, ?_, ?_⟩
      · rw [hEq]; exact hlookH0
      · have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
        have hnotin : ∀ idx, (idx, u) ∉ carried := by
          intro idx hcon
          have hleU := mkCarried_mem_lo hmk hcon
          exact absurd hleU (Nat.not_le_of_gt hlt)
        have hltHi : u < s1hi := Nat.lt_of_lt_of_le hlt hle
        rw [hframe u hltHi hnotin]
        exact hreg0

/-- Post-phi conversion (back-edge): a post-header-phi `RelEnv` under the
body-exit env `lb.ρ` plus the phi's carried-bind agreement restores `RelEnv`
under the body-entry env `ρb`. Carried ids go through the exit env
(`mem_preserv`) and the phi agreement; assigned-but-not-carried ids resolve
via `mkCarried_mem_lookup`; unassigned ids keep their entry reg
(`rho_preserv`) and the phi frame carries the match over. This generalizes
`whileLoop_correct`'s broke-path `hrelRb` to an arbitrary post-phi pair. -/
theorem conv_backRelEnv (budget : Nat)
    (nextB : MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply : Nat)
    (body : List HIR.Stmt) (carried : List (HIR.Id × ValId)) (sA : Nat)
    (ρb : List (HIR.Id × ValId)) (s1 : Nat) (lb : Lowered)
    (hmk : mkCarried ρ supply
      ((dedupIds (assignedIds body)).filterMap
        (fun id => (rhoLookup ρ id).map (fun _ => id))) =
      some (carried, sA, ρb))
    (hbody : lowerStmtsCFG (nextB + 2) (some nextB) false ρb (s1 + 1)
      (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩) body = some lb)
    (hloop : LoopStmts budget body)
    (hfresh : FreshAbove ρ supply)
    (envB : HEnv) (fenvL fenvP : FullEnv)
    (hrelL : RelEnv envB lb.ρ fenvL.env)
    (hbindP : ∀ id r w, (id, r) ∈ carried →
      lookupHEnv envB id = some (.lit w) → fenvP.env r = some w)
    (hframeP : ∀ r', (∀ idx, (idx, r') ∉ carried) → fenvP.env r' = fenvL.env r') :
    RelEnv envB ρb fenvP.env := by
  intro id u hlook
  rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmem, hid, hu⟩ | hbase
  · subst hid
    subst hu
    obtain ⟨u', hLb⟩ := lowerStmtsCFG_loopBody_mem_preserv budget (nextB + 2)
      nextB ρb (s1 + 1) (nextB + 3) s1 _ _ body lb id u rfl hbody hloop hlook
    obtain ⟨w, hlookH, hreg⟩ := hrelL id u' hLb
    exact ⟨w, hlookH, hbindP id u w hmem hlookH⟩
  · by_cases hass : id ∈ assignedIds body
    · have hmemIds : id ∈ (dedupIds (assignedIds body)).filterMap
        (fun id => (rhoLookup ρ id).map (fun _ => id)) := by
        rw [List.mem_filterMap]
        exact ⟨id, dedupIds_mem hass, by simp [hbase]⟩
      obtain ⟨r, hlookB, hmemC⟩ := mkCarried_mem_lookup hmemIds hmk
      have hur : r = u := Option.some.inj (hlookB.symm.trans hlook)
      subst hur
      obtain ⟨u', hLb⟩ := lowerStmtsCFG_loopBody_mem_preserv budget (nextB + 2)
        nextB ρb (s1 + 1) (nextB + 3) s1 _ _ body lb id r rfl hbody hloop hlook
      obtain ⟨w, hlookH, hreg⟩ := hrelL id u' hLb
      exact ⟨w, hlookH, hbindP id r w hmemC hlookH⟩
    · have hLb : rhoLookup lb.ρ id = some u := by
        have hEq := lowerStmtsCFG_loopBody_rho_preserv budget (nextB + 2) nextB
          ρb (s1 + 1) (nextB + 3) s1 _ _ body lb id rfl hbody hloop hass
        rw [hEq]
        exact hlook
      obtain ⟨w, hlookH, hreg⟩ := hrelL id u hLb
      refine ⟨w, hlookH, ?_⟩
      have hnotin : ∀ idx, (idx, u) ∉ carried := by
        intro idx hcon
        have hle := mkCarried_mem_lo hmk hcon
        have hlt : u < supply := hfresh id u (rhoLookup_some_mem _ _ _ hbase)
        exact absurd hle (Nat.not_le_of_gt hlt)
      rw [hframeP u hnotin]
      exact hreg

/-- Header lemma (loop recursion core): from a body-entry state (post-cond,
post-`const s1`, `RelEnv`-related under `ρb`) plus a completed body run at
fuel `fh`, run the worker to the header arrival, execute the back/trampoline
phis, and complete the remaining `fh`-fuel iterations to the exit/rest.
`value` exits use the direct back-edge (`conv_backRelEnv`); `continue` exits
use the trampoline (`tramp_post_RelEnv`); `broke` exits directly. The
remaining run uses the same `fh` (matching `runHIRWhile`'s fuel threading);
recursion lands on the predecessor, so structural induction suffices.
`whileLoop_correct`'s four recursion leaves apply it. -/
theorem header_loop_correct (budget : Nat) :
    ∀ (bId nextB : MIR.BlockId) (ρ : List (HIR.Id × ValId)) (supply : Nat)
      (c : HIR.Expr) (body rest : List HIR.Stmt)
      (carried : List (HIR.Id × ValId)) (sA : Nat) (ρb : List (HIR.Id × ValId))
      (vc : ValId) (ic : List MIR.Instr) (s1 : Nat)
      (lb lr : Lowered) (phis : List MIR.Instr),
      mkCarried ρ supply
          ((dedupIds (assignedIds body)).filterMap
            (fun id => (rhoLookup ρ id).map (fun _ => id))) =
          some (carried, sA, ρb) →
      lowerExpr ρb sA c = some (vc, ic, s1) →
      lowerStmtsCFG (nextB + 2) (some nextB) false ρb (s1 + 1) (nextB + 3) s1
          true (some ⟨nextB, nextB + 1, carried⟩) body = some lb →
      lowerStmtsCFG (nextB + 1) none false ρb (lb.supply + 1) lb.next
          lb.supply true none rest = some lr →
      mkHeaderPhis ρ bId carried
          ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
          (lb.blocks.filterMap (fun b =>
            match b.terminator with
            | .goto t =>
                if t == nextB &&
                    b.id != (lb.blocks.getLast?.map fun b => b.id).getD
                      (nextB + 2) then
                  some b.id
                else none
            | _ => none)) = some phis →
      LoopStmts budget body →
      BranchStmts budget rest →
      IsStraight c → SLWeight c < budget →
      FreshAbove ρ supply → bId < nextB →
      ∀ (fh : Nat) (envH : HEnv) (fenvB0 : FullEnv) (outB : HFlow) (envB : HEnv),
      RelEnv envH ρb fenvB0.env →
      fenvB0.env s1 = some .unit →
      runHIRStmts fh envH body (.value (.lit .unit)) = (outB, envB) →
      ∀ (res : HFlow) (env' : HEnv),
      ((∃ u, outB = .value u) ∨ outB = .continued) →
      (outB = .stuck → (res, env') = (.stuck, envB)) →
      (outB = .continued → runHIRWhile fh envB c body = (res, env')) →
      (∀ (u : HIR.Expr), outB = .value u →
        runHIRWhile fh envB c body = (res, env')) →
      ∀ (prog : Program) (f : Func) (F : Nat),
      (∀ b ∈ lb.blocks, b ∈ f.blocks) →
      (∀ b ∈ [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
          [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
          [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++
          lr.blocks,
        b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB C : Nat), F ≥ (2 + armBlockBound fuelB body) * (fh + 1) + C →
      armBlockBound fuelB rest ≤ C →
      ((res = .value (.lit .unit)) →
        ∃ F' fenvX, F' ≤ F ∧ F' ≥ 1 + armBlockBound fuelB rest ∧
          execBlockFromIn prog F f (some nextB)
              ⟨nextB + 2, lb.instrs, lb.term⟩ fenvB0 =
            execBlockFromIn prog F' f (some (nextB + 1))
              ⟨nextB + 1, lr.instrs, lr.term⟩ fenvX ∧
          RelEnv env' ρb fenvX.env ∧ fenvX.env lb.supply = some .unit) ∧
      ((∀ (e : HIR.Expr), res = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F f (some nextB)
              ⟨nextB + 2, lb.instrs, lb.term⟩ fenvB0 = some w_e)) := by
  intro bId nextB ρ supply c body rest carried sA ρb vc ic s1 lb lr phis hmk
    hcond hbody hrest hphis hloop hrestP hstr hlt hfresh hltB fh
  induction fh with
  | zero =>
      intro envH fenvB0 outB envB hrelB0 haccB0 hbrun res env' hout hstuck hcont hval
        prog f F hmemLb hsub hnodf fuelB C hF hCrest
      have hz : runHIRStmts 0 envH body (.value (.lit .unit)) = (.stuck, envH) := rfl
      rw [hz] at hbrun
      obtain ⟨houtEq, henvEq⟩ := Prod.mk.inj hbrun
      subst henvEq
      have hresStuck : (res, env') = (.stuck, envH) := hstuck houtEq.symm
      have hresEq : res = .stuck := congrArg Prod.fst hresStuck
      refine ⟨?_, ?_⟩
      · intro hres
        rw [hresEq] at hres
        exact absurd hres (by simp)
      · intro e hres
        rw [hresEq] at hres
        exact absurd hres (by simp)
  | succ fh ih =>
      intro envH fenvB0 outB envB hrelB0 haccB0 hbrun res env' hout hstuck hcont hval
        prog f F hmemLb hsub hnodf fuelB C hF hCrest
      cases houtB : outB with
      | stuck =>
          have hresStuck : (res, env') = (.stuck, envB) := hstuck houtB
          have hresEq : res = .stuck := congrArg Prod.fst hresStuck
          refine ⟨?_, ?_⟩
          · intro hres
            rw [hresEq] at hres
            exact absurd hres (by simp)
          · intro e hres
            rw [hresEq] at hres
            exact absurd hres (by simp)
      | broke =>
          rcases hout with ⟨u, h⟩ | h
          · rw [houtB] at h; exact absurd h (by simp)
          · rw [houtB] at h; exact absurd h (by simp)
      | returned e =>
          rcases hout with ⟨u, h⟩ | h
          · rw [houtB] at h; exact absurd h (by simp)
          · rw [houtB] at h; exact absurd h (by simp)
      | value u =>
          have hrem : runHIRWhile (fh + 1) envB c body = (res, env') := hval u houtB
          have hbrunV : runHIRStmts (fh + 1) envH body (.value (.lit .unit)) =
              (HFlow.value u, envB) := by
            rw [houtB] at hbrun
            exact hbrun
          have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
          have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
          have hexcl : CarriedExcl ρb carried := mkCarried_excl hfresh hmk
          have hsup : ∀ id r, (id, r) ∈ carried → r < s1 + 1 := by
            intro id r hmem
            have hlt2 : r < sA := mkCarried_mem_hi hmk hmem
            exact Nat.lt_of_lt_of_le hlt2 (Nat.le_trans hsA (Nat.le_succ _))
          have hdist : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried →
              r₁ = r₂ → id₁ = id₂ := by
            intro a b c d h1 h2 he
            subst he
            exact mkCarried_reg_inj hmk h1 h2
          have hexclLb : CarriedExcl lb.ρ carried :=
            lowerStmtsCFG_loopBody_excl budget (nextB + 2) (some nextB) ρb
              (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩)
              ⟨nextB, nextB + 1, carried⟩ body lb carried rfl hbody hloop
              hexcl hsup
          have hexpand : (2 + armBlockBound fuelB body) * (fh + 1) +
              (2 + armBlockBound fuelB body)
              = (2 + armBlockBound fuelB body) * (fh + 1 + 1) := by
            have h1 : (2 + armBlockBound fuelB body) * (fh + 1 + 1)
                = (2 + armBlockBound fuelB body) * (fh + 1) +
                  (2 + armBlockBound fuelB body) * 1 := by
              rw [Nat.mul_add]
            rw [h1, Nat.mul_one]
          have hFbody : F ≥ blockBound fuelB body +
              ((2 + armBlockBound fuelB body) * (fh + 1) + 1 + C) := by
            simp only [blockBound]
            omega
          have hmemBody : (⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ : Block) ∈
              [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
              [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
              [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
          have hmemHdr : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
              [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
              [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
              [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
          have hmemExit : (⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ : Block) ∈
              [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
              [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
              [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
          have hfindHdr : findBlock f nextB =
              some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
            findBlock_of_nodup_mem hnodf (hsub _ hmemHdr)
          have hfindExit : findBlock f (nextB + 1) =
              some ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ :=
            findBlock_of_nodup_mem hnodf (hsub _ hmemExit)
          have hfreshB : FreshAbove ρb (s1 + 1) :=
            FreshAbove.mono ρb sA (s1 + 1) (Nat.le_trans hsA (Nat.le_succ _)) hfrb
          obtain ⟨F', fenv_arr, hle, hge, heq_body, hrel_arr⟩ :=
            ((lowerStmtsCFG_loopBody_run budget (nextB + 2) ρb (s1 + 1)
              (nextB + 3) nextB s1 (some ⟨nextB, nextB + 1, carried⟩)
              ⟨nextB, nextB + 1, carried⟩ body lb rfl hbody hloop hfreshB
              (Nat.lt_succ_self _) nextB
              (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)))
              (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)) Value.unit envH
              fenvB0 hrelB0 haccB0 (fh + 1) envB (HFlow.value u) hbrunV prog f
              (some nextB) F hmemLb hnodf fuelB
              ((2 + armBlockBound fuelB body) * (fh + 1) + 1 + C) hFbody hexcl
              hsup hdist
              ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
              ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
              ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
              hfindHdr hfindExit hfindHdr).1 _ rfl)
          have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
              match a with
              | none => none
              | some ps =>
                  match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                  | some entrySrc, some backSrc =>
                      some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                        (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                  | _, _ => none) (some []) = some phis := by
            simpa [mkHeaderPhis] using hphis
          obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
            ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
            (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
            carried [] phis hfold
          have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
            have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true
              (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
            have hbnd := hinv.2.2.1
            cases hgl : lb.blocks.getLast? with
            | none =>
                simp only [Option.map_none, Option.getD_none]
                exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
            | some bb =>
                have hm : bb ∈ lb.blocks := getLast?_mem hgl
                have hb := hbnd bb hm
                simp only [Option.map_some, Option.getD_some]
                have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
          have htrFall : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)),
              t ≠ (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) := by
            intro t ht
            rw [List.mem_filterMap] at ht
            obtain ⟨b, hb, hfb⟩ := ht
            cases htb : b.terminator with
            | goto tt =>
                simp only [htb] at hfb
                by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                · simp only [hC, if_true] at hfb
                  have heq : t = b.id := (Option.some.inj hfb).symm
                  have hne : b.id ≠ (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) := by
                    have h2 := (Bool.and_eq_true_iff.mp hC).2
                    simpa using h2
                  rw [heq]
                  exact hne
                · simp only [hC] at hfb
                  exact absurd hfb (by simp)
            | _ =>
                simp only [htb] at hfb
                exact absurd hfb (by simp)
          obtain ⟨fenvBack, hexecPhis, hrelBackLb, hbindBack, hframeBack⟩ :=
            headerPhis_exec_back lb.ρ bId ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))
              (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
              carried phif (by
                intro q hq
                obtain ⟨esrc, bsrc, he1, he2, hfp⟩ := hphif q hq
                exact ⟨esrc, bsrc, he2, hfp⟩)
              (Ne.symm hfallNe) htrFall hexclLb hdist prog fenv_arr envB hrel_arr
          have hrelBack : RelEnv envB ρb fenvBack.env :=
            conv_backRelEnv budget nextB ρ supply body carried sA ρb s1 lb hmk hbody
              hloop hfresh envB fenv_arr fenvBack hrel_arr hbindBack hframeBack
          have hfrP : FreshAbove ρb sA :=
            FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
          simp only [runHIRWhile] at hrem
          cases heval : evalHIR 256 envB c with
          | none =>
              rw [heval] at hrem
              have hst : res = .stuck := (congrArg Prod.fst hrem).symm
              refine ⟨?_, ?_⟩
              · intro hres
                rw [hst] at hres
                exact absurd hres (by simp)
              · intro e hres
                rw [hst] at hres
                exact absurd hres (by simp)
          | some r =>
              rw [heval] at hrem
              cases r with
              | lit w =>
                  cases w with
                  | bool b =>
                      cases b with
                      | false =>
                          simp only [] at hrem
                          have hpair : (res, env') = ((.value (.lit .unit)), envB) := by
                            rw [hrem]
                          have henvEq : env' = envB := congrArg Prod.snd hpair
                          subst env'
                          have hresEq : res = .value (.lit .unit) :=
                            congrArg Prod.fst hpair
                          obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                            lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt
                              hfrP envB fenvBack hrelBack prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) _ heval
                          have hrw : (HIR.Expr.lit (.bool false)) = HIR.Expr.lit wc := hrc
                          have hwc : wc = .bool false := (HIR.Expr.lit.inj hrw).symm
                          subst hwc
                          have hbool : fenvC.boolOf vc = some false :=
                            boolOf_of_lit fenvC vc false hregC
                          have hphiEq : phis = (carried.map phif).flatten := by
                            rw [hflat]; simp
                          have hexPhiIc : execInstrsFullFromIn prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) fenv_arr
                              (phis ++ ic) = some fenvC := by
                            have happ := execInstrsFullFromIn_append prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)))
                              fenv_arr phis ic
                            rw [← hphiEq] at hexecPhis
                            simp only [happ, hexecPhis, hexC]
                          have hF'ge1 : F' ≥ 1 := by omega
                          obtain ⟨F1, rfl⟩ : ∃ n, F' = n + 1 := ⟨F' - 1, by omega⟩
                          have hbranch : execBlockFromIn prog (F1 + 1) f (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)))
                              ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
                              fenv_arr =
                              execBlockFromIn prog F1 f (some nextB)
                                ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                                fenvC :=
                            execBlockFromIn_branch_false prog F1 f (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) nextB
                              (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv_arr fenvC
                              ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                              hexPhiIc hbool hfindExit
                          have hnp_lr : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ lr.instrs := by
                            intro d p src hm
                            have hpure := lowerStmtsCFG_instrs_pure (nextB + 1) none false ρb
                              (lb.supply + 1) lb.next lb.supply true rest lr hrest _ hm
                            exact IsPure_not_phi hpure d p src rfl
                          have hconst : execInstrsFullFromIn prog (some nextB) fenvC
                              [MIR.Instr.const lb.supply Value.unit] =
                              some ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ := by
                            simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                          have hexit : execBlockFromIn prog F1 f (some nextB)
                              ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                              fenvC =
                              execBlockFromIn prog F1 f (some (nextB + 1))
                                ⟨nextB + 1, lr.instrs, lr.term⟩
                                ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ := by
                            cases hF1 : F1 with
                            | zero =>
                                simp only [execBlockFromIn]
                            | succ n =>
                                simp only [execBlockFromIn]
                                have happ : execInstrsFullFromIn prog (some nextB) fenvC
                                    (MIR.Instr.const lb.supply Value.unit :: lr.instrs) =
                                    execInstrsFullFromIn prog (some nextB)
                                      ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩
                                      lr.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB)
                                    fenvC [MIR.Instr.const lb.supply Value.unit] lr.instrs
                                  simp only at happ0
                                  rw [hconst] at happ0
                                  simpa using happ0
                                rw [happ]
                                have heq1 : execInstrsFullFromIn prog (some nextB)
                                    ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩
                                    lr.instrs =
                                    execInstrsFullFromIn prog (some (nextB + 1))
                                      ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩
                                      lr.instrs := by
                                  rw [execInstrsFullFromIn_of_noPhi prog (some nextB) _
                                    lr.instrs hnp_lr,
                                    execInstrsFullFromIn_of_noPhi prog (some (nextB + 1)) _
                                      lr.instrs hnp_lr]
                                rw [heq1]
                          have hF1le : F1 ≤ F := Nat.le_trans (Nat.le_succ _) hle
                          have hPge : 2 + armBlockBound fuelB body
                              ≤ (2 + armBlockBound fuelB body) * (fh + 1) := by
                            have hmul : (2 + armBlockBound fuelB body) * (fh + 1)
                                = (2 + armBlockBound fuelB body) * fh +
                                  (2 + armBlockBound fuelB body) := by
                              rw [Nat.mul_add, Nat.mul_one]
                            rw [hmul]
                            exact Nat.le_add_left _ _
                          have hF1ge : F1 ≥ 1 + armBlockBound fuelB rest := by
                            have h1 : F1 ≥ (2 + armBlockBound fuelB body) * (fh + 1) + C := by
                              omega
                            have h2 : (2 + armBlockBound fuelB body) * (fh + 1) + C
                                ≥ 1 + armBlockBound fuelB rest := by
                              have hP1 : 1 ≤ (2 + armBlockBound fuelB body) * (fh + 1) :=
                                Nat.le_trans (by omega) hPge
                              omega
                            exact Nat.le_trans h2 h1
                          refine ⟨?_, ?_⟩
                          · intro hres
                            refine ⟨F1, ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩,
                              hF1le, hF1ge, ?_, ?_, ?_⟩
                            · exact heq_body.trans (hbranch.trans hexit)
                            · have hrelC : RelEnv envB ρb fenvC.env := by
                                have hexPure : execInstrsFull fenvBack ic = some fenvC := by
                                  have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                    intro d p src hm
                                    exact IsPure_not_phi
                                      (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                                  have h1 : execInstrsFullFromIn prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) fenvBack ic =
                                      execInstrsFull fenvBack ic :=
                                    execInstrsFullFromIn_of_noPhi prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) fenvBack ic hnp
                                  rw [h1] at hexC
                                  exact hexC
                                exact RelEnv_exec envB ρb sA c vc ic s1 hcond fenvBack fenvC
                                  hrelBack hfrP hexPure
                              have hlb : s1 + 1 ≤ lb.supply :=
                                (lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb
                                  (s1 + 1) (nextB + 3) s1 true
                                  (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop).2.1
                              intro id u hlook
                              obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                              refine ⟨w, hlookH, ?_⟩
                              by_cases heq : u = lb.supply
                              · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                have h1 : lb.supply < sA := heq ▸ hlt
                                have hlt2 : sA < lb.supply :=
                                  Nat.lt_of_le_of_lt hsA
                                    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlb)
                                have hcontra : lb.supply < lb.supply := Nat.lt_trans h1 hlt2
                                exact absurd hcontra (Nat.lt_irrefl _)
                              · have hbeq : ¬ (u == lb.supply) := by simpa using heq
                                simp only [Env.update, hbeq]
                                exact hreg
                            · simp [Env.update]
                          · intro e hres
                            rw [hresEq] at hres
                            exact absurd hres (by simp)
                      | true =>
                          have hF'ge1 : F' ≥ 1 := by omega
                          obtain ⟨F1, rfl⟩ : ∃ n, F' = n + 1 := ⟨F' - 1, by omega⟩
                          obtain ⟨wc, hrc, fenvC, hexC, _hstoreC, hregC⟩ :=
                            lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt
                              hfrP envB fenvBack hrelBack prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) _ heval
                          have hrw : (HIR.Expr.lit (.bool true)) = HIR.Expr.lit wc := hrc
                          have hwc : wc = .bool true := (HIR.Expr.lit.inj hrw).symm
                          subst hwc
                          have hbool : fenvC.boolOf vc = some true :=
                            boolOf_of_lit fenvC vc true hregC
                          have hphiEq : phis = (carried.map phif).flatten := by
                            rw [hflat]; simp
                          have hexPhiIc : execInstrsFullFromIn prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) fenv_arr
                              (phis ++ ic) = some fenvC := by
                            have happ := execInstrsFullFromIn_append prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)))
                              fenv_arr phis ic
                            rw [← hphiEq] at hexecPhis
                            simp only [happ, hexecPhis, hexC]
                          have hfindBody : findBlock f (nextB + 2) =
                              some ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ :=
                            findBlock_of_nodup_mem hnodf (hsub _ hmemBody)
                          have hbranch1 : execBlockFromIn prog (F1 + 1) f (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)))
                              ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
                              fenv_arr =
                              execBlockFromIn prog F1 f (some nextB)
                                ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩
                                fenvC :=
                            execBlockFromIn_branch_true prog F1 f (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) nextB
                              (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv_arr fenvC
                              ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩
                              hexPhiIc hbool hfindBody
                          have hconst1 : execInstrsFullFromIn prog (some nextB) fenvC
                              [MIR.Instr.const s1 Value.unit] =
                              some ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                            simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                          have hexit1 : execBlockFromIn prog F1 f (some nextB)
                              ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩
                              fenvC =
                              execBlockFromIn prog F1 f (some nextB)
                                ⟨nextB + 2, lb.instrs, lb.term⟩
                                ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                            cases hF1c : F1 with
                            | zero =>
                                simp only [execBlockFromIn]
                            | succ n =>
                                simp only [execBlockFromIn]
                                have happ : execInstrsFullFromIn prog (some nextB) fenvC
                                    (MIR.Instr.const s1 Value.unit :: lb.instrs) =
                                    execInstrsFullFromIn prog (some nextB)
                                      ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩
                                      lb.instrs := by
                                  have happ0 := execInstrsFullFromIn_append prog (some nextB)
                                    fenvC [MIR.Instr.const s1 Value.unit] lb.instrs
                                  simp only at happ0
                                  rw [hconst1] at happ0
                                  simpa using happ0
                                rw [happ]
                          have hrelC1 : RelEnv envB ρb fenvC.env := by
                            have hexPure : execInstrsFull fenvBack ic = some fenvC := by
                              have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                intro d p src hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                              have h1 : execInstrsFullFromIn prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) fenvBack ic =
                                  execInstrsFull fenvBack ic :=
                                execInstrsFullFromIn_of_noPhi prog (some ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) fenvBack ic hnp
                              rw [h1] at hexC
                              exact hexC
                            exact RelEnv_exec envB ρb sA c vc ic s1 hcond fenvBack fenvC
                              hrelBack hfrP hexPure
                          have hrel2 : RelEnv envB ρb (fenvC.env.update s1 Value.unit) := by
                            intro id u hlook
                            obtain ⟨w, hlookH, hreg⟩ := hrelC1 id u hlook
                            refine ⟨w, hlookH, ?_⟩
                            by_cases heq : u = s1
                            · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                              have h1 : s1 < sA := heq ▸ hlt
                              have hcontra : s1 < s1 := Nat.lt_of_lt_of_le h1 hsA
                              exact absurd hcontra (Nat.lt_irrefl _)
                            · have hbeq : ¬ (u == s1) := by simpa using heq
                              simp only [Env.update, hbeq]
                              exact hreg
                          have hacc2 : fenvC.env.update s1 Value.unit s1 = some (.unit : Value) := by
                            simp [Env.update]
                          have hPge : 2 + armBlockBound fuelB body
                              ≤ (2 + armBlockBound fuelB body) * (fh + 1) := by
                            have hmul : (2 + armBlockBound fuelB body) * (fh + 1)
                                = (2 + armBlockBound fuelB body) * fh +
                                  (2 + armBlockBound fuelB body) := by
                              rw [Nat.mul_add, Nat.mul_one]
                            rw [hmul]
                            exact Nat.le_add_left _ _
                          have hF1 : F1 ≥ (2 + armBlockBound fuelB body) * (fh + 1) + C := by
                            omega
                          have hF1le : F1 ≤ F := Nat.le_trans (Nat.le_succ _) hle
                          have hFbody2 : F1 ≥ blockBound fuelB body + (1 + armBlockBound fuelB rest) := by
                            simp only [blockBound]
                            omega
                          cases h2 : runHIRStmts fh envB body (.value (.lit .unit)) with
                          | mk out2 env2 =>
                              rw [h2] at hrem
                              obtain ⟨_hv2, hb2, _hc2, hr2⟩ :=
                                (lowerStmtsCFG_loopBody_run budget (nextB + 2) ρb (s1 + 1)
                                  (nextB + 3) nextB s1 (some ⟨nextB, nextB + 1, carried⟩)
                                  ⟨nextB, nextB + 1, carried⟩ body lb rfl hbody hloop hfreshB
                                  (Nat.lt_succ_self _) nextB
                                  (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)))
                                  (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)) Value.unit envB
                                  ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ hrel2 hacc2 fh env2 out2 h2 prog f
                                  (some nextB) F1 hmemLb hnodf fuelB
                                  (1 + armBlockBound fuelB rest) hFbody2 hexcl
                                  hsup hdist
                                  ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
                                  ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                                  ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
                                  hfindHdr hfindExit hfindHdr)
                              cases out2 with
                              | stuck =>
                                  simp only [] at hrem
                                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                                  refine ⟨?_, ?_⟩
                                  · intro hres
                                    rw [hst] at hres
                                    exact absurd hres (by simp)
                                  · intro e hres
                                    rw [hst] at hres
                                    exact absurd hres (by simp)
                              | broke =>
                                  simp only [] at hrem
                                  have hpairB : (res, env') = ((.value (.lit .unit)), env2) := by rw [hrem]
                                  have henvBEq : env' = env2 := congrArg Prod.snd hpairB
                                  subst env'
                                  obtain ⟨F2, fenv_arr2, blkPrev2, hle2, hge2, heqB, hrelB, hbindB⟩ := hb2 rfl
                                  have hnp_lr : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ lr.instrs := by
                                    intro d p src hm
                                    have hpure := lowerStmtsCFG_instrs_pure (nextB + 1) none false ρb
                                      (lb.supply + 1) lb.next lb.supply true rest lr hrest _ hm
                                    exact IsPure_not_phi hpure d p src rfl
                                  have hlb : s1 + 1 ≤ lb.supply :=
                                    (lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb
                                      (s1 + 1) (nextB + 3) s1 true
                                      (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop).2.1
                                  have hconstB : execInstrsFullFromIn prog (some blkPrev2) fenv_arr2
                                      [MIR.Instr.const lb.supply Value.unit] =
                                      some ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩ := by
                                    simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                                  have hexitB : execBlockFromIn prog F2 f (some blkPrev2)
                                      ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                                      fenv_arr2 =
                                      execBlockFromIn prog F2 f (some (nextB + 1))
                                        ⟨nextB + 1, lr.instrs, lr.term⟩
                                        ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩ := by
                                    cases hF2 : F2 with
                                    | zero =>
                                        simp only [execBlockFromIn]
                                    | succ n =>
                                        simp only [execBlockFromIn]
                                        have happ : execInstrsFullFromIn prog (some blkPrev2) fenv_arr2
                                            (MIR.Instr.const lb.supply Value.unit :: lr.instrs) =
                                            execInstrsFullFromIn prog (some blkPrev2)
                                              ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩
                                              lr.instrs := by
                                          have happ0 := execInstrsFullFromIn_append prog (some blkPrev2)
                                            fenv_arr2 [MIR.Instr.const lb.supply Value.unit] lr.instrs
                                          simp only at happ0
                                          rw [hconstB] at happ0
                                          simpa using happ0
                                        rw [happ]
                                        have heq1 : execInstrsFullFromIn prog (some blkPrev2)
                                            ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩
                                            lr.instrs =
                                            execInstrsFullFromIn prog (some (nextB + 1))
                                              ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩
                                              lr.instrs := by
                                          rw [execInstrsFullFromIn_of_noPhi prog (some blkPrev2) _
                                            lr.instrs hnp_lr,
                                            execInstrsFullFromIn_of_noPhi prog (some (nextB + 1)) _
                                              lr.instrs hnp_lr]
                                        rw [heq1]
                                  have hrelBX : RelEnv env2 ρb
                                      (fenv_arr2.env.update lb.supply Value.unit) := by
                                    have hrelR : RelEnv env2 ρb fenv_arr2.env :=
                                      conv_backRelEnv budget nextB ρ supply body carried sA ρb s1 lb
                                        hmk hbody hloop hfresh env2 fenv_arr2 fenv_arr2 hrelB hbindB
                                        (by intro r _; rfl)
                                    intro id u hlook
                                    obtain ⟨w, hlookH, hreg⟩ := hrelR id u hlook
                                    refine ⟨w, hlookH, ?_⟩
                                    by_cases heq : u = lb.supply
                                    · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                      have h1 : lb.supply < sA := heq ▸ hlt
                                      have hlt2 : sA < lb.supply :=
                                        Nat.lt_of_le_of_lt hsA
                                          (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlb)
                                      have hcontra : lb.supply < lb.supply := Nat.lt_trans h1 hlt2
                                      exact absurd hcontra (Nat.lt_irrefl _)
                                    · have hbeq : ¬ (u == lb.supply) := by simpa using heq
                                      simp only [Env.update, hbeq]
                                      exact hreg
                                  refine ⟨?_, ?_⟩
                                  · intro hres
                                    have hresEq : res = .value (.lit .unit) :=
                                      congrArg Prod.fst hpairB
                                    refine ⟨F2, ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩,
                                      Nat.le_trans hle2 hF1le, hge2, ?_, hrelBX, ?_⟩
                                    · exact heq_body.trans (hbranch1.trans (hexit1.trans (heqB.trans hexitB)))
                                    · simp [Env.update]
                                  · intro e hres
                                    have hresEq : res = .value (.lit .unit) :=
                                      congrArg Prod.fst hpairB
                                    rw [hresEq] at hres
                                    exact absurd hres (by simp)
                              | returned e =>
                                  simp only [] at hrem
                                  have hpairR : (res, env') = ((.returned e), env2) := by rw [hrem]
                                  obtain ⟨w_e, hew, heqR⟩ := hr2 e rfl
                                  refine ⟨?_, ?_⟩
                                  · intro hres
                                    have hresEq : res = .returned e :=
                                      congrArg Prod.fst hpairR
                                    rw [hresEq] at hres
                                    exact absurd hres (by simp)
                                  · intro er hres
                                    have hresEq : res = .returned e :=
                                      congrArg Prod.fst hpairR
                                    rw [hresEq] at hres
                                    cases hres
                                    exact ⟨w_e, hew,
                                      heq_body.trans (hbranch1.trans (hexit1.trans heqR))⟩
                              | value u2 =>
                                  simp only [] at hrem
                                  have hrem_v : (res, env') = runHIRWhile fh env2 c body := hrem.symm
                                  obtain ⟨ihV, ihR⟩ := ih envB
                                    ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ (HFlow.value u2) env2
                                    hrel2 hacc2 h2 res env' (Or.inl ⟨u2, rfl⟩)
                                    (by intro h; exact absurd h (by simp))
                                    (by intro h; exact absurd h (by simp))
                                    (by intro u hu; cases hu; exact hrem_v.symm)
                                    prog f F1 hmemLb hsub hnodf fuelB C hF1 hCrest
                                  refine ⟨?_, ?_⟩
                                  · intro hres
                                    obtain ⟨F', fenvX, hleI, hgeI, heqI, hrelI, hunitI⟩ := ihV hres
                                    exact ⟨F', fenvX, Nat.le_trans hleI hF1le, hgeI,
                                      heq_body.trans (hbranch1.trans (hexit1.trans heqI)), hrelI, hunitI⟩
                                  · intro e hres
                                    obtain ⟨w_e, hew, heqI⟩ := ihR e hres
                                    exact ⟨w_e, hew,
                                      heq_body.trans (hbranch1.trans (hexit1.trans heqI))⟩
                              | continued =>
                                  simp only [] at hrem
                                  have hrem_c : (res, env') = runHIRWhile fh env2 c body := hrem.symm
                                  obtain ⟨ihV, ihR⟩ := ih envB
                                    ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ HFlow.continued env2
                                    hrel2 hacc2 h2 res env' (Or.inr rfl)
                                    (by intro h; exact absurd h (by simp))
                                    (by intro _; exact hrem_c.symm)
                                    (by intro u h; exact absurd h (by simp))
                                    prog f F1 hmemLb hsub hnodf fuelB C hF1 hCrest
                                  refine ⟨?_, ?_⟩
                                  · intro hres
                                    obtain ⟨F', fenvX, hleI, hgeI, heqI, hrelI, hunitI⟩ := ihV hres
                                    exact ⟨F', fenvX, Nat.le_trans hleI hF1le, hgeI,
                                      heq_body.trans (hbranch1.trans (hexit1.trans heqI)), hrelI, hunitI⟩
                                  · intro e hres
                                    obtain ⟨w_e, hew, heqI⟩ := ihR e hres
                                    exact ⟨w_e, hew,
                                      heq_body.trans (hbranch1.trans (hexit1.trans heqI))⟩
                  | int _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | string _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | pointer _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | float _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | unit =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | undef =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | some _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | none =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | ok _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | err _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | tuple_ _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | array_ _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | loc _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                  | closure _ _ =>
                      simp only [] at hrem
                      have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                      refine ⟨?_, ?_⟩
                      · intro hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
                      · intro e hres
                        rw [hst] at hres
                        exact absurd hres (by simp)
              | var _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | unop _ _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | binop _ _ _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | app _ _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | lam _ _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | «let» _ _ _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | ifThenElse _ _ _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | whileLoop _ _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | «match» _ _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | block _ =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
              | infer =>
                  simp only [] at hrem
                  have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
      | continued =>
          have hrem : runHIRWhile (fh + 1) envB c body = (res, env') := hcont houtB
          have hbrunC : runHIRStmts (fh + 1) envH body (.value (.lit .unit)) =
              (HFlow.continued, envB) := by
            rw [houtB] at hbrun
            exact hbrun
          have hfrb : FreshAbove ρb sA := (mkCarried_growth_fresh hfresh hmk).2
          have hsA : sA ≤ s1 := lower_mono.1 _ _ _ _ _ _ hcond
          have hexcl : CarriedExcl ρb carried := mkCarried_excl hfresh hmk
          have hsup : ∀ id r, (id, r) ∈ carried → r < s1 + 1 := by
            intro id r hmem
            have hlt2 : r < sA := mkCarried_mem_hi hmk hmem
            exact Nat.lt_of_lt_of_le hlt2 (Nat.le_trans hsA (Nat.le_succ _))
          have hdist : ∀ id₁ r₁ id₂ r₂, (id₁, r₁) ∈ carried → (id₂, r₂) ∈ carried →
              r₁ = r₂ → id₁ = id₂ := by
            intro a b c d h1 h2 he
            subst he
            exact mkCarried_reg_inj hmk h1 h2
          have hexclLb : CarriedExcl lb.ρ carried :=
            lowerStmtsCFG_loopBody_excl budget (nextB + 2) (some nextB) ρb
              (s1 + 1) (nextB + 3) s1 true (some ⟨nextB, nextB + 1, carried⟩)
              ⟨nextB, nextB + 1, carried⟩ body lb carried rfl hbody hloop
              hexcl hsup
          have hexpand : (2 + armBlockBound fuelB body) * (fh + 1) +
              (2 + armBlockBound fuelB body)
              = (2 + armBlockBound fuelB body) * (fh + 1 + 1) := by
            have h1 : (2 + armBlockBound fuelB body) * (fh + 1 + 1)
                = (2 + armBlockBound fuelB body) * (fh + 1) +
                  (2 + armBlockBound fuelB body) * 1 := by
              rw [Nat.mul_add]
            rw [h1, Nat.mul_one]
          have hFbody : F ≥ blockBound fuelB body +
              ((2 + armBlockBound fuelB body) * (fh + 1) + 1 + C) := by
            simp only [blockBound]
            omega
          have hmemBody : (⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ : Block) ∈
              [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
              [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
              [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
          have hmemHdr : (⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ : Block) ∈
              [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
              [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
              [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
          have hmemExit : (⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ : Block) ∈
              [⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩] ++
              [⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩] ++
              [⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩] ++ lr.blocks := by simp
          have hfindHdr : findBlock f nextB =
              some ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩ :=
            findBlock_of_nodup_mem hnodf (hsub _ hmemHdr)
          have hfindExit : findBlock f (nextB + 1) =
              some ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩ :=
            findBlock_of_nodup_mem hnodf (hsub _ hmemExit)
          have hfreshB : FreshAbove ρb (s1 + 1) :=
            FreshAbove.mono ρb sA (s1 + 1) (Nat.le_trans hsA (Nat.le_succ _)) hfrb
          obtain ⟨F', fenv_arr, blkPrev, hle, hge, heq_body, hcarried, hframe0, hforbid, hfallRel⟩ :=
            ((lowerStmtsCFG_loopBody_run budget (nextB + 2) ρb (s1 + 1)
              (nextB + 3) nextB s1 (some ⟨nextB, nextB + 1, carried⟩)
              ⟨nextB, nextB + 1, carried⟩ body lb rfl hbody hloop hfreshB
              (Nat.lt_succ_self _) nextB
              (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)))
              (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)) Value.unit envH
              fenvB0 hrelB0 haccB0 (fh + 1) envB HFlow.continued hbrunC prog f
              (some nextB) F hmemLb hnodf fuelB
              ((2 + armBlockBound fuelB body) * (fh + 1) + 1 + C) hFbody hexcl
              hsup hdist
              ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
              ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
              ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
              hfindHdr hfindExit hfindHdr).2.2.1 rfl)
          have hfold : carried.foldl (fun (a : Option (List Instr)) (p : HIR.Id × ValId) =>
              match a with
              | none => none
              | some ps =>
                  match rhoLookup ρ p.1, rhoLookup lb.ρ p.1 with
                  | some entrySrc, some backSrc =>
                      some (ps ++ [.phi p.2 bId entrySrc, .phi p.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                        (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map (.phi p.2 · p.2))
                  | _, _ => none) (some []) = some phis := by
            simpa [mkHeaderPhis] using hphis
          obtain ⟨phif, hphif, hflat⟩ := mkHeaderPhis_flatMap ρ bId
            ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) lb.ρ
            (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto t => if t == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
            carried [] phis hfold
          have hfallNe : ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) ≠ bId := by
            have hinv := lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb (s1 + 1) (nextB + 3) s1 true
              (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop
            have hbnd := hinv.2.2.1
            cases hgl : lb.blocks.getLast? with
            | none =>
                simp only [Option.map_none, Option.getD_none]
                exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB (Nat.le_add_right _ _))
            | some bb =>
                have hm : bb ∈ lb.blocks := getLast?_mem hgl
                have hb := hbnd bb hm
                simp only [Option.map_some, Option.getD_some]
                have hle : nextB ≤ bb.id := Nat.le_trans (Nat.le_add_right _ _) hb.1
                exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hltB hle)
          have htrFall : ∀ t ∈ (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)),
              t ≠ (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) := by
            intro t ht
            rw [List.mem_filterMap] at ht
            obtain ⟨b, hb, hfb⟩ := ht
            cases htb : b.terminator with
            | goto tt =>
                simp only [htb] at hfb
                by_cases hC : (tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) = true
                · simp only [hC, if_true] at hfb
                  have heq : t = b.id := (Option.some.inj hfb).symm
                  have hne : b.id ≠ (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) := by
                    have h2 := (Bool.and_eq_true_iff.mp hC).2
                    simpa using h2
                  rw [heq]
                  exact hne
                · simp only [hC] at hfb
                  exact absurd hfb (by simp)
            | _ =>
                simp only [htb] at hfb
                exact absurd hfb (by simp)
          have hP0 : ∀ id r, (id, r) ∈ carried → ∃ w,
              lookupHEnv envH id = some (.lit w) := by
            intro id r hmem
            obtain ⟨uρ, huρ⟩ := mkCarried_mem_domain hmk hmem
            obtain ⟨w, hw, _⟩ := hrelB0 id uρ huρ
            exact ⟨w, hw⟩
          have hP := spine_P budget carried (fh + 1) envH envB body hloop _ _ hbrunC hP0
          have hlookB : ∀ id, id ∉ assignedIds body →
              lookupHEnv envB id = lookupHEnv envH id := by
            intro id hnid
            exact runHIRStmts_loopBody_lookup budget body hloop (nextB + 2)
              (some nextB) ρb (s1 + 1) (nextB + 3) s1 true
              (some ⟨nextB, nextB + 1, carried⟩) ⟨nextB, nextB + 1, carried⟩
              lb rfl hbody (fh + 1) envH envB _ _ id hbrunC hnid
          have hleHi : supply ≤ s1 + 1 :=
            Nat.le_trans (Nat.le_trans (mkCarried_le hmk) hsA) (Nat.le_succ _)
          have hC : RelEnv envB ρb fenv_arr.env :=
            cont_post_RelEnv budget ρ supply body carried sA ρb hmk hfresh
              (s1 + 1) hleHi envB envH fenvB0 fenv_arr hrelB0 hcarried hP
              hframe0 hlookB
          have hneB : bId ≠ blkPrev := by
            intro hcon
            subst hcon
            exact absurd (Nat.lt_trans hltB hforbid) (Nat.lt_irrefl _)
          have hshape : ∀ q ∈ carried, ∃ entrySrc backSrc,
              phif q = ([MIR.Instr.phi q.2 bId entrySrc,
                MIR.Instr.phi q.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map
                  (MIR.Instr.phi q.2 · q.2)) := by
            intro q hq
            obtain ⟨entrySrc, backSrc, _, _, hfp⟩ := hphif q hq
            exact ⟨entrySrc, backSrc, hfp⟩
          have hvalB1 : ∀ id r, (id, r) ∈ carried → ∃ w, fenv_arr.env r = some w := by
            intro id r hmem
            obtain ⟨w, hw⟩ := hP id r hmem
            exact ⟨w, hcarried id r w hmem hw⟩
          have hvalFall : (blkPrev = ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))) →
                ∀ q ∈ carried, ∃ entrySrc backSrc w, fenv_arr.env q.2 = some w ∧
                fenv_arr.env backSrc = some w ∧
                phif q = ([MIR.Instr.phi q.2 bId entrySrc,
                  MIR.Instr.phi q.2 ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2)) backSrc] ++
                  (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none)).map
                    (MIR.Instr.phi q.2 · q.2)) := by
              intro hEq q hq
              obtain ⟨id, r⟩ := q
              obtain ⟨esrc, bsrc, _, hlook, hfp⟩ := hphif (id, r) hq
              obtain ⟨w, hw⟩ := hP id r hq
              have hcr : fenv_arr.env r = some w := hcarried id r w hq hw
              have hrelLb : RelEnv envB lb.ρ fenv_arr.env := hfallRel hEq
              obtain ⟨w', hlookH, hreg⟩ := hrelLb id bsrc hlook
              have heqw : w' = w :=
                HIR.Expr.lit.inj (Option.some.inj (hlookH.symm.trans hw))
              subst w'
              exact ⟨esrc, bsrc, w, hcr, hreg, hfp⟩
          have hexecPhi : execInstrsFullFromIn prog (some blkPrev) fenv_arr
                ((carried.map phif).flatten) = some fenv_arr := by
            exact headerPhis_all_identity bId
              ((lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2))
              (lb.blocks.filterMap (fun b : Block => match b.terminator with | .goto tt => if tt == nextB && b.id != (lb.blocks.getLast?.map fun b => b.id).getD (nextB + 2) then some b.id else none | _ => none))
              carried phif blkPrev prog fenv_arr hvalFall hshape hvalB1
              hneB hfallNe htrFall
          have hphiEq : phis = (carried.map phif).flatten := by
              rw [hflat]; simp
          rw [← hphiEq] at hexecPhi
          have hfrP : FreshAbove ρb sA :=
              FreshAbove.mono ρb sA sA (Nat.le_refl _) ((mkCarried_growth_fresh hfresh hmk).2)
          have hremW : runHIRWhile (fh + 1) envB c body = (res, env') := hrem
          simp only [runHIRWhile] at hrem
          cases heval : evalHIR 256 envB c with
          | none =>
                rw [heval] at hrem
                have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                refine ⟨?_, ?_⟩
                · intro hres
                  rw [hst] at hres
                  exact absurd hres (by simp)
                · intro e hres
                  rw [hst] at hres
                  exact absurd hres (by simp)
          | some r =>
                rw [heval] at hrem
                by_cases hbool : ∃ b : Bool, r = HIR.Expr.lit (.bool b)
                · obtain ⟨b, rfl⟩ := hbool
                  cases b with
                  | false =>
                      simp only [] at hrem
                      have hpair : (res, env') = ((.value (.lit .unit)), envB) := by
                        rw [hrem]
                      have henvEq : env' = envB := congrArg Prod.snd hpair
                      subst env'
                      have hresEq : res = .value (.lit .unit) :=
                        congrArg Prod.fst hpair
                      obtain ⟨wc, hrc, fenvC, hexC, hstoreC, hregC⟩ :=
                        lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt
                          hfrP envB fenv_arr hC prog (some blkPrev) _ heval
                      have hrw : (HIR.Expr.lit (.bool false)) = HIR.Expr.lit wc := hrc
                      have hwc : wc = .bool false := (HIR.Expr.lit.inj hrw).symm
                      subst hwc
                      have hbool : fenvC.boolOf vc = some false :=
                        boolOf_of_lit fenvC vc false hregC
                      have hexPhiIc : execInstrsFullFromIn prog (some blkPrev) fenv_arr
                          (phis ++ ic) = some fenvC := by
                        have happ := execInstrsFullFromIn_append prog (some blkPrev)
                          fenv_arr phis ic
                        simp only [happ, hexecPhi, hexC]
                      have hF'ge1 : F' ≥ 1 := by omega
                      obtain ⟨F1, rfl⟩ : ∃ n, F' = n + 1 := ⟨F' - 1, by omega⟩
                      have hbranch : execBlockFromIn prog (F1 + 1) f (some blkPrev)
                          ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
                          fenv_arr =
                          execBlockFromIn prog F1 f (some nextB)
                            ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                            fenvC :=
                        execBlockFromIn_branch_false prog F1 f (some blkPrev) nextB
                          (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv_arr fenvC
                          ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                          hexPhiIc hbool hfindExit
                      have hnp_lr : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ lr.instrs := by
                        intro d p src hm
                        have hpure := lowerStmtsCFG_instrs_pure (nextB + 1) none false ρb
                          (lb.supply + 1) lb.next lb.supply true rest lr hrest _ hm
                        exact IsPure_not_phi hpure d p src rfl
                      have hconst : execInstrsFullFromIn prog (some nextB) fenvC
                          [MIR.Instr.const lb.supply Value.unit] =
                          some ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ := by
                        simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                      have hexit : execBlockFromIn prog F1 f (some nextB)
                          ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                          fenvC =
                          execBlockFromIn prog F1 f (some (nextB + 1))
                            ⟨nextB + 1, lr.instrs, lr.term⟩
                            ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩ := by
                        cases hF1 : F1 with
                        | zero =>
                            simp only [execBlockFromIn]
                        | succ n =>
                            simp only [execBlockFromIn]
                            have happ : execInstrsFullFromIn prog (some nextB) fenvC
                                (MIR.Instr.const lb.supply Value.unit :: lr.instrs) =
                                execInstrsFullFromIn prog (some nextB)
                                  ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩
                                  lr.instrs := by
                              have happ0 := execInstrsFullFromIn_append prog (some nextB)
                                fenvC [MIR.Instr.const lb.supply Value.unit] lr.instrs
                              simp only at happ0
                              rw [hconst] at happ0
                              simpa using happ0
                            rw [happ]
                            have heq1 : execInstrsFullFromIn prog (some nextB)
                                ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩
                                lr.instrs =
                                execInstrsFullFromIn prog (some (nextB + 1))
                                  ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩
                                  lr.instrs := by
                              rw [execInstrsFullFromIn_of_noPhi prog (some nextB) _
                                lr.instrs hnp_lr,
                                execInstrsFullFromIn_of_noPhi prog (some (nextB + 1)) _
                                  lr.instrs hnp_lr]
                            rw [heq1]
                      have hF1le : F1 ≤ F := Nat.le_trans (Nat.le_succ _) hle
                      have hPge : 2 + armBlockBound fuelB body
                          ≤ (2 + armBlockBound fuelB body) * (fh + 1) := by
                        have hmul : (2 + armBlockBound fuelB body) * (fh + 1)
                            = (2 + armBlockBound fuelB body) * fh +
                              (2 + armBlockBound fuelB body) := by
                          rw [Nat.mul_add, Nat.mul_one]
                        rw [hmul]
                        exact Nat.le_add_left _ _
                      have hF1ge : F1 ≥ 1 + armBlockBound fuelB rest := by
                        have h1 : F1 ≥ (2 + armBlockBound fuelB body) * (fh + 1) + C := by
                          omega
                        have h2 : (2 + armBlockBound fuelB body) * (fh + 1) + C
                            ≥ 1 + armBlockBound fuelB rest := by
                          have hP1 : 1 ≤ (2 + armBlockBound fuelB body) * (fh + 1) :=
                            Nat.le_trans (by omega) hPge
                          omega
                        exact Nat.le_trans h2 h1
                      refine ⟨?_, ?_⟩
                      · intro hres
                        refine ⟨F1, ⟨fenvC.env.update lb.supply Value.unit, fenvC.store⟩,
                          hF1le, hF1ge, ?_, ?_, ?_⟩
                        · exact heq_body.trans (hbranch.trans hexit)
                        · have hrelC : RelEnv envB ρb fenvC.env := by
                            have hexPure : execInstrsFull fenv_arr ic = some fenvC := by
                              have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                                intro d p src hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                              have h1 : execInstrsFullFromIn prog (some blkPrev) fenv_arr ic =
                                  execInstrsFull fenv_arr ic :=
                                execInstrsFullFromIn_of_noPhi prog (some blkPrev) fenv_arr ic hnp
                              rw [h1] at hexC
                              exact hexC
                            exact RelEnv_exec envB ρb sA c vc ic s1 hcond fenv_arr fenvC
                              hC hfrP hexPure
                          have hlb : s1 + 1 ≤ lb.supply :=
                            (lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb
                              (s1 + 1) (nextB + 3) s1 true
                              (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop).2.1
                          intro id u hlook
                          obtain ⟨w, hlookH, hreg⟩ := hrelC id u hlook
                          refine ⟨w, hlookH, ?_⟩
                          by_cases heq : u = lb.supply
                          · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                            have h1 : lb.supply < sA := heq ▸ hlt
                            have hlt2 : sA < lb.supply :=
                              Nat.lt_of_le_of_lt hsA
                                (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlb)
                            have hcontra : lb.supply < lb.supply := Nat.lt_trans h1 hlt2
                            exact absurd hcontra (Nat.lt_irrefl _)
                          · have hbeq : ¬ (u == lb.supply) := by simpa using heq
                            simp only [Env.update, hbeq]
                            exact hreg
                        · simp [Env.update]
                      · intro e hres
                        rw [hresEq] at hres
                        exact absurd hres (by simp)
                  | true =>
                      have hF'ge1 : F' ≥ 1 := by omega
                      obtain ⟨F1, rfl⟩ : ∃ n, F' = n + 1 := ⟨F' - 1, by omega⟩
                      obtain ⟨wc, hrc, fenvC, hexC, _hstoreC, hregC⟩ :=
                        lowerCond_exec_agree budget ρb sA c vc ic s1 hcond hstr hlt
                          hfrP envB fenv_arr hC prog (some blkPrev) _ heval
                      have hrw : (HIR.Expr.lit (.bool true)) = HIR.Expr.lit wc := hrc
                      have hwc : wc = .bool true := (HIR.Expr.lit.inj hrw).symm
                      subst hwc
                      have hbool : fenvC.boolOf vc = some true :=
                        boolOf_of_lit fenvC vc true hregC
                      have hexPhiIc : execInstrsFullFromIn prog (some blkPrev) fenv_arr
                          (phis ++ ic) = some fenvC := by
                        have happ := execInstrsFullFromIn_append prog (some blkPrev)
                          fenv_arr phis ic
                        simp only [happ, hexecPhi, hexC]
                      have hfindBody : findBlock f (nextB + 2) =
                          some ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩ :=
                        findBlock_of_nodup_mem hnodf (hsub _ hmemBody)
                      have hbranch1 : execBlockFromIn prog (F1 + 1) f (some blkPrev)
                          ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
                          fenv_arr =
                          execBlockFromIn prog F1 f (some nextB)
                            ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩
                            fenvC :=
                        execBlockFromIn_branch_true prog F1 f (some blkPrev) nextB
                          (phis ++ ic) vc (nextB + 2) (nextB + 1) fenv_arr fenvC
                          ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩
                          hexPhiIc hbool hfindBody
                      have hconst1 : execInstrsFullFromIn prog (some nextB) fenvC
                          [MIR.Instr.const s1 Value.unit] =
                          some ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                        simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                      have hexit1 : execBlockFromIn prog F1 f (some nextB)
                          ⟨nextB + 2, .const s1 .unit :: lb.instrs, lb.term⟩
                          fenvC =
                          execBlockFromIn prog F1 f (some nextB)
                            ⟨nextB + 2, lb.instrs, lb.term⟩
                            ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ := by
                        cases hF1c : F1 with
                        | zero =>
                            simp only [execBlockFromIn]
                        | succ n =>
                            simp only [execBlockFromIn]
                            have happ : execInstrsFullFromIn prog (some nextB) fenvC
                                (MIR.Instr.const s1 Value.unit :: lb.instrs) =
                                execInstrsFullFromIn prog (some nextB)
                                  ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩
                                  lb.instrs := by
                              have happ0 := execInstrsFullFromIn_append prog (some nextB)
                                fenvC [MIR.Instr.const s1 Value.unit] lb.instrs
                              simp only at happ0
                              rw [hconst1] at happ0
                              simpa using happ0
                            rw [happ]
                      have hrelC1 : RelEnv envB ρb fenvC.env := by
                        have hexPure : execInstrsFull fenv_arr ic = some fenvC := by
                          have hnp : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ ic := by
                            intro d p src hm
                            exact IsPure_not_phi
                              (lower_isPure.1 _ _ _ _ _ _ hcond _ hm) d p src rfl
                          have h1 : execInstrsFullFromIn prog (some blkPrev) fenv_arr ic =
                              execInstrsFull fenv_arr ic :=
                            execInstrsFullFromIn_of_noPhi prog (some blkPrev) fenv_arr ic hnp
                          rw [h1] at hexC
                          exact hexC
                        exact RelEnv_exec envB ρb sA c vc ic s1 hcond fenv_arr fenvC
                          hC hfrP hexPure
                      have hrel2 : RelEnv envB ρb (fenvC.env.update s1 Value.unit) := by
                        intro id u hlook
                        obtain ⟨w, hlookH, hreg⟩ := hrelC1 id u hlook
                        refine ⟨w, hlookH, ?_⟩
                        by_cases heq : u = s1
                        · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                          have h1 : s1 < sA := heq ▸ hlt
                          have hcontra : s1 < s1 := Nat.lt_of_lt_of_le h1 hsA
                          exact absurd hcontra (Nat.lt_irrefl _)
                        · have hbeq : ¬ (u == s1) := by simpa using heq
                          simp only [Env.update, hbeq]
                          exact hreg
                      have hacc2 : fenvC.env.update s1 Value.unit s1 = some (.unit : Value) := by
                        simp [Env.update]
                      have hPge : 2 + armBlockBound fuelB body
                          ≤ (2 + armBlockBound fuelB body) * (fh + 1) := by
                        have hmul : (2 + armBlockBound fuelB body) * (fh + 1)
                            = (2 + armBlockBound fuelB body) * fh +
                              (2 + armBlockBound fuelB body) := by
                          rw [Nat.mul_add, Nat.mul_one]
                        rw [hmul]
                        exact Nat.le_add_left _ _
                      have hF1 : F1 ≥ (2 + armBlockBound fuelB body) * (fh + 1) + C := by
                        omega
                      have hF1le : F1 ≤ F := Nat.le_trans (Nat.le_succ _) hle
                      have hFbody2 : F1 ≥ blockBound fuelB body + (1 + armBlockBound fuelB rest) := by
                        simp only [blockBound]
                        omega
                      cases h2 : runHIRStmts fh envB body (.value (.lit .unit)) with
                      | mk out2 env2 =>
                          rw [h2] at hrem
                          obtain ⟨_hv2, hb2, _hc2, hr2⟩ :=
                            (lowerStmtsCFG_loopBody_run budget (nextB + 2) ρb (s1 + 1)
                              (nextB + 3) nextB s1 (some ⟨nextB, nextB + 1, carried⟩)
                              ⟨nextB, nextB + 1, carried⟩ body lb rfl hbody hloop hfreshB
                              (Nat.lt_succ_self _) nextB
                              (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)))
                              (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)) Value.unit envB
                              ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ hrel2 hacc2 fh env2 out2 h2 prog f
                              (some nextB) F1 hmemLb hnodf fuelB
                              (1 + armBlockBound fuelB rest) hFbody2 hexcl
                              hsup hdist
                              ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
                              ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                              ⟨nextB, phis ++ ic, .branch vc (nextB + 2) (nextB + 1)⟩
                              hfindHdr hfindExit hfindHdr)
                          cases out2 with
                          | stuck =>
                              simp only [] at hrem
                              have hst : res = .stuck := (congrArg Prod.fst hrem).symm
                              refine ⟨?_, ?_⟩
                              · intro hres
                                rw [hst] at hres
                                exact absurd hres (by simp)
                              · intro e hres
                                rw [hst] at hres
                                exact absurd hres (by simp)
                          | broke =>
                              simp only [] at hrem
                              have hpairB : (res, env') = ((.value (.lit .unit)), env2) := by rw [hrem]
                              have henvBEq : env' = env2 := congrArg Prod.snd hpairB
                              subst env'
                              obtain ⟨F2, fenv_arr2, blkPrev2, hle2, hge2, heqB, hrelB, hbindB⟩ := hb2 rfl
                              have hnp_lr : ∀ dst pred src, MIR.Instr.phi dst pred src ∉ lr.instrs := by
                                intro d p src hm
                                have hpure := lowerStmtsCFG_instrs_pure (nextB + 1) none false ρb
                                  (lb.supply + 1) lb.next lb.supply true rest lr hrest _ hm
                                exact IsPure_not_phi hpure d p src rfl
                              have hlb : s1 + 1 ≤ lb.supply :=
                                (lowerStmtsCFG_loopBody_inv budget (nextB + 2) (some nextB) ρb
                                  (s1 + 1) (nextB + 3) s1 true
                                  (some ⟨nextB, nextB + 1, carried⟩) body lb hbody hloop).2.1
                              have hconstB : execInstrsFullFromIn prog (some blkPrev2) fenv_arr2
                                  [MIR.Instr.const lb.supply Value.unit] =
                                  some ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩ := by
                                simp [execInstrsFullFromIn_eq, execInstrsFullFrom, evalInstrFull]
                              have hexitB : execBlockFromIn prog F2 f (some blkPrev2)
                                  ⟨nextB + 1, .const lb.supply .unit :: lr.instrs, lr.term⟩
                                  fenv_arr2 =
                                  execBlockFromIn prog F2 f (some (nextB + 1))
                                    ⟨nextB + 1, lr.instrs, lr.term⟩
                                    ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩ := by
                                cases hF2 : F2 with
                                | zero =>
                                    simp only [execBlockFromIn]
                                | succ n =>
                                    simp only [execBlockFromIn]
                                    have happ : execInstrsFullFromIn prog (some blkPrev2) fenv_arr2
                                        (MIR.Instr.const lb.supply Value.unit :: lr.instrs) =
                                        execInstrsFullFromIn prog (some blkPrev2)
                                          ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩
                                          lr.instrs := by
                                      have happ0 := execInstrsFullFromIn_append prog (some blkPrev2)
                                        fenv_arr2 [MIR.Instr.const lb.supply Value.unit] lr.instrs
                                      simp only at happ0
                                      rw [hconstB] at happ0
                                      simpa using happ0
                                    rw [happ]
                                    have heq1 : execInstrsFullFromIn prog (some blkPrev2)
                                        ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩
                                        lr.instrs =
                                        execInstrsFullFromIn prog (some (nextB + 1))
                                          ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩
                                          lr.instrs := by
                                      rw [execInstrsFullFromIn_of_noPhi prog (some blkPrev2) _
                                        lr.instrs hnp_lr,
                                        execInstrsFullFromIn_of_noPhi prog (some (nextB + 1)) _
                                          lr.instrs hnp_lr]
                                    rw [heq1]
                              have hrelBX : RelEnv env2 ρb
                                  (fenv_arr2.env.update lb.supply Value.unit) := by
                                have hrelR : RelEnv env2 ρb fenv_arr2.env :=
                                  conv_backRelEnv budget nextB ρ supply body carried sA ρb s1 lb
                                    hmk hbody hloop hfresh env2 fenv_arr2 fenv_arr2 hrelB hbindB
                                    (by intro r _; rfl)
                                intro id u hlook
                                obtain ⟨w, hlookH, hreg⟩ := hrelR id u hlook
                                refine ⟨w, hlookH, ?_⟩
                                by_cases heq : u = lb.supply
                                · have hlt : u < sA := hfrP id u (rhoLookup_some_mem _ _ _ hlook)
                                  have h1 : lb.supply < sA := heq ▸ hlt
                                  have hlt2 : sA < lb.supply :=
                                    Nat.lt_of_le_of_lt hsA
                                      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlb)
                                  have hcontra : lb.supply < lb.supply := Nat.lt_trans h1 hlt2
                                  exact absurd hcontra (Nat.lt_irrefl _)
                                · have hbeq : ¬ (u == lb.supply) := by simpa using heq
                                  simp only [Env.update, hbeq]
                                  exact hreg
                              refine ⟨?_, ?_⟩
                              · intro hres
                                have hresEq : res = .value (.lit .unit) :=
                                  congrArg Prod.fst hpairB
                                refine ⟨F2, ⟨fenv_arr2.env.update lb.supply Value.unit, fenv_arr2.store⟩,
                                  Nat.le_trans hle2 hF1le, hge2, ?_, hrelBX, ?_⟩
                                · exact heq_body.trans (hbranch1.trans (hexit1.trans (heqB.trans hexitB)))
                                · simp [Env.update]
                              · intro e hres
                                have hresEq : res = .value (.lit .unit) :=
                                  congrArg Prod.fst hpairB
                                rw [hresEq] at hres
                                exact absurd hres (by simp)
                          | returned e =>
                              simp only [] at hrem
                              have hpairR : (res, env') = ((.returned e), env2) := by rw [hrem]
                              obtain ⟨w_e, hew, heqR⟩ := hr2 e rfl
                              refine ⟨?_, ?_⟩
                              · intro hres
                                have hresEq : res = .returned e :=
                                  congrArg Prod.fst hpairR
                                rw [hresEq] at hres
                                exact absurd hres (by simp)
                              · intro er hres
                                have hresEq : res = .returned e :=
                                  congrArg Prod.fst hpairR
                                rw [hresEq] at hres
                                cases hres
                                exact ⟨w_e, hew,
                                  heq_body.trans (hbranch1.trans (hexit1.trans heqR))⟩
                          | value u2 =>
                              simp only [] at hrem
                              have hrem_v : (res, env') = runHIRWhile fh env2 c body := hrem.symm
                              obtain ⟨ihV, ihR⟩ := ih envB
                                ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ (HFlow.value u2) env2
                                hrel2 hacc2 h2 res env' (Or.inl ⟨u2, rfl⟩)
                                (by intro h; exact absurd h (by simp))
                                (by intro h; exact absurd h (by simp))
                                (by intro u hu; cases hu; exact hrem_v.symm)
                                prog f F1 hmemLb hsub hnodf fuelB C hF1 hCrest
                              refine ⟨?_, ?_⟩
                              · intro hres
                                obtain ⟨F', fenvX, hleI, hgeI, heqI, hrelI, hunitI⟩ := ihV hres
                                exact ⟨F', fenvX, Nat.le_trans hleI hF1le, hgeI,
                                  heq_body.trans (hbranch1.trans (hexit1.trans heqI)), hrelI, hunitI⟩
                              · intro e hres
                                obtain ⟨w_e, hew, heqI⟩ := ihR e hres
                                exact ⟨w_e, hew,
                                  heq_body.trans (hbranch1.trans (hexit1.trans heqI))⟩
                          | continued =>
                              simp only [] at hrem
                              have hrem_c : (res, env') = runHIRWhile fh env2 c body := hrem.symm
                              obtain ⟨ihV, ihR⟩ := ih envB
                                ⟨fenvC.env.update s1 Value.unit, fenvC.store⟩ HFlow.continued env2
                                hrel2 hacc2 h2 res env' (Or.inr rfl)
                                (by intro h; exact absurd h (by simp))
                                (by intro _; exact hrem_c.symm)
                                (by intro u h; exact absurd h (by simp))
                                prog f F1 hmemLb hsub hnodf fuelB C hF1 hCrest
                              refine ⟨?_, ?_⟩
                              · intro hres
                                obtain ⟨F', fenvX, hleI, hgeI, heqI, hrelI, hunitI⟩ := ihV hres
                                exact ⟨F', fenvX, Nat.le_trans hleI hF1le, hgeI,
                                  heq_body.trans (hbranch1.trans (hexit1.trans heqI)), hrelI, hunitI⟩
                              · intro e hres
                                obtain ⟨w_e, hew, heqI⟩ := ihR e hres
                                exact ⟨w_e, hew,
                                  heq_body.trans (hbranch1.trans (hexit1.trans heqI))⟩
                · -- A non-boolean condition value stalls the loop.
                  have hne : ∀ b : Bool, r ≠ HIR.Expr.lit (.bool b) :=
                    fun b hbeq => hbool ⟨b, hbeq⟩
                  have hstuckEq : (res, env') = (.stuck, envB) :=
                    hremW.symm.trans (runHIRWhile_succ_cond_other heval hne)
                  have hst : res = .stuck := congrArg Prod.fst hstuckEq
                  refine ⟨?_, ?_⟩
                  · intro hres
                    rw [hst] at hres
                    exact absurd hres (by simp)
                  · intro e hres
                    rw [hst] at hres
                    exact absurd hres (by simp)

end Morph.HIRToMIRCorrect
