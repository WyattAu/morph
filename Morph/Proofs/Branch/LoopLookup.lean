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

/-!
# Stage C loop-body lookup preservation: the `LoopBodyLookupAux` section

Eighth proof leaf out of the `HIRToMIRBranch` monolith: the
`LoopBodyLookupAux` section (`loopBody_lookup_*` per-constructor lemmas)
plus its followers — `runHIRStmts_loopBody_lookup`,
`loopBody_carried_of_assigned`, `runHIRWhile_succ_cond_other`,
`loopBody_assigned_carried`, `lowerStmtsCFG_loopBody_mem_preserv`,
`mkCarried_mem_ids`, `isChain_peel`, `lowerStmtsCFG_loopBody_carriedExcl`,
and `lowerStmtsCFG_loopBody_rho_preserv` (moved verbatim). The spine
lemmas downstream cite this leaf.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

section LoopBodyLookupAux

set_option linter.unusedVariables false in
theorem loopBody_lookup_nil (budget : Nat)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      [] = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv [] acc = (out, henv'))
    (hnid : id ∉ assignedIds []) :
    lookupHEnv henv' id = lookupHEnv henv id := by
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          rw [runHIRStmts_nil] at hrun
          cases hrun
          rfl
set_option linter.unusedVariables false in
theorem loopBody_lookup_exprStmt (budget : Nat)
    (e : HIR.Expr) (rest : List HIR.Stmt)
    (hstr : IsStraight e) (hlt : SLWeight e < budget)
    (hrs : LoopStmts budget rest)
    (ih : ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered),
      loop = some info →
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop rest =
        some L →
      ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv rest acc = (out, henv') →
      id ∉ assignedIds rest →
      lookupHEnv henv' id = lookupHEnv henv id)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.exprStmt e :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.exprStmt e :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.exprStmt e :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont false ρ s1 nextB v0 true loop
              rest with
          | none => rw [hr] at h; simp at h
          | some Lr =>
              rw [hr] at h
              simp only [assignedIds] at hnid
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
                      exact ih bId cont ρ s1 nextB v0 true loop info Lr hlo
                        hr _ _ _ _ _ _ hrun hnid
set_option linter.unusedVariables false in
theorem loopBody_lookup_varDecl (budget : Nat)
    (id' : HIR.Id) (τ : Typ) (init : HIR.Expr) (rest : List HIR.Stmt)
    (hstr : IsStraight init) (hlt : SLWeight init < budget)
    (hloop : LoopStmts budget rest) (hfree : VarFree init)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.varDecl id' τ init :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.varDecl id' τ init :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.varDecl id' τ init :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
      subst hlo
      simp only [lowerStmtsCFG] at h
      simp at h
set_option linter.unusedVariables false in
theorem loopBody_lookup_assign (budget : Nat)
    (id' : HIR.Id) (e : HIR.Expr) (rest : List HIR.Stmt)
    (hstr : IsStraight e) (hlt : SLWeight e < budget)
    (hrs : LoopStmts budget rest) (hfree : VarFree e)
    (ih : ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered),
      loop = some info →
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop rest =
        some L →
      ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv rest acc = (out, henv') →
      id ∉ assignedIds rest →
      lookupHEnv henv' id = lookupHEnv henv id)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.assign id' e :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.assign id' e :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.assign id' e :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont false (updAssoc ρ id' v0) s1
              nextB lastVal true loop rest with
          | none => rw [hr] at h; simp at h
          | some Lr =>
              rw [hr] at h
              simp only [assignedIds, List.mem_cons, not_or] at hnid
              obtain ⟨hne, hnid'⟩ := hnid
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
                      have htail := ih bId cont (updAssoc ρ id' v0) s1 nextB
                        lastVal true loop info Lr hlo hr _ _ _ _ _ _ hrun hnid'
                      rw [htail]
                      exact lookupHEnv_updateHEnv_ne (fun hh => hne hh.symm)
set_option linter.unusedVariables false in
theorem loopBody_lookup_nop (budget : Nat)
    (rest : List HIR.Stmt) (hrs : LoopStmts budget rest)
    (ih : ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered),
      loop = some info →
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop rest =
        some L →
      ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv rest acc = (out, henv') →
      id ∉ assignedIds rest →
      lookupHEnv henv' id = lookupHEnv henv id)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.nop :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.nop :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.nop :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
      simp only [lowerStmtsCFG] at h
      simp only [assignedIds] at hnid
      cases hr : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal
          loop rest with
      | none => rw [hr] at h; simp at h
      | some Lr =>
          rw [hr] at h
          cases fuel with
          | zero =>
              rw [runHIRStmts_zero] at hrun
              cases hrun
              rfl
          | succ fh =>
              simp only [runHIRStmts] at hrun
              exact ih bId cont ρ supply nextB lastVal hasVal loop info Lr
                hlo hr _ _ _ _ _ _ hrun hnid
set_option linter.unusedVariables false in
theorem loopBody_lookup_ifStmt (budget : Nat)
    (c : HIR.Expr) (th el rest : List HIR.Stmt)
    (hstr : IsStraight c) (hlt : SLWeight c < budget)
    (hath : ArmStmts budget th) (hael : ArmStmts budget el)
    (hrs : LoopStmts budget rest)
    (hno1 : ArmNoBreak th) (hno2 : ArmNoBreak el)
    (ih : ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered),
      loop = some info →
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop rest =
        some L →
      ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv rest acc = (out, henv') →
      id ∉ assignedIds rest →
      lookupHEnv henv' id = lookupHEnv henv id)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.ifStmt c th el :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.ifStmt c th el :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.ifStmt c th el :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
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
                      simp only [assignedIds, List.mem_append,
                        not_or] at hnid
                      obtain ⟨⟨hnt, hnel⟩, hnrest⟩ := hnid
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
                                        have h1 := runHIRStmts_arm_lookup
                                          budget hath _ _ _ _ _ id har
                                        have h2 := ih (nextB + 2) cont ρ
                                          (le.supply + 1) le.next le.supply
                                          true loop info lr hlo hr _ _ _ _ _ _
                                          hrun hnrest
                                        rw [h2, h1]
                                    | broke =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hath _ _ _ _ _ _ har
                                    | continued =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hath _ _ _ _ _ _ har
                                    | returned e =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hath _ _ _ _ _ _ har
                                    | stuck =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hath _ _ _ _ _ _ har
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
                                        have h1 := runHIRStmts_arm_lookup
                                          budget hael _ _ _ _ _ id har
                                        have h2 := ih (nextB + 2) cont ρ
                                          (le.supply + 1) le.next le.supply
                                          true loop info lr hlo hr _ _ _ _ _ _
                                          hrun hnrest
                                        rw [h2, h1]
                                    | broke =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hael _ _ _ _ _ _ har
                                    | continued =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hael _ _ _ _ _ _ har
                                    | returned e =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hael _ _ _ _ _ _ har
                                    | stuck =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hael _ _ _ _ _ _ har
                              · cases hrun
                                rfl
set_option linter.unusedVariables false in
theorem loopBody_lookup_ifStmtBreak (budget : Nat)
    (c : HIR.Expr) (th el rest : List HIR.Stmt)
    (hstr : IsStraight c) (hlt : SLWeight c < budget)
    (hath : ArmStmts budget th) (hael : ArmStmts budget el)
    (hrs : LoopStmts budget rest) (harm : ArmStmts budget rest)
    (ih : ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered),
      loop = some info →
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop rest =
        some L →
      ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv rest acc = (out, henv') →
      id ∉ assignedIds rest →
      lookupHEnv henv' id = lookupHEnv henv id)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.ifStmt c th el :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.ifStmt c th el :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.ifStmt c th el :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
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
                      simp only [assignedIds, List.mem_append,
                        not_or] at hnid
                      obtain ⟨⟨hnt, hnel⟩, hnrest⟩ := hnid
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
                                        have h1 := runHIRStmts_arm_lookup
                                          budget hath _ _ _ _ _ id har
                                        have h2 := ih (nextB + 2) cont ρ
                                          (le.supply + 1) le.next le.supply
                                          true loop info lr hlo hr _ _ _ _ _ _
                                          hrun hnrest
                                        rw [h2, h1]
                                    | broke =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hath _ _ _ _ _ _ har
                                    | continued =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hath _ _ _ _ _ _ har
                                    | returned e =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hath _ _ _ _ _ _ har
                                    | stuck =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hath _ _ _ _ _ _ har
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
                                        have h1 := runHIRStmts_arm_lookup
                                          budget hael _ _ _ _ _ id har
                                        have h2 := ih (nextB + 2) cont ρ
                                          (le.supply + 1) le.next le.supply
                                          true loop info lr hlo hr _ _ _ _ _ _
                                          hrun hnrest
                                        rw [h2, h1]
                                    | broke =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hael _ _ _ _ _ _ har
                                    | continued =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hael _ _ _ _ _ _ har
                                    | returned e =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hael _ _ _ _ _ _ har
                                    | stuck =>
                                        simp only [] at hrun
                                        cases hrun
                                        exact runHIRStmts_arm_lookup budget
                                          hael _ _ _ _ _ _ har
                              · cases hrun
                                rfl
set_option linter.unusedVariables false in
theorem loopBody_lookup_returnStmt (budget : Nat)
    (e : HIR.Expr) (rest : List HIR.Stmt)
    (hstr : IsStraight e) (hlt : SLWeight e < budget)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.returnStmt e :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.returnStmt e :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.returnStmt e :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
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
              | some w =>
                  rw [hev] at hrun
                  simp only [] at hrun
                  cases hrun
                  rfl
set_option linter.unusedVariables false in
theorem loopBody_lookup_breakStmt (budget : Nat)
    (rest : List HIR.Stmt) (hrs : LoopStmts budget rest)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.break :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.break :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.break :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hrun
          rfl
set_option linter.unusedVariables false in
theorem loopBody_lookup_continueStmt (budget : Nat)
    (rest : List HIR.Stmt) (hrs : LoopStmts budget rest)
    (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
    (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered)
    (hlo : loop = some info)
    (h : lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop
      (.continue :: rest) = some L)
    (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id)
    (hrun : runHIRStmts fuel henv (.continue :: rest) acc = (out, henv'))
    (hnid : id ∉ assignedIds (.continue :: rest)) :
    lookupHEnv henv' id = lookupHEnv henv id := by
      cases fuel with
      | zero =>
          rw [runHIRStmts_zero] at hrun
          cases hrun
          rfl
      | succ fh =>
          simp only [runHIRStmts] at hrun
          cases hrun
          rfl

end LoopBodyLookupAux

/-- HIR preservation (spine L2): a loop-body run preserves every unassigned
id's lookup. Straight-line steps only evaluate; arms are lookup-preserving
(`runHIRStmts_arm_lookup`); `assign` touches only its own id
(`lookupHEnv_updateHEnv_ne`); `varDecl` under `loop = some` contradicts the
lowering hypothesis. The re-entry argument cites this for non-carried ids. -/
theorem runHIRStmts_loopBody_lookup (budget : Nat) (ss : List HIR.Stmt) :
    ∀ (_hss : LoopStmts budget ss) (bId : MIR.BlockId) (cont : Option MIR.BlockId)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (loop : Option LoopInfo) (info : LoopInfo) (L : Lowered),
      loop = some info →
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal loop ss =
        some L →
      ∀ (fuel : Nat) (henv henv' : HEnv) (acc out : HFlow) (id : HIR.Id),
      runHIRStmts fuel henv ss acc = (out, henv') →
      id ∉ assignedIds ss →
      lookupHEnv henv' id = lookupHEnv henv id := by
  induction ss with
  | nil =>
      intro hss bId cont ρ supply nextB lastVal hasVal loop info L hlo h fuel
        henv henv' acc out id hrun hnid
      cases hss with
      | nil =>
          exact loopBody_lookup_nil budget bId cont ρ supply nextB lastVal
            hasVal loop info L hlo h fuel henv henv' acc out id hrun hnid
  | cons hd rest ih =>
      intro hss bId cont ρ supply nextB lastVal hasVal loop info L hlo h fuel
        henv henv' acc out id hrun hnid
      cases hss with
      | exprStmt e rest hstr hlt hrs =>
          exact loopBody_lookup_exprStmt budget e rest hstr hlt hrs (ih hrs)
            bId cont ρ supply nextB lastVal hasVal loop info L hlo h fuel henv
            henv' acc out id hrun hnid
      | varDecl id' τ init rest hstr hlt hloop hfree =>
          exact loopBody_lookup_varDecl budget id' τ init rest hstr hlt hloop
            hfree bId cont ρ supply nextB lastVal hasVal loop info L hlo h
            fuel henv henv' acc out id hrun hnid
      | assign id' e rest hstr hlt hrs hfree =>
          exact loopBody_lookup_assign budget id' e rest hstr hlt hrs hfree
            (ih hrs) bId cont ρ supply nextB lastVal hasVal loop info L hlo h
            fuel henv henv' acc out id hrun hnid
      | nop rest hrs =>
          exact loopBody_lookup_nop budget rest hrs (ih hrs) bId cont ρ
            supply nextB lastVal hasVal loop info L hlo h fuel henv henv' acc
            out id hrun hnid
      | ifStmt c th el rest hstr hlt hath hael hrs hno1 hno2 =>
          exact loopBody_lookup_ifStmt budget c th el rest hstr hlt hath hael
            hrs hno1 hno2 (ih hrs) bId cont ρ supply nextB lastVal hasVal loop
            info L hlo h fuel henv henv' acc out id hrun hnid
      | ifStmtBreak c th el rest hstr hlt hath hael hrs harm =>
          exact loopBody_lookup_ifStmtBreak budget c th el rest hstr hlt hath
            hael hrs harm (ih hrs) bId cont ρ supply nextB lastVal hasVal loop
            info L hlo h fuel henv henv' acc out id hrun hnid
      | returnStmt e rest hstr hlt =>
          exact loopBody_lookup_returnStmt budget e rest hstr hlt bId cont ρ
            supply nextB lastVal hasVal loop info L hlo h fuel henv henv' acc
            out id hrun hnid
      | breakStmt rest hrs =>
          exact loopBody_lookup_breakStmt budget rest hrs bId cont ρ supply
            nextB lastVal hasVal loop info L hlo h fuel henv henv' acc out id
            hrun hnid
      | continueStmt rest hrs =>
          exact loopBody_lookup_continueStmt budget rest hrs bId cont ρ supply
            nextB lastVal hasVal loop info L hlo h fuel henv henv' acc out id
            hrun hnid

/-- Loop-body classification (spine L1): an assigned id looked up in the
body-entry env resolves through its carried pair. If the id is missing from
the pre-loop env, `mkCarried_lookup` leaves only the carried case; if
present, it is in the filter input (`dedupIds_mem` plus the filterMap
witness), so `mkCarried_mem_lookup` applies and the two lookups agree
because `rhoLookup` is a function. -/
theorem loopBody_carried_of_assigned {ρ : List (HIR.Id × ValId)} {s : Nat}
    {body : List HIR.Stmt} {carried : List (HIR.Id × ValId)} {sA : Nat}
    {ρb : List (HIR.Id × ValId)}
    (hmk : mkCarried ρ s ((dedupIds (assignedIds body)).filterMap
      (fun j => (rhoLookup ρ j).map (fun _ => j))) = some (carried, sA, ρb))
    {id : HIR.Id} {u : ValId}
    (hlook : rhoLookup ρb id = some u)
    (hmem : id ∈ assignedIds body) :
    (id, u) ∈ carried := by
  cases hρ : rhoLookup ρ id with
  | none =>
      rcases mkCarried_lookup hmk hlook with ⟨i, rr, hmemc, rfl, rfl⟩ | hbase
      · exact hmemc
      · rw [hbase] at hρ; simp at hρ
  | some u₀ =>
      have hmemf : id ∈ (dedupIds (assignedIds body)).filterMap
          (fun j => (rhoLookup ρ j).map (fun _ => j)) := by
        apply List.mem_filterMap.mpr
        exact ⟨id, dedupIds_mem hmem, by rw [hρ]; rfl⟩
      obtain ⟨r, hrlook, hrmem⟩ := mkCarried_mem_lookup hmemf hmk
      have heq : r = u := Option.some.inj (hrlook.symm.trans hlook)
      rw [heq] at hrmem
      exact hrmem

/-- A non-boolean condition value stalls the loop. -/
theorem runHIRWhile_succ_cond_other {fh : Nat} {henv : HEnv} {c : HIR.Expr}
    {body : List HIR.Stmt} {v : HIR.Expr}
    (hcond : evalHIR 256 henv c = some v)
    (hne : ∀ b : Bool, v ≠ .lit (.bool b)) :
    runHIRWhile (fh + 1) henv c body = (.stuck, henv) := by
  simp only [runHIRWhile, hcond]
  split
  · rename_i heq
    rw [Option.some.injEq] at heq
    exact absurd heq (hne true)
  · rename_i heq
    rw [Option.some.injEq] at heq
    exact absurd heq (hne false)
  · rfl

/- Assigned bound ids are carried: `assignedIds` through `dedupIds`/`filterMap`
survives into `mkCarried`'s input list, so `mkCarried_mem_lookup` gives a
carried pair. Used to classify body-exit lookups (assigned ⇒ carried). -/
theorem loopBody_assigned_carried {ρ : List (HIR.Id × ValId)} {supply : Nat}
    {body : List HIR.Stmt} {carried : List (HIR.Id × ValId)} {sA : Nat}
    {ρb : List (HIR.Id × ValId)} {id : HIR.Id} {u : ValId}
    (hmk : mkCarried ρ supply
        ((dedupIds (assignedIds body)).filterMap
          (fun id => (rhoLookup ρ id).map (fun _ => id))) =
        some (carried, sA, ρb))
    (hass : id ∈ assignedIds body) (hlook : rhoLookup ρ id = some u) :
    ∃ r, (id, r) ∈ carried := by
  have hmemDedup : id ∈ dedupIds (assignedIds body) := dedupIds_mem hass
  have hmemFilt : id ∈ (dedupIds (assignedIds body)).filterMap
      (fun id => (rhoLookup ρ id).map (fun _ => id)) := by
    rw [List.mem_filterMap]
    exact ⟨id, hmemDedup, by simp [hlook]⟩
  obtain ⟨r, _, hmemC⟩ := mkCarried_mem_lookup hmemFilt hmk
  exact ⟨r, hmemC⟩

 /- Exit env binds every entry-bound id: `assign` rebinds through
`updAssoc` (still `some`), other constructors keep `ρ` or recurse with the
same entry. Used to feed `RelEnv` arrivals for carried ids. -/
theorem lowerStmtsCFG_loopBody_mem_preserv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (contB : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (loop : Option LoopInfo)
      (info : LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered) (id : HIR.Id) (u : ValId),
      loop = some info →
      lowerStmtsCFG bId (some contB) false ρ supply nextB lastVal true loop ss =
        some L →
      LoopStmts budget ss →
      rhoLookup ρ id = some u →
      ∃ u', rhoLookup L.ρ id = some u' := by
  intro bId contB ρ supply nextB lastVal loop info ss L id u hloop h hss hentry
  induction ss generalizing bId contB ρ supply nextB lastVal loop info L id u with
  | nil =>
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          obtain rfl := Option.some.inj h
          exact ⟨u, hentry⟩
  | cons s rest ih =>
      cases hss with
      | exprStmt e rest hstr _ hrs =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId (some contB) false ρ s1 nextB v0 true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  show ∃ u', rhoLookup q.ρ id = some u'
                  exact ih _ _ _ _ _ _ _ _ _ _ _ hloop hr hrs hentry
      | varDecl vd τ init rest hstr _ hrs _ =>
          cases hlo : loop with
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              simp at h
      | assign aid e rest hstr _ hrs _ =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId (some contB) false (updAssoc ρ aid v) s1 nextB lastVal true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  show ∃ u', rhoLookup q.ρ id = some u'
                  by_cases heq : id = aid
                  · have hentry' : rhoLookup ρ aid = some u := by
                      rw [← heq]
                      exact hentry
                    have hupd : rhoLookup (updAssoc ρ aid v) id = some v := by
                      rw [heq, rhoLookup_updAssoc_id, hentry']
                      rfl
                    exact ih _ _ _ _ _ _ _ _ _ _ _ hloop hr hrs hupd
                  · have hne : rhoLookup (updAssoc ρ aid v) id = some u := by
                      rw [rhoLookup_updAssoc_ne (fun hh => heq hh.symm) ρ]
                      exact hentry
                    exact ih _ _ _ _ _ _ _ _ _ _ _ hloop hr hrs hne
      | nop rest hrs =>
          simp only [lowerStmtsCFG] at h
          cases hr : lowerStmtsCFG bId (some contB) false ρ supply nextB lastVal true loop rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              obtain rfl := Option.some.inj h
              exact ih _ _ _ _ _ _ _ _ _ _ _ hloop hr hrs hentry
      | ifStmt c th el rest hstr _ hath hael hrs _ _ =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ lt.supply lt.next lastVal false loop el with
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
                      cases hr : lowerStmtsCFG (nextB + 2) (some contB) false ρ (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          show ∃ u', rhoLookup lr.ρ id = some u'
                          exact ih _ _ _ _ _ _ _ _ _ _ _ hloop hr hrs hentry
      | ifStmtBreak c th el rest hstr _ hath hael hrs hrest =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ lt.supply lt.next lastVal false loop el with
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
                      cases hr : lowerStmtsCFG (nextB + 2) (some contB) false ρ (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          show ∃ u', rhoLookup lr.ρ id = some u'
                          exact ih _ _ _ _ _ _ _ _ _ _ _ hloop hr hrs hentry
      | returnStmt e rest hstr _ =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              exact ⟨u, hentry⟩
      | breakStmt rest _ =>
          cases hlo : loop with
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hc : carryCopies ρ inf.carried with
              | none => rw [hc] at h; simp at h
              | some copies =>
                  rw [hc] at h
                  obtain rfl := Option.some.inj h
                  exact ⟨u, hentry⟩
      | continueStmt rest _ =>
          cases hlo : loop with
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hc : carryCopies ρ inf.carried with
              | none => rw [hc] at h; simp at h
              | some copies =>
                  rw [hc] at h
                  obtain rfl := Option.some.inj h
                  exact ⟨u, hentry⟩

 /- Carried pairs come from the input id list. -/
theorem mkCarried_mem_ids (ids : List HIR.Id) :
    ∀ (ρ : List (HIR.Id × ValId)) (s : Nat) (cs : List (HIR.Id × ValId))
      (s' : Nat) (ρ' : List (HIR.Id × ValId)) (id : HIR.Id) (r : ValId),
      mkCarried ρ s ids = some (cs, s', ρ') →
      (id, r) ∈ cs → id ∈ ids := by
  intro ρ s cs s' ρ' id r h hmem
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp at hmem
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
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              simp only [List.mem_cons] at hmem ⊢
              rcases hmem with hmem | hmem
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
                exact Or.inl rfl
              · exact Or.inr (ih _ _ _ _ _ hrec hmem)

/-- Assign-chains from a base env: every entry is the base with some updates,
each update at a register at or above `lo`. Body exits lower to such chains
over `ρb` (`assign` steps extend, everything else preserves). -/
inductive IsChain (base : List (HIR.Id × ValId)) (lo : Nat) :
    List (HIR.Id × ValId) → Prop where
  | base : IsChain base lo base
  | step (E : List (HIR.Id × ValId)) (aid : HIR.Id) (v : ValId) :
      IsChain base lo E → lo ≤ v → IsChain base lo (updAssoc E aid v)

/-- Peeling an assign-chain below `lo` recovers the base lookup: updates all
write at or above `lo`, so a small-reg hit must come from the base. -/
theorem isChain_peel (base : List (HIR.Id × ValId)) (lo : Nat)
    (E : List (HIR.Id × ValId)) (hc : IsChain base lo E) (id' : HIR.Id)
    (r : ValId) (hlook : rhoLookup E id' = some r) (hlt : r < lo) :
    rhoLookup base id' = some r := by
  induction hc with
  | base => exact hlook
  | step E aid v _ hv ih =>
      by_cases heq : id' = aid
      · rw [heq] at hlook ⊢
        rw [rhoLookup_updAssoc_id] at hlook
        cases hρ : rhoLookup E aid with
        | none => rw [hρ] at hlook; simp at hlook
        | some u0 =>
            rw [hρ] at hlook
            simp only [Option.map_some] at hlook
            have hrv : v = r := Option.some.inj hlook
            have hle : lo ≤ r := by rw [←hrv]; exact hv
            exact absurd (Nat.lt_of_le_of_lt hle hlt) (Nat.lt_irrefl _)
      · rw [rhoLookup_updAssoc_ne (fun hh => heq hh.symm)] at hlook
        exact ih hlook

/-- Body exits are exclusive over the carried set: a carried register resolves
only its own id. The exit env is an assign-chain over `ρb`; peeling below the
body-entry supply recovers the `ρb` lookup, and `F2` plus register injectivity
close it. -/
theorem lowerStmtsCFG_loopBody_carriedExcl (budget : Nat) :
    ∀ (bId : MIR.BlockId) (contB : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (loop : Option LoopInfo)
      (info : LoopInfo)
      (base : List (HIR.Id × ValId)) (lo spre : Nat)
      (carried : List (HIR.Id × ValId)) (sA : Nat) (ρb : List (HIR.Id × ValId))
      (preρ : List (HIR.Id × ValId)) (INPUT : List HIR.Id)
      (ss : List HIR.Stmt) (L : Lowered)
      (_hc : IsChain base lo ρ)
      (id : HIR.Id) (r : ValId) (id' : HIR.Id),
      loop = some info →
      lowerStmtsCFG bId (some contB) false ρ supply nextB lastVal true loop ss =
        some L →
      LoopStmts budget ss →
      lo ≤ supply →
      base = ρb →
      (∀ q ∈ carried, q.2 < lo) →
      mkCarried preρ spre INPUT = some (carried, sA, ρb) →
      FreshAbove preρ spre →
      (id, r) ∈ carried →
      rhoLookup L.ρ id' = some r →
      id' = id := by
  intro bId contB ρ supply nextB lastVal loop info base lo spre carried sA ρb
    preρ INPUT ss L hc id r id' hloop h hss hlo_le hbase hloCar hmk hfresh hmem hlook
  induction ss generalizing bId contB ρ supply nextB lastVal loop info L hc id' with
  | nil =>
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          obtain rfl := Option.some.inj h
          have hbase' : rhoLookup base id' = some r :=
            isChain_peel base lo ρ hc id' r hlook (hloCar (id, r) hmem)
          rw [hbase] at hbase'
          have hmem' : (id', r) ∈ carried :=
            mkCarried_lookup_high hfresh hmk hbase'
              (mkCarried_mem_lo hmk hmem)
          exact (mkCarried_reg_inj hmk hmem hmem').symm
  | cons s rest ih =>
      cases hss with
      | exprStmt e rest hstr _ hrs =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId (some contB) false ρ s1 nextB v0 true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  have hlookQ : rhoLookup q.ρ id' = some r := hlook
                  have hlo_le' : lo ≤ s1 :=
                    Nat.le_trans hlo_le (lower_mono.1 _ _ _ _ _ _ he)
                  exact ih _ _ _ _ _ _ _ _ _ hc _ hloop hr hrs hlo_le' hlookQ
      | varDecl vd τ init rest hstr _ hrs _ =>
          cases hlo : loop with
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              simp at h
      | assign aid e rest hstr _ hrs hfree =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId (some contB) false (updAssoc ρ aid v) s1 nextB lastVal true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  have hlookQ : rhoLookup q.ρ id' = some r := hlook
                  have hv : lo ≤ v :=
                    Nat.le_trans hlo_le
                      (lowerExpr_result_ge ρ supply e v ie s1 hstr hfree he)
                  have hc' : IsChain base lo (updAssoc ρ aid v) :=
                    IsChain.step ρ aid v hc hv
                  have hlo_le' : lo ≤ s1 :=
                    Nat.le_trans hlo_le (lower_mono.1 _ _ _ _ _ _ he)
                  exact ih _ _ _ _ _ _ _ _ _ hc' _ hloop hr hrs hlo_le' hlookQ
      | nop rest hrs =>
          simp only [lowerStmtsCFG] at h
          cases hr : lowerStmtsCFG bId (some contB) false ρ supply nextB lastVal true loop rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              obtain rfl := Option.some.inj h
              have hlookQ : rhoLookup q.ρ id' = some r := hlook
              exact ih _ _ _ _ _ _ _ _ _ hc _ hloop hr hrs hlo_le hlookQ
      | ifStmt c th el rest hstr _ hath hael hrs _ _ =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ lt.supply lt.next lastVal false loop el with
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
                      cases hr : lowerStmtsCFG (nextB + 2) (some contB) false ρ (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          have hlookQ : rhoLookup lr.ρ id' = some r := hlook
                          have hle1 : s1 ≤ lt.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath).2.1
                          have hle2 : lt.supply ≤ le.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he hael).2.1
                          have hlo_le' : lo ≤ le.supply + 1 := by
                            have h1 : lo ≤ supply := hlo_le
                            have h2 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                            omega
                          exact ih _ _ _ _ _ _ _ _ _ hc _ hloop hr hrs hlo_le' hlookQ
      | ifStmtBreak c th el rest hstr _ hath hael hrs hrest =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ lt.supply lt.next lastVal false loop el with
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
                      cases hr : lowerStmtsCFG (nextB + 2) (some contB) false ρ (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          have hlookQ : rhoLookup lr.ρ id' = some r := hlook
                          have hle1 : s1 ≤ lt.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ ht hath).2.1
                          have hle2 : lt.supply ≤ le.supply :=
                            (lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ _ he hael).2.1
                          have hlo_le' : lo ≤ le.supply + 1 := by
                            have h1 : lo ≤ supply := hlo_le
                            have h2 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                            omega
                          exact ih _ _ _ _ _ _ _ _ _ hc _ hloop hr hrs hlo_le' hlookQ
      | returnStmt e rest hstr _ =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              have hbase' : rhoLookup base id' = some r :=
                isChain_peel base lo ρ hc id' r hlook (hloCar (id, r) hmem)
              rw [hbase] at hbase'
              have hmem' : (id', r) ∈ carried :=
                mkCarried_lookup_high hfresh hmk hbase'
                  (mkCarried_mem_lo hmk hmem)
              exact (mkCarried_reg_inj hmk hmem hmem').symm
      | breakStmt rest _ =>
          cases hlo : loop with
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hcry : carryCopies ρ inf.carried with
              | none => rw [hcry] at h; simp at h
              | some copies =>
                  rw [hcry] at h
                  obtain rfl := Option.some.inj h
                  have hbase' : rhoLookup base id' = some r :=
                    isChain_peel base lo ρ hc id' r hlook (hloCar (id, r) hmem)
                  rw [hbase] at hbase'
                  have hmem' : (id', r) ∈ carried :=
                    mkCarried_lookup_high hfresh hmk hbase'
                      (mkCarried_mem_lo hmk hmem)
                  exact (mkCarried_reg_inj hmk hmem hmem').symm
      | continueStmt rest _ =>
          cases hlo : loop with
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hcry : carryCopies ρ inf.carried with
              | none => rw [hcry] at h; simp at h
              | some copies =>
                  rw [hcry] at h
                  obtain rfl := Option.some.inj h
                  have hbase' : rhoLookup base id' = some r :=
                    isChain_peel base lo ρ hc id' r hlook (hloCar (id, r) hmem)
                  rw [hbase] at hbase'
                  have hmem' : (id', r) ∈ carried :=
                    mkCarried_lookup_high hfresh hmk hbase'
                      (mkCarried_mem_lo hmk hmem)
                  exact (mkCarried_reg_inj hmk hmem hmem').symm

/- Body preserves lookups for unassigned ids: `assign` only updates its own
id (via `updAssoc`), `exprStmt`/`nop`/`if`/`break`/`continue`/`return` leave
`ρ` unchanged (arms preserve, `varDecl` refused under `loop = some`). By
induction on `LoopStmts`, generalizing the envs. -/
theorem lowerStmtsCFG_loopBody_rho_preserv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (contB : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (loop : Option LoopInfo)
      (info : LoopInfo)
      (ss : List HIR.Stmt) (L : Lowered) (id : HIR.Id),
      loop = some info →
      lowerStmtsCFG bId (some contB) false ρ supply nextB lastVal true loop ss =
        some L →
      LoopStmts budget ss →
      id ∉ assignedIds ss →
      rhoLookup L.ρ id = rhoLookup ρ id := by
  intro bId contB ρ supply nextB lastVal loop info ss L id hloop h hss hid
  induction ss generalizing bId contB ρ supply nextB lastVal loop info L id with
  | nil =>
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          obtain rfl := Option.some.inj h
          rfl
  | cons s rest ih =>
      cases hss with
      | exprStmt e rest hstr _ hrs =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId (some contB) false ρ s1 nextB v0 true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  show rhoLookup q.ρ id = rhoLookup ρ id
                  have hidR : id ∉ assignedIds rest := by
                    simp only [assignedIds] at hid
                    exact hid
                  exact ih _ _ _ _ _ _ _ _ _ _ hloop hr hrs hidR
      | varDecl vd τ init rest hstr _ hrs _ =>
          cases hlo : loop with
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              simp at h
      | assign aid e rest hstr _ hrs _ =>
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId (some contB) false (updAssoc ρ aid v) s1 nextB lastVal true loop rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  show rhoLookup q.ρ id = rhoLookup ρ id
                  have hidR : id ∉ assignedIds rest := by
                    simp only [assignedIds] at hid
                    exact fun hm => hid (List.mem_cons_of_mem _ hm)
                  have hne : id ≠ aid := by
                    intro heq
                    apply hid
                    simp only [assignedIds]
                    exact List.mem_cons.mpr (Or.inl heq)
                  have hmid := ih _ _ _ _ _ _ _ _ _ _ hloop hr hrs hidR
                  rw [hmid]
                  exact rhoLookup_updAssoc_ne (fun hh => hne hh.symm) ρ
      | nop rest hrs =>
          simp only [lowerStmtsCFG] at h
          cases hr : lowerStmtsCFG bId (some contB) false ρ supply nextB lastVal true loop rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              obtain rfl := Option.some.inj h
              show rhoLookup q.ρ id = rhoLookup ρ id
              have hidR : id ∉ assignedIds rest := by
                simp only [assignedIds] at hid
                exact hid
              exact ih _ _ _ _ _ _ _ _ _ _ hloop hr hrs hidR
      | ifStmt c th el rest hstr _ hath hael hrs _ _ =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ lt.supply lt.next lastVal false loop el with
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
                      cases hr : lowerStmtsCFG (nextB + 2) (some contB) false ρ (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          show rhoLookup lr.ρ id = rhoLookup ρ id
                          have hidR : id ∉ assignedIds rest := by
                            intro hm
                            apply hid
                            simp only [assignedIds]
                            exact List.mem_append_right
                              (assignedIds th ++ assignedIds el) hm
                          exact ih _ _ _ _ _ _ _ _ _ _ hloop hr hrs hidR
      | ifStmtBreak c th el rest hstr _ hath hael hrs hrest =>
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3) lastVal false loop th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ lt.supply lt.next lastVal false loop el with
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
                      cases hr : lowerStmtsCFG (nextB + 2) (some contB) false ρ (le.supply + 1) le.next le.supply true loop rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          show rhoLookup lr.ρ id = rhoLookup ρ id
                          have hidR : id ∉ assignedIds rest := by
                            intro hm
                            apply hid
                            simp only [assignedIds]
                            exact List.mem_append_right
                              (assignedIds th ++ assignedIds el) hm
                          exact ih _ _ _ _ _ _ _ _ _ _ hloop hr hrs hidR
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
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hc : carryCopies ρ inf.carried with
              | none => rw [hc] at h; simp at h
              | some copies =>
                  rw [hc] at h
                  obtain rfl := Option.some.inj h
                  rfl
      | continueStmt rest _ =>
          cases hlo : loop with
          | none => rw [hloop] at hlo; simp at hlo
          | some inf =>
              simp only [lowerStmtsCFG, hlo] at h
              cases hc : carryCopies ρ inf.carried with
              | none => rw [hc] at h; simp at h
              | some copies =>
                  rw [hc] at h
                  obtain rfl := Option.some.inj h
                  rfl

end Morph.HIRToMIRCorrect
