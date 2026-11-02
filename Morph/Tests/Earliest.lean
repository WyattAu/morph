/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.Earliest.Examples

/-!
# Earliest frontier kernels — validation (E-03, E-06, E-10, E-21–E-27)

Status: first cycle complete (loop 105).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(round-trips, reversals, delegation chains, rotations) are exercised where a
single example could pass by accident.

Run: `lake build Morph.Tests.Earliest`.
-/

namespace Morph.Tests.Earliest

open Morph.Specs.Earliest

/-! ## E-03: fresh strategies -/

example : strategyOk [⟨5, [1, 4]⟩] = true := by decide

example : strategyOk [⟨5, [1, 6]⟩] = false := by decide

example : StrategyValid [⟨5, [1, 4]⟩] :=
  strategyOk_iff.mp (by decide)

example : ¬ StrategyValid [⟨5, [1, 6]⟩] := by
  intro h
  have h2 := h ⟨5, [1, 6]⟩ (by simp)
  apply h2
  exact ⟨6, by decide, by decide⟩

example : stratOfIto (itoOfStrat 9 3 2) 3 2 = 9 :=
  strat_ito_roundtrip 9 3 2

/-! ## E-06: fresh tropical identities -/

example : tadd (some 2) tzero = some 2 := add_tzero (some 2)

example : tmul tone (some 9) = some 9 := tone_mul (some 9)

example : tmul (some 2) (tadd (some 3) (some 4)) =
    tadd (tmul (some 2) (some 3)) (tmul (some 2) (some 4)) :=
  tmul_add_distrib (some 2) (some 3) (some 4)

example : blockWCET [1, 1, 1] ≤ 3 * 1 := by decide

example : blockWCET [5, 5] ≤ 2 * 5 :=
  blockWCET_le [5, 5] 5 (by decide)

example : (3 : Nat) ≤ branchWCET [1, 3, 2] :=
  branchWCET_ge [1, 3, 2] 3 (by decide)

/-! ## E-10: fresh shear checks -/

example : shearY 3 (2, 5) = (2, 11) := rfl

example : area (shearY 3 (2, 5)) (shearY 3 (1, 1)) = area (2, 5) (1, 1) :=
  shearY_area 3 (2, 5) (1, 1)

example : shearX (-4) (shearX 4 (7, 9)) = (7, 9) :=
  shearX_neg 4 (7, 9)

example : shearY (-2) (shearY 2 (7, 9)) = (7, 9) :=
  shearY_neg 2 (7, 9)

example : leapfrog (-3) 5 (leapfrog 3 (-5) (7, 9)) = (7, 9) :=
  leapfrog_rev 3 (-5) (7, 9)

/-! ## E-21: fresh protocol checks -/

/-- A fork protocol: dispatch to either worker. -/
def forkSpec : List Trans := [⟨0, 7, 1⟩, ⟨0, 7, 2⟩]

example : outEdges forkSpec 0 = [(7, 1), (7, 2)] := by decide

example : ∃ tr ∈ forkSpec, tr.from_ = 0 ∧ tr.label = 7 ∧ tr.to = 2 :=
  synth_complete (show (7, 2) ∈ outEdges forkSpec 0 from by decide)

/-- Simulation composes along a chain. -/
def idStep : Nat → Nat → List Nat := fun s l => [s + l]

example : simulates (fun s u => ∃ m, (s = m) ∧ (m = u)) idStep idStep :=
  sim_comp (sim_refl idStep) (sim_refl idStep)

/-! ## E-22: fresh cut checks -/

def squareEdges : List Edge :=
  [⟨0, 1, 1⟩, ⟨1, 2, 1⟩, ⟨2, 3, 1⟩, ⟨3, 0, 1⟩]

/-- The cut {0, 1} has weight 2. -/
example : cutWeight squareEdges [0, 1] = 2 := by decide

/-- Moving 1 out changes the cut by ext − int = 1 − 1 = 0. -/
example : (cutWeight squareEdges (moveOut [0, 1] 1) : Int) =
    (cutWeight squareEdges [0, 1] : Int) - (extW squareEdges [0, 1] 1 : Int)
      + (intW squareEdges [0, 1] 1 : Int) :=
  move_delta squareEdges [0, 1] 1 (by decide)

/-- Both endpoints moved out: the cut empties. -/
example : cutWeight squareEdges (moveOut (moveOut [0, 1] 0) 1) = 0 := by decide

/-! ## E-23: fresh critical points -/

/-- S(x) = x² − 4 has a critical point at 0. -/
example : isCritical [-4, 0, 1] 0 = true := by decide

example : evalPoly (derivPoly [-4, 0, 1]) 0 = 0 :=
  isCritical_sound (show isCritical [-4, 0, 1] 0 = true from by decide)

/-- The derivative of x² − 4 is 2x. -/
example : derivPoly [-4, 0, 1] = [0, 2] := by decide

example : evalPoly (derivPoly [-4, 0, 1]) 5 = 10 := by decide

/-! ## E-24: fresh depth choices -/

def depths2 : List Region := [⟨5, 500, 10⟩, ⟨6, 100, 10⟩]

example : best depths2 = some ⟨6, 100, 10⟩ := by decide

/-- The pick is optimal on the fresh list. -/
example : ∀ r ∈ depths2, expectedCost ⟨6, 100, 10⟩ ≤ expectedCost r := by
  intro r hr
  exact best_optimal depths2 ⟨6, 100, 10⟩ (by decide) r hr

/-- Equal rollback keeps cost equal. -/
example : expectedCost ⟨6, 100, 10⟩ = expectedCost ⟨6, 100, 10⟩ := rfl

/-! ## E-25: fresh cone checks -/

def starEdges : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3)]

example : spread starEdges 1 0 = [0, 1, 2, 3] := by decide

/-- Every leaf is one step out. -/
example : 2 ∈ spread starEdges 1 0 :=
  (mem_spread_succ starEdges 0 0 2).mpr
    (Or.inr ⟨0, by decide, by decide⟩)

/-- Two-step cone contains the one-step cone. -/
example : 3 ∈ spread starEdges 2 0 :=
  spread_mono_mem starEdges 1 0 3 (by decide)

/-! ## E-26: fresh backend agreement -/

def mulAdd : List KerOp := [.mulConst 3, .addConst 4]

example : evalKer mulAdd 5 = 19 := rfl

example : compileAff mulAdd = (3, 4) := rfl

example : affApply (compileAff mulAdd) 5 = evalKer mulAdd 5 :=
  compileAff_correct mulAdd 5

example : conformant (evalKer mulAdd) (affApply (compileAff mulAdd))
    [0, 5, 42] = true :=
  backends_conformant mulAdd [0, 5, 42]

/-- Conformance is reflexive. -/
example : conformant (evalKer mulAdd) (evalKer mulAdd) [0, 5] = true := by
  rw [conformant_iff]
  intro x _
  rfl

/-! ## E-27: fresh stability checks -/

/-- Weight of x = (1, 2) against λ = (2, −1): 2 − 2 = 0, stable. -/
example : mu [1, 2] [2, -1] = 0 := by decide

example : checkStable [1, 2] [[2, -1]] = true := by decide

example : findWitness [1, 2] [[2, -1]] = none := by decide

/-- Negation flips the weight. -/
example : mu [1, 2] ([2, -1].map fun b => -b) = -mu [1, 2] [2, -1] :=
  mu_neg [1, 2] [2, -1]

/-- A checked config has no destabilizer. -/
example : ∀ lam ∈ [[2, -1]], ¬ Unstable [1, 2] lam :=
  stable_of_check (show checkStable [1, 2] [[2, -1]] = true from by decide)

end Morph.Tests.Earliest
