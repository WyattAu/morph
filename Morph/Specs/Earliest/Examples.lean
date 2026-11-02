/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.Earliest.Lemmas

/-!
# Earliest Frontier Kernels — examples (E-03, E-06, E-10, E-21–E-27)

Status: first cycle complete (loop 105).

Concrete instances of the ten cores. Every example is `decide`-checked; the
law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.Earliest

/-! ## E-03: a causal strategy and a biased one -/

/-- Read at 2, run at 3: causal. -/
example : strategyOk [⟨3, [2]⟩] = true := by decide

/-- Read at 5, run at 3: lookahead bias. -/
example : strategyOk [⟨3, [5]⟩] = false := by decide

/-- The causal strategy validates. -/
example : StrategyValid [⟨3, [2]⟩, ⟨4, [2, 3]⟩] :=
  strategyOk_iff.mp (by decide)

/-- The drift conversion with A = 2a: a = 3, b = 2, ∂b = 1. -/
example : stratOfIto 6 2 1 = 4 := by decide

example : itoOfStrat (stratOfIto 6 2 1) 2 1 = 6 :=
  ito_strat_roundtrip 6 2 1

/-! ## E-06: tropical arithmetic and WCET -/

example : tadd (some 3) (some 5) = some 5 := rfl

example : tadd tzero (some 5) = some 5 := tzero_add (some 5)

example : tmul (some 3) (some 5) = some 8 := rfl

example : tmul tzero (some 5) = tzero := tzero_mul (some 5)

example : blockWCET [4, 7, 2] = 13 := rfl

example : branchWCET [4, 7, 2] = 7 := rfl

example : blockWCET ([4, 7] ++ [2]) = blockWCET [4, 7] + blockWCET [2] :=
  blockWCET_append [4, 7] [2]

example : (7 : Nat) ≤ branchWCET [4, 7, 2] :=
  branchWCET_ge [4, 7, 2] 7 (by decide)

/-! ## E-10: shears and leapfrog -/

/-- A position shear moves q by c·p. -/
example : shearX 2 (3, 4) = (11, 4) := rfl

/-- Shears preserve the area form on a concrete pair. -/
example : area (shearX 2 (3, 4)) (shearX 2 (1, 1)) = area (3, 4) (1, 1) :=
  shearX_area 2 (3, 4) (1, 1)

/-- Leapfrog is symplectic on a concrete pair. -/
example : area (leapfrog 1 (-1) (3, 4)) (leapfrog 1 (-1) (1, 1)) =
    area (3, 4) (1, 1) :=
  leapfrog_area 1 (-1) (3, 4) (1, 1)

/-- Leapfrog reverses. -/
example : leapfrog (-1) 1 (leapfrog 1 (-1) (3, 4)) = (3, 4) :=
  leapfrog_rev 1 (-1) (3, 4)

/-- The origin is fixed. -/
example : leapfrog 2 (-3) (0, 0) = (0, 0) :=
  leapfrog_origin 2 (-3)

/-! ## E-21: a two-state protocol -/

/-- A tiny order protocol: new → ack → fill. -/
def orderSpec : List Trans := [⟨0, 1, 1⟩, ⟨1, 2, 2⟩]

example : outEdges orderSpec 0 = [(1, 1)] := by decide

example : outEdges orderSpec 1 = [(2, 2)] := by decide

example : (1, 1) ∈ outEdges orderSpec 0 := by decide

/-- The skeleton edge comes from a real transition. -/
example : ∃ tr ∈ orderSpec, tr.from_ = 0 ∧ tr.label = 1 ∧ tr.to = 1 :=
  synth_complete (show (1, 1) ∈ outEdges orderSpec 0 from by decide)

/-- The synthesized skeleton covers both states. -/
example : synth orderSpec [0, 1] =
    [(0, [(1, 1)]), (1, [(2, 2)])] := by decide

/-- Transition function of the order protocol. -/
def orderStep : Nat → Nat → List Nat
  | s, l => (outEdges orderSpec s).filterMap
      (fun e => if e.1 == l then some e.2 else none)

/-- Identity simulation on the order protocol. -/
example : simulates (· = ·) orderStep orderStep :=
  sim_refl orderStep

/-! ## E-22: a three-vertex cut -/

def triEdges : List Edge := [⟨0, 1, 5⟩, ⟨1, 2, 7⟩, ⟨0, 2, 3⟩]

/-- The cut {0} separates edges of weight 5 + 3. -/
example : cutWeight triEdges [0] = 8 := by decide

/-- The empty side cuts nothing. -/
example : cutWeight triEdges [] = 0 := cut_empty triEdges

/-- Moving 0 out of {0, 1} changes the cut by ext − int = 3 − 5. -/
example : (cutWeight triEdges (moveOut [0, 1] 0) : Int) =
    (cutWeight triEdges [0, 1] : Int) - (extW triEdges [0, 1] 0 : Int)
      + (intW triEdges [0, 1] 0 : Int) :=
  move_delta triEdges [0, 1] 0 (by decide)

/-- The moved vertex is gone. -/
example : 0 ∉ moveOut [0, 1] 0 := not_mem_moveOut_self [0, 1] 0

/-! ## E-23: cubic critical points -/

/-- S(x) = x³ − 3x has critical points at ±1. -/
example : isCritical [0, -3, 0, 1] 1 = true := by decide

example : isCritical [0, -3, 0, 1] (-1) = true := by decide

example : isCritical [0, -3, 0, 1] 2 = false := by decide

/-- An accepted critical point zeroes the derivative. -/
example : evalPoly (derivPoly [0, -3, 0, 1]) 1 = 0 :=
  isCritical_sound (show isCritical [0, -3, 0, 1] 1 = true from by decide)

/-- The power rule on the cubic. -/
example : evalPoly (derivPoly [0, -3, 0, 1]) 2 =
    dsum ([0, -3, 0, 1].drop 1) 1 2 :=
  derivPoly_eval [0, -3, 0, 1] 2

/-! ## E-24: picking the depth -/

def depths : List Region :=
  [⟨10, 100, 50⟩, ⟨12, 10, 50⟩, ⟨20, 1, 50⟩]

/-- Expected costs: 15000, 12500, 20050. -/
example : expectedCost ⟨12, 10, 50⟩ = 12500 := rfl

/-- The compiler picks the middle region. -/
example : best depths = some ⟨12, 10, 50⟩ := by decide

/-- The pick is optimal. -/
example : ∀ r ∈ depths, expectedCost ⟨12, 10, 50⟩ ≤ expectedCost r := by
  intro r hr
  have h := best_optimal depths ⟨12, 10, 50⟩ (by decide) r hr
  simpa using h

/-- Raising rollback never helps. -/
example : expectedCost ⟨12, 10, 50⟩ ≤ expectedCost ⟨12, 40, 50⟩ :=
  cost_mono rfl rfl (by decide)

/-! ## E-25: a three-node chain -/

def chainEdges : List (Nat × Nat) := [(0, 1), (1, 2)]

example : spread chainEdges 0 0 = [0] := rfl

example : spread chainEdges 1 0 = [0, 1] := by decide

example : spread chainEdges 2 0 = [0, 1, 1, 2] := by decide

/-- The cone grows monotonically. -/
example : 1 ∈ spread chainEdges 2 0 :=
  spread_mono_mem chainEdges 1 0 1 (by decide)

/-- Bounded growth is admitted at c = 2. -/
example : lyapZero chainEdges 0 2 = true := by decide

/-! ## E-26: add-then-multiply on both backends -/

def addMul : List KerOp := [.addConst 3, .mulConst 2]

/-- Direct: (5 + 3) × 2. -/
example : evalKer addMul 5 = 16 := rfl

/-- Compiled closed form: x ↦ 2x + 6. -/
example : compileAff addMul = (2, 6) := rfl

/-- The closed form agrees. -/
example : affApply (compileAff addMul) 5 = evalKer addMul 5 :=
  compileAff_correct addMul 5

/-- Both backends conform on a corpus. -/
example : conformant (evalKer addMul) (affApply (compileAff addMul))
    [0, 1, 5, 100] = true :=
  backends_conformant addMul [0, 1, 5, 100]

/-! ## E-27: a stable config and an unstable one -/

/-- Weight of x = (2, 1) against λ = (1, −1): 2 − 1 = 1 > 0. -/
example : mu [2, 1] [1, -1] = 1 := by decide

/-- Stable against the sample. -/
example : checkStable [2, 1] [[-1, 1], [0, -1]] = true := by decide

/-- No destabilizer in the sample. -/
example : ∀ lam ∈ [[-1, 1], [0, -1]], ¬ Unstable [2, 1] lam :=
  stable_of_check (show checkStable [2, 1] [[-1, 1], [0, -1]] = true from by decide)

/-- The witness for an unstable config. -/
example : findWitness [2, 1] [[-1, 1], [1, -1]] = some [1, -1] := by decide

/-- The witness is genuine. -/
example : [1, -1] ∈ [[-1, 1], [1, -1]] ∧ 0 < mu [2, 1] [1, -1] :=
  findWitness_sound [2, 1] [[-1, 1], [1, -1]] [1, -1]
    (show findWitness [2, 1] [[-1, 1], [1, -1]] = some [1, -1] from by decide)

/-- Sign symmetry of the weight. -/
example : mu [2, 1] ([1, -1].map fun b => -b) = -mu [2, 1] [1, -1] :=
  mu_neg [2, 1] [1, -1]

end Morph.Specs.Earliest
