/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchFGH.Examples

/-!
# Frontier Kernels — validation (E-48–E-57)

Status: first cycle complete (loop 108).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(involution, termination, localization, minimization) are exercised where a
single example could pass by accident.

Run: `lake build Morph.Tests.BatchFGH`.
-/

namespace Morph.Tests.BatchFGH

open Morph.Specs.BatchFGH

/-! ## E-48: involution on a fresh seed -/

/-- Mutating twice returns the fresh seed. -/
example : mut0 (mut0 ⟨4, 7⟩ 12 3) 12 4 = ⟨4, 7⟩ :=
  mut0_invol ⟨4, 7⟩ 12 3 (by decide)

/-- Mutation preserves positivity on the fresh seed. -/
example : seedPos (mut0 ⟨4, 7⟩ 12 3) :=
  mut0_pos ⟨4, 7⟩ 12 3 (by simp only [seedPos]; decide) (by decide)
    (by decide)

/-! ## E-49: cones on fresh placements -/

/-- A safe fresh reader sits outside the cone. -/
example : 2 * 5 + 1 < 20 := safeR_sound 2 1 20 5 (by decide)

/-- A fresh placement keeps every mutator out. -/
example : ∀ m ∈ [1, 4], 2 * 5 + m < 20 :=
  placeAll_sound 2 [1, 4] 20 5 (by decide)

/-! ## E-50: iterated repulsion on a fresh pair -/

/-- Two steps grow the gap by four. -/
example : gap (repelN 2 ⟨0, 5⟩) = gap ⟨0, 5⟩ + 2 * 2 :=
  repelN_gap 2 ⟨0, 5⟩ (by decide)

/-- Separation survives a step on the fresh pair. -/
example : (repel ⟨0, 5⟩).lo < (repel ⟨0, 5⟩).hi :=
  repel_ordered ⟨0, 5⟩ (by decide)

/-! ## E-51: shrinking a fresh expression -/

/-- One step drops the measure on a fresh redex. -/
example : msize (.const 7) < msize (.add (.const 0) (.const 7)) :=
  stepM_shrink (.add (.const 0) (.const 7)) (.const 7) (by decide)

/-- Fuel covering the measure normalizes the fresh expression. -/
example : isNormal (normM 4 (.add (.const 0) (.const 7))) = true :=
  normM_normal 4 (.add (.const 0) (.const 7)) (by decide)

/-! ## E-52: the other square and a non-cycle -/

/-- The chain-map square commutes on `c1`. -/
example : (bdyC .c1).map cmap = bdyD (cmap .c1) := cmap_chain .c1

/-- `c0` is not a cycle. -/
example : isCycleC .c0 = false := rfl

/-! ## E-53: a three-edge mesh with a dead direct link -/

def mesh3 : List (Nat × Nat) := [(0, 1), (1, 2), (0, 2)]

/-- The re-derived route keeps its endpoints. -/
example : ([0, 1, 2].head? = some 0 ∧ [0, 1, 2].getLast? = some 2) :=
  route2_ends mesh3 0 2 [(0, 2)] [0, 1, 2] (by decide)

/-- Every hop of the re-derived route is live. -/
example : hopsAlive mesh3 [(0, 2)] [0, 1, 2] = true :=
  route2_alive mesh3 0 2 [(0, 2)] [0, 1, 2] (by decide)

/-! ## E-54: constant weights localize -/

/-- Constant weights collapse to fixed plus twice the reps. -/
example : total (fun _ => (5 : Int)) ⟨[1], [(2, 3)]⟩ =
    isum [5] + 2 * isum [5] :=
  localize (fun _ => (5 : Int)) ⟨[1], [(2, 3)]⟩ (by decide)

/-- Four does not exceed nine. -/
example : countGt [1, 5, 3] 2 * 2 ≤ lsumN [1, 5, 3] :=
  markov [1, 5, 3] 2 (by decide)

/-! ## E-55: soundness both ways on fresh descriptors -/

/-- Admission unpacks to the three checks. -/
example : within 64 ⟨8, 16, true⟩ = true ∧ aligned ⟨8, 16, true⟩ = true ∧
    (⟨8, 16, true⟩ : Desc).flag = true :=
  admit_sound 64 ⟨8, 16, true⟩ (by decide)

/-- The three checks admit on a fresh descriptor. -/
example : admit 100 ⟨16, 32, true⟩ = true :=
  admit_complete 100 ⟨16, 32, true⟩ (by decide) (by decide) (by decide)

/-- A clean descriptor draws no rejection. -/
example : rejectReason 100 ⟨16, 32, true⟩ = none :=
  (reject_iff 100 ⟨16, 32, true⟩).mpr (by decide)

/-! ## E-56: a fresh program translates faithfully -/

/-- Add-two twice from one is five on both sides. -/
example : arun (transpL [.add 2, .add 2]) 1 =
    xrun [.add 2, .add 2] 1 :=
  transpL_correct [.add 2, .add 2] 1

/-! ## E-57: minimization on the toggle -/

/-- Acceptance survives minimization on a longer word. -/
example : accepts (minimize toggle) [true, false] =
    accepts toggle [true, false] :=
  accepts_min toggle [true, false] (by decide)

/-- Runs ignore minimization. -/
example : run (minimize toggle) [true] 0 = run toggle [true] 0 :=
  run_minimize toggle [true] 0

/-- Minimization never adds states to the toggle. -/
example : (minimize toggle).states.length ≤ toggle.states.length :=
  minimize_le toggle

end Morph.Tests.BatchFGH
