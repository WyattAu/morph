/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.InfrastructureSafetyContracts.Lemmas

/-!
Examples for InfrastructureSafetyContracts: a small heap, the two operations,
and the contracts holding or rejecting as specified.
-/
namespace Morph.Specs.InfrastructureSafetyContracts

/-- Two live blocks, `1` and `2`. -/
def h0 : Heap := { live := [1, 2] }

example : h0.live = [1, 2] := rfl

example : (h0.alloc 3).live = [3, 1, 2] := rfl

example : (h0.free 1).live = [2] := rfl

example : (h0.free 9).live = [1, 2] := rfl

/-- The initial heap is well formed. -/
example : Heap.WellFormed h0 := ⟨by decide, by decide⟩

/-- Allocation of a fresh non-null block satisfies its contract. -/
example : allocContract.post h0 (mkPtr 3) (h0.alloc 3) :=
  alloc_satisfies h0 3 (by decide)

/-- Freeing a live block satisfies its contract. -/
example : freeContract.post h0 (mkPtr 1) (h0.free 1) :=
  free_satisfies h0 1

/-- A double free is rejected: after freeing block `1`, its precondition fails. -/
example : ¬ freeContract.pre (h0.free 1) (mkPtr 1) :=
  no_double_free h0 (h0.free 1) (mkPtr 1) (free_satisfies h0 1)

/-- The null block never satisfies the free precondition of a well-formed heap. -/
example : ¬ freeContract.pre h0 (mkPtr 0) := by
  show ¬ (0 ∈ h0.live)
  decide

/-- The stack guard accepts a shallow stack and rejects one at the limit. -/
example : stackSafe 10 := by unfold stackSafe maxStackDepth; decide

example : ¬ stackSafe maxStackDepth := by
  unfold stackSafe maxStackDepth
  exact Nat.lt_irrefl _

end Morph.Specs.InfrastructureSafetyContracts
