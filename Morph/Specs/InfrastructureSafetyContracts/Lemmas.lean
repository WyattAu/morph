/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.InfrastructureSafetyContracts.Spec

/-!
Lemmas for InfrastructureSafetyContracts: the allocation and free operations
satisfy their contracts, freeing is idempotent in the safety sense (a freed
block cannot be freed again), and both operations preserve heap well-formedness
and the handle bound.
-/
namespace Morph.Specs.InfrastructureSafetyContracts

open Morph.Core

/-- Allocating block `id` satisfies the allocation postcondition. -/
theorem alloc_satisfies (h : Heap) (id : Nat) (hne : id ≠ 0) :
    allocContract.post h (mkPtr id) (h.alloc id) := by
  refine ⟨hne, ?_, rfl⟩
  simp [Heap.isLive, Heap.alloc, mkPtr]

/-- Freeing block `id` satisfies the free postcondition: it is not live after. -/
theorem free_satisfies (h : Heap) (id : Nat) :
    freeContract.post h (mkPtr id) (h.free id) :=
  Heap.isLive_free_self h id

/-- The free precondition is exactly liveness. -/
theorem free_requires_live (h : Heap) (p : Pointer) :
    freeContract.pre h p ↔ h.isLive p.block.id := Iff.rfl

/-- **No double free.** If a free succeeded (the block is dead afterwards), its
precondition - the block being live - can no longer hold. -/
theorem no_double_free (h h' : Heap) (p : Pointer)
    (hpost : freeContract.post h p h') :
    ¬ freeContract.pre h' p :=
  hpost

/-- Freeing one block leaves every other live block live. -/
theorem free_preserves_live_other (h : Heap) (id y : Nat) (hne : y ≠ id)
    (hy : h.isLive y) : (h.free id).isLive y :=
  (Heap.isLive_free_of_ne h id y hne).mpr hy

/-- Allocation leaves every previously live block live. -/
theorem alloc_preserves_live_old (h : Heap) (id y : Nat) (hy : h.isLive y) :
    (h.alloc id).isLive y :=
  (Heap.isLive_alloc h id y).mpr (Or.inr hy)

/-- **Allocation respects the handle bound.** The precondition reserves room for
one more handle, and the postcondition adds exactly one, so the result is still
below the cap. -/
theorem alloc_preserves_handle_bound (h h' : Heap) (p : Pointer)
    (hpre : allocContract.pre h p) (hpost : allocContract.post h p h') :
    handleCountSafe h'.live.length := by
  unfold handleCountSafe
  rw [hpost.2.2]
  exact hpre

/-- Freeing a block never increases the number of live blocks. -/
theorem free_does_not_grow (h : Heap) (id : Nat) :
    (h.free id).live.length ≤ h.live.length :=
  Heap.free_non_increasing h id

end Morph.Specs.InfrastructureSafetyContracts
