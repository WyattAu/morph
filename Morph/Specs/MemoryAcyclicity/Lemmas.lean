/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryAcyclicity.Spec

namespace Morph.Specs.MemoryAcyclicity

open Morph.Specs.CommonTypes

/-!
## Lemmas

Lemmas and auxiliary results for the MemoryAcyclicity specification.
-/

/-! ### Reference Counting -/

theorem strongReferences_empty (o : ObjectId) :
  strongReferences o { vertices := [], edges := [] } = 0 := rfl

theorem strongReferences_nil_edges (o : ObjectId) (vs : List ObjectId) :
  strongReferences o { vertices := vs, edges := [] } = 0 := by
  unfold strongReferences; simp

theorem weakReferences_zero (o : ObjectId) (G : ReferenceGraph) :
  weakReferences o G = 0 := rfl

/-! ### Path Properties -/

theorem hasPath_self (o : ObjectId) (G : ReferenceGraph) :
  hasPath o o G := by unfold hasPath; left; rfl

/-! ### Deallocation -/

theorem eventuallyDeallocated_trivial (o : ObjectId) :
  eventuallyDeallocated o := trivial

/-! ### Graph Properties -/

theorem strongReferences_nonneg (o : ObjectId) (G : ReferenceGraph) :
  strongReferences o G ≥ 0 := Nat.zero_le (strongReferences o G)

theorem weakReferences_nonneg (o : ObjectId) (G : ReferenceGraph) :
  weakReferences o G ≥ 0 := Nat.zero_le (weakReferences o G)

end Morph.Specs.MemoryAcyclicity
