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

theorem strongReferences_empty (o : ObjectId) :
  strongReferences o { vertices := [], edges := [] } = 0 := rfl

theorem hasPath_self (o : ObjectId) (G : ReferenceGraph) :
  hasPath o o G := by unfold hasPath; left; rfl

theorem weakReferences_zero (o : ObjectId) (G : ReferenceGraph) :
  weakReferences o G = 0 := rfl

theorem eventuallyDeallocated_trivial (o : ObjectId) :
  eventuallyDeallocated o := trivial

end Morph.Specs.MemoryAcyclicity
