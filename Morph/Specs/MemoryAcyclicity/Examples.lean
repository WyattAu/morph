/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryAcyclicity.Spec

namespace Morph.Specs.MemoryAcyclicity

open Morph.Specs.CommonTypes

/-!
## Examples

Concrete examples demonstrating the MemoryAcyclicity specification.
-/

def obj0 : ObjectId := { id := 0 }

def obj1 : ObjectId := { id := 1 }

def emptyGraph : ReferenceGraph := { vertices := [], edges := [] }

def singleNodeGraph : ReferenceGraph := { vertices := [obj0], edges := [] }

def twoNodeGraph : ReferenceGraph := {
  vertices := [obj0, obj1],
  edges := [(obj0, obj1)]
}

example : strongReferences obj0 emptyGraph = 0 := rfl

example : hasPath obj0 obj0 emptyGraph := by
  unfold hasPath; left; rfl

example : weakReferences obj0 emptyGraph = 0 := rfl

example : emptyGraph.vertices.length = 0 := rfl

example : twoNodeGraph.vertices.length = 2 := rfl

end Morph.Specs.MemoryAcyclicity
