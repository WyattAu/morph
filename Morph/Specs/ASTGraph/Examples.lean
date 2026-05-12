/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ASTGraph.Spec

namespace Morph.Specs.ASTGraph

open Morph.Specs.CommonTypes

/-!
## Examples

Concrete examples demonstrating the ASTGraph specification.
-/

instance : Inhabited ASTEdge where
  default := { source := { id := 0 }, target := { id := 0 }, edgeType := .parent }

def id0 : ObjectId := { id := 0 }

def id1 : ObjectId := { id := 1 }

def progNode : ASTNode := {
  id := id0,
  nodeType := ASTNodeType.program,
  children := [id1]
}

def funcNode : ASTNode := {
  id := id1,
  nodeType := ASTNodeType.function,
  children := []
}

def edge1 : ASTEdge := { source := id0, target := id1, edgeType := ASTEdgeType.child }

def g0 : ASTGraph := defaultASTGraph

def g1 : ASTGraph := addNode g0 progNode

def g2 : ASTGraph := addNode g1 funcNode

def g3 : ASTGraph := addEdge g2 edge1

example : g3.edges.length = 1 := rfl

example : g3.edges.head!.source = id0 := rfl

example : g3.edges.head!.target = id1 := rfl

example : g3.edges.head!.edgeType = ASTEdgeType.child := rfl

theorem program_ne_function : ASTNodeType.program ≠ ASTNodeType.function := by
  intro h; cases h

theorem parent_ne_child : ASTEdgeType.parent ≠ ASTEdgeType.child := by
  intro h; cases h

theorem forward_ne_backward_edge : ASTEdgeType.parent ≠ ASTEdgeType.next := by
  intro h; cases h

end Morph.Specs.ASTGraph
