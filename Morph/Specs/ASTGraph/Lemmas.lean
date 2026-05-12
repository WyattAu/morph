/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ASTGraph.Spec

namespace Morph.Specs.ASTGraph

open Morph.Specs.CommonTypes

/-!
## Lemmas

Lemmas and auxiliary results for the ASTGraph specification.
-/

theorem isReachable_refl (source : ObjectId) :
  isReachable defaultASTGraph source source := rfl

theorem defaultASTNode_empty_children (id : ObjectId) (t : ASTNodeType) :
  (defaultASTNode id t).children = [] := rfl

theorem defaultASTEdge_type (source target : ObjectId) :
  (defaultASTEdge source target).edgeType = ASTEdgeType.parent := rfl

theorem addEdge_cons (G : ASTGraph) (edge : ASTEdge) :
  (addEdge G edge).edges = edge :: G.edges := rfl

theorem astNodeType_cases (t : ASTNodeType) :
  t = .program ∨ t = .function ∨ t = .block ∨ t = .statement ∨
  t = .expression ∨ t = .identifier ∨ t = .literal := by
  cases t <;> simp

end Morph.Specs.ASTGraph
