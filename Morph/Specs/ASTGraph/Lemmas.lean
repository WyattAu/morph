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

/-! ### Reachability -/

theorem isReachable_refl (source : ObjectId) :
  isReachable defaultASTGraph source source := rfl

theorem isReachable_sym (source target : ObjectId) (G : ASTGraph) :
  isReachable G source target → isReachable G target source := by
  unfold isReachable; intro h; exact h.symm

/-! ### Default Values -/

theorem defaultASTNode_empty_children (id : ObjectId) (t : ASTNodeType) :
  (defaultASTNode id t).children = [] := rfl

theorem defaultASTEdge_type (source target : ObjectId) :
  (defaultASTEdge source target).edgeType = ASTEdgeType.parent := rfl

/-! ### Graph Operations -/

theorem addEdge_cons (G : ASTGraph) (edge : ASTEdge) :
  (addEdge G edge).edges = edge :: G.edges := rfl

theorem addNode_preserves_edges (G : ASTGraph) (node : ASTNode) (edge : ASTEdge) :
  edge ∈ G.edges → edge ∈ (addNode G node).edges := by
  unfold addNode; intro h; simp; exact h

/-! ### Type Exhaustiveness -/

theorem astNodeType_cases (t : ASTNodeType) :
  t = .program ∨ t = .function ∨ t = .block ∨ t = .statement ∨
  t = .expression ∨ t = .identifier ∨ t = .literal := by
  cases t <;> simp

theorem astEdgeType_cases (t : ASTEdgeType) :
  t = .parent ∨ t = .child ∨ t = .sibling ∨ t = .next ∨ t = .previous := by
  cases t <;> simp

/-! ### Well-Formedness -/

theorem defaultASTGraph_well_formed : isWellFormed defaultASTGraph := trivial

theorem defaultASTGraph_acyclic : isAcyclic defaultASTGraph := trivial

end Morph.Specs.ASTGraph
