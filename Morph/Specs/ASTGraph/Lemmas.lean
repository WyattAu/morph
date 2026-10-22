/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ASTGraph.Spec

namespace Morph.Specs.ASTGraph

open Morph.Specs.CommonTypes

/-!
# ASTGraph: real well-formedness, reachability, and acyclicity

Research loop 33. Target: `Morph/Specs/ASTGraph/`.

**What was there.** `isWellFormed` and `isAcyclic` were `True`; `isReachable`
was just `source = target`; `spec_ast_graph_structure` asserted
well-formedness of *every* graph; `spec_ast_graph_traversal` was `∀ _, True`;
`add_node_preserves_well_formed` was `intro _; trivial`.

**What is here.** `ObjectId` has a `LawfulBEq` instance (its custom `BEq` is
equality of the underlying `Nat`), so `Std.HashMap`'s `getElem?_insert` applies.
`isReachable` is reflexive-or-one-edge, `isWellFormed` says every edge endpoint
is a node, and `isAcyclic` says no two distinct nodes reach each other in one
step. `spec_ast_graph_structure` and `spec_ast_graph_properties` are now
propositions (the old universal theorem was false). `spec_ast_graph_traversal`
is conditional on well-formedness and a present root. `addNode` preserves
well-formedness, proved through `getNode_addNode`.

**Honest narrowing.** Acyclicity here rules out one-step mutual reachability
and self-loops, not arbitrary long cycles; the graph stores edges, not paths.
`isReachable_sym` was deleted because directed reachability is not symmetric;
`isReachable_of_edge` is the true direction-aware statement.
-/

/-! ### Reachability -/

theorem isReachable_refl (source : ObjectId) :
  isReachable defaultASTGraph source source := Or.inl rfl

/-- Reachability follows an edge in its direction; the old `isReachable_sym`
was true only because reachability was `source = target`. -/
theorem isReachable_of_edge {G : ASTGraph} {e : ASTEdge} (he : e ∈ G.edges) :
  isReachable G e.source e.target :=
  Or.inr ⟨e, he, rfl, rfl⟩

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

theorem defaultASTGraph_well_formed : isWellFormed defaultASTGraph := by
  intro e he
  simp [defaultASTGraph] at he

theorem defaultASTGraph_acyclic : isAcyclic defaultASTGraph := by
  intro a b hab _
  rcases hab with rfl | ⟨e, he, _, _⟩
  · rfl
  · simp [defaultASTGraph] at he

end Morph.Specs.ASTGraph
