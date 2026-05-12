/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.SecurityOCap.Spec

namespace Morph.Specs.SecurityOCap

/-!
## Lemmas

Lemmas and auxiliary results for the SecurityOCap specification.
-/

/-- The empty access graph is well-formed. -/
theorem empty_graph_well_formed :
    AccessGraph.well_formed { nodes := [], edges := [] } := trivial

/-- A singleton access graph is well-formed. -/
theorem singleton_graph_well_formed (n : Node) :
    AccessGraph.well_formed { nodes := [n], edges := [] } := trivial

/-- The empty access graph has valid edges (vacuously: no edges to check). -/
theorem empty_graph_edges_valid :
    AccessGraph.edges_valid { nodes := [], edges := [] } := by
  intro e h_mem
  simp at h_mem

/-- Path.exists is reflexive: every node can reach itself. -/
theorem path_exists_refl (g : AccessGraph) (n : Node) :
    Path.exists g n n := Or.inl rfl

/-- The connectivity rule is reflexive: any subject can access itself. -/
theorem connectivity_refl (g : AccessGraph) (n : Node) (op : Operation) :
    connectivity_rule g n n op := Or.inl rfl

/-- Allowed is reflexive for any operation. -/
theorem allowed_refl (g : AccessGraph) (n : Node) (op : Operation) :
    Allowed g n n op := Or.inl rfl

/-- Well-formedness plus edge validity implies spec_access_graph. -/
theorem valid_graph_satisfies_spec (g : AccessGraph)
    (h_wf : AccessGraph.well_formed g)
    (h_ev : AccessGraph.edges_valid g) :
    spec_access_graph g := ⟨h_wf, h_ev⟩

/-- A graph with at least one node and no edges has no global ambient authority. -/
theorem no_edges_no_global_authority (nodes : List Node)
    (n : Node) (h_mem : n ∈ nodes) :
    no_global_ambient_authority { nodes := nodes, edges := [] } := by
  unfold no_global_ambient_authority
  intro ⟨global_node, h⟩
  have ⟨e, h_e_mem, _, _⟩ := h n h_mem
  simp at h_e_mem

/-- Authority transfer holds when an edge exists in the graph. -/
theorem authority_transfer_from_edge (g : AccessGraph) (A _B O : Node)
    (e : Edge) (_h_mem : e ∈ g.edges) (_h_src : e.source = A) (_h_tgt : e.target = O) :
    authority_transfer g A _B O := by
  unfold authority_transfer
  exists e
  intro _
  trivial

/-- Adding a node preserves well-formedness (since well_formed is always true). -/
theorem add_node_preserves_well_formed (g : AccessGraph) (n : Node) :
    AccessGraph.well_formed g →
    AccessGraph.well_formed { g with nodes := n :: g.nodes } := fun h => h

/-- A graph satisfying spec_access_graph has well-formed edges. -/
theorem spec_access_graph_implies_edges_valid (g : AccessGraph)
    (h : spec_access_graph g) : AccessGraph.edges_valid g := h.right

end Morph.Specs.SecurityOCap
