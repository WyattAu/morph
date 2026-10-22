/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.SecurityOCap.Spec

namespace Morph.Specs.SecurityOCap

/-!
# SecurityOCap: reachability, authority, and four claims

Research loop 31. Target: `Morph/Specs/SecurityOCap/`.

**What was there.** Four `Prop := True` claims — `Path.transitive`,
`authority_inheritance`, `ctx_capability_root`, `spec_authority_inheritance` —
plus `authority_transfer`, written as an implication to `True`. `Node` and
`Edge` derived only `BEq`, so the computed `Reachable`/`Authority` could not be
related to graph membership.

**What is here.** `Node` and `Edge` now derive `DecidableEq`. `EdgeChain` and
`Reaches` give a genuine reflexive-transitive reachability relation, and
`Path.transitive` is proved by concatenating edge chains (`EdgeChain.append`).
`authority_inheritance` and `ctx_capability_root` say every function's authority
root is its context's `ctx` node, and are proved by `rfl`. `authority_transfer`
is now the real existence of an edge `A → O`, and `mem_Authority_iff` shows the
computed `Authority` list is exactly the targets of the context's edges.

**Not changed here.** `Path.exists` remains the one-step relation; it is related
to `Reaches` by `path_exists_reaches`, not silently identified with it.
-/

/-- The empty access graph is well-formed. -/
theorem empty_graph_well_formed :
    AccessGraph.well_formed { nodes := [], edges := [] } := by
  intro e hmem
  simp at hmem

/-- A singleton access graph is well-formed. -/
theorem singleton_graph_well_formed (n : Node) :
    AccessGraph.well_formed { nodes := [n], edges := [] } := by
  intro e hmem
  simp at hmem

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
    authority_transfer g A _B O :=
  ⟨e, _h_mem, _h_src, _h_tgt⟩

/-- **Adding a node preserves well-formedness.** The old proof was `fun h => h` —
a tautology, valid only because `well_formed` was `True`. Now that it means
"every edge's endpoints are nodes", the proof is real: the edges are unchanged,
and a node list that grew still contains every endpoint it did. -/
theorem add_node_preserves_well_formed (g : AccessGraph) (n : Node) :
    AccessGraph.well_formed g →
    AccessGraph.well_formed { g with nodes := n :: g.nodes } := by
  intro h e hmem
  have h' := h e hmem
  exact ⟨by simpa using Or.inr h'.1, by simpa using Or.inr h'.2⟩

/-- A graph satisfying spec_access_graph has well-formed edges. -/
theorem spec_access_graph_implies_edges_valid (g : AccessGraph)
    (h : spec_access_graph g) : AccessGraph.edges_valid g := h.right

/-! ### Reachability and the formerly-vacuous claims -/

/-- Concatenating two edge chains gives an edge chain to the final node. -/
def EdgeChain.append {g : AccessGraph} :
    {a b c : Node} → {es1 es2 : List Edge} →
    EdgeChain g a b es1 → EdgeChain g b c es2 →
    EdgeChain g a c (es1 ++ es2)
  | _, _, _, [], _, EdgeChain.nil _, h2 => h2
  | _, _, _, _ :: _, _, EdgeChain.cons hmem hsrc htgt htail, h2 =>
      EdgeChain.cons hmem hsrc htgt (EdgeChain.append htail h2)

/-- Reachability is transitive. -/
theorem reaches_trans {g : AccessGraph} {A B C : Node} :
    Reaches g A B → Reaches g B C → Reaches g A C := by
  intro ⟨es1, h1⟩ ⟨es2, h2⟩
  exact ⟨es1 ++ es2, EdgeChain.append h1 h2⟩

/-- A single edge is a (one-element) chain. -/
theorem path_exists_reaches {g : AccessGraph} {a b : Node}
    (h : Path.exists g a b) : Reaches g a b := by
  rcases h with rfl | ⟨e, hmem, hsrc, htgt⟩
  · exact ⟨[], EdgeChain.nil a⟩
  · exact ⟨[e], EdgeChain.cons hmem hsrc htgt (EdgeChain.nil b)⟩

theorem Path_transitive_holds (g : AccessGraph) (A B C : Node) :
    Path.transitive g A B C :=
  reaches_trans

theorem authority_inheritance_holds (ctx : CapabilityRoot) (f g : Function) :
    authority_inheritance ctx f g := rfl

theorem ctx_capability_root_holds (ctx : CapabilityRoot) (f : Function) :
    ctx_capability_root ctx f := rfl

theorem spec_authority_inheritance_holds (ctx : CapabilityRoot) (f g : Function) :
    spec_authority_inheritance ctx f g := rfl

/-- Membership in `Authority` is exactly having an edge from the context node,
which is the real content of `authority_transfer`. -/
theorem mem_Authority_iff (g : AccessGraph) (ctx : CapabilityRoot)
    (f : Function) (O : Node) :
    O ∈ Authority g ctx f ↔
      ∃ (e : Edge), e ∈ g.edges ∧ e.source = ctx.ctx ∧ e.target = O := by
  simp [Authority, List.mem_map, List.mem_filter, and_assoc]

end Morph.Specs.SecurityOCap
