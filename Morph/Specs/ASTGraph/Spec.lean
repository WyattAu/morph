/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Specs.CommonTypes

/-!
# Specification: AST Graph

**Source:** `spec/language/ast_graph_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-31
**Verified By:** Kilo Code

## Overview

This specification formalizes the AST (Abstract Syntax Tree) graph structure,
which represents the hierarchical relationships between language constructs.

## Known Issues

None identified. All specification points are clear and unambiguous.

-/
namespace Morph.Specs.ASTGraph

open Morph.Specs.CommonTypes

instance instBEqObjectId : BEq ObjectId where
  beq a b := a.id == b.id

instance : Hashable ObjectId where
  hash a := hash a.id

/-- The custom `BEq` on `ObjectId` is just equality of the underlying `Nat`, so
the `Std.HashMap` lemmas apply. -/
instance : LawfulBEq ObjectId where
  eq_of_beq {a b} h := by
    have hid : a.id = b.id := by simpa [instBEqObjectId] using h
    cases a; cases b; simp_all
  rfl {a} := by
    show (a.id == a.id) = true
    simp

/-!
## AST Node Types
-/

inductive ASTNodeType where
  | program : ASTNodeType
  | function : ASTNodeType
  | block : ASTNodeType
  | statement : ASTNodeType
  | expression : ASTNodeType
  | identifier : ASTNodeType
  | literal : ASTNodeType
  deriving Repr, BEq

/-!
## AST Edge Types
-/

inductive ASTEdgeType where
  | parent : ASTEdgeType
  | child : ASTEdgeType
  | sibling : ASTEdgeType
  | next : ASTEdgeType
  | previous : ASTEdgeType
  deriving Repr, BEq

/-!
## AST Node
-/

structure ASTNode where
  id : ObjectId
  nodeType : ASTNodeType
  children : List ObjectId

/-!
## AST Edge
-/

structure ASTEdge where
  source : ObjectId
  target : ObjectId
  edgeType : ASTEdgeType

/-!
## AST Graph
-/

structure ASTGraph where
  nodes : Std.HashMap ObjectId ASTNode
  edges : List ASTEdge

/-!
## AST Graph Operations
-/

def addNode (G : ASTGraph) (node : ASTNode) : ASTGraph :=
  { G with nodes := Std.HashMap.insert G.nodes node.id node }

def addEdge (G : ASTGraph) (edge : ASTEdge) : ASTGraph :=
  { G with edges := edge :: G.edges }

def getNode (G : ASTGraph) (id : ObjectId) : Option ASTNode :=
  Std.HashMap.get? G.nodes id

def getChildren (G : ASTGraph) (id : ObjectId) : List ObjectId :=
  match Std.HashMap.get? G.nodes id with
  | some node => node.children
  | none => []

/-!
## Reachability
-/

/-- One-step reachability: the node itself, or a direct edge. -/
def isReachable (G : ASTGraph) (source target : ObjectId) : Prop :=
  source = target ∨
    ∃ (e : ASTEdge), e ∈ G.edges ∧ e.source = source ∧ e.target = target

/-!
## AST Graph Properties
-/

def ASTGraph.hasNode (G : ASTGraph) (id : ObjectId) : Prop :=
  (getNode G id).isSome = true

/-- **Well-formedness**: every edge's endpoints are nodes of the graph. (This
was `True`.) -/
def isWellFormed (G : ASTGraph) : Prop :=
  ∀ (e : ASTEdge), e ∈ G.edges → G.hasNode e.source ∧ G.hasNode e.target

/-- **Acyclicity**: no two distinct nodes reach each other in one step. (This
was `True`.) -/
def isAcyclic (G : ASTGraph) : Prop :=
  ∀ (a b : ObjectId), isReachable G a b → isReachable G b a → a = b

/-!
## Specification Theorems
-/

/-- The structural requirement on an AST graph. (This was a theorem claiming
`isWellFormed G` for every `G`, which is false now that the predicate is real.) -/
def spec_ast_graph_structure (G : ASTGraph) : Prop := isWellFormed G

/-- The combined structural and acyclicity requirement. -/
def spec_ast_graph_properties (G : ASTGraph) : Prop :=
  isWellFormed G ∧ isAcyclic G

/-- **Traversal stays inside the graph**: every node reachable from a present
root is present, assuming the graph is well formed. -/
theorem spec_ast_graph_traversal (G : ASTGraph) (rootId : ObjectId)
    (hWF : isWellFormed G) (hroot : G.hasNode rootId) :
    ∀ (id : ObjectId), isReachable G rootId id → G.hasNode id := by
  intro id h
  rcases h with rfl | ⟨e, he, _, htgt⟩
  · exact hroot
  · subst htgt
    exact (hWF e he).2

theorem getNode_addNode (G : ASTGraph) (node : ASTNode) (id : ObjectId) :
    getNode (addNode G node) id =
      if node.id == id then some node else getNode G id := by
  unfold getNode addNode
  change (Std.HashMap.insert G.nodes node.id node)[id]? =
    if node.id == id then some node else G.nodes[id]?
  rw [Std.HashMap.getElem?_insert]

theorem add_node_preserves_well_formed (G : ASTGraph) (node : ASTNode) :
    isWellFormed G → isWellFormed (addNode G node) := by
  intro h e he
  have he' : e ∈ G.edges := by simpa [addNode] using he
  obtain ⟨hs, ht⟩ := h e he'
  unfold ASTGraph.hasNode at hs ht ⊢
  constructor
  · rw [getNode_addNode]
    by_cases hk : node.id == e.source
    · simp [hk]
    · simp [hk, hs]
  · rw [getNode_addNode]
    by_cases hk : node.id == e.target
    · simp [hk]
    · simp [hk, ht]

/-!
## Default Values
-/

def defaultASTGraph : ASTGraph :=
  { nodes := (∅ : Std.HashMap ObjectId ASTNode), edges := [] }

def defaultASTNode (id : ObjectId) (nodeType : ASTNodeType) : ASTNode :=
  { id := id, nodeType := nodeType, children := [] }

def defaultASTEdge (source target : ObjectId) : ASTEdge :=
  { source := source, target := target, edgeType := ASTEdgeType.parent }

end Morph.Specs.ASTGraph
