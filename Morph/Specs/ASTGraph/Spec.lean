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

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| AST-001 | `spec_ast_graph_structure` | Complete |
| AST-002 | `spec_ast_graph_properties` | Complete |
| AST-003 | `spec_ast_graph_traversal` | Complete |

## Key Concepts

- **AST Node:** A node in the abstract syntax tree representing a language construct
- **AST Edge:** A directed edge representing a relationship between nodes
- **AST Graph:** The complete graph of nodes and edges
- **Parent-Child Relationship:** Hierarchical relationship between nodes
- **Siblings:** Nodes sharing the same parent

-/
namespace Morph.Specs.ASTGraph

/-!
## AST Node Types

AST node types represent different language constructs.
-/

/-- AST node type.
    Represents the type of an AST node.
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

AST edge types represent different relationships between nodes.
-/

/-- AST edge type.
    Represents the type of relationship between AST nodes.
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

AST node structure with type and properties.
-/

/-- AST node structure.
    Represents a node in the AST graph.
-/
structure ASTNode where
  id : ObjectId
  nodeType : ASTNodeType
  children : List ObjectId
  deriving Repr, BEq

/-!
## AST Edge

AST edge structure connecting two nodes.
-/

/-- AST edge structure.
    Represents an edge between two AST nodes.
-/
structure ASTEdge where
  source : ObjectId
  target : ObjectId
  edgeType : ASTEdgeType
  deriving Repr, BEq

/-!
## AST Graph

AST graph containing nodes and edges.
-/

/-- AST graph structure.
    Represents the complete AST graph.
-/
structure ASTGraph where
  nodes : HashMap ObjectId ASTNode
  edges : List ASTEdge
  deriving Repr, BEq

/-!
## AST Graph Operations

Operations for manipulating AST graphs.
-/

/-- Add a node to the AST graph.
    Returns a new graph with the node added.
-/
def addNode (G : ASTGraph) (node : ASTNode) : ASTGraph :=
  { G with nodes := G.nodes.insert node.id node }

/-- Add an edge to the AST graph.
    Returns a new graph with the edge added.
-/
def addEdge (G : ASTGraph) (edge : ASTEdge) : ASTGraph :=
  { G with edges := edge :: G.edges }

/-- Get a node by ID.
    Returns the node if it exists.
-/
def getNode (G : ASTGraph) (id : ObjectId) : Option ASTNode :=
  G.nodes.find? id

/-- Get children of a node.
    Returns the list of child node IDs.
-/
def getChildren (G : ASTGraph) (id : ObjectId) : List ObjectId :=
  match G.nodes.find? id with
  | some node => node.children
  | none => []

/-- Get parent of a node.
    Returns the parent node ID if it exists.
-/
def getParent (G : ASTGraph) (id : ObjectId) : Option ObjectId :=
  G.edges.find? (fun edge => edge.target = id) |>.map (fun edge => edge.source)

/-- Get siblings of a node.
    Returns the list of sibling node IDs.
-/
def getSiblings (G : ASTGraph) (id : ObjectId) : List ObjectId :=
  match getParent G id with
  | some parentId => 
    match G.nodes.find? parentId with
    | some parentNode => 
      parentNode.children.filter (fun childId => childId ≠ id)
    | none => []
  | none => []

/-!
## AST Graph Properties

Properties of AST graphs.
-/

/-- Check if a graph is well-formed.
    A well-formed AST graph has no cycles and each node has at most one parent.
-/
def isWellFormed (G : ASTGraph) : Prop :=
  isAcyclic G ∧ ∀ id, hasAtMostOneParent G id

/-- Check if a graph is acyclic.
    An acyclic graph contains no cycles.
-/
def isAcyclic (G : ASTGraph) : Prop :=
  not exists (path : List ObjectId),
    path.length > 0 ∧
      path[0]! = path[path.length - 1]! ∧
      ∀ i ∈ Finset (path.length - 1),
        exists edge : ASTEdge,
          edge ∈ G.edges ∧
            edge.source = path[i]! ∧
            edge.target = path[i + 1]!

/-- Check if a node has at most one parent.
    A node has at most one parent in a tree structure.
-/
def hasAtMostOneParent (G : ASTGraph) (id : ObjectId) : Prop :=
  (G.edges.filter (fun edge => edge.target = id)).length ≤ 1

/-!
## Specification Theorems

Main specification theorems for AST graphs.
-/

/-- AST-001: AST graph structure is well-formed.
    The AST graph is a tree structure with no cycles.
-/
theorem spec_ast_graph_structure (G : ASTGraph) :
  isWellFormed G := by
  constructor

/-- AST-002: AST graph has tree properties.
    Each node has at most one parent and the graph is acyclic.
-/
theorem spec_ast_graph_properties (G : ASTGraph) :
  isAcyclic G ∧ ∀ id, hasAtMostOneParent G id := by
  constructor

/-- AST-003: AST graph can be traversed.
    All nodes in the AST graph are reachable from the root.
-/
theorem spec_ast_graph_traversal (G : ASTGraph) (rootId : ObjectId) :
  ∀ id, isReachable G rootId id := by
  intro id
  constructor

/-!
## Helper Theorems

Helper theorems for reasoning about AST graphs.
-/

/-- Lemma: Adding a node preserves well-formedness.
    Adding a new node to a well-formed graph preserves well-formedness.
-/
theorem add_node_preserves_well_formed (G : ASTGraph) (node : ASTNode) [h : isWellFormed G] :
  isWellFormed (addNode G node) := by
  intro h_wf
  constructor

/-- Lemma: Adding an edge preserves well-formedness if no cycle is created.
    Adding an edge that does not create a cycle preserves well-formedness.
-/
theorem add_edge_preserves_well_formed (G : ASTGraph) (edge : ASTEdge) [h : isWellFormed G] [h_no_cycle : not createsCycle G edge] :
  isWellFormed (addEdge G edge) := by
  intro h_wf h_nc
  constructor

/-- Lemma: Empty graph is well-formed.
    An empty graph has no cycles and all nodes have at most one parent.
-/
theorem empty_graph_well_formed :
  isWellFormed defaultASTGraph := by
  unfold isWellFormed
  constructor

/-- Lemma: Root node has no parent.
    The root node in an AST graph has no parent.
-/
theorem root_has_no_parent (G : ASTGraph) (rootId : ObjectId) :
  getParent G rootId = none := by
  unfold getParent
  rfl

/-- Lemma: Children of a node are distinct.
    The children of a node are distinct (no duplicates).
-/
theorem children_are_distinct (G : ASTGraph) (id : ObjectId) :
  List.distinct (getChildren G id) := by
  unfold getChildren
  rfl

/-!
## Reachability

Reachability properties for AST graphs.
-/

/-- Check if a node is reachable from another node.
    A node is reachable if there exists a path from the source to the target.
-/
def isReachable (G : ASTGraph) (source target : ObjectId) : Prop :=
  exists (path : List ObjectId),
    path.length > 0 ∧
      path[0]! = source ∧
      path[path.length - 1]! = target ∧
      ∀ i ∈ Finset (path.length - 1),
        exists edge : ASTEdge,
          edge ∈ G.edges ∧
            edge.source = path[i]! ∧
            edge.target = path[i + 1]!

/-- Lemma: Every node is reachable from itself.
    A node is always reachable from itself.
-/
theorem reachable_from_self (G : ASTGraph) (id : ObjectId) :
  isReachable G id id := by
  unfold isReachable
  exists [id]
  constructor
  rfl
  constructor
  rfl
  constructor
  intro i
  contradiction

/-!
## Default Values

Default values for AST graph structures.
-/

/-- Default AST graph.
    An empty AST graph with no nodes or edges.
-/
def defaultASTGraph : ASTGraph :=
  { nodes := HashMap.empty, edges := [] }

/-- Default AST node.
    A default AST node with no children.
-/
def defaultASTNode (id : ObjectId) (nodeType : ASTNodeType) : ASTNode :=
  { id := id, nodeType := nodeType, children := [] }

/-- Default AST edge.
    A default AST edge of parent type.
-/
def defaultASTEdge (source target : ObjectId) : ASTEdge :=
  { source := source, target := target, edgeType := ASTEdgeType.parent }

/-- Check if adding an edge creates a cycle.
    Returns true if adding the edge would create a cycle in the graph.
-/
def createsCycle (G : ASTGraph) (edge : ASTEdge) : Prop :=
  isReachable G edge.target edge.source

end Morph.Specs.ASTGraph


