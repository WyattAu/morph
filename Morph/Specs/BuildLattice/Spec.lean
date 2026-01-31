/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.BuildLattice

/--
Build node kind distinguishes different types of compilation units.
-/
inductive BuildNodeKind where
  | package : BuildNodeKind
  | module : BuildNodeKind
  | source : BuildNodeKind
  deriving Repr, BEq

/--
Build node represents a compilation unit with dependencies.
-/
structure BuildNode where
  id : String
  kind : BuildNodeKind
  dependencies : List String
  deriving Repr, BEq

/--
Build edge represents a dependency relationship.
-/
structure BuildEdge where
  src : String
  tgt : String
  deriving Repr, BEq

/--
Build order is a list of node IDs in valid build order.
-/
abbrev BuildOrder := List String

/--
Find the index of an element in a list, if present.
-/
def listIndexOf? [BEq α] (xs : List α) (x : α) : Option Nat :=
  let rec loop (i : Nat) (ys : List α) : Option Nat :=
    match ys with
    | [] => none
    | y :: rest => if y == x then some i else loop (i + 1) rest
  loop 0 xs

/--
Count occurrences of an element in a list.
-/
def listCount [BEq α] (xs : List α) (x : α) : Nat :=
  xs.foldl (fun acc y => if y == x then acc + 1 else acc) 0

/--
Check if build order is valid (contains all nodes and respects dependencies).
-/
def isValidBuildOrder (nodes : List BuildNode) (order : BuildOrder) : Bool :=
  let nodeIds := nodes.map fun n => n.id
  let hasAllNodes := nodeIds.all fun id => id ∈ order
  let respectsDependencies := nodes.all fun node =>
    node.dependencies.all fun dep =>
      let depIndex := listIndexOf? order dep
      let nodeIndex := listIndexOf? order node.id
      match depIndex, nodeIndex with
      | some di, some ni => di < ni
      | _, _ => false
  hasAllNodes ∧ respectsDependencies

/--
Partial order relation between nodes.
Note: This is a placeholder structure. For a proper partial order,
the le function must satisfy reflexivity, transitivity, and antisymmetry.
-/
structure PartialOrder where
  le : String → String → Bool

/--
Build lattice combines a partial order with meet and join operations.
-/
structure BuildLattice where
  partialOrder : PartialOrder
  nodes : List BuildNode
  edges : List BuildEdge

/--
Meet operation (greatest lower bound).
-/
def meet (lattice : BuildLattice) (x y : String) : Option String :=
  let lowerBounds := lattice.nodes.filter fun n =>
    lattice.partialOrder.le n.id x = true ∧ lattice.partialOrder.le n.id y = true
  if lowerBounds.isEmpty then none
  else
    let glb := lowerBounds.foldl (fun acc n =>
      match acc with
      | none => some n
      | some a => if lattice.partialOrder.le n.id a.id = true then some n else some a) none
    glb.map fun n => n.id

/--
Join operation (least upper bound).
-/
def join (lattice : BuildLattice) (x y : String) : Option String :=
  let upperBounds := lattice.nodes.filter fun n =>
    lattice.partialOrder.le x n.id = true ∧ lattice.partialOrder.le y n.id = true
  if upperBounds.isEmpty then none
  else
    let lub := upperBounds.foldl (fun acc n =>
      match acc with
      | none => some n
      | some a => if lattice.partialOrder.le a.id n.id = true then some n else some a) none
    lub.map fun n => n.id

/--
Check if a node is well-formed.
-/
def isNodeWellFormed (node : BuildNode) (allNodes : List BuildNode) : Bool :=
  let nodeIds := allNodes.map fun n => n.id
  node.dependencies.all fun dep => dep ∈ nodeIds

/--
Check if an edge is well-formed (both endpoints exist as nodes).
-/
def isEdgeWellFormed (edge : BuildEdge) (allNodes : List BuildNode) : Bool :=
  let nodeIds := allNodes.map fun n => n.id
  edge.src ∈ nodeIds ∧ edge.tgt ∈ nodeIds

/--
Check if the lattice is well-formed.
-/
def isWellFormed (lattice : BuildLattice) : Bool :=
  let nodesOk := lattice.nodes.all fun n => isNodeWellFormed n lattice.nodes
  let edgesOk := lattice.edges.all fun e => isEdgeWellFormed e lattice.nodes
  nodesOk ∧ edgesOk

/--
Check if the lattice has a direct cycle (edge from node to itself).
-/
def hasDirectCycle (lattice : BuildLattice) : Bool :=
  lattice.edges.any fun e => e.src = e.tgt

/--
Check if the lattice has a two-cycle (A→B and B→A).
-/
def hasTwoCycle (lattice : BuildLattice) : Bool :=
  lattice.edges.any fun e1 =>
    lattice.edges.any fun e2 =>
      e1.src = e2.tgt ∧ e1.tgt = e2.src ∧ e1.src ≠ e1.tgt

/--
Inhabited instance for BuildNode.
-/
instance : Inhabited BuildNode where
  default := { id := "", kind := BuildNodeKind.package, dependencies := [] }

/--
Inhabited instance for BuildNodeKind.
-/
instance : Inhabited BuildNodeKind where
  default := BuildNodeKind.package

/--
Inhabited instance for BuildEdge.
-/
instance : Inhabited BuildEdge where
  default := { src := "", tgt := "" }

/--
Inhabited instance for BuildLattice.
-/
instance : Inhabited BuildLattice where
  default := { partialOrder := { le := fun _ _ => false }, nodes := [], edges := [] }

end Morph.Specs.BuildLattice
