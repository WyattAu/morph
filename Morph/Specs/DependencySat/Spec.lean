/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.DependencySat

/-- Dependency node represents a build target with its dependencies. -/
structure DependencyNode where
  id : String
  dependencies : List String
  deriving Repr, BEq

/-- Dependency graph represents all nodes and their relationships. -/
structure DependencyGraph where
  nodes : List DependencyNode
  deriving Repr, BEq

/-- Saturation state tracks the progress of dependency saturation. -/
structure SaturationState where
  visited : List String
  saturated : List String
  deriving Repr, BEq

/-- Saturation result contains the final saturated dependencies. -/
structure SaturationResult where
  saturated : List String
  complete : Bool
  deriving Repr, BEq

/-- Check if a dependency graph is well-formed. -/
def isWellFormed (graph : DependencyGraph) : Bool :=
  let nodeIds := graph.nodes.map fun n => n.id
  graph.nodes.all fun node =>
    node.dependencies.all fun dep => dep ∈ nodeIds

/-- Check if a graph has a direct cycle (edge from node to itself). -/
def hasDirectCycle (graph : DependencyGraph) : Bool :=
  graph.nodes.any fun node => node.id ∈ node.dependencies

/-- Check if a graph has a two-cycle (A→B and B→A). -/
def hasTwoCycle (graph : DependencyGraph) : Bool :=
  graph.nodes.any fun node1 =>
    node1.dependencies.any fun dep1 =>
      graph.nodes.any fun node2 =>
        node2.id = dep1 ∧ node1.id ∈ node2.dependencies ∧ node1.id ≠ node2.id

/-- Create initial saturation state. -/
def initialSaturationState : SaturationState :=
  { visited := [], saturated := [] }

/-- Perform one step of saturation. -/
def saturateStep (graph : DependencyGraph) (state : SaturationState) : SaturationState :=
  let unsaturatedNodes := graph.nodes.filter fun n => n.id ∉ state.saturated
  let readyNodes := unsaturatedNodes.filter fun n =>
    n.dependencies.all fun dep => dep ∈ state.saturated
  if readyNodes.isEmpty then state
  else
    let newSaturated := state.saturated ++ readyNodes.map fun n => n.id
    let newVisited := state.visited ++ readyNodes.map fun n => n.id
    { visited := newVisited, saturated := newSaturated }

/-- Add transitive dependencies to a node. -/
partial def addTransitiveDependencies (graph : DependencyGraph) (node : DependencyNode) : DependencyNode :=
  let rec helper (visited : List String) (toVisit : List String) (accum : List String) : List String :=
    match toVisit with
    | [] => accum
    | current :: rest =>
        if current ∈ visited then
          helper visited rest accum
        else
          let visited' := current :: visited
          let deps := match graph.nodes.find? fun n => n.id = current with
            | some n => n.dependencies
            | none => []
          let accum' := deps ++ accum
          let toVisit' := deps ++ rest
          helper visited' toVisit' accum'
  let transitiveDeps := helper [] [node.id] []
  { id := node.id, dependencies := transitiveDeps }

/-- Check if a graph has a cycle. -/
partial def hasCycle (graph : DependencyGraph) : Bool :=
  let rec visit (visited : List String) (toVisit : List String) : Bool :=
    match toVisit with
    | [] => false
    | current :: rest =>
        if current ∈ visited then
          true
        else
          let visited' := current :: visited
          let deps := match graph.nodes.find? fun n => n.id = current with
            | some n => n.dependencies
            | none => []
          let toVisit' := deps ++ rest
          if visit visited' toVisit' then
            true
          else
            visit visited' rest
  graph.nodes.any fun node => visit [] [node.id]

/-- Compute transitive closure of dependencies. -/
def saturateDependencies (graph : DependencyGraph) : DependencyGraph :=
  let saturatedNodes := graph.nodes.map fun node => addTransitiveDependencies graph node
  { nodes := saturatedNodes }

end Morph.Specs.DependencySat
