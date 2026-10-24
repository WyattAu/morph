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

/-- Total number of declared dependencies. -/
def totalDependencies (graph : DependencyGraph) : Nat :=
  graph.nodes.foldl (fun acc n => acc + n.dependencies.length) 0

/-- One transitive-dependency walk, total by fuel. Each expansion marks a node
visited and pushes its dependencies, so at most `1 + totalDependencies` elements
are ever processed. -/
private def transitiveDepsFuel (graph : DependencyGraph) :
    Nat → List String → List String → List String → List String
  | 0, _, _, accum => accum
  | fuel + 1, visited, toVisit, accum =>
    match toVisit with
    | [] => accum
    | current :: rest =>
      if current ∈ visited then
        transitiveDepsFuel graph fuel visited rest accum
      else
        let deps := match graph.nodes.find? (fun n => n.id = current) with
          | some n => n.dependencies
          | none => []
        transitiveDepsFuel graph fuel (current :: visited) (deps ++ rest) (deps ++ accum)

/-- Add transitive dependencies to a node. Total: the walk is bounded by
`nodes.length + totalDependencies + 2` (one expansion per node, one push per
declared dependency). This was a `partial def` with a `let rec` inside. -/
def addTransitiveDependencies (graph : DependencyGraph) (node : DependencyNode) : DependencyNode :=
  let transitiveDeps :=
    transitiveDepsFuel graph (graph.nodes.length + totalDependencies graph + 2) [] [node.id] []
  { id := node.id, dependencies := transitiveDeps }

/-- Kahn's algorithm, total by fuel: each step removes at least one node, so
`nodes.length + 1` fuel suffices. -/
private def kahnFuel : Nat → List DependencyNode → Bool
  | 0, remaining => !remaining.isEmpty
  | fuel + 1, remaining =>
    if remaining.isEmpty then false
    else
      let ready := remaining.filter fun n =>
        n.dependencies.all fun dep => !remaining.any fun m => m.id = dep
      if ready.isEmpty then true
      else
        kahnFuel fuel (remaining.filter fun n => !ready.any fun m => m.id = n.id)

/-- Check if a graph has a cycle, by Kahn's algorithm: repeatedly drop nodes
whose dependencies have all been dropped; a cycle is exactly a non-empty
residue.

This replaces a `partial def` that ran a path-local DFS from every node. That
version was both non-total (no linear bound: the second recursive call re-ran
the remaining frontier, so the walk could be exponential) and **wrong**: it
reported a diamond (`A→B`, `A→C`, `B→D`, `C→D`) as a cycle, because `D` is
reached twice along different paths. Kahn accepts the diamond and rejects the
cycle, and `hasDirectCycle`/`hasTwoCycle` remain sound special cases. -/
def hasCycle (graph : DependencyGraph) : Bool :=
  kahnFuel (graph.nodes.length + 1) graph.nodes

/-- Compute transitive closure of dependencies. -/
def saturateDependencies (graph : DependencyGraph) : DependencyGraph :=
  let saturatedNodes := graph.nodes.map fun node => addTransitiveDependencies graph node
  { nodes := saturatedNodes }

end Morph.Specs.DependencySat
