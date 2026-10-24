/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.DependencySat.Spec

namespace Morph.Specs.DependencySat

/-- DS-EX-001: Simple dependency graph with linear chain. -/
def exampleSimpleGraph : DependencyGraph :=
  let nodeA : DependencyNode := { id := "module_a", dependencies := [] }
  let nodeB : DependencyNode := { id := "module_b", dependencies := ["module_a"] }
  let nodeC : DependencyNode := { id := "module_c", dependencies := ["module_b"] }
  { nodes := [nodeA, nodeB, nodeC] }

/-- DS-EX-002: Dependency graph with diamond dependency pattern. -/
def exampleDiamondGraph : DependencyGraph :=
  let nodeA : DependencyNode := { id := "module_a", dependencies := [] }
  let nodeB : DependencyNode := { id := "module_b", dependencies := ["module_a"] }
  let nodeC : DependencyNode := { id := "module_c", dependencies := ["module_a"] }
  let nodeD : DependencyNode := { id := "module_d", dependencies := ["module_b", "module_c"] }
  { nodes := [nodeA, nodeB, nodeC, nodeD] }

/-- DS-EX-003: Cyclic dependency graph. -/
def exampleCyclicGraph : DependencyGraph :=
  let nodeA : DependencyNode := { id := "module_a", dependencies := ["module_b"] }
  let nodeB : DependencyNode := { id := "module_b", dependencies := ["module_a"] }
  { nodes := [nodeA, nodeB] }

/-- The diamond is **not** a cycle: `module_d` is reached twice but never
recursively. (The old path-local DFS reported `true` here.) -/
example : hasCycle exampleDiamondGraph = false := by native_decide

/-- The two-cycle is a cycle. -/
example : hasCycle exampleCyclicGraph = true := by native_decide

/-- A direct self-dependency is a cycle. -/
example :
    hasCycle { nodes := [{ id := "a", dependencies := ["a"] }] } = true := by
  native_decide

/-- Unknown dependencies are ignored, so they do not create a cycle. -/
example :
    hasCycle { nodes := [{ id := "a", dependencies := ["missing"] }] } = false := by
  native_decide

/-- Transitive dependencies of `module_d`: `[a, a, b, c]` - the closure, with
the original algorithm's duplicate accumulation preserved. -/
example :
    (addTransitiveDependencies exampleDiamondGraph
      { id := "module_d", dependencies := ["module_b", "module_c"] }).dependencies.length
      = 4 := by
  native_decide

end Morph.Specs.DependencySat
