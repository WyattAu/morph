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

end Morph.Specs.DependencySat
