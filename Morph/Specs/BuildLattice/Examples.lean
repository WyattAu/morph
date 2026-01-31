/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.BuildLattice.Spec

namespace Morph.Specs.BuildLattice

/-- BL-EX-001: Simple two-node lattice. -/
def exampleTwoNodeLattice : BuildLattice :=
  let nodes := [
    { id := "A", kind := BuildNodeKind.package, dependencies := [] },
    { id := "B", kind := BuildNodeKind.package, dependencies := ["A"] }
  ]
  let edges := [
    { src := "A", tgt := "B" }
  ]
  let partialOrder := {
    le := fun x y =>
      match x, y with
      | "A", "A" => true
      | "B", "B" => true
      | "A", "B" => true
      | _, _ => false
  }
  { partialOrder, nodes, edges }

/-- BL-EX-002: Three-node lattice with diamond dependency. -/
def exampleThreeNodeLattice : BuildLattice :=
  let nodes := [
    { id := "A", kind := BuildNodeKind.package, dependencies := [] },
    { id := "B", kind := BuildNodeKind.package, dependencies := ["A"] },
    { id := "C", kind := BuildNodeKind.package, dependencies := ["A"] }
  ]
  let edges := [
    { src := "A", tgt := "B" },
    { src := "A", tgt := "C" }
  ]
  let partialOrder := {
    le := fun x y =>
      match x, y with
      | "A", "A" => true
      | "B", "B" => true
      | "C", "C" => true
      | "A", "B" => true
      | "A", "C" => true
      | _, _ => false
  }
  { partialOrder, nodes, edges }

/-- BL-EX-003: Topological order for two-node lattice. -/
def exampleTopologicalOrder : BuildOrder := ["A", "B"]

/-- BL-EX-004: Meet operation on two-node lattice. -/
def exampleMeetOperation : Option String :=
  meet exampleTwoNodeLattice "A" "B"

/-- BL-EX-005: Join operation on two-node lattice. -/
def exampleJoinOperation : Option String :=
  join exampleTwoNodeLattice "A" "B"

/-- BL-EX-006: Cyclic lattice with two-cycle. -/
def exampleCyclicLattice : BuildLattice :=
  let nodes := [
    { id := "A", kind := BuildNodeKind.package, dependencies := ["B"] },
    { id := "B", kind := BuildNodeKind.package, dependencies := ["A"] }
  ]
  let edges := [
    { src := "A", tgt := "B" },
    { src := "B", tgt := "A" }
  ]
  let partialOrder := {
    le := fun x y =>
      match x, y with
      | "A", "A" => true
      | "B", "B" => true
      | "A", "B" => true
      | "B", "A" => true
      | _, _ => false
  }
  { partialOrder, nodes, edges }

/-- BL-EX-007: Linear chain of three nodes. -/
def exampleLinearChain : BuildLattice :=
  let nodes := [
    { id := "A", kind := BuildNodeKind.package, dependencies := [] },
    { id := "B", kind := BuildNodeKind.package, dependencies := ["A"] },
    { id := "C", kind := BuildNodeKind.package, dependencies := ["B"] }
  ]
  let edges := [
    { src := "A", tgt := "B" },
    { src := "B", tgt := "C" }
  ]
  let partialOrder := {
    le := fun x y =>
      match x, y with
      | "A", "A" => true
      | "B", "B" => true
      | "C", "C" => true
      | "A", "B" => true
      | "A", "C" => true
      | "B", "C" => true
      | _, _ => false
  }
  { partialOrder, nodes, edges }

/-- BL-EX-008: Topological order for linear chain. -/
def exampleLinearOrder : BuildOrder := ["A", "B", "C"]

/-- BL-EX-009: Empty lattice. -/
def exampleEmptyLattice : BuildLattice :=
  let nodes := []
  let edges := []
  let partialOrder := { le := fun _ _ => false }
  { partialOrder, nodes, edges }

/-- BL-EX-010: Lattice with multiple dependencies. -/
def exampleMultipleDepsLattice : BuildLattice :=
  let nodes := [
    { id := "A", kind := BuildNodeKind.package, dependencies := [] },
    { id := "B", kind := BuildNodeKind.package, dependencies := ["A"] },
    { id := "C", kind := BuildNodeKind.package, dependencies := ["A"] },
    { id := "D", kind := BuildNodeKind.package, dependencies := ["B", "C"] }
  ]
  let edges := [
    { src := "A", tgt := "B" },
    { src := "A", tgt := "C" },
    { src := "B", tgt := "D" },
    { src := "C", tgt := "D" }
  ]
  let partialOrder := {
    le := fun x y =>
      match x, y with
      | "A", "A" => true
      | "B", "B" => true
      | "C", "C" => true
      | "D", "D" => true
      | "A", "B" => true
      | "A", "C" => true
      | "A", "D" => true
      | "B", "D" => true
      | "C", "D" => true
      | _, _ => false
  }
  { partialOrder, nodes, edges }

/-- BL-EX-011: Topological order for multiple dependencies. -/
def exampleMultipleDepsOrder : BuildOrder := ["A", "B", "C", "D"]

/-- BL-EX-012: Well-formed check on two-node lattice. -/
def exampleIsWellFormed : Bool :=
  isWellFormed exampleTwoNodeLattice

/-- BL-EX-013: Direct cycle check on cyclic lattice. -/
def exampleHasDirectCycle : Bool :=
  hasDirectCycle exampleCyclicLattice

/-- BL-EX-014: Two-cycle check on cyclic lattice. -/
def exampleHasTwoCycle : Bool :=
  hasTwoCycle exampleCyclicLattice

/-- BL-EX-015: Valid build order check. -/
def exampleIsValidBuildOrder : Bool :=
  isValidBuildOrder exampleTwoNodeLattice.nodes exampleTopologicalOrder

/-- BL-EX-016: Meet on same element. -/
def exampleMeetSame : Option String :=
  meet exampleTwoNodeLattice "A" "A"

/-- BL-EX-017: Join on same element. -/
def exampleJoinSame : Option String :=
  join exampleTwoNodeLattice "B" "B"

end Morph.Specs.BuildLattice
