/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.BuildLattice.Spec
import Morph.Specs.BuildLattice.Examples

namespace Morph.Specs.BuildLattice

/-!
## Lemmas

Lemmas about the build lattice system.
-/

/-! ### BuildNodeKind Exhaustiveness -/

theorem buildNodeKind_cases (k : BuildNodeKind) :
    k = BuildNodeKind.package ∨ k = BuildNodeKind.module ∨ k = BuildNodeKind.source := by
  cases k <;> simp

/-! ### Cycle Detection -/

theorem hasDirectCycle_empty :
    hasDirectCycle exampleEmptyLattice = false := by
  unfold hasDirectCycle; decide

theorem hasDirectCycle_twoNode :
    hasDirectCycle exampleTwoNodeLattice = false := by
  unfold hasDirectCycle; decide

theorem hasDirectCycle_cyclic :
    hasDirectCycle exampleCyclicLattice = false := by
  unfold hasDirectCycle; decide

theorem hasTwoCycle_cyclic :
    hasTwoCycle exampleCyclicLattice = true := by
  unfold hasTwoCycle; decide

theorem hasTwoCycle_empty :
    hasTwoCycle exampleEmptyLattice = false := by
  unfold hasTwoCycle; decide

theorem hasTwoCycle_twoNode :
    hasTwoCycle exampleTwoNodeLattice = false := by
  unfold hasTwoCycle; decide

/-! ### List Index -/

theorem listIndexOfQ_found :
    listIndexOf? ["A", "B", "C"] "B" = some 1 := by
  unfold listIndexOf?; decide

theorem listIndexOfQ_notFound :
    listIndexOf? ["A", "B", "C"] "D" = none := by
  unfold listIndexOf?; decide

theorem listIndexOfQ_empty :
    listIndexOf? ([] : List String) "A" = none := by
  unfold listIndexOf?; rfl

/-! ### List Count -/

theorem listCount_empty (x : String) :
    listCount ([] : List String) x = 0 := by
  unfold listCount; simp

/-! ### Node Well-Formedness -/

theorem isNodeWellFormed_no_deps :
    isNodeWellFormed { id := "A", kind := BuildNodeKind.package, dependencies := [] }
      [{ id := "A", kind := BuildNodeKind.package, dependencies := [] }] = true := by
  unfold isNodeWellFormed; simp

/-! ### Edge Well-Formedness -/

theorem isEdgeWellFormed_valid :
    isEdgeWellFormed { src := "A", tgt := "B" }
      [{ id := "A", kind := BuildNodeKind.package, dependencies := [] },
       { id := "B", kind := BuildNodeKind.package, dependencies := [] }] = true := by
  unfold isEdgeWellFormed; decide

theorem isEdgeWellFormed_invalid_src :
    isEdgeWellFormed { src := "X", tgt := "B" }
      [{ id := "A", kind := BuildNodeKind.package, dependencies := [] }] = false := by
  unfold isEdgeWellFormed; decide

/-! ### Well-Formedness -/

theorem isWellFormed_empty :
    isWellFormed exampleEmptyLattice = true := by
  unfold isWellFormed; decide

theorem isWellFormed_twoNode :
    isWellFormed exampleTwoNodeLattice = true := by
  unfold isWellFormed; decide

theorem isWellFormed_linearChain :
    isWellFormed exampleLinearChain = true := by
  unfold isWellFormed; decide

/-! ### Build Order -/

theorem isValidBuildOrder_twoNode :
    isValidBuildOrder exampleTwoNodeLattice.nodes ["A", "B"] = true := by
  unfold isValidBuildOrder; decide

theorem isValidBuildOrder_linearChain :
    isValidBuildOrder exampleLinearChain.nodes ["A", "B", "C"] = true := by
  unfold isValidBuildOrder; decide

/-! ### Meet/Join on Concrete Lattices -/

theorem meet_A_B_in_twoNode :
    meet exampleTwoNodeLattice "A" "B" = some "A" := by
  unfold meet; decide

theorem join_A_B_in_twoNode :
    join exampleTwoNodeLattice "A" "B" = some "B" := by
  unfold join; decide

theorem meet_same_A :
    meet exampleTwoNodeLattice "A" "A" = some "A" := by
  unfold meet; decide

theorem join_same_B :
    join exampleTwoNodeLattice "B" "B" = some "B" := by
  unfold join; decide

end Morph.Specs.BuildLattice
