/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.DependencySat.Spec

namespace Morph.Specs.DependencySat

/-!
## Lemmas

Lemmas about the dependency saturation system.
-/

/-! ### Saturation State -/

theorem initialSaturationState_empty :
  initialSaturationState.visited = [] ∧ initialSaturationState.saturated = [] := by
  unfold initialSaturationState; constructor <;> rfl

/-! ### Well-Formedness -/

theorem isWellFormed_empty : isWellFormed { nodes := [] } = true := by
  unfold isWellFormed; simp

theorem isWellFormed_single_no_deps :
  isWellFormed { nodes := [{ id := "a", dependencies := [] }] } = true := by
  unfold isWellFormed; simp

theorem isWellFormed_self_dep :
  isWellFormed { nodes := [{ id := "a", dependencies := ["a"] }] } = true := by
  unfold isWellFormed; simp

/-! ### Cycle Detection -/

theorem hasDirectCycle_self_ref :
  hasDirectCycle { nodes := [{ id := "a", dependencies := ["a"] }] } = true := by
  unfold hasDirectCycle; simp

theorem hasDirectCycle_no_self_ref :
  hasDirectCycle { nodes := [{ id := "a", dependencies := ["b"] }] } = false := by
  unfold hasDirectCycle; simp

theorem hasTwoCycle_pair :
  hasTwoCycle { nodes := [
    { id := "a", dependencies := ["b"] },
    { id := "b", dependencies := ["a"] }
  ] } = true := by
  unfold hasTwoCycle; decide

theorem hasTwoCycle_none :
  hasTwoCycle { nodes := [
    { id := "a", dependencies := ["b"] }
  ] } = false := by
  unfold hasTwoCycle; decide

/-! ### Dependency Node -/

theorem depNode_id_eq (n : DependencyNode) : n.id = n.id := rfl

theorem depNode_deps_nil_no_cycle :
  hasDirectCycle { nodes := [{ id := "a", dependencies := [] }] } = false := by
  unfold hasDirectCycle; simp

/-! ### Graph Properties -/

theorem isWellFormed_two_mutual :
  isWellFormed { nodes := [
    { id := "a", dependencies := ["b"] },
    { id := "b", dependencies := ["a"] }
  ] } = true := by
  unfold isWellFormed; simp

theorem isWellFormed_empty_graph :
  isWellFormed { nodes := [] } = true := by
  unfold isWellFormed; simp

end Morph.Specs.DependencySat
