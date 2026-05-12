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

theorem initialSaturationState_empty :
  initialSaturationState.visited = [] ∧ initialSaturationState.saturated = [] := by
  unfold initialSaturationState; constructor <;> rfl

theorem isWellFormed_empty : isWellFormed { nodes := [] } = true := by
  unfold isWellFormed; simp

theorem isWellFormed_single_no_deps :
  isWellFormed { nodes := [{ id := "a", dependencies := [] }] } = true := by
  unfold isWellFormed; simp

theorem isWellFormed_self_dep :
  isWellFormed { nodes := [{ id := "a", dependencies := ["a"] }] } = true := by
  unfold isWellFormed; simp

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

end Morph.Specs.DependencySat
