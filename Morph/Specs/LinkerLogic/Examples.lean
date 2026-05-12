/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.LinkerLogic

/-!
## Examples

Concrete examples for the LinkerLogic specification.
-/

example : 1 ∈ ([1, 2, 3] : List Nat) := by simp

example : 4 ∉ ([1, 2, 3] : List Nat) := by simp

example : ([] : List String).Nodup := by constructor

example : ([] : List String).length = 0 := rfl

example : ["a", "b"].length = 2 := rfl

example : ["a", "a"].Nodup = false := by simp

example : ["a", "b"].Nodup = true := by simp

end Morph.Specs.LinkerLogic
