/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.ScopingLambdaCalculus

/-!
## Examples

Concrete examples for the ScopingLambdaCalculus specification.
-/

example : (["a", "b", "c"] : List String).length = 3 := rfl

example : "a" ∈ (["a", "b"] : List String) := by simp

example : "c" ∉ (["a", "b"] : List String) := by simp

end Morph.Specs.ScopingLambdaCalculus
