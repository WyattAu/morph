/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.DualOptimization

/-!
## Examples

Concrete examples for the DualOptimization specification.
-/

example : Nat.max 3 5 = 5 := rfl

example : Nat.min 3 5 = 3 := rfl

example : Nat.max (Nat.max 1 2) 3 = Nat.max 1 (Nat.max 2 3) := rfl

example (n : Nat) : Nat.max 0 n = n := by cases n <;> rfl

example (n : Nat) : Nat.min 0 n = 0 := by cases n <;> rfl

end Morph.Specs.DualOptimization
