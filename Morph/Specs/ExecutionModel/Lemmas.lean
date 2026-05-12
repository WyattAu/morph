/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.ExecutionModel

/-!
## Lemmas

Lemmas for the ExecutionModel specification.
This module will contain proofs about evaluation order,
step semantics, and execution properties.
-/

theorem nat_add_comm (m n : Nat) : m + n = n + m := Nat.add_comm m n

theorem nat_mul_zero (n : Nat) : n * 0 = 0 := Nat.mul_zero n

theorem nat_zero_mul (n : Nat) : 0 * n = 0 := Nat.zero_mul n

end Morph.Specs.ExecutionModel
