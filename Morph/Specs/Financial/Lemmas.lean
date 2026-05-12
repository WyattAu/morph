/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.Financial

/-!
## Lemmas

Lemmas for the Financial specification.
This module will contain proofs about financial computations,
interest calculations, and monetary rounding.
-/

theorem nat_add_assoc (a b c : Nat) : a + b + c = a + (b + c) := Nat.add_assoc a b c

theorem nat_mul_comm (m n : Nat) : m * n = n * m := Nat.mul_comm m n

theorem nat_sub_self (n : Nat) : n - n = 0 := Nat.sub_self n

end Morph.Specs.Financial
