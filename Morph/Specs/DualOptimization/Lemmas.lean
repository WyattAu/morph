/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.DualOptimization

/-!
## Lemmas

Lemmas for the DualOptimization specification.
This module will contain proofs about primal-dual optimization,
Lagrangian duality, and optimality conditions.
-/

theorem nat_max_comm (m n : Nat) : Nat.max m n = Nat.max n m := Nat.max_comm m n

theorem nat_max_assoc (a b c : Nat) :
  Nat.max (Nat.max a b) c = Nat.max a (Nat.max b c) := Nat.max_assoc a b c

theorem nat_min_comm (m n : Nat) : Nat.min m n = Nat.min n m := Nat.min_comm m n

theorem nat_min_max_distrib (a b c : Nat) :
  Nat.min a (Nat.max b c) = Nat.max (Nat.min a b) (Nat.min a c) :=
  Nat.min_max_distrib_left a b c

end Morph.Specs.DualOptimization
