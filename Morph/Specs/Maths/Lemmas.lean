/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.Maths

/-!
## Lemmas

Lemmas for the Maths specification.
This module will contain general mathematical proofs
used throughout the Morph project.
-/

theorem nat_add_zero (n : Nat) : n + 0 = n := Nat.add_zero n

theorem nat_zero_add (n : Nat) : 0 + n = n := Nat.zero_add n

theorem nat_succ_add (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) :=
  Nat.succ_add m n

theorem nat_add_succ (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) :=
  Nat.add_succ m n

end Morph.Specs.Maths
