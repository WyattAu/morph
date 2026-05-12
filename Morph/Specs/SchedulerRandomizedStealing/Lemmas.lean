/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulerRandomizedStealing.Spec

namespace Morph.Specs.SchedulerRandomizedStealing

/-!
## Lemmas

Lemmas and auxiliary results for the SchedulerRandomizedStealing specification.
-/

/-! ### Balanced System -/

theorem isBalanced_empty : isBalanced [] := by
  unfold isBalanced; intro _ w1 _ w2; simp_all

theorem isBalanced_singleton (b : Bin) : isBalanced [b] := by
  unfold isBalanced; simp

theorem isFair_empty : isFair [] := by
  unfold isFair; trivial

/-! ### List Min/Max -/

theorem listMin_empty : listMin [] = 0 := rfl

theorem listMax_empty : listMax [] = 0 := rfl

theorem listMin_singleton (n : Nat) : listMin [n] = n := rfl

theorem listMax_singleton (n : Nat) : listMax [n] = n := rfl

/-! ### Imbalance and Queue Length -/

theorem maxImbalance_empty : maxImbalance [] = 0 := rfl

theorem minQueueLength_empty : minQueueLength [] = 0 := rfl

theorem listMin_cons_two (m n : Nat) : listMin [m, n] = Nat.min m n := rfl

theorem listMax_cons_two (m n : Nat) : listMax [m, n] = Nat.max m n := rfl

/-! ### Ball/Bin Properties -/

theorem ball_id_nonneg (b : Ball) : b.id ≥ 0 := Nat.zero_le b.id

theorem bin_id_nonneg (b : Bin) : b.id ≥ 0 := Nat.zero_le b.id

theorem bin_balls_length_nonneg (b : Bin) : b.balls.length ≥ 0 := Nat.zero_le b.balls.length

end Morph.Specs.SchedulerRandomizedStealing
