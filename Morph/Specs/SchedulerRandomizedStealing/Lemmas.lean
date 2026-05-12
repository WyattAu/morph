/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulerRandomizedStealing.Spec

namespace Morph.Specs.SchedulerRandomizedStealing

/-!
## Lemmas

Lemmas and auxiliary results for the SchedulerRandomizedStealing specification.
-/

theorem isBalanced_empty : isBalanced [] := by
  unfold isBalanced; intro _ w1 _ w2; simp_all

theorem listMin_empty : listMin [] = 0 := rfl

theorem listMax_empty : listMax [] = 0 := rfl

theorem listMin_singleton (n : Nat) : listMin [n] = n := rfl

theorem listMax_singleton (n : Nat) : listMax [n] = n := rfl

theorem maxImbalance_empty : maxImbalance [] = 0 := rfl

theorem minQueueLength_empty : minQueueLength [] = 0 := rfl

end Morph.Specs.SchedulerRandomizedStealing
