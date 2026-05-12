/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulerRandomizedStealing.Spec

namespace Morph.Specs.SchedulerRandomizedStealing

/-!
## Examples

Concrete examples demonstrating the SchedulerRandomizedStealing specification.
-/

def ball1 : Ball := { id := 0 }

def ball2 : Ball := { id := 1 }

def bin1 : Bin := { id := 0, balls := [ball1, ball2] }

def bin2 : Bin := { id := 1, balls := [ball1] }

example : bin1.balls.length = 2 := rfl

example : bin2.balls.length = 1 := rfl

def emptyBin : Bin := { id := 0, balls := [] }

example : emptyBin.balls.length = 0 := rfl

example : isFair [] := by unfold isFair; simp

example : listMin [] = 0 := rfl

example : listMax [] = 0 := rfl

example : maxImbalance [] = 0 := rfl

example : minQueueLength [] = 0 := rfl

end Morph.Specs.SchedulerRandomizedStealing
