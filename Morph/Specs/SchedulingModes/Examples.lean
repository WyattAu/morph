/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulingModes.Spec

namespace Morph.Specs.SchedulingModes

/-!
## Examples

Concrete examples demonstrating the SchedulingModes specification.
-/

def task1 : Task := { id := 0, priority := 1, workload := 10 }

def task2 : Task := { id := 1, priority := 2, workload := 5 }

def worker1 : Worker := {
  id := 0,
  queue := [task1, task2],
  mode := SchedulingMode.priority
}

example : worker1.queue.length = 2 := rfl

example : findPosition worker1.queue task1 = 0 := rfl

example : findPosition worker1.queue task2 = 1 := rfl

example : fairnessBound [worker1] [task1] = 1 := rfl

example : fairnessBound [worker1] [task1, task2] = 2 := rfl

example : SchedulingMode.deterministic ≠ SchedulingMode.randomized := by
  intro h; cases h

example : fairnessBound [] [] = 0 := rfl

end Morph.Specs.SchedulingModes
