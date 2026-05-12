/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulingModes.Spec

namespace Morph.Specs.SchedulingModes

/-!
## Lemmas

Lemmas and auxiliary results for the SchedulingModes specification.
-/

theorem fairnessBound_empty : fairnessBound [] [] = 0 := rfl

theorem fairnessBound_cons (w : Worker) (ws : List Worker) (tasks : List Task) :
  fairnessBound (w :: ws) tasks = (ws.length + 1) * tasks.length := by
  unfold fairnessBound; simp

theorem findPosition_empty (task : Task) :
  findPosition [] task = 0 := rfl

theorem schedulingMode_cases (m : SchedulingMode) :
  m = SchedulingMode.deterministic ∨ m = SchedulingMode.randomized ∨
  m = SchedulingMode.priority ∨ m = SchedulingMode.workStealing := by
  cases m <;> simp

theorem fairnessBound_nil_tasks (ws : List Worker) :
  fairnessBound ws [] = 0 := rfl

end Morph.Specs.SchedulingModes
