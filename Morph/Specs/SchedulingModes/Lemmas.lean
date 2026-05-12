/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulingModes.Spec

namespace Morph.Specs.SchedulingModes

/-!
## Lemmas

Lemmas and auxiliary results for the SchedulingModes specification.
-/

/-! ### Fairness Bound -/

theorem fairnessBound_empty : fairnessBound [] [] = 0 := rfl

theorem fairnessBound_cons (w : Worker) (ws : List Worker) (tasks : List Task) :
  fairnessBound (w :: ws) tasks = (ws.length + 1) * tasks.length := by
  unfold fairnessBound; simp

theorem fairnessBound_nil_tasks (ws : List Worker) :
  fairnessBound ws [] = 0 := rfl

theorem fairnessBound_nil_workers (tasks : List Task) :
  fairnessBound ([] : List Worker) tasks = 0 := by
  unfold fairnessBound; simp

/-! ### Find Position -/

theorem findPosition_empty (task : Task) :
  findPosition [] task = 0 := rfl

theorem findPosition_found (task : Task) (rest : List Task) :
  findPosition (task :: rest) task = 0 := by
  unfold findPosition; simp

/-! ### Scheduling Mode Exhaustiveness -/

theorem schedulingMode_cases (m : SchedulingMode) :
  m = SchedulingMode.deterministic ∨ m = SchedulingMode.randomized ∨
  m = SchedulingMode.priority ∨ m = SchedulingMode.workStealing := by
  cases m <;> simp

/-! ### Worker/Task Properties -/

theorem worker_id_nonneg (w : Worker) : w.id ≥ 0 := Nat.zero_le w.id

theorem task_id_nonneg (t : Task) : t.id ≥ 0 := Nat.zero_le t.id

theorem task_priority_nonneg (t : Task) : t.priority ≥ 0 := Nat.zero_le t.priority

theorem task_workload_nonneg (t : Task) : t.workload ≥ 0 := Nat.zero_le t.workload

end Morph.Specs.SchedulingModes
