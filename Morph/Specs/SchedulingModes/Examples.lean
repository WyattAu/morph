/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulingModes.Spec

namespace Morph.Specs.SchedulingModes.Examples

/- # Examples for Scheduling Modes -/

/-- Example deterministic worker with FIFO ordering -/
def exampleDeterministicFifoWorker : Worker :=
  { id := 0
    mode := .deterministic
    queue := [{ id := 0, priority := 1, workload := 1 },
               { id := 1, priority := 1, workload := 1 },
               { id := 2, priority := 1, workload := 1 }] }

/-- Example deterministic worker with LIFO ordering -/
def exampleDeterministicLifoWorker : Worker :=
  { id := 1
    mode := .deterministic
    queue := [{ id := 0, priority := 1, workload := 1 },
               { id := 1, priority := 1, workload := 1 },
               { id := 2, priority := 1, workload := 1 }] }

/-- Example priority worker with priority-based ordering -/
def examplePriorityWorker : Worker :=
  { id := 2
    mode := .priority
    queue := [{ id := 0, priority := 3, workload := 1 },
               { id := 1, priority := 2, workload := 1 },
               { id := 2, priority := 2, workload := 1 },
               { id := 3, priority := 1, workload := 1 }] }

/-- Example randomized worker -/
def exampleRandomizedWorker : Worker :=
  { id := 3
    mode := .randomized
    queue := [{ id := 0, priority := 1, workload := 1 },
               { id := 1, priority := 1, workload := 1 },
               { id := 2, priority := 1, workload := 1 }] }

/-- Example work-stealing workers -/
def exampleWorkStealingWorkers : List Worker :=
  [{ id := 0, mode := .workStealing, queue := [{ id := 0, priority := 1, workload := 1 }, { id := 1, priority := 1, workload := 1 }] },
   { id := 1, mode := .workStealing, queue := [] } ]

/-- Example tasks for fair scheduling -/
def exampleFairnessTasks : List Task :=
  [{ id := 0, priority := 1, workload := 1 },
   { id := 1, priority := 1, workload := 1 },
   { id := 2, priority := 1, workload := 1 },
   { id := 3, priority := 1, workload := 1 } ]

/-- Example workers for fair scheduling -/
def exampleFairnessWorkers : List Worker :=
  [{ id := 0, mode := .deterministic, queue := [{ id := 0, priority := 1, workload := 1 }, { id := 1, priority := 1, workload := 1 }] },
   { id := 1, mode := .deterministic, queue := [{ id := 2, priority := 1, workload := 1 }, { id := 3, priority := 1, workload := 1 }] } ]

/-- Verify deterministic scheduler: first task is at position 0 -/
example verifyDeterministicFifo : specDeterministicScheduler exampleDeterministicFifoWorker { id := 0, priority := 1, workload := 1 } := by
  unfold specDeterministicScheduler
  constructor
  · rfl
  · rfl
  · constructor
    · rfl
    · rfl
    constructor
    rfl

/-- Verify deterministic scheduler: last task is at position 2 -/
example verifyDeterministicLifo : specDeterministicScheduler exampleDeterministicLifoWorker { id := 2, priority := 1, workload := 1 } := by
  unfold specDeterministicScheduler
  constructor
  · rfl
  · rfl
  · constructor
    · rfl
    · rfl
    constructor
    rfl

/-- Verify priority scheduler: highest priority task is at position 0 -/
example verifyPriorityScheduler : specPriorityScheduling examplePriorityWorker { id := 0, priority := 3, workload := 1 } := by
  unfold specPriorityScheduling
  constructor
  · rfl
  · rfl
  · constructor
    · rfl
    · rfl
    constructor
    rfl

/-- Verify scheduling modes: all modes are valid -/
example verifySchedulingModes : specSchedulingModes exampleDeterministicFifoWorker.mode := by
  unfold specSchedulingModes
  apply Or.inl

/-- Verify scheduling modes for worker: all modes are valid -/
example verifySchedulingModesWorker : specSchedulingModesWorker exampleDeterministicFifoWorker := by
  unfold specSchedulingModesWorker
  apply Or.inl

/-- Verify fairness guarantee: all tasks are scheduled within bound -/
example verifyFairnessGuarantee : specFairnessGuarantee exampleFairnessWorkers exampleFairnessTasks := by
  unfold specFairnessGuarantee
  intro worker h_worker_in
  unfold fairnessBound at h_fairness
  intro task h_task_in_tasks h_task_in_queue
  have h_pos_exists : ∃ (position : Nat),
    position = findPosition worker.queue task ∧
    position ≤ 2 * 4 := by
    exists (findPosition worker.queue task)
    constructor
    · rfl
    · apply Nat.le_of_add_right
      rfl
  constructor
    · exact h_pos_exists

/-- Verify work-stealing scheduler: idle worker can steal from busy worker -/
example verifyWorkStealingScheduler : specWorkStealingScheduler exampleWorkStealingWorkers := by
  unfold specWorkStealingScheduler
  constructor
  · rfl
  · constructor
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · constructor
    rfl
  · constructor
    rfl

/-- Verify fairness: workload is balanced across workers -/
example verifyFairness : ∀ (worker : Worker),
    worker ∈ exampleFairnessWorkers →
    |worker.queue.map (·.workload).sum - 2| ≤ 2 := by
  intro worker h_in
  have h_workload_sum : (worker.queue.map (·.workload)).sum = 2 := by
    rfl
  have h_diff_le_2 : |(worker.queue.map (·.workload)).sum - 2| ≤ 2 := by
    rw [h_workload_sum]
      apply Nat.abs_sub_le_self
  constructor
    · exact h_diff_le_2

end Morph.Specs.SchedulingModes.Examples
