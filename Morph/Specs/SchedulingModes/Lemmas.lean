/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulingModes.Spec
import Std

namespace Morph.Specs.SchedulingModes

/- # Lemmas for Scheduling Modes -/

/-- Deterministic scheduler selects first task in queue -/
theorem lemmaDeterministicSchedulerSelectsFirst (workers : List Worker) (task : Task) :
    specDeterministicScheduler workers task →
      ∃ (worker : Worker),
        worker ∈ workers ∧
        worker.mode = .deterministic ∧
        task ∈ worker.queue ∧
        findPosition worker.queue task = 0 := by
  intro h_spec
  cases h_spec
  | intro worker h_worker_props h_task_in_queue
    unfold specDeterministicScheduler at h_spec
    cases h_worker_props
    | intro h_in_workers h_mode h_task_exists h_pos_exists
      unfold findPosition at h_pos_exists
      match worker.queue with
      | [] => contradiction
      | t :: rest =>
        if t.id = task.id then
          rfl
        else
          have h_pos_gt_0 : findPosition rest task > 0 := by
            apply Nat.add_pos
            rfl
          contradiction

/-- Deterministic scheduler is deterministic: same inputs produce same outputs -/
theorem lemmaDeterministicSchedulerIsDeterministic (workers : List Worker) (task1 task2 : Task) :
    specDeterministicScheduler workers task1 ∧
    specDeterministicScheduler workers task2 →
      findPosition (workers.find? (fun w => w.mode = .deterministic ∧ task1 ∈ w.queue) queue) task1 =
      findPosition (workers.find? (fun w => w.mode = .deterministic ∧ task2 ∈ w.queue) queue) task2 := by
  intro h_spec1 h_spec2
  have h_worker1_exists : ∃ (worker1 : Worker),
    worker1 ∈ workers ∧
    worker1.mode = .deterministic ∧
    task1 ∈ worker1.queue := by
    cases h_spec1
  | intro worker1 h_worker1_props h_task1_in_queue
      exact worker1
  have h_worker2_exists : ∃ (worker2 : Worker),
    worker2 ∈ workers ∧
    worker2.mode = .deterministic ∧
    task2 ∈ worker2.queue := by
    cases h_spec2
  | intro worker2 h_worker2_props h_task2_in_queue
      exact worker2
  have h_pos1 : findPosition worker1.queue task1 = findPosition worker1.queue task1 := by
    rfl
  have h_pos2 : findPosition worker2.queue task2 = findPosition worker2.queue task2 := by
    rfl
  have h_worker1_eq_worker2 : worker1 = worker2 := by
    cases h_worker1_exists
    | intro w1 h_w1_props
      cases h_worker2_exists
      | intro w2 h_w2_props
        have h_mode_eq : w1.mode = w2.mode := by
          cases h_w1_props <; rfl <; cases h_w2_props <; rfl
        have h_task_eq : task1 = task2 := by
          cases h_w1_props.2 <; rfl <; cases h_w2_props.2 <; rfl
        exact ⟨h_mode_eq, h_task_eq⟩
  have h_queue_eq : w1.queue = w2.queue := by
    cases h_worker1_eq_worker2
      rfl
  rw [h_queue_eq] at h_pos2
  exact h_pos1

/-- Priority scheduler selects highest priority task -/
theorem lemmaPrioritySchedulerSelectsHighest (workers : List Worker) (task : Task) :
    specPriorityScheduling workers task →
      ∃ (worker : Worker),
        worker ∈ workers ∧
        worker.mode = .priority ∧
        task ∈ worker.queue ∧
        findHighestPriorityPosition worker.queue task = 0 := by
  intro h_spec
  cases h_spec
  | intro worker h_worker_props h_task_in_queue
    unfold specPriorityScheduling at h_spec
    cases h_worker_props
    | intro h_in_workers h_mode h_task_exists h_pos_exists
      unfold findHighestPriorityPosition at h_pos_exists
      match worker.queue with
      | [] => contradiction
      | t :: rest =>
        if t.priority > task.priority then
          have h_pos_gt_0 : findHighestPriorityPosition rest task > 0 := by
            apply Nat.add_pos
            rfl
          contradiction
        else if t.priority = task.priority ∧ t.id = task.id then
          rfl
        else
          have h_pos_gt_0 : findHighestPriorityPosition rest task > 0 := by
            apply Nat.add_pos
            rfl
          contradiction

/-- Priority scheduler respects priority ordering -/
theorem lemmaPrioritySchedulerRespectsPriority (workers : List Worker) (task1 task2 : Task) :
    specPriorityScheduling workers task1 ∧
    specPriorityScheduling workers task2 ∧
    task1.priority > task2.priority →
      findHighestPriorityPosition (workers.find? (fun w => w.mode = .priority ∧ task1 ∈ w.queue) queue) task1 <
        findHighestPriorityPosition (workers.find? (fun w => w.mode = .priority ∧ task2 ∈ w.queue) queue) task2 := by
  intro h_spec1 h_spec2 h_priority_gt
  have h_worker1_exists : ∃ (worker1 : Worker),
    worker1 ∈ workers ∧
    worker1.mode = .priority ∧
    task1 ∈ worker1.queue := by
    cases h_spec1
  | intro worker1 h_worker1_props h_task1_in_queue
      exact worker1
  have h_worker2_exists : ∃ (worker2 : Worker),
    worker2 ∈ workers ∧
    worker2.mode = .priority ∧
    task2 ∈ worker2.queue := by
    cases h_spec2
  | intro worker2 h_worker2_props h_task2_in_queue
      exact worker2
  have h_pos1 : findHighestPriorityPosition worker1.queue task1 = 0 := by
    cases h_worker1_exists
    | intro w1 h_w1_props
      cases h_worker2_exists
      | intro w2 h_w2_props
        have h_mode_eq : w1.mode = w2.mode := by
          cases h_w1_props <; rfl <; cases h_w2_props <; rfl
        have h_queue1_eq : w1.queue = w2.queue := by
          cases h_worker1_eq_worker2
            rfl
        have h_task1_in_queue2 : task1 ∈ w2.queue := by
          cases h_w1_props.2 <; rw [h_queue1_eq] <; exact h_task1_in_queue
        unfold findHighestPriorityPosition
        match w2.queue with
        | [] => contradiction
        | t :: rest =>
          if t.priority > task1.priority then
            have h_pos1_gt_0 : findHighestPriorityPosition rest task1 > 0 := by
              apply Nat.add_pos
              rfl
            have h_pos2_ge_0 : findHighestPriorityPosition rest task2 ≥ 0 := by
              apply Nat.zero_le
            have h_pos1_lt_pos2 : 0 < findHighestPriorityPosition rest task2 := by
              rw [h_pos1_gt_0] at h_pos2_ge_0
              apply Nat.lt_of_add_right
                rfl
                exact Nat.zero_le
            contradiction
          else if t.priority = task1.priority ∧ t.id = task1.id then
            have h_pos1_eq_0 : findHighestPriorityPosition rest task1 = 0 := by
              rfl
            have h_pos2_ge_0 : findHighestPriorityPosition rest task2 ≥ 0 := by
              apply Nat.zero_le
            have h_pos1_lt_pos2 : 0 < findHighestPriorityPosition rest task2 := by
              rw [h_pos1_eq_0] at h_pos2_ge_0
              apply Nat.lt_of_add_right
                rfl
                exact Nat.zero_le
          else
            have h_pos1_eq_0 : findHighestPriorityPosition rest task1 = 0 := by
              rfl
            have h_pos2_ge_0 : findHighestPriorityPosition rest task2 ≥ 0 := by
              apply Nat.zero_le
            have h_pos1_lt_pos2 : 0 < findHighestPriorityPosition rest task2 := by
              rw [h_pos1_eq_0] at h_pos2_ge_0
              apply Nat.lt_of_add_right
                rfl
                exact Nat.zero_le
    exact h_pos1_lt_pos2

/-- Fairness guarantee ensures all tasks are scheduled -/
theorem lemmaFairnessGuaranteed (workers : List Worker) (tasks : List Task) :
    specFairnessGuarantee workers tasks →
      ∀ (worker : Worker),
        worker ∈ workers →
          ∀ (task : Task),
            task ∈ tasks ∧
              task ∈ worker.queue →
                ∃ (t : Nat),
                  t ≤ fairnessBound workers tasks ∧
                  taskIsScheduledAt worker task t := by
  intro h_fairness worker h_worker_in task h_task_in_tasks
  unfold specFairnessGuarantee at h_fairness
  unfold fairnessBound at h_fairness
  intro task h_task_in_queue
  have h_pos_exists : ∃ (position : Nat),
    position = findPosition worker.queue task ∧
    position ≤ workers.length * tasks.length := by
    exists (findPosition worker.queue task)
    constructor
    · rfl
    · apply Nat.mul_le
      apply Nat.le_of_add_left
        rfl
  constructor
    · exact h_pos_exists

/-- Work-stealing scheduler can balance load -/
theorem lemmaWorkStealingSchedulerCanBalance (workers : List Worker) (idleWorker busyWorker : Worker) :
    specWorkStealingScheduler workers ∧
    idleWorker ∈ workers ∧
    idleWorker.mode = .workStealing ∧
    busyWorker ∈ workers ∧
    busyWorker.queue.length > 0 ∧
    idleWorker.queue.length < busyWorker.queue.length →
      ∃ (task : Task),
        task ∈ busyWorker.queue ∧
        task ∉ idleWorker.queue := by
  intro h_spec h_idle_in h_idle_mode h_busy_in h_busy_queue_gt_0 h_idle_queue_lt_busy
  unfold specWorkStealingScheduler at h_spec
  have h_task_exists : ∃ (task : Task), task ∈ busyWorker.queue := by
    cases h_busy_queue_gt_0
  | [] => contradiction
  | t :: rest =>
      exists t
      constructor
      · rfl
  have h_task_not_in_idle : task ∉ idleWorker.queue := by
    intro h_task_in_idle
    cases h_idle_queue_lt_busy
    | [] => rfl
    | t' :: rest' =>
      if t' = task then
        have h_queue_eq : idleWorker.queue = busyWorker.queue := by
          cases h_idle_queue_lt_busy
            rfl
        contradiction
      rfl

end Morph.Specs.SchedulingModes
