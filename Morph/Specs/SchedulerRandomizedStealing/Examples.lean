/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulerRandomizedStealing.Spec

namespace Morph.Specs.SchedulerRandomizedStealing.Examples

/- # Examples for Scheduler Randomized Stealing -/

/-- Example workers for work-stealing scheduler -/
def exampleWorkers : List Bin :=
  [{ id := 0, balls := [{ id := 0 }, { id := 1 }, { id := 2 }, { id := 3 } }]

/-- Example tasks for distribution -/
def exampleTasks : List Ball :=
  [{ id := 0 }, { id := 1 }, { id := 2 }, { id := 3 }, { id := 4 }, { id := 5 } ]

/-- Example bins after balls-into-bins algorithm -/
def exampleBins : List Bin :=
  ballsIntoBinsAlgorithm exampleTasks exampleWorkers

/-- Verify work-stealing scheduler: idle worker can steal from busy worker -/
example verifyWorkStealingScheduler : specWorkStealingScheduler exampleWorkers := by
  unfold specWorkStealingScheduler
  constructor
  · rfl
  · constructor
    rfl
  · rfl
  · rfl

/-- Verify balls-into-bins algorithm: each ball is in exactly one bin -/
example verifyBallsIntoBinsAlgorithm : specBallsIntoBinsAlgorithm exampleTasks exampleBins := by
  unfold specBallsIntoBinsAlgorithm
  intro b h_b_in_bins
  unfold ballsIntoBinsAlgorithm at h_b_in_bins
  have h_ball_in_bin : ∃ (bin : Bin), bin ∈ h_b_in_bins ∧ b ∈ bin.balls := by
    intro b h_bin_in_bin
    exact h_bin_in_bin
  constructor
    · exact h_bin_in_bin.1
    · exact h_bin_in_bin.2

/-- Verify balls-into-bins completeness: every ball is in exactly one bin -/
example verifyBallsIntoBinsComplete : specBallsIntoBinsComplete exampleTasks exampleBins := by
  unfold specBallsIntoBinsComplete
  intro b h_complete
  unfold specBallsIntoBinsAlgorithm at h_complete
  have h_unique_bin : ∀ (b : Bin), b ∈ exampleBins →
    ∃! (uniqueBin : Bin), uniqueBin ∈ exampleBins ∧ b ∈ uniqueBin.balls ∧ b = uniqueBin := by
    intro b h_b_in_bins
    unfold specBallsIntoBinsAlgorithm at h_b_in_bins
    have h_ball_in_bin : ∃ (bin : Bin), bin ∈ h_b_in_bins ∧ b ∈ bin.balls := by
      intro b h_bin_in_bin
      exact h_bin_in_bin
    intro uniqueBin h_unique
    have h_unique_in_bins : uniqueBin ∈ exampleBins ∧ b ∈ uniqueBin.balls ∧ b = uniqueBin := by
      constructor
      · exact h_unique.1
      · exact h_unique.2
      · exact h_unique.3
    constructor
      · exact h_unique
    exact h_unique

/-- Verify balls-into-bins balance: maximum deviation from average is bounded by 1 -/
example verifyBallsIntoBinsBalanced : specBallsIntoBinsBalanced exampleTasks exampleBins := by
  unfold specBallsIntoBinsBalanced
  intro b h_balanced
  unfold specBallsIntoBinsAlgorithm at h_balanced
  have h_avg : exampleTasks.length / exampleBins.length := by
    rfl
  have h_max_deviation : ∀ (bin : Bin),
    bin ∈ ballsIntoBinsAlgorithm exampleTasks exampleBins →
      |bin.balls.length - h_avg| ≤ 1 := by
    intro bin h_bin_in_bins
    unfold ballsIntoBinsAlgorithm at h_bin_in_bins
    have h_count_eq : bin.balls.length = exampleTasks.length := by
      rfl
    have h_deviation_le_1 : |bin.balls.length - h_avg| ≤ 1 := by
      rw [h_count_eq, h_avg]
      apply Nat.abs_sub_le_self
    constructor
      · exact h_deviation_le_1

/-- Verify convergence bounds: maximum imbalance decreases exponentially -/
example verifyConvergenceBounds : specConvergenceBounds exampleWorkers 2 := by
  unfold specConvergenceBounds
  constructor
  · rfl
  · rfl
  intro k h_k
  unfold convergenceBound at exampleWorkers
  have h_bound : Nat.ceil (exampleWorkers.length / (k + 1)) := by
    rfl
  have h_max_imbalance : maxImbalance exampleWorkers = 2 := by
    rfl
  have h_imbalance_le_bound : h_max_imbalance ≤ h_bound := by
    constructor
    · exact h_imbalance_le_bound

/-- Verify balanced system: all workers have equal or nearly equal queues -/
example verifyBalancedSystem : isBalanced exampleWorkers := by
  unfold isBalanced
  intro w1 w2 h_w1_in h_w2_in
  constructor
  · rfl
  · rfl
  · rfl
  constructor
    · rfl
  · rfl

/-- Verify fairness: workload is balanced across workers -/
example verifyFairness : isFair exampleWorkers exampleTasks := by
  unfold isFair at h_fairness
  constructor
  · rfl
  · rfl
  intro w h_w_in
  have h_workload : w.balls.length = (w.map (·.workload)).sum := by
    rfl
  have h_avg_workload : h_workload / exampleWorkers.length := by
    rfl
  have h_diff_le : |w.balls.length - h_avg_workload| ≤ h_avg_workload := by
    constructor
      · exact h_workload
      · exact h_diff_le
      · rfl
  constructor
    · exact h_diff_le

/-- Verify work-stealing scheduler can balance load -/
example verifyWorkStealingCanBalance : ∀ (workers : List Bin) (idleWorker busyWorker : Bin),
    idleWorker ∈ workers ∧
    busyWorker ∈ workers ∧
    idleWorker.balls.length = 0 ∧
    busyWorker.balls.length > 0 →
      ∃ (task : Ball),
        task ∈ busyWorker.balls ∧
        task ∉ idleWorker.balls := by
  intro workers idleWorker busyWorker h_idle_empty h_busy_gt_0
  unfold isBalanced at workers
  have h_total_balls : idleWorker.balls.length + busyWorker.balls.length = 2 := by
    rfl
  have h_total_tasks : exampleTasks.length = 5 := by
    rfl
  have h_avg_balls : h_total_balls / workers.length = 2 := by
    rfl
  have h_idle_avg : idleWorker.balls.length / workers.length = 0 := by
    rfl
  have h_busy_avg : busyWorker.balls.length / workers.length = 1 := by
    rfl
  have h_busy_has_task : busyWorker.balls.length > 0 := by
      rfl
  have h_busy_can_give : h_busy_avg ≤ h_avg_balls := by
      rw [h_busy_avg, h_avg_balls]
    have h_task_exists : ∃ (task : Ball), task ∈ busyWorker.balls := by
    cases h_busy_has_task
    | [] => contradiction
    | t :: rest =>
      exists t
      constructor
      · rfl
      · rfl
      constructor
    · exact h_task_exists

end Morph.Specs.SchedulerRandomizedStealing.Examples
