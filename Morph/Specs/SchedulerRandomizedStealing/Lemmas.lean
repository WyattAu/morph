/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SchedulerRandomizedStealing.Spec
import Std

namespace Morph.Specs.SchedulerRandomizedStealing

/- # Lemmas for Scheduler Randomized Stealing -/

/-- Work-stealing scheduler progress: if workers exist and have tasks, progress is made -/
theorem lemmaWorkStealingSchedulerProgress (workers : List Bin) (tasks : List Ball) :
    specWorkStealingScheduler workers →
      ∀ (w : Bin),
        w ∈ workers →
          w.balls.length > 0 ∨
            ∃ (w' : Bin),
              w' ∈ workers ∧
              w'.balls.length > 0 := by
  intro h_spec w h_w_in
  unfold specWorkStealingScheduler at h_spec
  intro w h_w_in
  by_cases h_w.balls.length_gt_0
  case h_gt_0 => exact h_gt_0
  case h_le_0 =>
    have h_exists_busy : ∃ (w' : Bin), w' ∈ workers ∧ w'.balls.length > 0 := by
      have h_w'_in : w' ∈ workers := by
      have h_w'_gt_0 : w'.balls.length > 0 := by
      exists w'
      constructor
        · exact h_w'_in
        · exact h_w'_gt_0
    exact h_exists_busy

/-- Work-stealing scheduler termination: all workers eventually complete their tasks -/
theorem lemmaWorkStealingSchedulerTermination (workers : List Bin) (tasks : List Ball) :
    specWorkStealingScheduler workers →
      ∀ (w : Bin),
        w ∈ workers →
          w.balls.length = 0 := by
  intro h_spec w h_w_in
  unfold specWorkStealingScheduler at h_spec
  intro w h_w_in
  have h_all_empty : ∀ (w' : Bin), w' ∈ workers → w'.balls.length = 0 := by
    intro w' h_w'_in
    have h_w'_empty : w'.balls.length = 0 := by
      cases h_w'_in
      | intro h_w'_eq
        rw [h_w'_eq]
      | intro h_w'_ne
        contradiction
  have h_w_empty : w.balls.length = 0 := by
    cases h_w_in
    rfl
  exact h_all_empty w h_w_empty

/-- Balls-into-bins completeness: every ball is placed in exactly one bin -/
theorem lemmaBallsIntoBinsComplete (balls : List Ball) (bins : List Bin) :
    specBallsIntoBinsAlgorithm balls bins →
      ∀ (b : Ball),
        b ∈ balls →
        ∃ (bin : Bin),
          bin ∈ bins ∧
          b ∈ bin.balls := by
  intro h_spec b h_b
  unfold specBallsIntoBinsAlgorithm at h_spec
  cases h_spec
  | intro bin h_bin_in h_b_in_bin
    exact bin
      constructor
      · exact h_bin_in
      · exact h_b_in_bin

/-- Balls-into-bins balance: distribution is nearly balanced -/
theorem lemmaBallsIntoBinsBalanced (balls : List Ball) (bins : List Bin) :
    specBallsIntoBinsAlgorithm balls bins →
    let avgBalls := balls.length / bins.length
    ∀ (bin : Bin),
      bin ∈ ballsIntoBinsAlgorithm balls bins →
        |bin.balls.length - avgBalls| ≤ 1 := by
  intro h_spec bin h_bin_in
  unfold specBallsIntoBinsAlgorithm at h_bin_in
  unfold ballsIntoBinsAlgorithm at h_bin_in
  have h_avg_eq : avgBalls = balls.length / bins.length := by
    rfl
  have h_count_eq : (bins.map (·.balls.length)).sum = balls.length := by
    have h_count_sum_eq : (balls.map (fun bin => (bin.balls.filter (fun b => b ∈ balls)).length)).sum =
      (bins.map (·.balls)).sum := by
      have h_filter_eq : ∀ (bin : Bin), bin ∈ ballsIntoBinsAlgorithm balls bins →
        (bin.balls.filter (fun b => b ∈ balls)).length = bin.balls.length := by
        intro bin h_bin_in
        unfold ballsIntoBinsAlgorithm at h_bin_in
        unfold ballsIntoBinsAlgorithm at h_bin_in
        have h_all_balls_in_bin : ∀ (b : Ball), b ∈ balls → b ∈ bin.balls := by
          intro b h_b_in
          exact h_b_in
        have h_filter_eq : bin.balls.filter (fun b => b ∈ balls) = bin.balls := by
          apply List.filter_eq_self.mpr
          intro b h_b_in_bin
          exact h_all_balls_in_bin b h_b_in_bin
      have h_sum_eq : (bins.map (fun bin => (bin.balls.filter (fun b => b ∈ balls)).length)).sum =
        (bins.map (·.balls)).sum := by
        rw [← h_filter_eq]
      have h_sum_eq_avg : (bins.map (·.balls.length)).sum = balls.length := by
        rw [h_count_eq, h_sum_eq, h_avg_eq]
    have h_bin_count : bin.balls.length = (bins.map (fun b' => (b'.balls.filter (fun b => b ∈ balls)).length)[bin.id] := by
      apply List.length_map
      intro b'
      apply List.mem_of_mem_filter
      exact h_all_balls_in_bin b h_bin_in
    have h_diff_le : |bin.balls.length - avgBalls| ≤ 1 := by
    rw [h_bin_count, h_avg_eq]
      apply Nat.le_of_add_right
      apply Nat.abs_sub_le_self
      apply Nat.div_le_self
      rfl

/-- Convergence bounds: maximum imbalance decreases exponentially -/
theorem lemmaConvergenceBounds (workers : List Bin) (k : Nat) :
    specConvergenceBounds workers k →
    ∀ (workers' : List Bin),
      workers' = workers →
        maxImbalance workers' ≤ convergenceBound workers' k := by
  intro h_spec workers' h_eq
  unfold specConvergenceBounds at h_spec
  rw [h_eq]
  intro workers'
  unfold convergenceBound at workers'
  unfold maxImbalance at workers'
  unfold minQueueLength at workers'
  have h_max : maxImbalance workers' = (workers'.map (·.balls.length)).getD 0 0 >.max := by
    rfl
  have h_min : minQueueLength workers' = (workers'.map (·.balls.length)).getD 0 0 >.min := by
    rfl
  have h_bound : convergenceBound workers' k = Nat.ceil (workers'.length / (k + 1)) := by
    rfl
  have h_diff_le : h_max - h_min ≤ h_bound := by
    have h_diff_eq : (workers'.length / (k + 1)) - 1 ≤ h_bound := by
      have h_div_eq : workers'.length / (k + 1) - 1 = workers'.length - workers'.length / (k + 1) := by
        rw [Nat.sub_sub_self]
      have h_div_le : workers'.length - workers'.length / (k + 1) = (workers'.length * (k + 1) - workers'.length) / (k + 1) := by
        rw [Nat.mul_sub_right, Nat.mul_sub_left]
      have h_div_le_bound : (workers'.length - workers'.length / (k + 1)) ≤ h_bound := by
        rw [h_div_eq]
        apply Nat.div_le_self
        rfl
    have h_diff_le_bound : h_max - h_min ≤ h_bound := by
      rw [h_diff_le, h_diff_le_bound]
    exact h_diff_le_bound

/-- Balanced system: all workers have equal or nearly equal queues -/
theorem lemmaBalancedSystem (workers : List Bin) :
    isBalanced workers →
      ∀ (w1 w2 : Bin),
        w1 ∈ workers ∧
        w2 ∈ workers →
          |w1.balls.length - w2.balls.length| ≤ 1 := by
  intro h_balanced w1 w2 h_w1_in h_w2_in
  unfold isBalanced at h_balanced
  intro w1 w2
  have h_diff : |w1.balls.length - w2.balls.length| ≤ 1 := by
    have h_max : max w1.balls.length w2.balls.length = w1.balls.length := by
      cases h_diff
      | h_ge => exact h_ge
      | h_le => exact h_le
    have h_abs_diff : |w1.balls.length - w2.balls.length| = w1.balls.length - w2.balls.length := by
      rw [h_max]
    have h_diff_le_1 : |w1.balls.length - w2.balls.length| ≤ 1 := by
      rw [h_diff_le_1]
    exact h_diff

/-- Fairness: workload is balanced across workers -/
theorem lemmaFairness (workers : List Bin) (tasks : List Ball) :
    isFair workers tasks →
      ∀ (w : Bin),
        w ∈ workers →
        |w.balls.length - totalWorkload workers tasks| ≤ totalWorkload workers tasks := by
  intro h_fairness w h_w_in
  unfold isFair at h_fairness
  intro w h_w_in
  have h_workload : w.balls.length = (w.balls.map (·.workload)).sum := by
    rfl
  have h_total_workload : totalWorkload workers tasks := by
    rfl
  have h_avg_workload : h_total_workload / workers.length := by
    rfl
  have h_diff_le : |w.balls.length - h_avg_workload| ≤ h_avg_workload := by
    rw [h_workload, h_avg_workload]
    apply Nat.le_of_add_right
      apply Nat.div_le_self
      rfl

end Morph.Specs.SchedulerRandomizedStealing
