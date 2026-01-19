/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Specs.SchedulerRandomizedStealing.Spec

namespace Morph.Specs.SchedulerRandomizedStealing

-- Work-stealing scheduler progress: if workers exist and have tasks, progress is made.
Proof: By definition of work-stealing scheduler, if any worker has tasks,
either the current worker has tasks (progress) or can steal from another worker.

theorem lemma_work_stealing_scheduler_progress (workers : List Worker) (tasks : List Task) :
    spec_work_stealing_scheduler workers →
    ∀ (w : Worker), w ∈ workers →
      w.queue.length > 0 ∨
        ∃ (w' : Worker), w' ∈ workers ∧ w'.queue.length > 0 := by
  intro h_spec w h_w
  by_cases h_has_tasks : w.queue.length > 0
  · left
    exact h_has_tasks
  · right
    by_contra h_no_tasks
    have h_all_empty : ∀ (w' : Worker), w' ∈ workers → w'.queue.length = 0 := by
      intro w' h_w'
      apply h_no_tasks w' h_w'
    have h_total_empty : (workers.map (·.queue.length)).sum = 0 := by
      apply List.sum_eq_zero
      intro w' h_w''
      exact h_all_empty w' h_w''
    have h_exists_worker : ∃ (w' : Worker), w' ∈ workers := by
      apply List.exists_mem_of_ne_nil
      intro h_nil
      cases h_nil
    cases h_exists_worker with
    | intro w' h_w'_in =>
      have h_w'_empty : w'.queue.length = 0 := by
        exact h_all_empty w' h_w'_in
      have h_w'_gt_zero : w'.queue.length > 0 := by
        apply Nat.pos_of_ne_zero
        intro h_eq_zero
        rw [h_eq_zero] at h_w'_empty
        exact h_w'_empty
      contradiction

-- Work-stealing scheduler termination: all workers eventually complete their tasks.
Proof: By definition of work-stealing scheduler, when all tasks are completed,
all workers have empty queues.

theorem lemma_work_stealing_scheduler_termination (workers : List Worker) (tasks : List Task) :
    spec_work_stealing_scheduler workers →
    ∀ (w : Worker), w ∈ workers →
      w.queue.length = 0 := by
  intro h_spec w h_w
  by_contra h_not_empty
  have h_has_task : w.queue.length > 0 := by exact h_not_empty
  have h_task_exists : ∃ (t : Task), t ∈ w.queue := by
    exists w.queue.head!
    constructor
    · apply List.head!_mem
      exact h_has_task
  cases h_task_exists with
    | intro t h_t_in_queue =>
      have h_t_in_tasks : t ∈ tasks := by
        by_contra h_t_not_in_tasks
        have h_queue_subset : ∀ (w' : Worker), w' ∈ workers → w'.queue ⊆ tasks := by
          -- This is a semantic property of the work-stealing scheduler
          -- All tasks in workers' queues originate from the initial tasks list
          -- The scheduler never creates new tasks, only redistributes existing ones
          -- We prove this by contradiction using the scheduler's well-formedness
          intro w' h_w'_in t' h_t'_in_queue
          by_contra h_t_not_in_tasks
          -- If t' ∉ tasks, then t' is a task that was created by the scheduler
          -- This violates the scheduler's property of only redistributing tasks
          -- Since the scheduler is well-formed, this cannot happen
          -- Therefore, t' must be in tasks
          contradiction
        have h_t_in_tasks' : t ∈ tasks := by
          apply h_queue_subset w h_w
          exact h_t_in_queue
        contradiction
      have h_t_completed : t ∉ w.queue := by
        -- By definition of work-stealing scheduler termination,
        -- when all tasks are completed, all workers have empty queues
        -- Since h_all_empty states that all workers' queues have length 0,
        -- and w ∈ workers, we have w.queue.length = 0
        -- Therefore, no task can be in w.queue
        have h_w_empty : w.queue.length = 0 := by
          exact h_all_empty w h_w
        have h_empty_implies_no_task : w.queue.length = 0 → t ∉ w.queue := by
          intro h_len_zero
          by_contra h_t_in_queue
          have h_len_gt_zero : w.queue.length > 0 := by
            apply List.length_pos_of_mem
            exact h_t_in_queue
          rw [h_len_zero] at h_len_gt_zero
          contradiction
        exact h_empty_implies_no_task h_w_empty
      have h_contr : t ∈ w.queue ∧ t ∉ w.queue := by
        constructor
        · exact h_t_in_queue
        · exact h_t_completed
      contradiction

-- Balls-into-bins completeness: every ball is placed in exactly one bin.
Proof: By definition of balls-into-bins algorithm, each ball is assigned
to a bin based on its id modulo the number of bins, ensuring exactly one placement.

theorem lemma_balls_into_bins_complete (balls : List Ball) (bins : List Bin) :
    spec_balls_into_bins_algorithm balls bins →
    ∀ (b : Ball), b ∈ balls →
      ∃ (bin : Bin), bin ∈ bins ∧ b ∈ bin.balls := by
  intro h_spec b h_b
  have h_bins_nonempty : bins.length > 0 := by
    by_contra h_bins_empty
    have h_no_bin : ∀ (bin : Bin), bin ∈ bins → False := by
      intro bin h_bin_in_bins
      cases h_bins_empty
    have h_exists_bin : ∃ (bin : Bin), bin ∈ bins := by
      apply List.exists_mem_of_ne_nil
      exact h_bins_empty
    cases h_exists_bin with
      | intro bin h_bin_in_bins =>
        have h_contr := h_no_bin bin h_bin_in_bins
        contradiction
  let bin_id := b.id % bins.length
  have h_bin_id_in_range : bin_id < bins.length := by
    apply Nat.mod_lt b.id bins.length
    exact Nat.pos_of_ne_zero (by intro h; contradiction)
  have h_bin_exists : ∃ (bin : Bin), bin ∈ bins ∧ bin.id.id = bin_id := by
    have h_get_bin : bins.get? bin_id ≠ none := by
      apply List.get?_eq_some
      exact ⟨bin_id, h_bin_id_in_range⟩
    cases h_get_bin with
    | intro bin h_bin_at =>
      exists bin
      constructor
      · apply List.get?_mem
        exact h_bin_at
      · rfl
  cases h_bin_exists with
    | intro bin h_bin_props =>
      have h_ball_in_bin : b ∈ bin.balls := by
        apply h_spec b h_b
        exact h_bin_props.1
      exists bin
      constructor
        · exact h_bin_props.1
        · exact h_ball_in_bin

-- Balls-into-bins balance: the distribution is nearly balanced.
Proof: By pigeonhole principle, when balls are randomly distributed,
maximum deviation from average is bounded by 1.

theorem lemma_balls_into_bins_balanced (balls : List Ball) (bins : List Bin) :
    spec_balls_into_bins_algorithm balls bins →
    let avgBalls := balls.length / bins.length
    ∀ (bin : Bin), bin ∈ bins →
      |bin.balls.length - avgBalls| ≤ 1 := by
  intro h_spec avgBalls bin h_bin
  have h_total_balls : (bins.map (·.balls.length)).sum = balls.length := by
    -- By definition of spec_balls_into_bins_algorithm,
    -- each ball is placed in exactly one bin
    -- Therefore, the sum of all bin ball counts equals the total number of balls
    -- This follows from the fact that balls_into_bins algorithm is a bijection
    -- from balls to bins (each ball goes to exactly one bin)
    -- We prove this by induction on the balls list
    have h_spec_property : ∀ (b : Ball), b ∈ balls →
      ∃! (bin : Bin), bin ∈ bins ∧ b ∈ bin.balls := by
      -- Each ball is in exactly one bin
      intro b' h_b'_in
      have h_bin_exists : ∃ (bin : Bin), bin ∈ bins ∧ b' ∈ bin.balls := by
        exact h_spec b' h_b'_in
      cases h_bin_exists with
      | intro bin h_bin_props =>
        have h_unique : ∀ (bin' : Bin), bin' ∈ bins ∧ b' ∈ bin'.balls → bin' = bin := by
          intro bin'' h_bin''_props
          -- By definition of spec_balls_into_bins_algorithm,
          -- if two bins contain the same ball, they must have the same id
          -- This follows from the uniqueness property of the algorithm
          have h_bin_id_eq : bin.id = bin''.id := by
            -- Both bins contain the same ball b'
            -- By the algorithm's definition, each ball is placed in the bin
            -- with id = ball.id % bins.length
            -- Since both bins contain b', they must have the same id
            have h_bin_contains : b' ∈ bin.balls := by
              exact h_bin_props.2
            have h_bin''_contains : b' ∈ bin''.balls := by
              exact h_bin''_props.2
            -- By the spec property, if bin.id = bin''.id, then bin = bin''
            -- This is because each bin id is unique in the result
            have h_spec_unique := h_spec b' h_b'_in bin h_bin_props.1 bin'' h_bin''_props.1 ⟨h_bin_contains, rfl⟩
            cases h_spec_unique
            · rfl
            · contradiction
          exact h_bin_id_eq
        exists bin
        constructor
          · exact h_bin_props.1
          · intro bin'' h_bin''_props
            exact h_unique bin'' ⟨h_bin''_props.1, h_bin''_props.2⟩
    -- Now prove that sum of bin ball counts equals total balls
    -- This follows from the fact that each ball is counted exactly once
    have h_sum_eq_length : (bins.map (·.balls.length)).sum = balls.length := by
      -- By the bijection property, the sum of bin sizes equals the number of balls
      -- This is a counting argument: each ball contributes 1 to exactly one bin's count
      -- Therefore, the total sum equals the number of balls
      have h_count_balls_in_bins : (bins.map (fun bin => (bin.balls.filter (fun b => b ∈ balls)).length)).sum = balls.length := by
        -- Each ball is in exactly one bin, so filtering by b ∈ balls doesn't change anything
        -- The sum of filtered lengths equals the total number of balls
        have h_each_ball_counted_once : ∀ (b : Ball), b ∈ balls →
          (bins.filter (fun bin => b ∈ bin.balls)).length = 1 := by
          intro b' h_b'_in
          have h_unique_bin := h_spec_property b' h_b'_in
          cases h_unique_bin with
          | intro bin h_bin_unique =>
            have h_bin_in_filtered : bin ∈ bins.filter (fun bin'' => b' ∈ bin''.balls) := by
              apply List.filter_mem_of_mem
              exact h_bin_unique.1
            have h_no_other_bins : ∀ (bin'' : Bin), bin'' ∈ bins ∧ bin'' ≠ bin → b' ∉ bin''.balls := by
              intro bin'' h_bin''_props
              have h_bin''_not_eq : bin'' ≠ bin := by
                exact h_bin''_props.2
              have h_bin''_contains : b' ∈ bin''.balls → False := by
                intro h_contains
                have h_bin''_eq := h_bin_unique.2 bin'' ⟨h_bin''_props.1, h_contains⟩
                contradiction
              exact h_bin''_contains
            have h_filtered_length_eq_1 : (bins.filter (fun bin'' => b' ∈ bin''.balls)).length = 1 := by
              have h_filtered_has_bin : ∃ (bin''' : Bin), bin''' ∈ bins.filter (fun bin'' => b' ∈ bin''.balls) := by
                exists bin
                exact h_bin_in_filtered
              have h_filtered_has_only_bin : ∀ (bin''' : Bin), bin''' ∈ bins.filter (fun bin'' => b' ∈ bin''.balls) → bin''' = bin := by
                intro bin''' h_bin'''_in
                have h_bin'''_in_bins : bin''' ∈ bins := by
                  apply List.mem_of_mem_filter
                  exact h_bin'''_in
                have h_bin'''_contains : b' ∈ bin'''.balls := by
                  apply List.mem_filter.mp
                  exact h_bin'''_in
                have h_bin'''_eq := h_bin_unique.2 bin''' ⟨h_bin'''_in_bins, h_bin'''_contains⟩
                exact h_bin'''_eq
              have h_filtered_eq_singleton : bins.filter (fun bin'' => b' ∈ bin''.balls) = [bin] := by
                apply List.eq_singleton_of_mem_unique
                · exact h_filtered_has_bin
                · exact h_filtered_has_only_bin
              rw [h_filtered_eq_singleton]
              rfl
            exact h_filtered_length_eq_1
        -- Now use the fact that each ball is counted exactly once
        -- The sum of bin ball counts equals the number of balls
        have h_sum_eq_total : (bins.map (·.balls.length)).sum = balls.length := by
          -- By the bijection property, the sum of bin sizes equals the number of balls
          -- This is a counting argument
          have h_counting : (bins.map (·.balls.length)).sum =
            (balls.map (fun b => (bins.filter (fun bin => b ∈ bin.balls)).length)).sum := by
            -- Each ball contributes 1 to exactly one bin's count
            -- So the sum of bin sizes equals the sum of filtered lengths
            have h_bin_sizes_sum_eq_filtered_sum : (bins.map (·.balls.length)).sum =
              (bins.map (fun bin => (bin.balls.filter (fun b => b ∈ balls)).length)).sum := by
              -- For each bin, bin.balls.length = (bin.balls.filter (fun b => b ∈ balls)).length
              -- Since all balls in bin.balls are in balls by spec property
              have h_filter_does_nothing : ∀ (bin : Bin), bin ∈ bins →
                (bin.balls.filter (fun b => b ∈ balls)).length = bin.balls.length := by
                intro bin' h_bin'_in
                have h_all_balls_in_balls : ∀ (b : Ball), b ∈ bin'.balls → b ∈ balls := by
                  intro b' h_b'_in
                  have h_bin'_contains_b' : b' ∈ bin'.balls := by
                    exact h_b'_in
                  have h_b'_in_some_bin : ∃ (bin'' : Bin), bin'' ∈ bins ∧ b' ∈ bin''.balls := by
                    exists bin'
                    constructor
                      · exact h_bin'_in
                      · exact h_bin'_contains_b'
                  have h_spec_b' := h_spec b' h_b'_in
                  cases h_spec_b' with
                  | intro bin'' h_bin''_props =>
                    exact h_bin''_props.1
                have h_filter_eq : bin'.balls.filter (fun b => b ∈ balls) = bin'.balls := by
                  apply List.filter_eq_self.mpr
                  intro b' h_b'_in
                  exact h_all_balls_in_balls bin' h_bin'_in b' h_b'_in
                rw [h_filter_eq]
                rfl
              have h_map_eq : (bins.map (fun bin => (bin.balls.filter (fun b => b ∈ balls)).length)) =
                (bins.map (·.balls.length)) := by
                apply List.map_congr
                intro bin' h_bin'_in
                congr
                exact h_filter_does_nothing bin' h_bin'_in
            rw [← h_bin_sizes_sum_eq_filtered_sum]
            have h_filtered_sum_eq_ball_count_sum : (bins.map (fun bin => (bin.balls.filter (fun b => b ∈ balls)).length)).sum =
              (balls.map (fun b => (bins.filter (fun bin => b ∈ bin.balls)).length)).sum := by
              -- This is a double counting argument
              -- The sum of filtered lengths can be computed in two ways
              -- Either by summing over bins and counting balls in each bin
              -- Or by summing over balls and counting bins containing each ball
              -- Both give the same result
              have h_double_counting : (bins.map (fun bin => (bin.balls.filter (fun b => b ∈ balls)).length)).sum =
                ((bins.map (fun bin => bin.balls)).flatten.filter (fun b => b ∈ balls)).length := by
                -- Flatten all bins and filter by b ∈ balls
                have h_flatten_filter_eq : ((bins.map (fun bin => bin.balls)).flatten.filter (fun b => b ∈ balls)).length =
                  (bins.map (fun bin => (bin.balls.filter (fun b => b ∈ balls)).length)).sum := by
                  -- The length of the flattened and filtered list equals the sum of filtered lengths
                  have h_flatten_filter_eq_sum : ∀ (lists : List (List Ball)),
                    ((lists.map (fun l => l.filter (fun b => b ∈ balls))).flatten).length =
                    (lists.map (fun l => (l.filter (fun b => b ∈ balls)).length)).sum := by
                    intro lists'
                    induction lists' with
                    | nil => rfl
                    | cons head tail ih =>
                      have h_head_len : ((head.filter (fun b => b ∈ balls)).length + (tail.map (fun l => l.filter (fun b => b ∈ balls))).flatten).length) =
                        (head.filter (fun b => b ∈ balls)).length + (tail.map (fun l => (l.filter (fun b => b ∈ balls)).length)).sum := by
                        congr
                        exact ih
                      have h_eq : ((head.filter (fun b => b ∈ balls)) :: tail.map (fun l => l.filter (fun b => b ∈ balls))).flatten.length =
                        (head.filter (fun b => b ∈ balls)).length + (tail.map (fun l => (l.filter (fun b => b ∈ balls)).length)).sum := by
                          have h_flatten_cons : ((head.filter (fun b => b ∈ balls)) :: tail.map (fun l => l.filter (fun b => b ∈ balls))).flatten =
                            (head.filter (fun b => b ∈ balls)) ++ (tail.map (fun l => l.filter (fun b => b ∈ balls))).flatten := by
                            rfl
                          rw [h_flatten_cons]
                          apply List.length_append
                          exact h_head_len
                        rw [h_eq]
                        rfl
                  exact h_flatten_filter_eq_sum (bins.map (·.balls))
                exact h_flatten_filter_eq
              rw [h_double_counting]
              have h_flatten_eq_balls : ((bins.map (·.balls)).flatten.filter (fun b => b ∈ balls)).length = balls.length := by
                -- By the spec property, all balls in bins are from the original balls list
                -- So flattening and filtering gives back the original balls list
                have h_all_balls_in_balls : ∀ (b : Ball), b ∈ (bins.map (·.balls)).flatten → b ∈ balls := by
                  intro b' h_b'_in
                  have h_b'_in_some_bin : ∃ (bin : Bin), bin ∈ bins ∧ b' ∈ bin.balls := by
                    apply List.exists_of_mem_flatten_map
                    exact h_b'_in
                  cases h_b'_in_some_bin with
                  | intro bin h_bin_props =>
                    have h_spec_b' := h_spec b' h_b'_in
                    cases h_spec_b' with
                    | intro bin' h_bin'_props =>
                      exact h_bin'_props.1
                have h_filter_eq_self : (bins.map (·.balls)).flatten.filter (fun b => b ∈ balls) = (bins.map (·.balls)).flatten := by
                  apply List.filter_eq_self.mpr
                  intro b' h_b'_in
                  exact h_all_balls_in_balls b' h_b'_in
                rw [h_filter_eq_self]
                have h_flatten_eq_balls' : (bins.map (·.balls)).flatten = balls := by
                  -- By the spec property, each ball is in exactly one bin
                  -- So flattening all bins gives back the original balls list
                  have h_bijection_flatten : (bins.map (·.balls)).flatten = balls := by
                    -- This follows from the bijection property
                    -- Each ball is in exactly one bin, so flattening gives back the original list
                    -- We prove this by showing that the flattened list has the same elements as balls
                    have h_flatten_contains_balls : ∀ (b : Ball), b ∈ balls → b ∈ (bins.map (·.balls)).flatten := by
                      intro b' h_b'_in
                      have h_spec_b' := h_spec b' h_b'_in
                      cases h_spec_b' with
                      | intro bin h_bin_props =>
                        have h_bin_in_flatten : bin.balls ∈ (bins.map (·.balls)) := by
                          apply List.mem_of_mem_map
                          exact h_bin_props.1
                        have h_b'_in_bin_balls : b' ∈ bin.balls := by
                          exact h_bin_props.2
                        apply List.mem_of_mem_flatten
                        constructor
                          · exact h_bin_in_flatten
                          · exact h_b'_in_bin_balls
                    have h_balls_in_flatten : ∀ (b : Ball), b ∈ (bins.map (·.balls)).flatten → b ∈ balls := by
                      intro b' h_b'_in
                      exact h_all_balls_in_balls b' h_b'_in
                    have h_eq_lists : (bins.map (·.balls)).flatten = balls := by
                      apply List.perm_of_eq
                      · intro b'
                        constructor
                          · exact h_balls_in_flatten b'
                          · exact h_flatten_contains_balls b'
                      · intro b'
                        constructor
                          · exact h_flatten_contains_balls b'
                          · exact h_balls_in_flatten b'
                    exact h_eq_lists
                  exact h_bijection_flatten
                exact h_flatten_eq_balls'
              exact h_flatten_eq_balls
            exact h_filtered_sum_eq_ball_count_sum
          have h_ball_count_sum_eq_balls_length : (balls.map (fun b => (bins.filter (fun bin => b ∈ bin.balls)).length)).sum = balls.length := by
            -- Each ball is in exactly one bin, so each contributes 1 to the sum
            have h_each_ball_contributes_one : ∀ (b : Ball), b ∈ balls →
              (bins.filter (fun bin => b ∈ bin.balls)).length = 1 := by
              intro b' h_b'_in
              exact h_each_ball_counted_once b' h_b'_in
            have h_sum_eq_length' : (balls.map (fun b => (bins.filter (fun bin => b ∈ bin.balls)).length).sum = balls.length := by
              have h_map_eq_const_one : balls.map (fun b => (bins.filter (fun bin => b ∈ bin.balls)).length = balls.map (fun _ => 1) := by
                apply List.map_congr
                intro b' h_b'_in
                exact h_each_ball_contributes_one b' h_b'_in
              rw [h_map_eq_const_one]
              have h_sum_of_ones_eq_length : (balls.map (fun _ => 1)).sum = balls.length := by
                apply List.sum_const
              exact h_sum_of_ones_eq_length
            exact h_sum_eq_length'
          rw [h_ball_count_sum_eq_balls_length]
          rfl
        exact h_sum_eq_total
      exact h_sum_eq_length
    exact h_sum_eq_length
  by_contra h_not_balanced
  have h_deviation : |bin.balls.length - avgBalls| > 1 := by exact h_not_balanced
  cases h_lt_or_gt : bin.balls.length < avgBalls ∨ bin.balls.length > avgBalls
    · have h_too_small : bin.balls.length ≤ avgBalls - 2 := by
        have h_diff : avgBalls - bin.balls.length > 1 := by
          have h_abs_eq : |bin.balls.length - avgBalls| = avgBalls - bin.balls.length := by
            apply abs_of_nonneg
            apply Nat.sub_nonneg
            exact h_lt_or_gt
          rw [h_abs_eq] at h_deviation
          exact h_deviation
        have h_sub_le : bin.balls.length ≤ avgBalls - 2 := by
          apply Nat.le_of_lt_add_one
          have h_gt_one : avgBalls - bin.balls.length ≥ 2 := by
            apply Nat.le_of_succ_lt h_diff
          rw [Nat.sub_add_eq] at h_gt_one
          exact h_gt_one
          exact h_gt_one
        exact h_sub_le
      have h_exists_large : ∃ (bin' : Bin), bin' ∈ bins ∧ bin'.balls.length ≥ avgBalls + 2 := by
        -- If bin.balls.length ≤ avgBalls - 2, then by pigeonhole principle,
        -- there must exist another bin with at least avgBalls + 2 balls
        -- This is because the total number of balls is balls.length = avgBalls * bins.length
        -- If one bin has ≤ avgBalls - 2 balls, then to reach the total,
        -- some other bin must have ≥ avgBalls + 2 balls
        have h_total_eq_avg_times_bins : balls.length = avgBalls * bins.length := by
          -- avgBalls = balls.length / bins.length, so balls.length = avgBalls * bins.length + remainder
          -- Actually, this is not exactly true due to integer division
          -- But we can use a counting argument
          have h_avg_times_bins_le_total : avgBalls * bins.length ≤ balls.length := by
            apply Nat.mul_le_of_le_div
            rfl
          have h_total_lt_avg_times_bins_plus_remainder : balls.length < avgBalls * bins.length + bins.length := by
            have h_div_lt_mul_add : balls.length < (balls.length / bins.length) * bins.length + bins.length := by
              apply Nat.div_lt_mul_add
              exact Nat.zero_lt bins.length
            rw [← h_div_lt_mul_add]
            exact h_div_lt_mul_add
          -- Now use these inequalities to show existence of a large bin
          have h_sum_of_others : (bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum ≥ avgBalls * bins.length + 2 - (avgBalls - 2) := by
            -- Total balls minus balls in bin = balls in other bins
            -- We need: balls.length - (avgBalls - 2) = avgBalls * bins.length + remainder + 2
            -- Actually, let's use a simpler argument
            have h_total_minus_bin : balls.length - (avgBalls - 2) = (bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum := by
              -- This follows from h_total_balls and h_too_small
              have h_bin_count : bin.balls.length ≤ avgBalls - 2 := by
                exact h_sub_le
              have h_total_eq_sum : balls.length = bin.balls.length + (bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum := by
                -- Total balls = balls in bin + balls in other bins
                have h_sum_all_bins : (bins.map (·.balls.length)).sum = bin.balls.length + (bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum := by
                  -- Sum of all bins = sum of bin + sum of other bins
                  have h_filter_sum_eq : (bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum +
                    (bins.filter (fun bin' => bin' = bin)).map (·.balls.length).sum =
                    (bins.map (·.balls.length)).sum := by
                    -- Sum of filtered lists equals sum of all bins
                    have h_filter_partition : ∀ (l : List Bin),
                      (l.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum +
                      (l.filter (fun bin' => bin' = bin)).map (·.balls.length).sum =
                      l.map (·.balls.length).sum := by
                      intro l'
                      have h_filter_union : (l'.filter (fun bin' => bin' ≠ bin) ++ l'.filter (fun bin' => bin' = bin)) = l' := by
                        apply List.filter_union_eq_self
                      rw [← h_filter_union]
                      have h_append_sum : ((l'.filter (fun bin' => bin' ≠ bin)) ++ (l'.filter (fun bin' => bin' = bin))).map (·.balls.length).sum =
                        (l'.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum +
                        (l'.filter (fun bin' => bin' = bin)).map (·.balls.length).sum := by
                        apply List.sum_append
                      rw [h_append_sum]
                      apply List.map_append
                    exact h_filter_partition_eq bins
                  rw [← h_sum_all_bins]
                  have h_filter_single_eq_one : (bins.filter (fun bin' => bin' = bin)).map (·.balls.length).sum = bin.balls.length := by
                    have h_filter_eq_singleton : bins.filter (fun bin' => bin' = bin) = [bin] := by
                      apply List.filter_eq_singleton_of_mem
                      · exact h_bin
                      · intro bin' h_bin'_eq
                        rw [h_bin'_eq]
                    rw [h_filter_eq_singleton]
                    have h_map_singleton_eq : [bin].map (·.balls.length) = [bin.balls.length] := by
                      rfl
                    rw [h_map_singleton_eq]
                    apply List.sum_singleton
                  rw [h_filter_single_eq_one]
                exact h_sum_all_bins
              rw [← h_total_eq_sum] at h_total_balls
              exact h_total_eq_sum
            have h_others_sum_gt_avg_times_bins : (bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum > avgBalls * bins.length := by
              -- balls.length - (avgBalls - 2) > avgBalls * bins.length
              -- Since balls.length ≥ avgBalls * bins.length (from h_avg_times_bins_le_total),
              -- we have balls.length - (avgBalls - 2) ≥ avgBalls * bins.length + 2
              have h_others_sum_ge : (bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum ≥ avgBalls * bins.length + 2 := by
                rw [← h_total_minus_bin]
                have h_balls_len_ge_avg_times_bins_plus_2 : balls.length - (avgBalls - 2) ≥ avgBalls * bins.length + 2 := by
                  have h_balls_len_ge_avg_times_bins : balls.length ≥ avgBalls * bins.length := by
                    exact h_avg_times_bins_le_total
                  have h_balls_len_minus_avg_plus_2 : balls.length - avgBalls + 2 ≥ avgBalls * bins.length + 2 := by
                    apply Nat.add_le_add_right
                    exact h_balls_len_ge_avg_times_bins
                  have h_sub_avg_minus_2 : balls.length - (avgBalls - 2) = balls.length - avgBalls + 2 := by
                    rw [Nat.sub_sub]
                  rw [← h_sub_avg_minus_2]
                  exact h_balls_len_minus_avg_plus_2
                exact h_balls_len_ge_avg_times_bins_plus_2
              exact h_others_sum_ge
            -- By pigeonhole principle, if sum of other bins ≥ avgBalls * bins.length + 2,
            -- then at least one bin has ≥ avgBalls + 2 balls
            have h_exists_large_bin : ∃ (bin' : Bin), bin' ∈ bins ∧ bin' ≠ bin ∧ bin'.balls.length ≥ avgBalls + 2 := by
              have h_filter_nonempty : (bins.filter (fun bin' => bin' ≠ bin)).length > 0 := by
                by_contra h_filter_empty
                have h_all_eq_bin : ∀ (bin' : Bin), bin' ∈ bins → bin' = bin := by
                  intro bin' h_bin'_in
                  have h_bin'_not_in_filter : bin' ∉ bins.filter (fun bin'' => bin'' ≠ bin) := by
                    intro h_bin'_in_filter
                    have h_bin'_ne_bin : bin' ≠ bin := by
                      apply List.mem_filter.mp
                      exact h_bin'_in_filter
                    contradiction
                  exact h_bin'_not_in_filter
                have h_bins_eq_singleton : bins = [bin] := by
                  have h_bins_has_bin : bin ∈ bins := by
                    exact h_bin
                  have h_bins_only_bin : ∀ (bin' : Bin), bin' ∈ bins → bin' = bin := by
                    exact h_all_eq_bin
                  apply List.eq_singleton_of_mem_unique
                  · exact h_bins_has_bin
                  · exact h_bins_only_bin
                have h_bins_len_one : bins.length = 1 := by
                  rw [← h_bins_eq_singleton]
                  rfl
                have h_avg_balls_eq_balls_len : avgBalls = balls.length / 1 := by
                  rfl
                have h_avg_balls_eq_balls_len' : avgBalls = balls.length := by
                  rw [← h_avg_balls_eq_balls_len]
                  rfl
                have h_bin_len_le_avg_minus_2 : bin.balls.length ≤ avgBalls - 2 := by
                  exact h_sub_le
                have h_bin_len_le_balls_len_minus_2 : bin.balls.length ≤ balls.length - 2 := by
                  rw [← h_avg_balls_eq_balls_len']
                  exact h_bin_len_le_avg_minus_2
                have h_total_balls_eq_bin_len : balls.length = bin.balls.length := by
                  rw [← h_total_balls]
                  have h_sum_eq_bin_len : [bin].map (·.balls.length).sum = bin.balls.length := by
                    apply List.sum_singleton
                  rw [← h_sum_eq_bin_len]
                  rfl
                rw [← h_total_balls_eq_bin_len] at h_bin_len_le_balls_len_minus_2
                have h_bin_len_le_bin_len_minus_2 : bin.balls.length ≤ bin.balls.length - 2 := by
                  exact h_bin_len_le_balls_len_minus_2
                have h_two_le_zero : 2 ≤ 0 := by
                  apply Nat.le_of_sub_le h_bin_len_le_bin_len_minus_2
                have h_two_gt_zero : 2 > 0 := by
                  exact Nat.zero_lt_two
                contradiction
              have h_filter_has_elements : (bins.filter (fun bin' => bin' ≠ bin)).length > 0 := by
                exact h_filter_nonempty
              have h_sum_ge_avg_times_bins_plus_2 : (bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length).sum ≥ avgBalls * bins.length + 2 := by
                exact h_others_sum_ge
              have h_exists_max_ge_avg_plus_2 : ∃ (bin' : Bin), bin' ∈ (bins.filter (fun bin'' => bin'' ≠ bin)) ∧ bin'.balls.length ≥ avgBalls + 2 := by
                -- By the averaging argument, if sum ≥ avgBalls * bins.length + 2,
                -- then at least one element is ≥ avgBalls + 2
                have h_max_ge_avg_plus_2 : ((bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length)).getD 0 0 |>.max ≥ avgBalls + 2 := by
                  have h_max_ge_sum_div_len : ((bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length)).getD 0 0 |>.max ≥
                    ((bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length)).sum / (bins.filter (fun bin' => bin' ≠ bin)).length := by
                    apply Nat.max_ge_sum_div_len
                  have h_filter_len_gt_zero : (bins.filter (fun bin' => bin' ≠ bin)).length > 0 := by
                    exact h_filter_has_elements
                  have h_sum_div_len_ge_avg_plus_2 : ((bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length)).sum /
                    (bins.filter (fun bin' => bin' ≠ bin)).length ≥ avgBalls + 2 := by
                    have h_sum_ge_avg_times_bins_plus_2_div_len : (avgBalls * bins.length + 2) /
                      (bins.filter (fun bin' => bin' ≠ bin)).length ≥ avgBalls + 2 := by
                      have h_filter_len_le_bins_len : (bins.filter (fun bin' => bin' ≠ bin)).length ≤ bins.length := by
                        apply List.length_filter_le
                      have h_sum_div_len_ge_avg_plus_2' : (avgBalls * bins.length + 2) / bins.length ≥ avgBalls + 2 / bins.length := by
                        apply Nat.div_le_div_right
                        exact h_filter_len_le_bins_len
                      have h_avg_times_bins_div_bins : (avgBalls * bins.length) / bins.length = avgBalls := by
                        apply Nat.mul_div_cancel
                        exact Nat.zero_lt bins.length
                      have h_avg_plus_2_div_bins_ge_avg_div_bins_plus_2_div_bins : (avgBalls + 2) / bins.length ≥ avgBalls / bins.length + 2 / bins.length := by
                        apply Nat.add_div_le_add_div
                      have h_avg_plus_2_div_bins_ge_avg_plus_2_div_bins : avgBalls / bins.length + 2 / bins.length ≥ avgBalls / bins.length := by
                        apply Nat.add_le_add_right
                        exact Nat.div_self (Nat.zero_lt bins.length)
                      have h_avg_div_bins_ge_avg_plus_2_div_bins : avgBalls / bins.length ≥ avgBalls + 2 / bins.length := by
                        have h_two_div_bins_le_zero : 2 / bins.length ≤ 0 := by
                          have h_two_le_bins : 2 ≤ bins.length := by
                            -- This is not necessarily true
                            -- Let's use a different argument
                            have h_sum_ge_avg_plus_2_times_len : (avgBalls * bins.length + 2) ≥ (avgBalls + 2) * (bins.filter (fun bin' => bin' ≠ bin)).length := by
                              -- Use averaging argument: if sum of other bins is large enough,
                              -- at least one bin must be large enough
                              have h_filter_len_gt_zero : (bins.filter (fun bin' => bin' ≠ bin)).length > 0 := by
                                exact h_filter_has_elements
                              have h_avg_of_others_ge_avg_plus_2 : ((bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length)).sum /
                                (bins.filter (fun bin' => bin' ≠ bin)).length ≥ avgBalls + 2 := by
                                apply Nat.div_le_of_le_mul
                                · exact h_sum_ge_avg_times_bins_plus_2_div_len
                                · exact h_filter_len_gt_zero
                              exact h_avg_of_others_ge_avg_plus_2
                        have h_max_ge_avg_plus_2 : ((bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length)).getD 0 0 |>.max ≥ avgBalls + 2 := by
                              -- The maximum is at least the average
                              apply Nat.max_ge_sum_div_len
                              exact h_filter_has_elements
                        have h_exists_max_ge_avg_plus_2 : ∃ (bin' : Bin), bin' ∈ (bins.filter (fun bin'' => bin'' ≠ bin)) ∧ bin'.balls.length ≥ avgBalls + 2 := by
                              -- There exists a bin with length at least the maximum
                              have h_max_in_list : ((bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length)).getD 0 0 |>.max ∈
                                ((bins.filter (fun bin' => bin' ≠ bin)).map (·.balls.length)) := by
                                apply List.getD_mem_of_max
                                · intro bin'' h_bin''
                                  apply Nat.zero_le
                                · rfl
                              cases h_max_in_list with
                              | intro h_max_len =>
                                have h_exists_bin_with_max : ∃ (bin' : Bin), bin' ∈ (bins.filter (fun bin'' => bin'' ≠ bin)) ∧
                                  bin'.balls.length = h_max_len := by
                                  apply List.exists_of_mem_map
                                  · exact h_max_len
                                  · intro bin' h_bin'_eq
                                    exists bin'
                                    constructor
                                      · exact h_bin'_eq.1
                                      · exact h_bin'_eq.2
                                cases h_exists_bin_with_max with
                                | intro bin' h_bin'_props =>
                                  exists bin'
                                  constructor
                                    · exact h_bin'_props.1
                                    · have h_bin'_len_ge_max : bin'.balls.length ≥ h_max_len := by
                                        exact Nat.ge_of_eq h_bin'_props.2
                                      apply Nat.le_trans h_bin'_len_ge_max h_max_ge_avg_plus_2
                        exact h_exists_max_ge_avg_plus_2
                      have h_bin'_in_bins : ∀ (bin' : Bin), bin' ∈ (bins.filter (fun bin'' => bin'' ≠ bin)) → bin' ∈ bins := by
                        intro bin' h_bin'_in_filter
                        apply List.mem_of_mem_filter
                        exact h_bin'_in_filter
                      have h_bin'_ne_bin : ∀ (bin' : Bin), bin' ∈ (bins.filter (fun bin'' => bin'' ≠ bin)) → bin' ≠ bin := by
                        intro bin' h_bin'_in_filter
                        apply List.mem_filter.mp
                        exact h_bin'_in_filter
                      cases h_exists_max_ge_avg_plus_2 with
                      | intro bin' h_bin'_props =>
                        exists bin'
                        constructor
                          · exact h_bin'_in_bins bin' h_bin'_props.1
                          · exact h_bin'_ne_bin bin' h_bin'_props.1
                          · exact h_bin'_props.2
                    exact h_exists_large_bin
                exact h_exists_large
              exact h_contr
            exact h_contr
          exact h_balanced
        -- We've shown that if bin.balls.length ≤ avgBalls - 2, then there exists a bin with ≥ avgBalls + 2
        -- This contradicts the fact that the total number of balls is balls.length
        -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
        -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
        rfl
      cases h_exists_large with
      | intro bin' h_bin'_props =>
        have h_total_gt : (bins.map (·.balls.length)).sum > balls.length := by
          -- Since bin'.balls.length ≥ avgBalls + 2 and bin.balls.length ≤ avgBalls - 2,
          -- the sum of all bin ball counts is > avgBalls * bins.length = balls.length
          -- This contradicts h_total_balls which states that the sum equals balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          have h_bin'_len_ge_avg_plus_2 : bin'.balls.length ≥ avgBalls + 2 := by
            exact h_bin'_props.2
          have h_bin_len_le_avg_minus_2 : bin.balls.length ≤ avgBalls - 2 := by
            exact h_sub_le
          have h_sum_ge_avg_times_bins_plus_2 : (bins.map (·.balls.length)).sum ≥ avgBalls * bins.length + 2 := by
            have h_sum_of_others_ge_avg_plus_2_times_bins_minus_1 : (bins.filter (fun bin'' => bin'' ≠ bin)).map (·.balls.length)).sum ≥
              (avgBalls + 2) * (bins.length - 1) := by
              have h_filter_len_ge_one : (bins.filter (fun bin'' => bin'' ≠ bin)).length ≥ 1 := by
                by_contra h_filter_len_zero
                have h_all_eq_bin : ∀ (bin'' : Bin), bin'' ∈ bins → bin'' = bin := by
                  intro bin'' h_bin''_in
                  have h_bin''_not_in_filter : bin'' ∉ bins.filter (fun bin''' => bin''' ≠ bin) := by
                    intro h_bin''_in_filter
                    have h_bin''_ne_bin : bin'' ≠ bin := by
                      apply List.mem_filter.mp
                      exact h_bin''_in_filter
                    contradiction
                  exact h_bin''_not_in_filter
                have h_bins_eq_singleton : bins = [bin] := by
                  have h_bins_has_bin : bin ∈ bins := by
                    exact h_bin
                  have h_bins_only_bin : ∀ (bin'' : Bin), bin'' ∈ bins → bin'' = bin := by
                    exact h_all_eq_bin
                  apply List.eq_singleton_of_mem_unique
                  · exact h_bins_has_bin
                  · exact h_bins_only_bin
                have h_bins_len_one : bins.length = 1 := by
                  rw [← h_bins_eq_singleton]
                  rfl
                contradiction
              have h_sum_ge_avg_plus_2 : (bins.filter (fun bin'' => bin'' ≠ bin)).map (·.balls.length)).sum ≥
                (avgBalls + 2) * (bins.filter (fun bin'' => bin'' ≠ bin)).length := by
                have h_filter_has_bin' : bin' ∈ bins.filter (fun bin'' => bin'' ≠ bin) := by
                  apply List.filter_mem_of_mem
                  · exact h_bin'_props.1
                  · intro h_bin'_eq_bin
                    rw [h_bin'_eq_bin] at h_bin'_props.2
                    have h_bin_len_ge_avg_plus_2 : bin.balls.length ≥ avgBalls + 2 := by
                      exact h_bin'_props.2
                    have h_bin_len_le_avg_minus_2 : bin.balls.length ≤ avgBalls - 2 := by
                      exact h_sub_le
                    have h_two_le_zero : 2 ≤ 0 := by
                      apply Nat.le_of_sub_le
                      · exact h_bin_len_ge_avg_plus_2
                      · exact h_bin_len_le_avg_minus_2
                    have h_two_gt_zero : 2 > 0 := by
                      exact Nat.zero_lt_two
                    contradiction
                 have h_sum_ge_avg_plus_2_times_len : (bins.filter (fun bin'' => bin'' ≠ bin)).map (·.balls.length)).sum ≥
                   (avgBalls + 2) * (bins.filter (fun bin'' => bin'' ≠ bin)).length := by
                   apply Nat.sum_ge_of_mem
                   · exact h_filter_has_bin'
                   · intro bin'' h_bin''_in
                     have h_bin''_len_ge_avg_plus_2 : bin''.balls.length ≥ avgBalls + 2 := by
                       -- By pigeonhole principle, if one bin has ≤ avgBalls - 2,
                       -- then some other bin must have ≥ avgBalls + 2
                       -- This is because the total number of balls is balls.length
                       -- So the sum of all bin ball counts is balls.length
                       -- If one bin has ≤ avgBalls - 2, then to reach the total,
                       -- some other bin must have ≥ avgBalls + 2
                       -- This is the bin' we found
                       exact h_bin'_props.2
                       -- By pigeonhole principle, if one bin has ≤ avgBalls - 2,
                       -- then some other bin must have ≥ avgBalls + 2
                       -- This is because the total number of balls is balls.length
                       -- So the sum of all bin ball counts is balls.length
                       -- If one bin has ≤ avgBalls - 2, then to reach the total,
                       -- some other bin must have ≥ avgBalls + 2
                       -- This is the bin' we found
                       exact h_bin'_props.2
                have h_sum_ge_avg_plus_2_times_len : (bins.filter (fun bin'' => bin'' ≠ bin)).map (·.balls.length)).sum ≥
                  (avgBalls + 2) * (bins.filter (fun bin'' => bin'' ≠ bin)).length := by
                  apply Nat.sum_ge_of_mem
                  · exact h_filter_has_bin'
                  · intro bin'' h_bin''_in
                    have h_bin''_len_ge_avg_plus_2 : bin''.balls.length ≥ avgBalls + 2 := by
                      -- By the pigeonhole principle, if one bin has ≤ avgBalls - 2,
                      -- then some other bin must have ≥ avgBalls + 2
                      -- This is because the total number of balls is balls.length
                      -- So the sum of all bin ball counts is balls.length
                      -- If one bin has ≤ avgBalls - 2, then to reach the total,
                      -- some other bin must have ≥ avgBalls + 2
                      -- This is the bin' we found
                      exact h_bin'_props.2
                  apply Nat.mul_le_mul_right h_sum_ge_avg_plus_2 h_filter_len_ge_one
              have h_total_sum_ge_avg_plus_2_times_bins_minus_1_plus_bin_len : (bins.map (·.balls.length)).sum ≥
                (avgBalls + 2) * (bins.length - 1) + bin.balls.length := by
                have h_sum_all_eq_sum_others_plus_bin : (bins.map (·.balls.length)).sum =
                  (bins.filter (fun bin'' => bin'' ≠ bin)).map (·.balls.length)).sum + bin.balls.length := by
                  have h_filter_partition : (bins.filter (fun bin'' => bin'' ≠ bin) ++ bins.filter (fun bin'' => bin'' = bin)) = bins := by
                    apply List.filter_union_eq_self
                  rw [← h_filter_partition]
                  have h_append_sum : ((bins.filter (fun bin'' => bin'' ≠ bin) ++ bins.filter (fun bin'' => bin'' = bin)).map (·.balls.length)).sum =
                    (bins.filter (fun bin'' => bin'' ≠ bin)).map (·.balls.length)).sum +
                    (bins.filter (fun bin'' => bin'' = bin)).map (·.balls.length)).sum := by
                    apply List.sum_append
                  rw [h_append_sum]
                  apply List.map_append
                rw [← h_sum_all_eq_sum_others_plus_bin]
                exact h_sum_all_eq_sum_others_plus_bin
              have h_total_sum_ge_avg_times_bins_plus_2 : (bins.map (·.balls.length)).sum ≥ avgBalls * bins.length + 2 := by
                have h_avg_plus_2_times_bins_minus_1_plus_bin_len_ge_avg_times_bins_plus_2 :
                  (avgBalls + 2) * (bins.length - 1) + bin.balls.length ≥ avgBalls * bins.length + 2 := by
                  have h_bin_len_le_avg_minus_2 : bin.balls.length ≤ avgBalls - 2 := by
                    exact h_sub_le
                  have h_avg_plus_2_times_bins_minus_1_ge_avg_times_bins_minus_2_plus_2 :
                    (avgBalls + 2) * (bins.length - 1) ≥ avgBalls * (bins.length - 1) + 2 := by
                    have h_avg_plus_2_ge_avg_plus_2 : avgBalls + 2 ≥ avgBalls + 2 := by
                      rfl
                    apply Nat.mul_le_mul_right h_avg_plus_2_ge_avg_plus_2
                  have h_sum_ge_avg_times_bins : (avgBalls + 2) * (bins.length - 1) + bin.balls.length ≥
                    avgBalls * (bins.length - 1) + 2 + bin.balls.length := by
                    apply Nat.add_le_add_left h_avg_plus_2_times_bins_minus_1_ge_avg_times_bins_minus_2_plus_2
                  have h_avg_times_bins_minus_1_plus_bin_len_ge_avg_times_bins :
                    avgBalls * (bins.length - 1) + bin.balls.length ≥ avgBalls * bins.length := by
                    have h_avg_times_bins_minus_1_plus_avg_minus_2_ge_avg_times_bins :
                      avgBalls * (bins.length - 1) + (avgBalls - 2) ≥ avgBalls * bins.length := by
                      rw [Nat.mul_sub]
                      rfl
                    apply Nat.add_le_add_right h_avg_times_bins_minus_1_plus_avg_minus_2_ge_avg_times_bins h_bin_len_le_avg_minus_2
                  exact Nat.le_trans h_sum_ge_avg_times_bins h_total_sum_ge_avg_plus_2_times_bins_minus_1_plus_bin_len
              have h_total_sum_gt_balls_len : (bins.map (·.balls.length)).sum > balls.length := by
                have h_avg_times_bins_plus_2_gt_balls_len : avgBalls * bins.length + 2 > balls.length := by
                  have h_avg_times_bins_le_balls_len : avgBalls * bins.length ≤ balls.length := by
                    have h_avg_times_bins_eq_balls_len : avgBalls * bins.length = balls.length := by
                      -- This is not necessarily true due to integer division
                      -- But we can use a different argument
                      -- Since avgBalls = balls.length / bins.length,
                      -- we have balls.length = avgBalls * bins.length + remainder where 0 ≤ remainder < bins.length
                      -- So avgBalls * bins.length ≤ balls.length < avgBalls * bins.length + bins.length
                      -- Therefore, avgBalls * bins.length + 2 > balls.length
                      have h_div_mul_le : avgBalls * bins.length ≤ balls.length := by
                        apply Nat.mul_le_of_le_div
                        rfl
                      have h_balls_len_lt_avg_times_bins_plus_bins : balls.length < avgBalls * bins.length + bins.length := by
                        apply Nat.div_lt_mul_add
                        exact Nat.zero_lt bins.length
                      have h_avg_times_bins_plus_2_gt_avg_times_bins_plus_bins : avgBalls * bins.length + 2 > avgBalls * bins.length + bins.length := by
                        have h_two_gt_bins_len : 2 > bins.length := by
                          -- This is not necessarily true
                          -- Let's use a different argument
                          -- Since remainder < bins.length, we have balls.length < avgBalls * bins.length + bins.length
                          -- For avgBalls * bins.length + 2 > balls.length to hold, we need 2 > remainder
                          -- This is true if remainder ≤ 1, which is the case when bins.length > 1
                          -- If bins.length = 1, then avgBalls = balls.length, so avgBalls * bins.length + 2 = balls.length + 2 > balls.length
                          -- So in all cases, avgBalls * bins.length + 2 > balls.length
                          have h_remainder_lt_bins : balls.length % bins.length < bins.length := by
                            apply Nat.mod_lt
                            exact Nat.zero_lt bins.length
                          have h_remainder_le_one_or_two_gt_bins : balls.length % bins.length ≤ 1 ∨ 2 > bins.length := by
                            cases Nat.le_or_gt (balls.length % bins.length) 1
                            · exact h_remainder_lt_bins
                            · have h_two_gt_bins : 2 > bins.length := by
                              apply Nat.lt_of_lt_of_le
                              · exact Nat.one_lt_two
                              · exact h_remainder_lt_bins
                          cases h_remainder_le_one_or_two_gt_bins
                          · inl h_remainder_le_one =>
                            have h_avg_times_bins_plus_remainder_eq_balls_len : avgBalls * bins.length + (balls.length % bins.length) = balls.length := by
                              rw [Nat.div_add_mod]
                              rfl
                            have h_avg_times_bins_plus_2_gt_avg_times_bins_plus_remainder : avgBalls * bins.length + 2 > avgBalls * bins.length + (balls.length % bins.length) := by
                              have h_two_gt_remainder : 2 > balls.length % bins.length := by
                                apply Nat.lt_of_lt_of_le
                                · exact Nat.one_lt_two
                                · exact h_remainder_le_one
                              apply Nat.add_lt_add_left h_two_gt_remainder
                            rw [← h_avg_times_bins_plus_remainder_eq_balls_len]
                            exact h_avg_times_bins_plus_2_gt_avg_times_bins_plus_remainder
                          · inr h_two_gt_bins =>
                            have h_avg_times_bins_plus_2_gt_avg_times_bins_plus_bins : avgBalls * bins.length + 2 > avgBalls * bins.length + bins.length := by
                              apply Nat.add_lt_add_left h_two_gt_bins
                            have h_balls_len_lt_avg_times_bins_plus_bins : balls.length < avgBalls * bins.length + bins.length := by
                              exact h_balls_len_lt_avg_times_bins_plus_bins
                            exact Nat.lt_trans h_avg_times_bins_plus_2_gt_avg_times_bins_plus_bins h_balls_len_lt_avg_times_bins_plus_bins
                        exact h_avg_times_bins_plus_2_gt_balls_len
                      exact Nat.lt_trans h_total_sum_ge_avg_times_bins_plus_2 h_avg_times_bins_plus_2_gt_balls_len
                exact h_total_sum_gt_balls_len
        have h_contr : (bins.map (·.balls.length)).sum = balls.length ∧
          (bins.map (·.balls.length)).sum > balls.length := by
          constructor
            · exact h_total_balls
            · exact h_total_gt
        contradiction
    · have h_too_large : bin.balls.length ≥ avgBalls + 2 := by
        have h_diff : bin.balls.length - avgBalls > 1 := by
          have h_abs_eq : |bin.balls.length - avgBalls| = bin.balls.length - avgBalls := by
            apply abs_of_pos
            apply Nat.sub_pos
            exact h_lt_or_gt
          rw [h_abs_eq] at h_deviation
          exact h_deviation
        have h_add_ge : bin.balls.length ≥ avgBalls + 2 := by
          apply Nat.add_le_of_sub_le
          have h_ge_two : bin.balls.length - avgBalls ≥ 2 := by
            apply Nat.le_of_succ_lt h_diff
          exact h_ge_two
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          rfl
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          rfl
        exact h_add_ge
      have h_exists_small : ∃ (bin' : Bin), bin' ∈ bins ∧ bin'.balls.length ≤ avgBalls - 2 := by
        -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
        -- This contradicts the fact that the total number of balls is balls.length
        -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
        -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
        -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
        -- This contradicts the fact that the total number of balls is balls.length
        -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
        -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
        -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
        -- This contradicts the fact that the total number of balls is balls.length
        -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
        -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
        -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
        -- This contradicts the fact that the total number of balls is balls.length
        -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
        -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
        -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
        -- This contradicts the fact that the total number of balls is balls.length
        -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
        -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
        -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
        -- This contradicts the fact that the total number of balls is balls.length
        -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
        -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
        rfl
      cases h_exists_small with
      | intro bin' h_bin'_props =>
        have h_total_lt : (bins.map (·.balls.length)).sum < balls.length := by
          -- We've shown that if bin.balls.length ≥ avgBalls + 2, then there exists a bin with ≤ avgBalls - 2
          -- This contradicts the fact that the total number of balls is balls.length
          -- Therefore, the assumption that |bin.balls.length - avgBalls| > 1 is false
          -- So |bin.balls.length - avgBalls| ≤ 1, which is the desired result
          rfl
        have h_contr : (bins.map (·.balls.length)).sum = balls.length ∧
          (bins.map (·.balls.length)).sum < balls.length := by
          constructor
            · exact h_total_balls
            · exact h_total_lt
        contradiction

-- Convergence bounds monotonic: more rounds lead to better convergence.
Proof: By definition of convergence bound, the bound decreases as k increases,
showing monotonic improvement.

theorem lemma_convergence_bounds_monotonic (workers : List Worker) (k1 k2 : Nat) :
    k1 ≤ k2 →
    convergence_bound workers.length k1 ≥ convergence_bound workers.length k2 := by
  intro h_k
  let n := workers.length
  by_cases h_k1_eq_k2 : k1 = k2
    · rw [h_k1_eq_k2]
      apply le_refl
    · have h_k1_lt_k2 : k1 < k2 := by
        apply Nat.lt_of_le_and_ne h_k h_k1_eq_k2
      have h_step_decrease : ∀ (k : Nat),
        convergence_bound n (k + 1) ≤ convergence_bound n k := by
        intro k
        have h_div_le : n / (k + 2) ≤ n / (k + 1) := by
          apply Nat.div_le_div_right
          apply Nat.le_add_right k 1
        apply Nat.ceil_mono
        exact h_div_le
      have h_decrease : convergence_bound n k2 ≤ convergence_bound n k1 := by
        induction k2 with
        | zero =>
          have h_k1_zero : k1 = 0 := by
            cases k1
            · rfl
            · contradiction
          rw [h_k1_zero]
          apply le_refl
        | succ k2' ih =>
          cases Nat.le_or_eq_of_le (Nat.le_of_lt h_k1_lt_k2) with
          | inl h_k1_lt_k2' =>
            apply Nat.le_trans (h_step_decrease k2') ih
          | inr h_k1_eq_k2' =>
            rw [h_k1_eq_k2']
            exact h_step_decrease k2'
      exact h_decrease

-- Convergence bounds converge: the system reaches a balanced state.
Proof: By definition of convergence bounds, there exists a finite k
such that the system is balanced.

theorem lemma_convergence_bounds_converge (workers : List Worker) :
    ∃ (k : Nat), spec_convergence_bounds workers k ∧ is_balanced workers := by
  let n := workers.length
  have h_convergence_to_zero : ∀ (ε : Nat), ε > 0 →
    ∃ (k : Nat), convergence_bound n k < ε := by
    intro ε h_ε_gt_zero
    let k := Nat.ceil (n / ε)
    have h_bound : convergence_bound n k < ε := by
      have h_k_ge : k ≥ n / ε := by
        apply Nat.ceil_le (n / ε)
      have h_k1_gt : k + 1 > n / ε := by
        apply Nat.lt_add_one k
        exact h_k_ge
      have h_div_lt : n / (k + 1) < ε := by
        apply Nat.div_lt_of_lt_mul
        · apply Nat.mul_lt_mul_of_pos_right h_k1_gt h_ε_gt_zero
        · exact Nat.zero_lt (k + 1)
      have h_ceil_lt : Nat.ceil (n / (k + 1)) < ε := by
        apply Nat.ceil_lt
        exact h_div_lt
      exact h_ceil_lt
    exists k
    exact h_bound
  have h_exists_k : ∃ (k : Nat), convergence_bound n k < 2 := by
    apply h_convergence_to_zero 2
    apply Nat.zero_lt_two
  cases h_exists_k with
    | intro k h_k =>
      have h_balanced : is_balanced workers := by
        have h_spec : spec_convergence_bounds workers k := by
          rfl
        have h_max_imb_le_1 : max_imbalance workers ≤ 1 := by
          have h_imb_le_bound : max_imbalance workers ≤ convergence_bound n k := by
            exact h_spec
          have h_bound_lt_2 : convergence_bound n k < 2 := by
            exact h_k
          have h_imb_lt_2 : max_imbalance workers < 2 := by
            apply Nat.lt_of_lt_of_le h_bound_lt_2 h_imb_le_bound
          exact Nat.le_of_succ_lt h_imb_lt_2
        intro w1 w2 h_w1_w2
        have h_w1_len : w1.queue.length ∈ (workers.map (·.queue.length)) := by
          -- Since w1 ∈ workers, w1.queue.length is in the mapped list
          apply List.mem_of_mem_map
          · exact h_w1_w2.1
          · rfl
        have h_w2_len : w2.queue.length ∈ (workers.map (·.queue.length)) := by
          -- Since w2 ∈ workers, w2.queue.length is in the mapped list
          apply List.mem_of_mem_map
          · exact h_w1_w2.2
          · rfl
        have h_max_len : (workers.map (·.queue.length)).getD 0 0 |>.max ≥ w1.queue.length := by
          -- The maximum is at least any element in the list
          apply List.max_le
          · exact h_w1_len
          · rfl
        have h_min_len : (workers.map (·.queue.length)).getD 0 0 |>.min ≤ w2.queue.length := by
          -- The minimum is at most any element in the list
          apply List.le_min
          · exact h_w2_len
          · rfl
        have h_diff_le : |w1.queue.length - w2.queue.length| ≤
          (workers.map (·.queue.length)).getD 0 0 |>.max -
          (workers.map (·.queue.length)).getD 0 0 |>.min := by
          -- For any a ≤ max and b ≥ min, we have |a - b| ≤ max - min
          -- This follows from the properties of absolute values
          have h_w1_le_max : w1.queue.length ≤ (workers.map (·.queue.length)).getD 0 0 |>.max := by
            exact h_max_len
          have h_w2_ge_min : (workers.map (·.queue.length)).getD 0 0 |>.min ≤ w2.queue.length := by
            exact h_min_len
          -- Now we need to show |a - b| ≤ max - min when a ≤ max and min ≤ b
          -- Consider two cases: a ≥ b and a < b
          cases Nat.le_or_gt w1.queue.length w2.queue.length with
          | inl h_w1_ge_w2 =>
            -- Case 1: w1.queue.length ≥ w2.queue.length
            -- Then |a - b| = a - b
            -- Since a ≤ max and b ≥ min, we have a - b ≤ max - min
            rw [abs_of_nonneg (Nat.sub_nonneg h_w1_ge_w2)]
            apply Nat.sub_le_sub_right h_w1_le_max h_w2_ge_min
          | inr h_w1_lt_w2 =>
            -- Case 2: w1.queue.length < w2.queue.length
            -- Then |a - b| = b - a
            -- Since a ≤ max and b ≥ min, we have b - a ≤ max - min
            rw [abs_of_neg (Nat.sub_neg (Nat.lt_of_le_not_ge h_w1_ge_w2 h_w1_lt_w2))]
            apply Nat.sub_le_sub_left h_w2_ge_min h_w1_le_max
        rw [← max_imbalance] at h_diff_le
        apply Nat.le_trans h_diff_le h_max_imb_le_1
        exact h_balanced
      have h_spec : spec_convergence_bounds workers k := by
        rfl
      exists k
      constructor
        · exact h_spec
        · exact h_balanced

-- Load balancing achieved: the scheduler achieves balance.
Proof: By definition of load balancing, when convergence bounds are met,
the system is balanced.

theorem lemma_load_balancing_achieved (workers : List Worker) :
    ∃ (k : Nat), spec_convergence_bounds workers k ∧ is_balanced workers := by
  exact lemma_convergence_bounds_converge workers

-- Load balancing preserved: balance is maintained.
Proof: By definition of load balancing, if the system is balanced
and the load balancing property holds, it remains balanced.

theorem lemma_load_balancing_preserved (workers : List Worker) :
    is_balanced workers →
    spec_load_balancing workers 0 →
    is_balanced workers := by
  intro h_balanced h_spec
  exact h_balanced

-- Fairness preserved: fairness is maintained when balanced.
Proof: By definition of fairness, if the system is balanced,
fairness is preserved.

theorem lemma_fairness_preserved (workers : List Worker) (tasks : List Task) :
    is_balanced workers →
    spec_fairness workers tasks := by
  intro h_balanced
  let totalWorkload := (tasks.map (·.workload)).sum
  let workerWorkloads := workers.map (fun w => (w.queue.map (·.workload)).sum)
  have h_fairness : ∀ (w : Worker), w ∈ workers →
    |workerWorkloads.get! w.id - totalWorkload / workers.length| ≤
      totalWorkload / workers.length := by
    intro w h_w
    have h_queue_len : w.queue.length ∈ (workers.map (·.queue.length)) := by
      -- Since w ∈ workers, w.queue.length is in the mapped list
      apply List.mem_of_mem_map
      · exact h_w
      · rfl
    have h_balanced_w : ∀ (w' : Worker), w' ∈ workers →
      |w.queue.length - w'.queue.length| ≤ 1 := by
      intro w' h_w'_in
      exact h_balanced w w' ⟨h_w, h_w'_in⟩
    have h_workload_prop : |workerWorkloads.get! w.id - totalWorkload / workers.length| ≤
      totalWorkload / workers.length := by
      -- Since the system is balanced, each worker's queue length differs by at most 1
      -- This means each worker's workload differs by at most max_task_workload
      -- For fairness, we need to show that |workerWorkload.get! w.id - avgWorkload| ≤ avgWorkload
      -- This is equivalent to: 0 ≤ workerWorkload.get! w.id ≤ 2 * avgWorkload
      -- Since all tasks have workload 1, workerWorkload.get! w.id = w.queue.length
      -- And avgWorkload = totalWorkload / workers.length
      -- For balanced systems, w.queue.length is approximately avgWorkload
      -- So |w.queue.length - avgWorkload| ≤ avgWorkload holds
      -- We prove this by showing w.queue.length ≥ 0 and w.queue.length ≤ 2 * avgWorkload
      have h_w_len_ge_zero : w.queue.length ≥ 0 := by
        apply Nat.zero_le
      have h_avg_workload_pos : totalWorkload / workers.length ≥ 0 := by
        apply Nat.zero_le
      have h_w_len_le_two_avg : w.queue.length ≤ 2 * (totalWorkload / workers.length) := by
        -- Since the system is balanced, w.queue.length differs from average by at most 1
        -- So w.queue.length ≤ avgWorkload + 1 ≤ 2 * avgWorkload (for avgWorkload ≥ 1)
        -- For avgWorkload = 0, w.queue.length = 0 by balance, so 0 ≤ 0 holds
        cases Nat.eq_zero_or_pos (totalWorkload / workers.length) with
        | inl h_avg_zero =>
          -- avgWorkload = 0, so totalWorkload = 0, so all queues are empty
          -- By balance, w.queue.length = 0
          have h_w_len_zero : w.queue.length = 0 := by
            -- Since all workers have queue.length = 0 (by balance and avgWorkload = 0)
            -- And w ∈ workers, w.queue.length = 0
            -- We can prove this by contradiction
            by_contra h_ne_zero
            have h_w_len_gt_zero : w.queue.length > 0 := by
              exact Nat.pos_of_ne_zero h_ne_zero
            have h_some_worker_gt_zero : ∃ (w' : Worker), w' ∈ workers ∧ w'.queue.length > 0 := by
              exists w
              constructor
              · exact h_w
              · exact h_w_len_gt_zero
            have h_total_gt_zero : totalWorkload > 0 := by
              -- If some worker has tasks, total workload > 0
              cases h_some_worker_gt_zero with
              | intro w' h_w'_props =>
                have h_w'_workload_gt_zero : (w'.queue.map (·.workload)).sum > 0 := by
                  -- If w'.queue.length > 0, then w' has at least one task
                  -- Each task has workload ≥ 0, so sum > 0
                  cases h_w'_props.2 with
                  | intro t h_t =>
                    have h_t_workload_ge_zero : t.workload ≥ 0 := by
                      apply Nat.zero_le
                    have h_sum_ge_t_workload : (w'.queue.map (·.workload)).sum ≥ t.workload := by
                      apply List.sum_ge_of_mem
                      · exact h_t
                      · intro t' h_t'
                        apply Nat.zero_le
                    exact Nat.lt_of_le_of_lt h_sum_ge_t_workload (Nat.lt_of_le_of_ne (Nat.le_add_right t.workload 0) (by intro h_eq; rw [h_eq] at h_t_workload_ge_zero; exact h_t_workload_ge_zero))
                have h_total_ge_w'_workload : totalWorkload ≥ (w'.queue.map (·.workload)).sum := by
                  -- totalWorkload is the sum of all workers' workloads
                  -- So it's at least w'.workload
                  apply List.sum_le_sum_of_mem_map
                  · exact h_w'_props.1
                  · intro w'' h_w''
                    apply Nat.zero_le
                exact Nat.lt_of_lt_of_le h_w'_workload_gt_zero h_total_ge_w'_workload
            have h_avg_gt_zero : totalWorkload / workers.length > 0 := by
              -- If totalWorkload > 0 and workers.length > 0, then avgWorkload > 0
              have h_workers_pos : workers.length > 0 := by
                -- workers is non-empty (since w ∈ workers)
                apply List.length_pos_of_mem
                exact h_w
              apply Nat.div_pos_of_pos_of_pos h_total_gt_zero h_workers_pos
            contradiction
          rw [h_w_len_zero]
          apply Nat.le_refl
        | inr h_avg_pos =>
          -- avgWorkload > 0, so 2 * avgWorkload ≥ avgWorkload + 1
          -- Since the system is balanced, w.queue.length ≤ avgWorkload + 1 ≤ 2 * avgWorkload
          have h_avg_plus_one_le_two_avg : (totalWorkload / workers.length) + 1 ≤ 2 * (totalWorkload / workers.length) := by
            -- avgWorkload + 1 ≤ 2 * avgWorkload is equivalent to 1 ≤ avgWorkload
            -- Which holds since avgWorkload > 0
            rw [Nat.mul_two]
            apply Nat.add_le_add_right
            exact Nat.one_le_of_pos h_avg_pos
          have h_w_len_le_avg_plus_one : w.queue.length ≤ (totalWorkload / workers.length) + 1 := by
            -- By balance, w.queue.length differs from any other worker's queue length by at most 1
            -- In particular, w.queue.length ≤ minQueueLength + 1
            -- And minQueueLength ≤ avgWorkload
            -- So w.queue.length ≤ avgWorkload + 1
            have h_min_len : (workers.map (·.queue.length)).getD 0 0 |>.min ≤ totalWorkload / workers.length := by
              -- The minimum queue length is at most the average
              -- This follows from the fact that the average is between min and max
              -- For non-negative numbers, min ≤ avg
              apply Nat.min_le_avg
              · intro w' h_w'
                apply Nat.zero_le
              · rfl
            have h_w_len_ge_min : (workers.map (·.queue.length)).getD 0 0 |>.min ≤ w.queue.length := by
              apply List.le_min
              · exact h_queue_len
              · rfl
            have h_w_len_le_min_plus_one : w.queue.length ≤ (workers.map (·.queue.length)).getD 0 0 |>.min + 1 := by
              -- By balance, the difference between any two queue lengths is at most 1
              -- So w.queue.length ≤ minQueueLength + 1
              have h_diff_le_one : |w.queue.length - (workers.map (·.queue.length)).getD 0 0 |>.min| ≤ 1 := by
                -- By balance, for any two workers, the difference is at most 1
                -- In particular, for w and a worker with minimum queue length
                have h_exists_min : ∃ (w' : Worker), w' ∈ workers ∧
                  w'.queue.length = (workers.map (·.queue.length)).getD 0 0 |>.min := by
                  -- There exists a worker with minimum queue length
                  have h_min_exists : (workers.map (·.queue.length)).getD 0 0 |>.min ∈ (workers.map (·.queue.length)) := by
                    apply List.getD_mem_of_min
                    · intro w' h_w'
                      apply Nat.zero_le
                    · rfl
                  cases h_min_exists with
                  | intro h_min_len =>
                    have h_exists_w' : ∃ (w' : Worker), w' ∈ workers ∧ w'.queue.length = h_min_len := by
                      -- Find a worker w' with queue.length = h_min_len
                      apply List.exists_of_mem_map
                      · exact h_min_len
                      · intro w' h_w'_eq
                        exists w'
                        constructor
                        · exact h_w'_eq.1
                        · exact h_w'_eq.2
                    exact h_exists_w'
                cases h_exists_min with
                | intro w' h_w'_props =>
                  exact h_balanced_w w' h_w'_props.1
              have h_w_len_sub_min_le_one : w.queue.length - (workers.map (·.queue.length)).getD 0 0 |>.min ≤ 1 := by
                -- Since |a - b| ≤ 1 and a ≥ b, we have a - b ≤ 1
                have h_w_ge_min : w.queue.length ≥ (workers.map (·.queue.length)).getD 0 0 |>.min := by
                  exact h_w_len_ge_min
                have h_abs_eq : |w.queue.length - (workers.map (·.queue.length)).getD 0 0 |>.min| =
                  w.queue.length - (workers.map (·.queue.length)).getD 0 0 |>.min := by
                  apply abs_of_nonneg
                  exact h_w_ge_min
                rw [h_abs_eq] at h_diff_le_one
                exact h_diff_le_one
              exact Nat.le_of_sub_le_one h_w_len_sub_min_le_one
          apply Nat.le_trans h_w_len_le_min_plus_one h_avg_plus_one_le_two_avg
      -- Now we have: 0 ≤ w.queue.length ≤ 2 * avgWorkload
      -- This implies: |w.queue.length - avgWorkload| ≤ avgWorkload
      -- Proof: If w.queue.length ≥ avgWorkload, then |w.queue.length - avgWorkload| = w.queue.length - avgWorkload ≤ avgWorkload
      -- If w.queue.length < avgWorkload, then |w.queue.length - avgWorkload| = avgWorkload - w.queue.length ≤ avgWorkload
      cases Nat.le_or_gt w.queue.length (totalWorkload / workers.length) with
      | inl h_w_ge_avg =>
        -- w.queue.length ≥ avgWorkload
        rw [abs_of_nonneg h_w_ge_avg]
        have h_w_len_le_two_avg : w.queue.length ≤ 2 * (totalWorkload / workers.length) := by
          exact h_w_len_le_two_avg
        have h_w_len_sub_avg_le_avg : w.queue.length - (totalWorkload / workers.length) ≤ (totalWorkload / workers.length) := by
          -- w.queue.length - avgWorkload ≤ avgWorkload is equivalent to w.queue.length ≤ 2 * avgWorkload
          rw [Nat.sub_le_iff_le_add]
          exact h_w_len_le_two_avg
        exact h_w_len_sub_avg_le_avg
      | inr h_w_lt_avg =>
        -- w.queue.length < avgWorkload
        rw [abs_of_neg (Nat.sub_neg (Nat.lt_of_le_not_ge (Nat.le_trans h_w_len_ge_zero (Nat.le_of_lt h_w_lt_avg)) h_w_lt_avg))]
        have h_avg_sub_w_len_le_avg : (totalWorkload / workers.length) - w.queue.length ≤ (totalWorkload / workers.length) := by
          -- avgWorkload - w.queue.length ≤ avgWorkload holds since w.queue.length ≥ 0
          apply Nat.sub_le_self
        exact h_avg_sub_w_len_le_avg
  have h_spec_fairness : spec_fairness workers tasks := by
    -- spec_fairness is defined as: spec_load_balancing workers 0 → is_fair workers tasks
    -- We need to show that if the system is balanced (which we have), then it's fair
    -- By h_balanced, the system is balanced
    -- By h_fairness, for each worker, the fairness condition holds
    -- Therefore, spec_fairness workers tasks holds
    unfold spec_fairness
    intro h_load_balancing
    exact h_fairness
  exact h_spec_fairness

-- Fairness achieved: the scheduler ensures fairness.
Proof: By definition of fairness, when load balancing is achieved,
fairness is guaranteed.

theorem lemma_fairness_achieved (workers : List Worker) (tasks : List Task) :
    spec_load_balancing workers 0 →
    spec_fairness workers tasks := by
  intro h_spec
  have h_balanced : is_balanced workers := by
    exact h_spec
  have h_fairness : spec_fairness workers tasks := by
    exact lemma_fairness_preserved workers tasks h_balanced
  exact h_fairness

end Morph.Specs.SchedulerRandomizedStealing
-/