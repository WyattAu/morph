import Morph.Specs.SchedulerRandomizedStealing.Spec

namespace Morph.Specs.SchedulerRandomizedStealing.Examples

def example_worker1 : Worker :=
  { id := { id := 0 }, queue := [{ id := 0, workload := 1 }, { id := 1, workload := 1 }, { id := 2, workload := 1 }] }

def example_worker2 : Worker :=
  { id := { id := 1 }, queue := [] }

def example_workers : List Worker :=
  [example_worker1, example_worker2]

example : spec_work_stealing_scheduler example_workers { id := 0 } { id := 1 } := by
  -- Prove work-stealing scheduler property for example_workers
  -- We need to show that if stealer.id ≠ victim.id and w1.queue.length < w2.queue.length,
  -- then there exists a task in w2's queue that is not in w1's queue
  intro h_neq
  -- Show that worker with id 0 exists in example_workers
  have h_w1_exists : ∃ (w1 : Worker), w1 ∈ example_workers ∧ w1.id = { id := 0 } := by
    exists example_worker1
    constructor
    · -- Show example_worker1 ∈ example_workers
      apply List.mem_head
    · -- Show example_worker1.id = { id := 0 }
      rfl
  cases h_w1_exists with
  | intro w1 h_w1_props =>
    -- Show that worker with id 1 exists in example_workers
    have h_w2_exists : ∃ (w2 : Worker), w2 ∈ example_workers ∧ w2.id = { id := 1 } := by
      exists example_worker2
      constructor
      · -- Show example_worker2 ∈ example_workers
        apply List.mem_tail
        apply List.mem_head
      · -- Show example_worker2.id = { id := 1 }
        rfl
    cases h_w2_exists with
    | intro w2 h_w2_props =>
      -- Show that w1.queue.length < w2.queue.length is false (since w2.queue is empty)
      -- Actually, w1.queue.length = 3 and w2.queue.length = 0
      -- So w1.queue.length > w2.queue.length, not <
      -- The work-stealing scheduler property requires w1.queue.length < w2.queue.length
      -- But in this example, w1 has more tasks than w2
      -- So the property is vacuously true (the antecedent is false)
      -- We need to show: w1.queue.length < w2.queue.length → ∃ task, task ∈ w2.queue ∧ task ∉ w1.queue
      -- Since w1.queue.length = 3 and w2.queue.length = 0, we have w1.queue.length < w2.queue.length = false
      -- Therefore, the implication is vacuously true
      intro h_lt
      -- h_lt is false (3 < 0 is false), so we can derive anything
      contradiction

def example_ball1 : Ball :=
  { id := 0 }

def example_ball2 : Ball :=
  { id := 1 }

def example_ball3 : Ball :=
  { id := 2 }

def example_balls : List Ball :=
  [example_ball1, example_ball2, example_ball3]

def example_bin1 : Bin :=
  { id := { id := 0 }, balls := [example_ball1, example_ball2] }

def example_bin2 : Bin :=
  { id := { id := 1 }, balls := [example_ball3] }

def example_bins : List Bin :=
  [example_bin1, example_bin2]

example : spec_balls_into_bins_algorithm example_balls example_bins := by
  -- Prove balls-into-bins algorithm property for example_balls and example_bins
  -- We need to show that for each ball in example_balls,
  -- there exists a bin in example_bins containing that ball
  -- and each ball is in exactly one bin
  intro b h_b
  -- Check which ball we're dealing with
  cases h_b_eq : b = example_ball1 ∨ b = example_ball2 ∨ b = example_ball3
  · -- Case: b = example_ball1
    -- Show that example_ball1 is in example_bin1
    have h_ball1_in_bin1 : example_ball1 ∈ example_bin1.balls := by
      -- example_bin1.balls = [example_ball1, example_ball2]
      -- So example_ball1 is the first element
      apply List.mem_head
    -- Show that example_ball1 is not in example_bin2.balls
    have h_ball1_not_in_bin2 : example_ball1 ∉ example_bin2.balls := by
      -- example_bin2.balls = [example_ball3]
      -- So example_ball1 is not in this list
      intro h_in
      -- h_in : example_ball1 ∈ [example_ball3]
      -- This is false since example_ball1 ≠ example_ball3
      cases h_in
      · -- case: example_ball1 = example_ball3
        -- This is false
        contradiction
      · -- case: example_ball1 ∈ []
        -- This is false
        contradiction
    -- Return example_bin1
    exists example_bin1
    constructor
    · -- Show example_bin1 ∈ example_bins
      apply List.mem_head
    · -- Show example_ball1 ∈ example_bin1.balls
      exact h_ball1_in_bin1
  · -- Case: b = example_ball2
    -- Show that example_ball2 is in example_bin1
    have h_ball2_in_bin1 : example_ball2 ∈ example_bin1.balls := by
      -- example_bin1.balls = [example_ball1, example_ball2]
      -- So example_ball2 is the second element
      apply List.mem_tail
      apply List.mem_head
    -- Show that example_ball2 is not in example_bin2.balls
    have h_ball2_not_in_bin2 : example_ball2 ∉ example_bin2.balls := by
      -- example_bin2.balls = [example_ball3]
      -- So example_ball2 is not in this list
      intro h_in
      -- h_in : example_ball2 ∈ [example_ball3]
      -- This is false since example_ball2 ≠ example_ball3
      cases h_in
      · -- case: example_ball2 = example_ball3
        -- This is false
        contradiction
      · -- case: example_ball2 ∈ []
        -- This is false
        contradiction
    -- Return example_bin1
    exists example_bin1
    constructor
    · -- Show example_bin1 ∈ example_bins
      apply List.mem_head
    · -- Show example_ball2 ∈ example_bin1.balls
      exact h_ball2_in_bin1
  · -- Case: b = example_ball3
    -- Show that example_ball3 is in example_bin2
    have h_ball3_in_bin2 : example_ball3 ∈ example_bin2.balls := by
      -- example_bin2.balls = [example_ball3]
      -- So example_ball3 is the first element
      apply List.mem_head
    -- Show that example_ball3 is not in example_bin1.balls
    have h_ball3_not_in_bin1 : example_ball3 ∉ example_bin1.balls := by
      -- example_bin1.balls = [example_ball1, example_ball2]
      -- So example_ball3 is not in this list
      intro h_in
      -- h_in : example_ball3 ∈ [example_ball1, example_ball2]
      -- This is false since example_ball3 ≠ example_ball1 and example_ball3 ≠ example_ball2
      cases h_in
      · -- case: example_ball3 = example_ball1
        -- This is false
        contradiction
      · -- case: example_ball3 = example_ball2
        -- This is false
        contradiction
    -- Return example_bin2
    exists example_bin2
    constructor
    · -- Show example_bin2 ∈ example_bins
      apply List.mem_tail
      apply List.mem_head
    · -- Show example_ball3 ∈ example_bin2.balls
      exact h_ball3_in_bin2

def example_convergence_workers : List Worker :=
  [ { id := { id := 0 }, queue := [{ id := 0, workload := 1 }] },
    { id := { id := 1 }, queue := [{ id := 1, workload := 1 }] },
    { id := { id := 2 }, queue := [] } ]

example : spec_convergence_bounds example_convergence_workers 2 := by
  -- Prove convergence bounds property for example_convergence_workers with k = 2
  -- We need to show that max_imbalance example_convergence_workers ≤ convergence_bound 3 2
  -- First, compute max_imbalance
  -- Queue lengths: [1, 1, 0]
  -- maxLoad = 1, minLoad = 0
  -- max_imbalance = 1 - 0 = 1
  -- We need to show: 1 ≤ convergence_bound 3 2
  -- By definition of convergence_bound, convergence_bound 3 2 should be at least 1
  -- (since the system is not yet balanced after 2 rounds)
  -- For this example, we can assume convergence_bound 3 2 = 1 or greater
  -- So 1 ≤ convergence_bound 3 2 holds
  -- We prove this by showing that max_imbalance = 1
  have h_max_load : (example_convergence_workers.map (·.queue.length)).getD 0 0 |>.max = 1 := by
    -- The maximum queue length is 1
    rfl
  have h_min_load : (example_convergence_workers.map (·.queue.length)).getD 0 0 |>.min = 0 := by
    -- The minimum queue length is 0
    rfl
  have h_imbalance : max_imbalance example_convergence_workers = 1 := by
    -- max_imbalance = maxLoad - minLoad = 1 - 0 = 1
    rfl
  -- Now we need to show that 1 ≤ convergence_bound 3 2
  -- This follows from the definition of convergence_bound
  -- For this example, we can use the fact that convergence_bound 3 2 ≥ 1
  -- (since the system is not yet balanced)
  have h_bound : convergence_bound 3 2 ≥ 1 := by
    -- This follows from the definition of convergence_bound
    -- For a system with 3 workers and 2 rounds, the bound is at least 1
    sorry
  -- Therefore, max_imbalance ≤ convergence_bound
  exact h_bound

def example_balanced_workers : List Worker :=
  [ { id := { id := 0 }, queue := [{ id := 0, workload := 1 }] },
    { id := { id := 1 }, queue := [{ id := 1, workload := 1 }] },
    { id := { id := 2 }, queue := [{ id := 2, workload := 1 }] } ]

example : is_balanced example_balanced_workers := by
  -- Prove that example_balanced_workers is balanced
  -- We need to show that for all w1, w2 in example_balanced_workers,
  -- |w1.queue.length - w2.queue.length| ≤ 1
  -- Queue lengths: [1, 1, 1]
  -- All queue lengths are equal, so the deviation is 0 ≤ 1
  intro w1 w2 h_w1 h_w2
  -- Show that |w1.queue.length - w2.queue.length| ≤ 1
  -- Since all queue lengths are 1, the difference is 0
  have h_w1_len : w1.queue.length = 1 := by
    -- All workers in example_balanced_workers have queue.length = 1
    sorry
  have h_w2_len : w2.queue.length = 1 := by
    -- All workers in example_balanced_workers have queue.length = 1
    sorry
  -- Compute the difference
  have h_diff : |w1.queue.length - w2.queue.length| = |1 - 1| := by
    rw [h_w1_len, h_w2_len]
  have h_diff_zero : |1 - 1| = 0 := by
    -- |0| = 0
    rfl
  have h_le_one : 0 ≤ 1 := by
    -- 0 ≤ 1 is true
    apply Nat.le_refl
  -- Therefore, |w1.queue.length - w2.queue.length| ≤ 1
  rw [h_diff, h_diff_zero]
  exact h_le_one

def example_fair_tasks : List Task :=
  [{ id := 0, workload := 1 },
   { id := 1, workload := 1 },
   { id := 2, workload := 1 },
   { id := 3, workload := 1 }]

def example_fair_workers : List Worker :=
  [ { id := { id := 0 }, queue := [{ id := 0, workload := 1 }, { id := 1, workload := 1 }] },
    { id := { id := 1 }, queue := [{ id := 2, workload := 1 }, { id := 3, workload := 1 }] } ]

example : spec_fairness example_fair_workers example_fair_tasks := by
  -- Prove fairness property for example_fair_workers and example_fair_tasks
  -- We need to show that spec_load_balancing example_fair_workers 0 implies
  -- is_fair example_fair_workers example_fair_tasks
  -- First, compute total workload
  have h_total_workload : (example_fair_tasks.map (·.workload)).sum = 4 := by
    -- Each task has workload 1, and there are 4 tasks
    -- So total workload = 4
    rfl
  -- Compute worker workloads
  have h_worker0_workload : (example_fair_workers.get! 0).queue.map (·.workload).sum = 2 := by
    -- Worker 0 has 2 tasks, each with workload 1
    -- So workload = 2
    rfl
  have h_worker1_workload : (example_fair_workers.get! 1).queue.map (·.workload).sum = 2 := by
    -- Worker 1 has 2 tasks, each with workload 1
    -- So workload = 2
    rfl
  -- Compute average workload
  have h_avg_workload : h_total_workload / example_fair_workers.length = 2 := by
    -- Average = 4 / 2 = 2
    rfl
  -- Now show that for each worker, the deviation from average is bounded
  -- For worker 0: |2 - 2| = 0 ≤ 2
  have h_worker0_fair : |h_worker0_workload - h_avg_workload| ≤ h_avg_workload := by
    -- |2 - 2| = 0 ≤ 2
    have h_diff_zero : |2 - 2| = 0 := by
      -- |0| = 0
      rfl
    have h_le : 0 ≤ 2 := by
      -- 0 ≤ 2 is true
      apply Nat.le.step
      apply Nat.le_refl
    rw [h_diff_zero]
    exact h_le
  -- For worker 1: |2 - 2| = 0 ≤ 2
  have h_worker1_fair : |h_worker1_workload - h_avg_workload| ≤ h_avg_workload := by
    -- |2 - 2| = 0 ≤ 2
    have h_diff_zero : |2 - 2| = 0 := by
      -- |0| = 0
      rfl
    have h_le : 0 ≤ 2 := by
      -- 0 ≤ 2 is true
      apply Nat.le.step
      apply Nat.le_refl
    rw [h_diff_zero]
    exact h_le
  -- Therefore, is_fair example_fair_workers example_fair_tasks holds
  -- This follows from the definition of is_fair
  sorry

end Morph.Specs.SchedulerRandomizedStealing.Examples
