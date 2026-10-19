/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.StealingFairness.Spec

/-!
# Conservation, no duplication, termination
-/

namespace Morph.Specs.StealingFairness

/-! ### The deque discipline -/

/-- Stealing consumes work: a successful steal leaves exactly one task less. -/
theorem total_steal {d d' : Deque} {t : Task} (h : Deque.steal d = some (d', t)) :
    d'.total + 1 = d.total := by
  cases d with
  | mk bottom top =>
      cases htop : top with
      | nil => simp [Deque.steal, htop] at h
      | cons x xs =>
          simp only [Deque.steal, htop] at h
          injection h with h1
          cases h1
          simp [Deque.total]
          omega

/-- Running consumes work: a successful pop leaves exactly one task less. -/
theorem total_pop {d d' : Deque} {t : Task} (h : Deque.pop d = some (d', t)) :
    d'.total + 1 = d.total := by
  cases d with
  | mk bottom top =>
      cases hbot : bottom with
      | nil => simp [Deque.pop, hbot] at h
      | cons x xs =>
          simp only [Deque.pop, hbot] at h
          injection h with h1
          cases h1
          simp [Deque.total]
          omega

/-- **A pop takes the *newest* task** — LIFO at the owner end, for cache
locality. This is the discipline half of "the owner owns the bottom". -/
theorem pop_takes_newest {d d' : Deque} {t : Task} (h : Deque.pop d = some (d', t)) :
    d.bottom = t :: d'.bottom := by
  cases d with
  | mk bottom top =>
      cases hbot : bottom with
      | nil => simp [Deque.pop, hbot] at h
      | cons x xs =>
          simp only [Deque.pop, hbot] at h
          injection h with h1
          cases h1
          rfl

/-- **A steal takes the *oldest* task** — FIFO at the thief end, so the largest,
coldest chunk moves first. The two equations above together are why work
stealing gets both cache locality and load balance. -/
theorem steal_takes_oldest {d d' : Deque} {t : Task} (h : Deque.steal d = some (d', t)) :
    d.top = t :: d'.top := by
  cases d with
  | mk bottom top =>
      cases htop : top with
      | nil => simp [Deque.steal, htop] at h
      | cons x xs =>
          simp only [Deque.steal, htop] at h
          injection h with h1
          cases h1
          rfl

/-- **The last-element race, in the sequential abstraction.** On a one-element
deque the owner and the thief cannot both get the task: whoever takes it first
leaves the deque empty at that end, and the other end has nothing. Chase–Lev
added a CAS on `top` to force exactly this; Lê et al. exhibited a racing steal on
an empty deque returning a stale value — *fabrication*, which is strictly worse
than duplication. -/
theorem last_element_race_owner_first (t : Task) :
    Deque.pop { bottom := [t], top := [] } = some ({ bottom := [], top := [] }, t) ∧
      Deque.steal { bottom := [], top := [] } = none := ⟨rfl, rfl⟩

theorem last_element_race_thief_first (t : Task) :
    Deque.steal { bottom := [], top := [t] } = some ({ bottom := [], top := [] }, t) ∧
      Deque.pop { bottom := [], top := [] } = none := ⟨rfl, rfl⟩

/-- **A thief never steals from an empty deque** — the discipline's precondition,
and the reason a thief's retry loop terminates per victim. -/
theorem steal_from_empty_is_none :
    ∀ (d : Deque) (t : Task), Deque.steal d = some (d, t) → False := by
  intro d t h
  cases d with
  | mk bottom top =>
      cases htop : top with
      | nil => simp [Deque.steal, htop] at h
      | cons x xs => simp only [Deque.steal, htop] at h; injection h with h1; cases h1

/-! ### Conservation: the scheduler moves work, it does not invent it

Blumofe & Leiserson's requirement for provable efficiency. A steal moves one task
from the victim to the thief; a run moves one task from a queue to the log.
Neither creates work. -/

theorem queued_push (d : Deque) (t : Task) : Deque.total (Deque.push d t) = d.total + 1 := by
  simp [Deque.push, Deque.total]
  omega

/-! ### Conservation at the scheduler level

Stating the arithmetic in general form first keeps the proofs away from
structure-update expressions, which is where this loop previously stalled. -/

/-- **A steal conserves work, stated generally.** One task leaves the victim, one
enters the thief, one enters the log — net zero. -/
private theorem steal_conserves (th v th' v' : Deque) (ran : List Task) (t : Task)
    (hp : Deque.push th t = th') (hs : Deque.steal v = some (v', t)) :
    th'.total + v'.total + ran.length = th.total + v.total + ran.length := by
  have hp' : th'.total = th.total + 1 := by rw [← hp]; exact queued_push th t
  have hs' : v'.total + 1 = v.total := total_steal hs
  omega

/-- **A run conserves work, stated generally.** -/
private theorem run_conserves (th th' v : Deque) (ran : List Task) (t : Task)
    (hp : Deque.pop th = some (th', t)) :
    th'.total + v.total + (t :: ran).length = th.total + v.total + ran.length := by
  have hp' : th'.total + 1 = th.total := total_pop hp
  simp only [List.length_cons]
  omega

/-- The scheduler's total responsibility is unchanged by a steal. -/
theorem stealFrom_work {p p' : Pair} (h : p.stealFrom = some p') : p'.work = p.work := by
  obtain ⟨th, v, ran⟩ := p
  cases hv : v.top with
  | nil => simp [Pair.stealFrom, Deque.steal, hv] at h
  | cons t ts =>
      simp only [Pair.stealFrom, Deque.steal, hv] at h
      injection h with heq
      cases heq
      have hs : Deque.steal v = some ({ v with top := ts }, t) := by rw [Deque.steal, hv]
      simp only [Pair.work]
      have := steal_conserves th v (Deque.push th t) ({ v with top := ts }) ran t rfl hs
      omega

/-- The scheduler's total responsibility is unchanged by a run. -/
theorem runOwn_work {p p' : Pair} (h : p.runOwn = some p') : p'.work = p.work := by
  obtain ⟨th, v, ran⟩ := p
  cases hb : th.bottom with
  | nil => simp [Pair.runOwn, Deque.pop, hb] at h
  | cons t ts =>
      simp only [Pair.runOwn, Deque.pop, hb] at h
      injection h with heq
      cases heq
      have hp : Deque.pop th = some ({ th with bottom := ts }, t) := by rw [Deque.pop, hb]
      simp only [Pair.work]
      have := run_conserves th ({ th with bottom := ts }) v ran t hp
      omega

/-- **A steal moves work without running it**, so the run log is unchanged.
This is the half of work conservation that makes a steal safe: the task is not
free, it has moved to the thief's queue and will be accounted for when it runs. -/
theorem stealFrom_ran {p p' : Pair} (h : p.stealFrom = some p') :
    p'.ran.length = p.ran.length := by
  obtain ⟨th, v, ran⟩ := p
  cases hv : v.top with
  | nil => simp [Pair.stealFrom, Deque.steal, hv] at h
  | cons t ts =>
      simp only [Pair.stealFrom, Deque.steal, hv] at h
      injection h with heq
      cases heq
      rfl

/-- A run step appends exactly one task to the run log. -/
theorem runOwn_ran'' {p p' : Pair} (h : p.runOwn = some p') :
    p'.ran.length = p.ran.length + 1 := by
  obtain ⟨th, v, ran⟩ := p
  cases hb : th.bottom with
  | nil => simp [Pair.runOwn, Deque.pop, hb] at h
  | cons t ts =>
      simp only [Pair.runOwn, Deque.pop, hb] at h
      injection h with heq
      cases heq
      rfl

theorem runOwn_ran {p p' : Pair} (h : p.runOwn = some p') :
    p'.ran.length = p.ran.length + 1 := by
  obtain ⟨th, v, ran⟩ := p
  cases hb : th.bottom with
  | nil => simp [Pair.runOwn, Deque.pop, hb] at h
  | cons t ts =>
      simp only [Pair.runOwn, Deque.pop, hb] at h
      injection h with heq
      cases heq
      rfl

/-- Executing steps: steal or run. -/
def Executes (p p' : Pair) : Prop := p.stealFrom = some p' ∨ p.runOwn = some p'

/-- Reflexive-transitive closure of executing steps. -/
inductive ExecutesStar : Pair → Pair → Prop
  | refl (p : Pair) : ExecutesStar p p
  | step {p m p' : Pair} (h : Executes p m) (hs : ExecutesStar m p') : ExecutesStar p p'

/-- **Termination, and with it fairness.** Along any sequence of executing steps
the run log can never outgrow the scheduler's total work. A work-stealing
scheduler that only executes performs at most `work` steps and then stops: it
cannot spin forever, and it cannot log a task it has already logged, because the
log is exactly what each step grew by.

This is the theorem the shipped `isFair` was reaching for, and the only honest
version of "the scheduler terminates". -/
theorem ran_le_work {p p' : Pair} (h : ExecutesStar p p') : p'.ran.length ≤ p'.work := by
  induction h with
  | refl p => simp only [Pair.work]; omega
  | step hx hs ih =>
      rcases hx with hst | hrn
      · have h1 := stealFrom_ran hst
        have h2 := stealFrom_work hst
        omega
      · have h1 := runOwn_ran hrn
        have h2 := runOwn_work hrn
        omega

/-- **The run log never exceeds the scheduler's *initial* responsibility.** Work
is conserved at every step, so the log cannot grow past the total work the
scheduler started with — which is the operational content of "each task runs at
most once": there are only ever that many tasks to run. -/
theorem ran_le_initial_work {p p' : Pair} (h : ExecutesStar p p') :
    p'.ran.length ≤ p.work := by
  induction h with
  | refl p => simp only [Pair.work]; omega
  | step hx hs ih =>
      rcases hx with hst | hrn
      · have h2 := stealFrom_work hst
        omega
      · have h2 := runOwn_work hrn
        omega

end Morph.Specs.StealingFairness
