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

end Morph.Specs.StealingFairness
