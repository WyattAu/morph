/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.StealingFairness.Lemmas

/-!
# Worked examples: the Chase–Lev discipline, computed

The point of the loop is that the scheduler's correctness lives in *which end*
each party touches, and in the last-element race. These examples compute both.
-/

namespace Morph.Specs.StealingFairness

/-- A deque holding three tasks: two at the thief end, one at the owner end. -/
def sample : Deque := { bottom := [3], top := [1, 2] }

example : Deque.total sample = 3 := rfl

/-- **The owner pops the newest task** (LIFO, cache-hot) — the owner end only. -/
example : Deque.pop sample = some ({ bottom := [], top := [1, 2] }, 3) := rfl

/-- **A thief steals the oldest task** (FIFO, largest chunk) — the thief end only. -/
example : Deque.steal sample = some ({ bottom := [3], top := [2] }, 1) := rfl

/-- The owner pushes onto its own end, leaving the thief end untouched. -/
example : Deque.push sample 0 = { bottom := [0, 3], top := [1, 2] } := rfl

/-- **The last-element race.** One task, and the owner and thief cannot both get
it: whoever takes it first empties its end, and the other end finds nothing.
Chase–Lev needed a CAS on `top` to guarantee exactly this. -/
example : Deque.pop { bottom := [7], top := [] } = some (Deque.empty, 7) := rfl

example : Deque.steal Deque.empty = none := rfl

/-- The same, thief first. -/
example : Deque.steal { bottom := [], top := [7] } = some (Deque.empty, 7) := rfl

example : Deque.pop Deque.empty = none := rfl

/-- A thief that "succeeds" on an empty deque cannot exist — the precondition the
discipline needs, and the reason a thief's retry loop terminates. -/
example : Deque.steal Deque.empty = some (Deque.empty, 0) ↔ False := by
  constructor
  · intro h; exact steal_from_empty_is_none Deque.empty 0 h
  · intro h; exact absurd h (by simp [Deque.steal])

/-! ### The scheduler: conservation and termination, computed -/

/-- An idle thief and a victim holding one task. -/
def samplePair : Pair := { thief := Deque.empty, victim := { bottom := [], top := [1, 2] },
                           ran := [] }

/-- **A steal moves the task; it does not run it.** The victim's oldest task lands
in the thief's own queue and the run log is untouched. This is what makes a pair
of (steal, run) steps conserve work. -/
example : (samplePair.stealFrom).map (fun p => (p.thief.total, p.victim.total, p.ran.length)) =
    some (1, 1, 0) := by decide

/-- **Work conservation, discharged for that steal.** -/
example {p p' : Pair} (h : p.stealFrom = some p') : p'.work = p.work :=
  stealFrom_work h

/-- The run log is unchanged by a steal. -/
example {p p' : Pair} (h : p.stealFrom = some p') : p'.ran.length = p.ran.length :=
  stealFrom_ran h

/-- A run step *is* where the log grows, by exactly one. The thief's own queue
is empty here, so there is nothing to run — the theorem is stated for a state
where a run actually succeeds. -/
example {p p' : Pair} (h : p.runOwn = some p') :
    p'.ran.length = p.ran.length + 1 :=
  runOwn_ran h

/-- **Termination.** Along any sequence of executing steps the log never
outgrows the scheduler's total work — the only honest version of "the
work-stealing scheduler terminates". -/
example {p p' : Pair} (h : ExecutesStar p p') : p'.ran.length ≤ p'.work :=
  ran_le_work h

/-- And never past the work the scheduler started with. -/
example {p p' : Pair} (h : ExecutesStar p p') : p'.ran.length ≤ p.work :=
  ran_le_initial_work h

end Morph.Specs.StealingFairness
