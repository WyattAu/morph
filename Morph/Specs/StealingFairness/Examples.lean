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

end Morph.Specs.StealingFairness
