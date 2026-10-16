/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ActorDeadlock.Lemmas

namespace Morph.Specs.ActorDeadlock

/-! ## Worked examples

The theorems are usable as-is; these examples check the model against
concrete two-actor systems. -/

/-- Two actors, nobody waiting, both runnable: not a deadlock. -/
def bothRunning : Sys where
  actors := [0, 1]
  run := [0, 1]
  waitOn := fun _ => none

example : bothRunning.run ≠ [] := by
  decide

/-- `ask`: actor 0 asks actor 1 and blocks; only actor 1 is left runnable. -/
def afterAsk : Sys := Ask bothRunning 0 1

example : afterAsk.run = [1] := by
  decide

/-- The outstanding request is recorded in the wait-for graph. -/
example : Waits afterAsk 0 1 := by
  rfl

example : waitEdges afterAsk = [(0, 1)] := by
  decide

/-- `serve`: actor 1 satisfies the request and actor 0 becomes runnable again. -/
def afterServe : Sys := Serve afterAsk 1 0

example : afterServe.run = [0, 1] := by
  decide

example : ¬ Blocked afterServe 0 := by
  simp [Blocked, afterServe, Serve, Ask, bothRunning]

/-- A wait-for graph with a cycle: 0 waits for 1, 1 waits for 0, nobody runs.
This is exactly the deadlock the rank condition rules out, and it shows the
model is not vacuous: the theorems need `Ranked`, and a cycle is a real
configuration. -/
def cyclic : Sys where
  actors := [0, 1]
  run := []
  waitOn := fun p => if p = 0 then some 1 else if p = 1 then some 0 else none

example : Deadlock cyclic := by
  rfl

example : Waits cyclic 0 1 ∧ Waits cyclic 1 0 := by
  exact ⟨rfl, rfl⟩

/-- ... and such a cycle cannot respect any rank: a rank would have to satisfy
`rank 0 < rank 1 < rank 0`. -/
example : ¬ ∃ rank : Actor → Nat, Ranked cyclic rank := by
  rintro ⟨rank, h⟩
  have h1 := h 0 1 (by rfl)
  have h2 := h 1 0 (by rfl)
  omega

/-! ## The system-level theorem, instantiated -/

theorem WF_bothRunning : WF bothRunning := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro p hp
    simp [bothRunning] at hp
    rcases hp with rfl | rfl
    · exact Or.inr (by simp [Runnable, bothRunning])
    · exact Or.inr (by simp [Runnable, bothRunning])
  · intro p q h
    simp [bothRunning] at h
  · intro p
    simp [bothRunning]

theorem Ranked_bothRunning : Ranked bothRunning (fun p => p) := by
  intro p q h
  simp [bothRunning] at h

/-- The actor set never changes, so a reachable state has an actor to argue
from. -/
theorem actors_unchanged (rank : Actor → Nat) (s s' : Sys)
    (hrun : Steps rank s s') : s'.actors = s.actors := by
  induction hrun with
  | refl => rfl
  | tail x mid hsteps hstep =>
      rename_i ih
      cases hstep with
      | ask p q hp' hq hlt => exact ih
      | serve q p hq hw => exact ih

/-- **Deadlock freedom for a concrete system:** from a well-formed state whose
waits respect the rank order, no execution by any scheduler can reach a
deadlock. -/
theorem bothRunning_deadlockFree :
    ∀ s', Steps (fun p => p) bothRunning s' → s'.run ≠ [] := by
  intro s' hrun
  have hmem : 0 ∈ s'.actors := by
    rw [actors_unchanged _ _ _ hrun]
    decide
  exact progress_invariant bothRunning s' (fun p => p) WF_bothRunning
    Ranked_bothRunning (by decide) hrun hmem

end Morph.Specs.ActorDeadlock