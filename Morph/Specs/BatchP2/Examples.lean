/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP2.Lemmas

/-!
# Feasible-50 kernels — P2 examples

Status: first cycle complete (loop 110).

Concrete instances of the ten cores. Every example is `decide`/`rfl`-checked;
the law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.BatchP2

/-! ## E-151: a forked nursery -/

/-- Two leaves under one fork. -/
example : leafCount (.fork (.leaf 1) (.leaf 2)) = 2 := rfl

/-- Join lists both items. -/
example : joinAll (.fork (.leaf 1) (.leaf 2)) = [1, 2] := rfl

/-- Join length matches the count. -/
example : (joinAll (.fork (.leaf 1) (.leaf 2))).length =
    leafCount (.fork (.leaf 1) (.leaf 2)) :=
  joinAll_length _

/-! ## E-156: combining two batches -/

/-- Batch sum is the list sum. -/
example : batch [1, 2, 3] = 6 := rfl

/-- Combined batches add. -/
example : batchAdd [1, 2] [3] = batch [1, 2] + batch [3] :=
  batchAdd_eq [1, 2] [3]

/-! ## E-157: writing keeps reads clean -/

/-- An even cell reads clean. -/
example : readOk ⟨4, 9⟩ = true := by decide

/-- A write keeps the read clean. -/
example : readOk (writeSeq ⟨4, 9⟩ 10) = true :=
  readOk_write ⟨4, 9⟩ 10 (by decide)

/-- An odd cell is mid-write. -/
example : readOk ⟨5, 9⟩ = false := by decide

/-! ## E-159: replaying a log -/

/-- Replay lists task order. -/
example : replay [(1, 7), (2, 8)] = [1, 2] := rfl

/-- Replay length matches. -/
example : replayLen [(1, 7), (2, 8)] = 2 :=
  replayLen_eq _

/-- A logged task appears. -/
example : 2 ∈ replay [(1, 7), (2, 8)] :=
  mem_replay _ 2 8 (by decide)

/-! ## E-160: handing a message over -/

/-- Transfer sets the owner. -/
example : (give ⟨1, 42⟩ 7).owner = 7 :=
  give_owner ⟨1, 42⟩ 7

/-- The payload survives. -/
example : payloadOf (give ⟨1, 42⟩ 7) = 42 :=
  give_payload ⟨1, 42⟩ 7

/-! ## E-161: restarting a child -/

/-- A failed child restarts. -/
example : restart (.failed 3) = .restarted :=
  restart_failed 3

/-- Restart is idempotent on the example. -/
example : restart (restart (.failed 3)) = restart (.failed 3) :=
  restart_idem _

/-! ## E-162: admitting inside the window -/

/-- Five units fit a 3-used 10-limit window. -/
example : admitC ⟨10, 3⟩ 5 = true := by decide

/-- The admission fits the limit. -/
example : 5 + (⟨10, 3⟩ : Credit).used ≤ (⟨10, 3⟩ : Credit).limit :=
  admitC_sound ⟨10, 3⟩ 5 (by decide) (by decide)

/-- Nine units do not fit. -/
example : admitC ⟨10, 3⟩ 9 = false := by decide

/-! ## E-163: delivering once -/

/-- First delivery accepted. -/
example : deliver [1] 2 = (true, [2, 1]) :=
  deliver_fresh [1] 2 (by decide)

/-- Redelivery refused. -/
example : deliver [1] 1 = (false, [1]) :=
  deliver_dup [1] 1 (by decide)

/-! ## E-172: merging replicas -/

/-- Merge takes the max. -/
example : mergeG ⟨3⟩ ⟨5⟩ = ⟨5⟩ := rfl

/-- Merge commutes on the example. -/
example : mergeG ⟨3⟩ ⟨5⟩ = mergeG ⟨5⟩ ⟨3⟩ :=
  mergeG_comm _ _

/-- Increment grows. -/
example : (⟨3⟩ : GCount).v < ((incr ⟨3⟩)).v :=
  incr_gt _

/-! ## E-174: naming a cycle -/

/-- The pair deadlocks. -/
example : deadlock2 [(1, 2), (2, 1)] 1 2 = true := by decide

/-- The test names both edges. -/
example : (1, 2) ∈ [(1, 2), (2, 1)] ∧ (2, 1) ∈ [(1, 2), (2, 1)] :=
  deadlock2_sound _ 1 2 (by decide)

/-- No self-loop here. -/
example : deadlockSelf [(1, 2), (2, 1)] 1 = false := by decide

end Morph.Specs.BatchP2
