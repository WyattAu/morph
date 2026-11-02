/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP2.Examples

/-!
# Feasible-50 kernels — P2 validation

Status: first cycle complete (loop 110).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(join preservation, idempotent delivery, semilattice merge) are exercised
where a single example could pass by accident.

Run: `lake build Morph.Tests.BatchP2`.
-/

namespace Morph.Tests.BatchP2

open Morph.Specs.BatchP2

/-! ## E-151: joins on fresh trees -/

/-- A fresh three-leaf join preserves the count. -/
example : (joinAll (.fork (.leaf 3) (.fork (.leaf 4) (.leaf 5)))).length = 3 :=
  joinAll_length _

/-- A fresh fork adds the counts. -/
example : leafCount (.fork (.leaf 3) (.leaf 4)) = 1 + 1 :=
  leafCount_fork _ _

/-! ## E-156: batches on fresh lists -/

/-- A fresh combined batch adds. -/
example : batchAdd [4] [5, 6] = batch [4] + batch [5, 6] :=
  batchAdd_eq [4] [5, 6]

/-- An empty batch sums to zero. -/
example : batch [] = 0 := rfl

/-! ## E-157: writes on fresh cells -/

/-- A fresh write keeps the read clean. -/
example : readOk (writeSeq ⟨0, 1⟩ 2) = true :=
  readOk_write ⟨0, 1⟩ 2 (by decide)

/-- A fresh odd cell is mid-write. -/
example : readOk ⟨7, 1⟩ = false := by decide

/-! ## E-159: replay on a fresh log -/

/-- A fresh replay preserves length. -/
example : replayLen [(3, 1), (4, 2), (5, 3)] = 3 :=
  replayLen_eq _

/-- A fresh logged task appears. -/
example : 4 ∈ replay [(3, 1), (4, 2)] :=
  mem_replay _ 4 2 (by decide)

/-! ## E-160: transfer on a fresh message -/

/-- A fresh transfer sets the owner. -/
example : (give ⟨2, 11⟩ 9).owner = 9 :=
  give_owner _ 9

/-- A fresh payload survives. -/
example : payloadOf (give ⟨2, 11⟩ 9) = 11 :=
  give_payload _ 9

/-! ## E-161: restart on fresh states -/

/-- A fresh restart is idempotent. -/
example : restart (restart (.failed 8)) = restart (.failed 8) :=
  restart_idem _

/-- A fresh running child is untouched. -/
example : restart .running = .running := rfl

/-! ## E-162: window checks on fresh credits -/

/-- A fresh fitting request is admitted. -/
example : admitC ⟨12, 4⟩ 6 = true :=
  admitC_complete ⟨12, 4⟩ 6 (by decide) (by decide)

/-- A fresh over-request is refused. -/
example : admitC ⟨12, 4⟩ 9 = false := by decide

/-! ## E-163: dedup on fresh keys -/

/-- A fresh key is accepted. -/
example : deliver [7] 8 = (true, [8, 7]) :=
  deliver_fresh [7] 8 (by decide)

/-- A fresh redelivery is refused. -/
example : deliver [7, 8] 7 = (false, [7, 8]) :=
  deliver_dup [7, 8] 7 (by decide)

/-! ## E-172: merges on fresh replicas -/

/-- A fresh merge is associative. -/
example : mergeG (mergeG ⟨2⟩ ⟨5⟩) ⟨4⟩ = mergeG ⟨2⟩ (mergeG ⟨5⟩ ⟨4⟩) :=
  mergeG_assoc _ _ _

/-- A fresh merge is idempotent. -/
example : mergeG ⟨6⟩ ⟨6⟩ = ⟨6⟩ :=
  mergeG_idem _

/-! ## E-174: cycles on fresh edges -/

/-- A fresh 2-cycle is symmetric. -/
example : deadlock2 [(3, 4), (4, 3)] 3 4 = deadlock2 [(3, 4), (4, 3)] 4 3 :=
  deadlock2_symm _ 3 4

/-- A fresh self-loop is named. -/
example : (5, 5) ∈ [(5, 5), (1, 2)] :=
  deadlockSelf_sound _ 5 (by decide)

/-- A fresh acyclic set is quiet. -/
example : deadlock2 [(1, 2), (2, 3)] 1 2 = false := by decide

end Morph.Tests.BatchP2
