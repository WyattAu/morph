/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP4.Examples

/-!
# Feasible-50 kernels — P4 validation

Status: first cycle complete (loop 110).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(roundtrips, session walks, budget monotonicity) are exercised where a single
example could pass by accident.

Run: `lake build Morph.Tests.BatchP4`.
-/

namespace Morph.Tests.BatchP4

open Morph.Specs.BatchP4

/-! ## E-380: framing on fresh payloads -/

/-- A fresh roundtrip. -/
example : parseFrame (mkFrame [9, 8]) = some [9, 8] :=
  parse_mk _

/-- A fresh mismatch is rejected. -/
example : parseFrame (0, [9, 8]) = none :=
  parse_bad 0 [9, 8] (by decide)

/-! ## E-381: conformance on fresh messages -/

/-- A fresh encoding conforms. -/
example : conforms (encodeM ⟨.fix, [5, 6]⟩) = true :=
  encode_conforms _

/-- A fresh out-of-range tag fails. -/
example : conforms (9, [5]) = false := by decide

/-! ## E-382: walks on fresh states -/

/-- A fresh close lands down. -/
example : sstep .sync .close = some .down := sstep_close _

/-- A fresh gap-fill reaches up. -/
example : sstep .sync .gapfill = some .up := sstep_gapfill

/-- A fresh heartbeat stays up. -/
example : sstep .up .heartbeat = some .up := sstep_heartbeat

/-- A fresh illegal step is none. -/
example : sstep .down .gapfill = none := rfl

/-! ## E-383: buckets on fresh windows -/

/-- A fresh take preserves the account. -/
example : (⟨6, 12⟩ : Bucket).tokens + 6 = (⟨12, 12⟩ : Bucket).tokens ∧
    (⟨6, 12⟩ : Bucket).cap = (⟨12, 12⟩ : Bucket).cap :=
  takeB_sound ⟨12, 12⟩ 6 ⟨6, 12⟩ rfl

/-- A fresh refill respects the cap. -/
example : (refill ⟨12, 12⟩ 9).tokens ≤ 12 :=
  refill_cap ⟨12, 12⟩ 9

/-- A fresh empty bucket refuses. -/
example : takeB ⟨0, 4⟩ 1 = none :=
  takeB_empty ⟨0, 4⟩ 1 (by decide)

/-! ## E-384: disconnect on fresh conns -/

/-- A fresh disconnect clears. -/
example : (disconnect ⟨true, [3, 4, 5]⟩).pending = [] :=
  disconnect_empty _

/-- A fresh disconnect kills. -/
example : (disconnect ⟨true, [3]⟩).alive = false :=
  disconnect_dead _

/-! ## E-385: sync on fresh cursors -/

/-- A fresh sync is consistent. -/
example : consistent (syncB ⟨1, 1⟩ ⟨8, 2⟩) ⟨8, 2⟩ = true :=
  sync_consistent _ _

/-- A fresh stale backup fails. -/
example : consistent ⟨1, 1⟩ ⟨8, 2⟩ = false := by decide

/-! ## E-392: scheduling fresh queues -/

/-- A fresh high queue wins. -/
example : sched [2] [7, 8] = some 2 := sched_hi 2 [] [7, 8]

/-- A fresh low queue runs when high is empty. -/
example : sched [] [7, 8] = some 7 := sched_lo 7 [8]

/-- Fresh empty queues idle. -/
example : sched [] [] = none := sched_none

/-! ## E-393: shaping fresh budgets -/

/-- A fresh fitting burst is admitted. -/
example : allow ⟨5, 5⟩ 9 = true :=
  allow_complete ⟨5, 5⟩ 9 (by decide)

/-- A fresh over-budget burst is refused. -/
example : allow ⟨5, 5⟩ 11 = false := by decide

/-- Fresh burst growth admits more. -/
example : allow ⟨5, 6⟩ 10 = true :=
  allow_burst ⟨5, 5⟩ 10 (by decide)

/-! ## E-396: capture on fresh batches -/

/-- A fresh record roundtrips. -/
example : parseCap (mkCap 3 [8]) = some (3, [8]) :=
  cap_roundtrip 3 [8]

/-- A fresh capture preserves length. -/
example : (caps 3 [[8], [9]]).length = 2 :=
  caps_length 3 [[8], [9]]

/-- A fresh truncated record is rejected. -/
example : parseCap (3, 5, [8]) = none := by decide

/-! ## E-398: clocks on fresh values -/

/-- A fresh send ticks. -/
example : 10 < sendL 10 := sendL_gt 10

/-- A fresh merge covers both. -/
example : 2 ≤ recvL 2 9 ∧ 9 ≤ recvL 2 9 :=
  ⟨recvL_left 2 9, recvL_right 2 9⟩

/-- A fresh merge is symmetric. -/
example : recvL 9 2 = recvL 2 9 := recvL_symm 9 2

end Morph.Tests.BatchP4
