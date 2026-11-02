/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP4.Lemmas

/-!
# Feasible-50 kernels — P4 examples

Status: first cycle complete (loop 110).

Concrete instances of the ten cores. Every example is `decide`/`rfl`-checked;
the law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.BatchP4

/-! ## E-380: framing a payload -/

/-- Framing then parsing roundtrips. -/
example : parseFrame (mkFrame [1, 2, 3]) = some [1, 2, 3] :=
  parse_mk _

/-- A wrong length is rejected. -/
example : parseFrame (2, [1, 2, 3]) = none :=
  parse_bad 2 [1, 2, 3] (by decide)

/-! ## E-381: encoding a message -/

/-- Every tag encodes in range. -/
example : tagToNat .itch ≤ 2 := tag_bound _

/-- An encoded message conforms. -/
example : conforms (encodeM ⟨.mdp, [1]⟩) = true :=
  encode_conforms _

/-- Tag 3 is out of range. -/
example : conforms (3, [1]) = false := by decide

/-! ## E-382: walking the session -/

/-- Logon reaches sync. -/
example : sstep .down .logon = some .sync := sstep_logon

/-- Close lands down from up. -/
example : sstep .up .close = some .down := sstep_close _

/-- Down admits no heartbeat. -/
example : sstep .down .heartbeat = none := sstep_down_hb

/-! ## E-383: spending tokens -/

/-- Taking 3 of 10 leaves 7. -/
example : takeB ⟨10, 10⟩ 3 = some ⟨7, 10⟩ := rfl

/-- The take preserves the account. -/
example : (⟨7, 10⟩ : Bucket).tokens + 3 = (⟨10, 10⟩ : Bucket).tokens ∧
    (⟨7, 10⟩ : Bucket).cap = (⟨10, 10⟩ : Bucket).cap :=
  takeB_sound ⟨10, 10⟩ 3 ⟨7, 10⟩ rfl

/-- Overspending is refused. -/
example : takeB ⟨2, 10⟩ 5 = none :=
  takeB_empty ⟨2, 10⟩ 5 (by decide)

/-- Refill respects the cap. -/
example : (refill ⟨8, 10⟩ 5).tokens ≤ 10 :=
  refill_cap ⟨8, 10⟩ 5

/-! ## E-384: dropping on disconnect -/

/-- Disconnect kills and clears. -/
example : disconnect ⟨true, [1, 2]⟩ = ⟨false, []⟩ := rfl

/-- Liveness dies. -/
example : (disconnect ⟨true, [1]⟩).alive = false :=
  disconnect_dead _

/-! ## E-385: syncing the backup -/

/-- Sync restores consistency. -/
example : consistent (syncB ⟨0, 0⟩ ⟨4, 9⟩) ⟨4, 9⟩ = true :=
  sync_consistent _ _

/-- Consistency names the agreement. -/
example : (⟨4, 9⟩ : Backup).seq = (⟨4, 9⟩ : Prim).seq ∧
    (⟨4, 9⟩ : Backup).dat = (⟨4, 9⟩ : Prim).dat :=
  consistent_sound _ _ (by decide)

/-- A stale backup is inconsistent. -/
example : consistent ⟨3, 9⟩ ⟨4, 9⟩ = false := by decide

/-! ## E-392: scheduling -/

/-- High priority wins. -/
example : sched [5, 1] [9] = some 5 := sched_hi 5 [1] [9]

/-- Low runs when high is empty. -/
example : sched [] [9] = some 9 := sched_lo 9 []

/-- Both empty idles. -/
example : sched [] [] = none := sched_none

/-! ## E-393: shaping -/

/-- Five units fit rate 3 plus burst 4. -/
example : allow ⟨3, 4⟩ 5 = true := by decide

/-- The admission fits the budget. -/
example : 5 ≤ (⟨3, 4⟩ : Shaper).rate + (⟨3, 4⟩ : Shaper).burst :=
  allow_sound ⟨3, 4⟩ 5 (by decide)

/-- Eight units do not fit. -/
example : allow ⟨3, 4⟩ 8 = false := by decide

/-- Extra burst admits more. -/
example : allow ⟨3, 5⟩ 7 = true :=
  allow_burst ⟨3, 4⟩ 7 (by decide)

/-! ## E-396: capturing -/

/-- Records parse back. -/
example : parseCap (mkCap 7 [1, 2]) = some (7, [1, 2]) :=
  cap_roundtrip 7 [1, 2]

/-- Capture preserves length. -/
example : (caps 7 [[1], [2, 3]]).length = 2 :=
  caps_length 7 [[1], [2, 3]]

/-- Payloads survive capture. -/
example : (7, [2, 3]) ∈ caps 7 [[1], [2, 3]] :=
  caps_mem 7 [[1], [2, 3]] [2, 3] (by decide)

/-! ## E-398: ticking -/

/-- Sends move forward. -/
example : 4 < sendL 4 := sendL_gt 4

/-- Receives cover both clocks. -/
example : 3 ≤ recvL 3 5 ∧ 5 ≤ recvL 3 5 :=
  ⟨recvL_left 3 5, recvL_right 3 5⟩

/-- Merging is symmetric. -/
example : recvL 3 5 = recvL 5 3 := recvL_symm 3 5

end Morph.Specs.BatchP4
