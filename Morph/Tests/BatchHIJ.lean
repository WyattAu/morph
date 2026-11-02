/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchHIJ.Examples

/-!
# Frontier Kernels — validation (E-58–E-67)

Status: first cycle complete (loop 109).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(accounting, crossing, descent, impact) are exercised where a single example
could pass by accident.

Run: `lake build Morph.Tests.BatchHIJ`.
-/

namespace Morph.Tests.BatchHIJ

open Morph.Specs.BatchHIJ

/-! ## E-58: accounting on a fresh step -/

/-- A fresh drop-free step accounts exactly. -/
example : stepBuf 7 5 3 + 3 = 7 + 5 :=
  dropFree_sound 7 5 3 (by decide)

/-- The fresh level never exceeds inflow. -/
example : stepBuf 7 5 3 ≤ 7 + 5 :=
  stepBuf_le 7 5 3

/-- A fresh over-drain is refused. -/
example : dropFree 7 5 20 = false := by decide

/-! ## E-59: walls on a fresh path -/

/-- A fresh crossing names its wall. -/
example : ∃ w ∈ [4, 6, 11], 3 < w ∧ w ≤ 9 :=
  crosses_sound 3 9 [4, 6, 11] (by decide)

/-- A fresh quiet barcode stays quiet on every wall. -/
example : ∀ w ∈ [1, 12, 15], ¬(3 < w ∧ w ≤ 9) :=
  crosses_none 3 9 [1, 12, 15] (by decide)

/-- A fresh off-path wall is off. -/
example : between 3 9 12 = false := by decide

/-! ## E-60: flags on a fresh book -/

/-- A fresh positive bundle is found. -/
example : ∃ b ∈ ([⟨-2, 1⟩, ⟨7, 2⟩] : List Bundle), 0 < b.deg :=
  flagAll_sound _ (by decide)

/-- A fresh positive book raises the flag. -/
example : flagAll ([⟨-2, 1⟩, ⟨7, 2⟩] : List Bundle) = true :=
  flagAll_complete _ ⟨⟨7, 2⟩, by simp, by decide⟩

/-- A fresh negative leg is quiet. -/
example : hnFlag ⟨-5, 4⟩ = false := by decide

/-! ## E-61: flows on fresh quantities -/

/-- Fresh remaining plus sold equals the start. -/
example : flow1 12 3 2 + drained 12 3 2 = 12 :=
  drained_add 12 3 2

/-- Fresh decoupling preserves the asset count. -/
example : (liquidate [12, 5, 9] 3 2).length = 3 :=
  liquidate_length [12, 5, 9] 3 2

/-- A fresh zero rate leaves stock untouched. -/
example : flow1 12 0 9 = 12 :=
  flow1_zero 12 9

/-! ## E-62: descent on a fresh pair -/

/-- Fresh migration preserves total load. -/
example : (stepKN ⟨1, 8⟩).lo + (stepKN ⟨1, 8⟩).hi = 1 + 8 :=
  stepKN_sum ⟨1, 8⟩

/-- Fresh gap shrinks by two. -/
example : knGap (stepKN ⟨1, 8⟩) + 2 = knGap ⟨1, 8⟩ :=
  stepKN_gap2 ⟨1, 8⟩ (by decide) (by decide)

/-- Fresh equilibrium holds still. -/
example : stepKN ⟨6, 7⟩ = ⟨6, 7⟩ :=
  stepKN_stable ⟨6, 7⟩ (by decide)

/-! ## E-63: checks on fresh bundles -/

/-- A fresh zero leg admits. -/
example : admitA ⟨9, 4, 0, 11⟩ = true :=
  admitA_zero ⟨9, 4, 0, 11⟩ rfl

/-- A fresh nonzero product is rejected. -/
example : admitA ⟨9, 4, 3, 11⟩ = false := by decide

/-- Fresh exact admission lifts to tolerance. -/
example : admitTol ⟨9, 4, 0, 11⟩ 5 = true :=
  admitTol_of_admit _ 5 (by decide)

/-! ## E-64: guard on a fresh trace -/

/-- Fresh prunes never exceed the trace. -/
example : pruneCount [2, 14, 6, 20] 10 ≤ 4 :=
  pruneCount_le [2, 14, 6, 20] 10

/-- A fresh all-quiet trace keeps everything. -/
example : pruneCount [2, 6] 10 = 0 :=
  pruneCount_all_stay [2, 6] 10 (by decide)

/-- A fresh breach is pruned. -/
example : stay 20 10 = false := by decide

/-! ## E-65: shaping a fresh order -/

/-- Fresh slices add back. -/
example : (split2 14).1 + (split2 14).2 = 14 :=
  split2_add 14

/-- Fresh split never increases the impact model. -/
example : shapeImpact 14 ≤ 14 * 14 :=
  shapeImpact_le 14

/-- A fresh odd split fits. -/
example : (split2 13).2 ≤ 13 :=
  split2_snd_le 13

/-! ## E-66: fences on fresh direction sets -/

/-- A fresh elision shares no covector. -/
example : ∀ d ∈ [5, 6], d ∉ [7, 8] :=
  elideFence_sound [5, 6] [7, 8] (by decide)

/-- Fresh disjointness is complete. -/
example : disjointD [5, 6] [7, 8] = true :=
  disjointD_complete [5, 6] [7, 8] (by decide)

/-- A fresh shared covector blocks elision. -/
example : elideFence [5, 6] [6, 9] = false := by decide

/-! ## E-67: guard on a fresh book -/

/-- A fresh chamber exit is named. -/
example : 0 < charge 8 3 ∧ charge 2 9 ≤ 0 :=
  anchor_sound 8 3 2 9 (by decide)

/-- A fresh stable book never anchors. -/
example : anchor 8 3 9 4 = false :=
  anchor_stable 8 3 9 4 (by decide)

/-- A fresh quiet guard passes inventory through. -/
example : heldAfter 8 3 9 4 = 4 :=
  heldAfter_noanchor 8 3 9 4 (by decide)

end Morph.Tests.BatchHIJ
