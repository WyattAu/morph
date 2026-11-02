/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchHIJ.Lemmas

/-!
# Frontier Kernels — examples (E-58–E-67)

Status: first cycle complete (loop 109).

Concrete instances of the ten cores. Every example is `decide`/`rfl`-checked;
the law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.BatchHIJ

/-! ## E-58: one buffer step -/

/-- A step with room to drain. -/
example : stepBuf 10 3 4 = 9 := rfl

/-- The drain fits inside what arrived. -/
example : dropFree 10 3 4 = true := by decide

/-- An over-drain is refused. -/
example : dropFree 10 3 20 = false := by decide

/-- A two-day schedule folds to 1. -/
example : drainAll 5 [(3, 2), (1, 6)] = 1 := rfl

/-- The certificate on the fresh step. -/
example : stepBuf 10 3 4 + 4 = 10 + 3 :=
  dropFree_sound 10 3 4 (by decide)

/-! ## E-59: walls on an update path -/

/-- 5 lies on the path from 2 to 8. -/
example : between 2 8 5 = true := by decide

/-- 1 lies off the path. -/
example : between 2 8 1 = false := by decide

/-- The update crosses the tracked wall at 5. -/
example : crosses 2 8 [1, 5, 9] = true := by decide

/-- No tracked wall on this path. -/
example : crosses 2 8 [1, 9, 12] = false := by decide

/-- The crossing names its witness. -/
example : ∃ w ∈ [1, 5, 9], 2 < w ∧ w ≤ 8 :=
  crosses_sound 2 8 [1, 5, 9] (by decide)

/-! ## E-60: flagging a positive bundle -/

/-- Positive degree is flagged. -/
example : hnFlag ⟨5, 3⟩ = true := by decide

/-- Negative degree is quiet. -/
example : hnFlag ⟨-2, 3⟩ = false := by decide

/-- One positive bundle raises the polygon flag. -/
example : flagAll ([⟨-1, 2⟩, ⟨4, 1⟩] : List Bundle) = true := by decide

/-- An all-negative book stays quiet. -/
example : flagAll ([⟨-1, 2⟩, ⟨-3, 1⟩] : List Bundle) = false := by decide

/-- The flag names its bundle. -/
example : ∃ b ∈ ([⟨-1, 2⟩, ⟨4, 1⟩] : List Bundle), 0 < b.deg :=
  flagAll_sound _ (by decide)

/-! ## E-61: draining one asset -/

/-- One flow drops 10 to 4. -/
example : flow1 10 2 3 = 4 := rfl

/-- Two assets drain independently. -/
example : liquidate [10, 7] 2 3 = [4, 1] := rfl

/-- Six units sold off the first asset. -/
example : drained 10 2 3 = 6 := rfl

/-- Remaining plus sold equals the start. -/
example : flow1 10 2 3 + drained 10 2 3 = 10 :=
  drained_add 10 2 3

/-! ## E-62: one migration step -/

/-- The gap of the ordered pair. -/
example : knGap ⟨2, 9⟩ = 7 := rfl

/-- Migration moves one unit each way. -/
example : stepKN ⟨2, 9⟩ = ⟨3, 8⟩ := rfl

/-- At gap 1 the flow has stopped. -/
example : stepKN ⟨4, 5⟩ = ⟨4, 5⟩ := rfl

/-- The gap shrinks by two. -/
example : knGap (stepKN ⟨2, 9⟩) + 2 = knGap ⟨2, 9⟩ :=
  stepKN_gap2 ⟨2, 9⟩ (by decide) (by decide)

/-! ## E-63: admitting an atomic route -/

/-- Zero left leg: the error vanishes. -/
example : adhmErr ⟨3, 5, 0, 7⟩ = 0 := by decide

/-- The route is admitted. -/
example : admitA ⟨3, 5, 0, 7⟩ = true := by decide

/-- A nonzero product is rejected. -/
example : admitA ⟨3, 5, 2, 7⟩ = false := by decide

/-- Admission is the vanishing product. -/
example : admitA ⟨3, 5, 0, 7⟩ = true ↔ (0 : Int) * 7 = 0 :=
  admitA_iff ⟨3, 5, 0, 7⟩

/-! ## E-64: guarding a trace -/

/-- Low expansion stays. -/
example : stay 3 10 = true := by decide

/-- High expansion is pruned. -/
example : stay 12 10 = false := by decide

/-- One prune on the trace. -/
example : pruneCount [3, 12, 5] 10 = 1 := rfl

/-- An all-quiet trace keeps everything. -/
example : pruneCount [3, 5] 10 = 0 :=
  pruneCount_all_stay [3, 5] 10 (by decide)

/-! ## E-65: shaping an order -/

/-- Ten splits five-five. -/
example : split2 10 = (5, 5) := rfl

/-- Seven splits three-four. -/
example : split2 7 = (3, 4) := rfl

/-- The linear impact of ten is fifty. -/
example : shapeImpact 10 = 50 := rfl

/-- The slices add back. -/
example : (split2 10).1 + (split2 10).2 = 10 :=
  split2_add 10

/-! ## E-66: disjoint wave-fronts -/

/-- Disjoint direction sets pass. -/
example : disjointD [1, 2] [3, 4] = true := by decide

/-- A shared covector fails the check. -/
example : disjointD [1, 2] [2, 3] = false := by decide

/-- The fence elides on disjoint sets. -/
example : elideFence [1, 2] [3, 4] = true := by decide

/-- Elision shares no direction. -/
example : ∀ d ∈ [1, 2], d ∉ [3, 4] :=
  elideFence_sound [1, 2] [3, 4] (by decide)

/-! ## E-67: holding the book -/

/-- The charge is depth minus inventory. -/
example : charge 10 4 = 6 := rfl

/-- Leaving the chamber fires the anchor. -/
example : anchor 10 4 3 8 = true := by decide

/-- Staying inside never anchors. -/
example : anchor 10 4 12 3 = false := by decide

/-- The fired guard holds the quoted depth. -/
example : heldAfter 10 4 3 8 = 10 :=
  heldAfter_anchor 10 4 3 8 (by decide)

end Morph.Specs.BatchHIJ
