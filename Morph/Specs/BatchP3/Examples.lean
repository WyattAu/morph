/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP3.Lemmas

/-!
# Feasible-50 kernels — P3 examples

Status: first cycle complete (loop 110).

Concrete instances of the ten cores. Every example is `decide`/`rfl`-checked;
the law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.BatchP3

/-! ## E-177: driving the lines -/

/-- Every write ends modified. -/
example : wrM .I = .M := wrM_is_M _

/-- Reading invalid shares. -/
example : rdM .I = .S := rdM_I

/-- Reading modified is stable. -/
example : rdM .M = .M := rdM_M

/-! ## E-178: forwarding -/

/-- The buffered store forwards. -/
example : readB (writeB [] 3 42) 3 0 = 42 :=
  read_write_hit [] 3 42 0

/-- Other addresses read through. -/
example : readB (writeB [] 3 42) 7 0 = 0 :=
  read_write_miss [] 3 7 42 0 (by decide)

/-! ## E-187: checking a trace -/

/-- Ordered doorbells pass. -/
example : orderedB ⟨1, 10⟩ ⟨2, 20⟩ = true := by decide

/-- A two-descriptor trace passes. -/
example : checkOrder [⟨1, 10⟩, ⟨2, 20⟩] = true := by decide

/-- A reordered trace fails. -/
example : checkOrder [⟨2, 20⟩, ⟨1, 10⟩] = false := by decide

/-- The positive check names its parts. -/
example : orderedB ⟨1, 10⟩ ⟨2, 20⟩ = true ∧ checkOrder [⟨2, 20⟩] = true :=
  checkOrder_cons ⟨1, 10⟩ ⟨2, 20⟩ [] (by decide)

/-! ## E-199: running the suite -/

/-- A matching case passes. -/
example : runLitmus 5 5 = true := runLitmus_match 5

/-- A mismatching case fails. -/
example : runLitmus 5 6 = false := by decide

/-- The suite passes on matches. -/
example : suiteAll [(1, 1), (2, 2)] = true :=
  suiteAll_complete _ (by decide)

/-- The suite names its witnesses. -/
example : ∀ p ∈ [(1, 1), (2, 2)], p.1 = p.2 :=
  suiteAll_sound _ (by decide)

/-! ## E-354: probing -/

/-- Offset zero stays home. -/
example : probe 7 0 5 = 7 % 5 := probe_hit 7 5

/-- The probe stays in bounds. -/
example : probe 7 3 5 < 5 := probe_bound 7 3 5 (by decide)

/-! ## E-355: adding and querying -/

/-- An added index queries true. -/
example : queryB (addB [] [3, 5]) 3 = true :=
  query_add_hit [] [3, 5] 3 (by decide)

/-- Old indices survive. -/
example : queryB (addB [1] [3]) 1 = true :=
  query_add_old [1] [3] 1 (by decide)

/-- A never-added index is absent. -/
example : queryB [1] 9 = false := by decide

/-! ## E-360: replaying -/

/-- Replay sums the ops. -/
example : replayW 10 [1, 2, 3] = 16 := rfl

/-- Replay splits over append. -/
example : replayW 10 ([1] ++ [2, 3]) = replayW (replayW 10 [1]) [2, 3] :=
  replayW_append [1] [2, 3] 10

/-- Truncation keeps the tail. -/
example : 4 ≤ ((4, 9) : Nat × Nat).1 :=
  trunc_mem 4 [(3, 1), (4, 9)] (4, 9) (by decide)

/-! ## E-362: writing and snapshotting -/

/-- A written key reads back. -/
example : readStore (writeStore [] 1 99) 1 = some 99 :=
  write_hit [] 1 99

/-- Other keys read through. -/
example : readStore (writeStore [] 1 99) 2 = none :=
  write_miss [] 1 2 99 (by decide)

/-- The snapshot reads the store. -/
example : readSnap (takeSnap [(1, 99)]) 1 = some 99 :=
  snap_read _ _

/-! ## E-363: visibility -/

/-- A live begun row is visible. -/
example : visible ⟨2, 0⟩ 5 = true :=
  vis_live ⟨2, 0⟩ 5 (by decide) rfl

/-- A future row is invisible. -/
example : visible ⟨8, 0⟩ 5 = false :=
  invis_future ⟨8, 0⟩ 5 (by decide)

/-- An ended row is invisible. -/
example : visible ⟨1, 4⟩ 9 = false := by decide

/-! ## E-366: maintaining the view -/

/-- The view sums the base. -/
example : view [1, 2, 3] = 6 := rfl

/-- Adding a row adds to the view. -/
example : view (addView [2, 3] 1) = 1 + view [2, 3] :=
  view_add [2, 3] 1

end Morph.Specs.BatchP3
