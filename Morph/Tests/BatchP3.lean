/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP3.Examples

/-!
# Feasible-50 kernels — P3 validation

Status: first cycle complete (loop 110).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(replay splitting, snapshot isolation, suite soundness) are exercised where a
single example could pass by accident.

Run: `lake build Morph.Tests.BatchP3`.
-/

namespace Morph.Tests.BatchP3

open Morph.Specs.BatchP3

/-! ## E-177: transitions on fresh states -/

/-- A fresh write ends modified. -/
example : wrM .E = .M := wrM_is_M _

/-- A fresh exclusive read is stable. -/
example : rdM .E = .E := rdM_E

/-- A fresh shared read is stable. -/
example : rdM .S = .S := rdM_S

/-! ## E-178: forwarding on fresh buffers -/

/-- A fresh buffered store forwards. -/
example : readB (writeB [(1, 10)] 2 20) 2 0 = 20 :=
  read_write_hit _ 2 20 0

/-- A fresh unrelated address reads through. -/
example : readB (writeB [(1, 10)] 2 20) 1 0 = 10 :=
  read_write_miss _ 2 1 20 0 (by decide)

/-! ## E-187: order on fresh traces -/

/-- A fresh singleton is ordered. -/
example : checkOrder [⟨4, 1⟩] = true :=
  checkOrder_single _

/-- A fresh three-trace check splits. -/
example : orderedB ⟨1, 5⟩ ⟨3, 6⟩ = true ∧ checkOrder [⟨3, 6⟩, ⟨9, 7⟩] = true :=
  checkOrder_cons ⟨1, 5⟩ ⟨3, 6⟩ [⟨9, 7⟩] (by decide)

/-- A fresh inversion fails. -/
example : checkOrder [⟨3, 6⟩, ⟨1, 5⟩] = false := by decide

/-! ## E-199: suites on fresh cases -/

/-- A fresh suite passes on matches. -/
example : suiteAll [(7, 7)] = true :=
  suiteAll_complete _ (by decide)

/-- A fresh suite fails on a mismatch. -/
example : suiteAll [(7, 8)] = false := by decide

/-- A fresh positive suite names witnesses. -/
example : ∀ p ∈ [(7, 7), (8, 8)], p.1 = p.2 :=
  suiteAll_sound _ (by decide)

/-! ## E-354: probes on fresh tables -/

/-- A fresh home probe hits. -/
example : probe 11 0 8 = 11 % 8 := probe_hit 11 8

/-- A fresh probe stays in bounds. -/
example : probe 11 6 8 < 8 := probe_bound 11 6 8 (by decide)

/-! ## E-355: filters on fresh indices -/

/-- A fresh added index queries true. -/
example : queryB (addB [2] [4, 6]) 4 = true :=
  query_add_hit [2] [4, 6] 4 (by decide)

/-- A fresh absent index is absent. -/
example : queryB (addB [2] [4]) 9 = false := by decide

/-! ## E-360: replay on fresh logs -/

/-- A fresh replay splits. -/
example : replayW 0 ([5] ++ [6, 7]) = replayW (replayW 0 [5]) [6, 7] :=
  replayW_append [5] [6, 7] 0

/-- A fresh truncation keeps the tail. -/
example : 2 ≤ ((2, 4) : Nat × Nat).1 :=
  trunc_mem 2 [(1, 3), (2, 4)] (2, 4) (by decide)

/-- A fresh pre-checkpoint entry is dropped. -/
example : trunc 5 [(1, 3), (7, 4)] = [(7, 4)] := rfl

/-! ## E-362: isolation on fresh stores -/

/-- A fresh snapshot over a write sees it. -/
example : readSnap (takeSnap (writeStore [] 4 50)) 4 = some 50 :=
  snap_write [] 4 50

/-- A fresh write misses other keys. -/
example : readStore (writeStore [(1, 2)] 4 50) 1 = some 2 :=
  write_miss _ 4 1 50 (by decide)

/-! ## E-363: visibility on fresh rows -/

/-- A fresh live row is visible. -/
example : visible ⟨0, 0⟩ 3 = true :=
  vis_live ⟨0, 0⟩ 3 (by decide) rfl

/-- A fresh future row is invisible. -/
example : visible ⟨10, 0⟩ 3 = false :=
  invis_future ⟨10, 0⟩ 3 (by decide)

/-- A fresh ended row is invisible. -/
example : visible ⟨0, 2⟩ 5 = false := by decide

/-! ## E-366: views on fresh bases -/

/-- A fresh add tracks the view. -/
example : view (addView [5] 7) = 7 + view [5] :=
  view_add [5] 7

end Morph.Tests.BatchP3
