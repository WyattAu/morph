/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchDEF.Examples

/-!
# Frontier Kernels — validation (E-38–E-47)

Status: first cycle complete (loop 107).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(roundtrip, idempotence, reversal, exclusion) are exercised where a single
example could pass by accident.

Run: `lake build Morph.Tests.BatchDEF`.
-/

namespace Morph.Tests.BatchDEF

open Morph.Specs.BatchDEF

/-! ## E-38: blocked certificates on a fresh instance -/

/-- A blocked certificate names a genuine violation. -/
example : ∃ l k, (l, k) ∈ [7, 5].zip ([⟨"a", 4⟩, ⟨"b", 6⟩] : List Link) ∧
    l = 7 ∧ k.name = "a" ∧ k.cap < l :=
  solve_blocked_viol [7, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] ⟨7, "a", 1, 2⟩
    (by decide)

/-- A blocked instance is never feasible. -/
example : solve [7, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] ≠ .ok := by decide

/-- Satisfied pairs fit in the total on a fresh instance. -/
example : satCount [7, 5] [⟨"a", 4⟩, ⟨"b", 6⟩] ≤
    ([7, 5].zip ([⟨"a", 4⟩, ⟨"b", 6⟩] : List Link)).length :=
  satCount_le _ _

/-! ## E-39: slicing laws on a fresh tree -/

/-- Pruning twice is the same tree the checker accepts. -/
example : eval (prune (prune (.add (.const 0) (.const 5)))) =
    eval (.add (.const 0) (.const 5)) :=
  eval_prune _

/-- Pruning leaves no dead weight. -/
example : deadCount (prune (.add (.const 0) (.const 5))) = 0 :=
  prune_noDead _

/-- Negation negates the value. -/
example : eval (neg (.add (.const 3) (.const (-2)))) =
    -eval (.add (.const 3) (.const (-2))) :=
  neg_eval _

/-- Every cut splits the value. -/
example : eval (.add (.const 1) (.const 2)) + eval (.const 0) =
    eval (.add (.const 1) (.const 2)) :=
  cut_eval (.add (.const 1) (.const 2))
    ((.add (.const 1) (.const 2)), .const 0) (by decide)

/-! ## E-40: conformance on a fresh kernel -/

/-- Observable agreement on fresh cells. -/
example : evalCells (lowerReg [(5, 6), (7, 8)]) =
    evalCells (lowerStack [(5, 6), (7, 8)]) :=
  conform_eval _

/-- Register volume is exact. -/
example : (lowerReg [(5, 6), (7, 8)]).length = 4 := volReg _

/-- The register sum splits into q and p parts. -/
example : lsum (lowerReg [(5, 6), (7, 8)]) =
    lsum ([(5, 6), (7, 8)].map (·.1)) + lsum ([(5, 6), (7, 8)].map (·.2)) :=
  lowerReg_eval _

/-! ## E-41: the Borromean verdict transfers -/

def triModT : List (Nat × Nat) := [(0, 1), (1, 2), (2, 0)]

/-- A firing Massey kernel forces a global cycle. -/
example : hasCycle triModT = true :=
  massey_sound triModT 0 1 2 (by decide)

/-- A firing kernel has no back-edges. -/
example : (1, 0) ∉ triModT ∧ (2, 1) ∉ triModT ∧ (0, 2) ∉ triModT :=
  massey_excl _ _ _ _ (by decide)

/-- The triangle reaches around in three steps. -/
example : 0 ∈ reachE triModT 3 [0] :=
  mem3 triModT 0 1 2 (by decide) (by decide) (by decide)

/-- One hop enters the step closure. -/
example : 1 ∈ stepE triModT [0] :=
  step_mem triModT [0] 0 1 (by decide) (by decide)

/-! ## E-42: certificates on fresh extents -/

/-- A checked layout is pairwise disjoint. -/
example : (extents [4, 8]).Pairwise fun p q => disj p q :=
  cert_sound _ (by decide)

/-- Soundness then completeness roundtrips on three fields. -/
example : disjointCheck (extents [4, 8, 2]) = true :=
  cert_complete _ (cert_sound _ (by decide))

/-- Sizes survive layout. -/
example : (extentsAux 0 [4, 8]).map Prod.snd = [4, 8] :=
  sizes_preserved _ _

/-! ## E-43: deformation preserves endpoints on the reroute -/

/-- The reroute keeps both endpoints. -/
example : ([0, 2].head? = [0, 1, 2].head? ∧
    [0, 2].getLast? = [0, 1, 2].getLast?) :=
  deform_ends [0, 1, 2] dprEdges [1] [0, 2] (by decide)

/-- An already-good fresh path is a fixed point. -/
example : deform [3, 4, 5] [(3, 4), (4, 5)] [9] = some [3, 4, 5] := by decide

/-! ## E-44: hit and miss on fresh entries -/

/-- Hitting lookup pushes the upsert through. -/
example : findK 1 (upsert ⟨1, 2, 5⟩ [⟨1, 1, 3⟩]) =
    best ⟨1, 2, 5⟩ (findK 1 [⟨1, 1, 3⟩]) :=
  findK_upsert_hit _ _ _ rfl

/-- Missing lookup passes through. -/
example : findK 1 (upsert ⟨9, 1, 1⟩ [⟨1, 2, 5⟩]) =
    findK 1 [⟨1, 2, 5⟩] :=
  findK_upsert_miss _ _ _ (by decide)

/-- Failover is idempotent on fresh state. -/
example : upsert ⟨7, 3, 1⟩ (upsert ⟨7, 3, 1⟩ []) =
    upsert ⟨7, 3, 1⟩ [] :=
  upsert_idem _ _

/-! ## E-45: energy splits on a fresh signal -/

/-- Parseval on a fresh signal. -/
example : sumsq ([4, -3, 0].filter (isBound 2)) +
    sumsq ([4, -3, 0].filter fun x => !(isBound 2 x)) = sumsq [4, -3, 0] :=
  scatter_parseval _ _

/-- Sample counts are preserved. -/
example : ([4, -3, 0].filter (isBound 2)).length +
    ([4, -3, 0].filter fun x => !(isBound 2 x)).length = [4, -3, 0].length :=
  scatter_lengths _ _

/-! ## E-46: reversal and the classical limit -/

/-- Reversing negates the correction on fresh ops. -/
example : star [3, 2, 1] = 2 * lsumI [1, 2, 3] - star [1, 2, 3] :=
  star_reverse [1, 2, 3]

/-- Vanishing brackets kill the correction. -/
example : corr [0, 0] = 0 := corr_zero _ (by decide)

/-! ## E-47: disjoint verdicts -/

/-- Spacelike excludes timelike on a fresh operator. -/
example : classify ⟨0, 1, -1, 0⟩ 5 ≠ .time :=
  space_not_time _ _ (by decide)

/-- Every operator gets a verdict. -/
example : classify ⟨1, 2, 3, 4⟩ 5 = .space ∨
    classify ⟨1, 2, 3, 4⟩ 5 = .time ∨ classify ⟨1, 2, 3, 4⟩ 5 = .light :=
  classify_total _ _

end Morph.Tests.BatchDEF
