/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP1.Examples

/-!
# Feasible-50 kernels — P1 validation

Status: first cycle complete (loop 110).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(optimization soundness, fixpoint monotonicity, lifecycle exactness) are
exercised where a single example could pass by accident.

Run: `lake build Morph.Tests.BatchP1`.
-/

namespace Morph.Tests.BatchP1

open Morph.Specs.BatchP1

/-! ## E-104: soundness on a fresh expression -/

/-- A fresh optimization preserves evaluation. -/
example : peval (popt (.add (.const 8) (.add (.const 0) (.const 2)))) =
    peval (.add (.const 8) (.add (.const 0) (.const 2))) :=
  popt_sound _

/-- The validator accepts the fresh optimized pair. -/
example : validOpt (.add (.const 8) (.const 0)) (popt (.add (.const 8) (.const 0))) = true :=
  validOpt_of_opt _

/-- A genuinely different pair is rejected. -/
example : validOpt (.const 8) (.const 9) = false := by decide

/-! ## E-113: agreement on fresh verdicts -/

/-- Fresh equality passes. -/
example : agree true true = true :=
  agree_complete true true rfl

/-- A fresh mismatch names inequality. -/
example : (true : Bool) ≠ false :=
  fun h => Bool.noConfusion (agree_sound true false (by simp [agree, h]))

/-! ## E-116: transfer on a fresh instruction -/

/-- Fresh uses survive. -/
example : 4 ∈ transfer ⟨2, [4, 6]⟩ [2, 9] :=
  mem_transfer_use ⟨2, [4, 6]⟩ [2, 9] 4 (by decide)

/-- A fresh unused def is dropped. -/
example : 2 ∉ transfer ⟨2, [4]⟩ [9] :=
  not_mem_transfer_def ⟨2, [4]⟩ [9] (by decide)

/-! ## E-120: conflicts on a fresh context -/

/-- A fresh held place is refused. -/
example : acceptLoan [⟨3, 1⟩, ⟨5, 2⟩] 3 7 = false := by decide

/-- A fresh free place is accepted with no conflict. -/
example : conflicts [⟨3, 1⟩, ⟨5, 2⟩] 9 = false :=
  acceptLoan_sound _ 9 4 (by decide)

/-! ## E-123: monotone runs on fresh inputs -/

/-- Fresh join bounds the right. -/
example : 9 ≤ mj 4 9 := le_mj_right 4 9

/-- Fresh transfer is monotone. -/
example : mtrans 5 3 ≤ mtrans 5 8 :=
  mono_mtrans 5 3 8 (by decide)

/-- A fresh three-step run only grows. -/
example : 2 ≤ runM [1, 1, 1] 2 := by decide

/-! ## E-124: hulls on fresh intervals -/

/-- A fresh hull is valid. -/
example : ivalOk (ivalJoin ⟨2, 4⟩ ⟨0, 3⟩) :=
  ivalJoin_valid _ _ (by simp only [ivalOk]; decide) (by simp only [ivalOk]; decide)

/-- Fresh widening keeps the lower bound down. -/
example : (widen ⟨2, 4⟩ ⟨0, 3⟩).lo ≤ 2 :=
  widen_lo ⟨2, 4⟩ ⟨0, 3⟩

/-- Fresh widening covers the old top. -/
example : 4 ≤ (widen ⟨2, 4⟩ ⟨0, 9⟩).hi :=
  widen_hi ⟨2, 4⟩ ⟨0, 9⟩

/-! ## E-137: illegal transitions on fresh states -/

/-- A filled order admits nothing. -/
example : ostep .filled .ack = none :=
  ostep_filled .ack

/-- Acked cannot re-ack. -/
example : ostep .acked .ack = none := rfl

/-! ## E-141: brands on fresh orders -/

/-- A fresh same-venue pair matches. -/
example : matchSame ⟨7, 1⟩ ⟨7, 2⟩ = true :=
  matchSame_complete _ _ rfl

/-- A fresh cross-venue pair is rejected. -/
example : matchSame ⟨7, 1⟩ ⟨8, 1⟩ = false := by decide

/-! ## E-148: coverage on fresh rows -/

/-- A fresh wildcard-headed row covers. -/
example : coversAny [.wild] none = true :=
  coversAny_wild _ _

/-- A fresh literal-only row is not flagged. -/
example : hasWild [.lit 1, .lit 2] = false := rfl

/-! ## E-149: composition on fresh rows -/

/-- Fresh composition adds the counts. -/
example : (compose [4, 5] [6, 7]).length = 2 + 2 :=
  compose_length [4, 5] [6, 7]

/-- Fresh right fields survive. -/
example : 7 ∈ compose [4, 5] [6, 7] :=
  mem_compose_right [4, 5] [6, 7] 7 (by decide)

/-- A fresh absent field is absent. -/
example : hasField [4, 5] 9 = false := by decide

end Morph.Tests.BatchP1
