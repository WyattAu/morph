/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP1.Lemmas

/-!
# Feasible-50 kernels — P1 examples

Status: first cycle complete (loop 110).

Concrete instances of the ten cores. Every example is `decide`/`rfl`-checked;
the law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.BatchP1

/-! ## E-104: the rule fires -/

/-- `3 + 0` optimizes to `3`. -/
example : popt (.add (.const 3) (.const 0)) = .const 3 := rfl

/-- `0 + 4` optimizes to `4`. -/
example : popt (.add (.const 0) (.const 4)) = .const 4 := rfl

/-- Evaluation is preserved on the example. -/
example : peval (popt (.add (.const 3) (.const 0))) = peval (.add (.const 3) (.const 0)) :=
  popt_sound _

/-- The validator accepts the optimized pair. -/
example : validOpt (.add (.const 3) (.const 0)) (.const 3) = true := by decide

/-! ## E-113: agreement checks -/

/-- Matching verdicts agree. -/
example : agree true true = true := rfl

/-- Mismatched verdicts disagree. -/
example : agree true false = false := rfl

/-- Agreement on the fresh pair. -/
example : (false : Bool) = false :=
  agree_sound false false (agree_refl false)

/-! ## E-116: one backward step -/

/-- Uses survive the transfer. -/
example : 7 ∈ transfer ⟨5, [7]⟩ [1, 5] :=
  mem_transfer_use ⟨5, [7]⟩ [1, 5] 7 (by decide)

/-- The empty block is the identity. -/
example : seqLive [] [1, 2] = [1, 2] := rfl

/-! ## E-120: accepting a loan -/

/-- The empty context accepts. -/
example : acceptLoan [] 3 9 = true := rfl

/-- Acceptance on the fresh context. -/
example : conflicts [⟨1, 2⟩] 5 = false :=
  acceptLoan_sound [⟨1, 2⟩] 5 8 (by decide)

/-- A held place is refused. -/
example : acceptLoan [⟨1, 2⟩] 1 8 = false := rfl

/-! ## E-123: joins and runs -/

/-- Join bounds both sides. -/
example : 3 ≤ mj 3 5 := le_mj_left 3 5

/-- The empty run is the identity. -/
example : runM [] 7 = 7 := rfl

/-- A two-step run adds both. -/
example : runM [2, 3] 10 = 15 := rfl

/-- Monotonicity on the fresh pair. -/
example : runM [2, 3] 4 ≤ runM [2, 3] 9 :=
  runM_mono [2, 3] 4 9 (by decide)

/-! ## E-124: hulls -/

/-- Join of overlapping intervals. -/
example : ivalJoin ⟨1, 5⟩ ⟨3, 7⟩ = ⟨1, 7⟩ := rfl

/-- The joined hull is valid. -/
example : ivalOk (ivalJoin ⟨1, 5⟩ ⟨3, 7⟩) :=
  ivalJoin_valid _ _ (by simp only [ivalOk]; decide) (by simp only [ivalOk]; decide)

/-- Widening covers the old upper bound. -/
example : 5 ≤ (widen ⟨1, 5⟩ ⟨2, 9⟩).hi :=
  widen_hi ⟨1, 5⟩ ⟨2, 9⟩

/-! ## E-137: walking the lifecycle -/

/-- Placed acks. -/
example : ostep .placed .ack = some .acked :=
  ostep_placed_ack

/-- Acked fills. -/
example : ostep .acked .fill = some .filled :=
  ostep_acked_fill

/-- Placed cannot fill. -/
example : ostep .placed .fill = none :=
  ostep_placed_fill_none

/-! ## E-141: brand checks -/

/-- Same venue matches. -/
example : matchSame ⟨1, 10⟩ ⟨1, 20⟩ = true := by decide

/-- Cross-venue is rejected. -/
example : matchSame ⟨1, 10⟩ ⟨2, 10⟩ = false := by decide

/-- The match names equal venues. -/
example : (⟨1, 10⟩ : BOrder).venue = (⟨1, 20⟩ : BOrder).venue :=
  matchSame_sound _ _ (by decide)

/-! ## E-148: covering rows -/

/-- A leading wildcard covers. -/
example : coversAny [.wild, .lit 3] (some 9) = true :=
  coversAny_wild _ _

/-- The empty row covers nothing. -/
example : coversAny [] (some 9) = false :=
  coversAny_nil _

/-- A wildcard row is flagged. -/
example : hasWild [.lit 1, .wild] = true := by decide

/-! ## E-149: composing rows -/

/-- Composition concatenates. -/
example : compose [1, 2] [3] = [1, 2, 3] := rfl

/-- Left fields survive. -/
example : 1 ∈ compose [1, 2] [3] :=
  mem_compose_left [1, 2] [3] 1 (by decide)

/-- The membership test agrees. -/
example : hasField (compose [1, 2] [3]) 3 = true := by decide

end Morph.Specs.BatchP1
