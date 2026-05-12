/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.UnitGroupTheory.Spec

namespace Morph.Specs.UnitGroupTheory

/-!
## Lemmas

Lemmas and auxiliary results for the UnitGroupTheory specification.
-/

/-! ### Identity Vector -/

theorem identityVector_length (n : Nat) :
  (identityVector n).exponents.length = n := by
  unfold identityVector; simp

theorem identityVector_all_zero (n : Nat) :
  (identityVector n).exponents = List.replicate n 0 := rfl

/-! ### Base Unit Evaluation -/

theorem evaluateBaseLength : (evaluateUnitExpression (.base .length)).exponents = [1, 0, 0, 0] := rfl

theorem evaluateBaseMass : (evaluateUnitExpression (.base .mass)).exponents = [0, 1, 0, 0] := rfl

theorem evaluateBaseTime : (evaluateUnitExpression (.base .time)).exponents = [0, 0, 1, 0] := rfl

theorem evaluateBaseCurrency : (evaluateUnitExpression (.base .currency)).exponents = [0, 0, 0, 1] := rfl

/-! ### Compound Expressions -/

theorem evaluateMul_length_mass : (evaluateUnitExpression (.mul (.base .length) (.base .mass))).exponents = [1, 1, 0, 0] := rfl

theorem evaluateDiv_length_time : (evaluateUnitExpression (.div (.base .length) (.base .time))).exponents = [1, 0, -1, 0] := rfl

theorem evaluatePow_length_sq : (evaluateUnitExpression (.pow (.base .length) 2)).exponents = [2, 0, 0, 0] := rfl

theorem evaluatePow_length_neg1 : (evaluateUnitExpression (.pow (.base .length) (-1))).exponents = [-1, 0, 0, 0] := rfl

theorem evaluateMul_length_length : (evaluateUnitExpression (.mul (.base .length) (.base .length))).exponents = [2, 0, 0, 0] := rfl

/-! ### Base Unit Exhaustiveness -/

theorem baseUnit_cases (u : BaseUnit) :
  u = .length ∨ u = .mass ∨ u = .time ∨ u = .currency := by
  cases u <;> simp

/-! ### Vector Operations -/

theorem exponentiateUnitVector_length (v : UnitVector) (n : Int) :
  (exponentiateUnitVector v n).exponents.length = v.exponents.length := by
  unfold exponentiateUnitVector; simp

/-! ### Compatibility -/

theorem areCompatible_refl (v : UnitVector) :
  areCompatible v v = true := by
  unfold areCompatible; simp

theorem areCompatible_symm (v1 v2 : UnitVector) :
  areCompatible v1 v2 = areCompatible v2 v1 := by
  unfold areCompatible; simp [Eq.comm]

end Morph.Specs.UnitGroupTheory
