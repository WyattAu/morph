/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.UnitGroupTheory.Spec

namespace Morph.Specs.UnitGroupTheory

/-!
## Lemmas

Lemmas and auxiliary results for the UnitGroupTheory specification.
-/

theorem identityVector_length (n : Nat) :
  (identityVector n).exponents.length = n := by
  unfold identityVector; simp

theorem identityVector_all_zero (n : Nat) :
  (identityVector n).exponents = List.replicate n 0 := rfl

theorem evaluateBaseLength : (evaluateUnitExpression (.base .length)).exponents = [1, 0, 0, 0] := rfl

theorem evaluateBaseMass : (evaluateUnitExpression (.base .mass)).exponents = [0, 1, 0, 0] := rfl

theorem evaluateBaseTime : (evaluateUnitExpression (.base .time)).exponents = [0, 0, 1, 0] := rfl

theorem evaluateBaseCurrency : (evaluateUnitExpression (.base .currency)).exponents = [0, 0, 0, 1] := rfl

theorem evaluateMul_length_mass : (evaluateUnitExpression (.mul (.base .length) (.base .mass))).exponents = [1, 1, 0, 0] := rfl

theorem evaluateDiv_length_time : (evaluateUnitExpression (.div (.base .length) (.base .time))).exponents = [1, 0, -1, 0] := rfl

theorem evaluatePow_length_sq : (evaluateUnitExpression (.pow (.base .length) 2)).exponents = [2, 0, 0, 0] := rfl

theorem baseUnit_cases (u : BaseUnit) :
  u = .length ∨ u = .mass ∨ u = .time ∨ u = .currency := by
  cases u <;> simp

end Morph.Specs.UnitGroupTheory
