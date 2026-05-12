/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.UnitGroupTheory.Spec

namespace Morph.Specs.UnitGroupTheory

/-!
## Examples

Concrete examples demonstrating the UnitGroupTheory specification.
-/

def lengthUnit : UnitVector := evaluateUnitExpression (.base .length)

def massUnit : UnitVector := evaluateUnitExpression (.base .mass)

def timeUnit : UnitVector := evaluateUnitExpression (.base .time)

def velocityUnit : UnitVector := evaluateUnitExpression (.div (.base .length) (.base .time))

def areaUnit : UnitVector := evaluateUnitExpression (.pow (.base .length) 2)

example : lengthUnit.exponents = [1, 0, 0, 0] := rfl

example : massUnit.exponents = [0, 1, 0, 0] := rfl

example : timeUnit.exponents = [0, 0, 1, 0] := rfl

example : velocityUnit.exponents = [1, 0, -1, 0] := rfl

example : areaUnit.exponents = [2, 0, 0, 0] := rfl

example : areCompatible lengthUnit lengthUnit = true := rfl

example : areCompatible lengthUnit massUnit = false := rfl

def dimless : UnitVector := identityVector 4

example : dimless.exponents = [0, 0, 0, 0] := rfl

example : exponentiateUnitVector lengthUnit 3 = { exponents := [3, 0, 0, 0] } := rfl

end Morph.Specs.UnitGroupTheory
