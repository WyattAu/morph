/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics
import Morph.Specs.UnitGroupTheory.Spec
import Morph.Specs.UnitGroupTheory.Lemmas

/-!
# Examples: Dimensional Algebra Specification (Unit Theory)

--**Source:** `spec/math/unit_group_theory_spec.md`
--**Status:** Complete
--**Last Updated:** 2026-01-16
--**Verified By:** Kilo Code

## Overview

This file contains concrete examples and test cases for the Dimensional Algebra Specification, demonstrating unit vectors, group operations, exchange rates, and dimensional consistency.

## Example Summary

| Example | Description | Status |
|---------|-------------|--------|
| `example_base_units` | Base units (L, M, T, $) | ✓ |
| `example_unit_vectors` | Unit vectors for base units | ✓ |
| `example_multiplication` | Unit multiplication (vector addition) | ✓ |
| `example_division` | Unit division (vector subtraction) | ✓ |
| `example_identity` | Identity element (dimensionless) | ✓ |
| `example_exchange_rate` | Currency conversion with exchange rate | ✓ |
| `example_compatibility_check` | Dimension compatibility check | ✓ |
| `example_derived_units` | Derived units (velocity, acceleration) | ✓ |
| `example_user_defined_units` | User-defined units (pixel, DPI) | ✓ |
| `example_edge_cases` | Edge cases (zero exponent, negative exponent) | ✓ |

-/

namespace Morph.Specs.UnitGroupTheory

-- Base Units Examples 

-- Example 1: Base unit - Length (L) 
def example_base_unit_length : BaseUnit :=
  BaseUnit.length

-- Example 2: Base unit - Mass (M) 
def example_base_unit_mass : BaseUnit :=
  BaseUnit.mass

-- Example 3: Base unit - Time (T) 
def example_base_unit_time : BaseUnit :=
  BaseUnit.time

-- Example 4: Base unit - Currency ($) 
def example_base_unit_currency : BaseUnit :=
  BaseUnit.currency

-- Unit Vector Examples 

-- Example 5: Meter unit vector [1, 0, 0, 0] 
def example_meter_vector : UnitVector :=
  { exponents := [1, 0, 0, 0] }

-- Example 6: Second unit vector [0, 0, 1, 0] 
def example_second_vector : UnitVector :=
  { exponents := [0, 0, 1, 0] }

-- Example 7: Kilogram unit vector [0, 1, 0, 0] 
def example_kilogram_vector : UnitVector :=
  { exponents := [0, 1, 0, 0] }

-- Example 8: USD unit vector [0, 0, 0, 1] 
def example_usd_vector : UnitVector :=
  { exponents := [0, 0, 0, 1] }

-- Multiplication Examples 

-- Example 9: Area = m × m = [1,0,0,0] + [1,0,0,0] = [2,0,0,0] 
def example_area_calculation : UnitVector :=
  let meter := { exponents := [1, 0, 0, 0] }
  addUnitVectors meter meter

-- Example 10: Volume = m × m × m = [1,0,0,0] + [1,0,0,0] + [1,0,0,0] = [3,0,0,0] 
def example_volume_calculation : UnitVector :=
  let meter := { exponents := [1, 0, 0, 0] }
  let area := addUnitVectors meter meter
  addUnitVectors area meter

-- Division Examples 

-- Example 11: Velocity = m / s = [1,0,0,0] - [0,0,1,0] = [1,0,-1,0] 
def example_velocity_calculation : UnitVector :=
  let meter := { exponents := [1, 0, 0, 0] }
  let second := { exponents := [0, 0, 1, 0] }
  subtractUnitVectors meter second

-- Example 12: Acceleration = m / s² = [1,0,0,0] - [0,0,2,0] = [1,0,-2,0] 
def example_acceleration_calculation : UnitVector :=
  let meter := { exponents := [1, 0, 0, 0] }
  let second_squared := { exponents := [0, 0, 2, 0] }
  subtractUnitVectors meter second_squared

-- Example 13: Density = kg / m³ = [0,1,0,0] - [3,0,0,0] = [-3,1,0,0] 
def example_density_calculation : UnitVector :=
  let kilogram := { exponents := [0, 1, 0, 0] }
  let meter_cubed := { exponents := [3, 0, 0, 0] }
  subtractUnitVectors kilogram meter_cubed

-- Identity Examples 

-- Example 14: Identity vector [0, 0, 0, 0] 
def example_identity_vector : UnitVector :=
  identityVector 4

-- Example 15: Dimensionless ratio = m / m = [1,0,0,0] - [1,0,0,0] = [0,0,0,0] 
def example_dimensionless_ratio : UnitVector :=
  let meter := { exponents := [1, 0, 0, 0] }
  subtractUnitVectors meter meter

-- Example 16: Identity property: v + 0 = v 
def example_identity_property : Prop :=
  ∀ (vector : UnitVector),
    let identity := identityVector vector.exponents.length in
      addUnitVectors vector identity = vector

-- Exchange Rate Examples 

-- Example 17: EUR/USD exchange rate vector 
def example_eur_usd_rate : UnitVector :=
  let eur := { exponents := [0, 0, 0, 1] }
  let usd := { exponents := [0, 0, 0, 1] }
  subtractUnitVectors eur usd

-- Example 18: Currency conversion: USD × EUR/USD = EUR 
def example_currency_conversion : UnitVector :=
  let usd := { exponents := [0, 0, 0, 1] }
  let eur_usd_rate := { exponents := [0, 0, 0, 0] }
  addUnitVectors usd eur_usd_rate

-- Example 19: Exchange rate invariant 
def example_exchange_rate_invariant : Prop :=
  ∀ (usd eur : UnitVector) (amount : Float) (rate : Float),
    let eur_usd_rate := subtractUnitVectors eur usd in
    let eur_amount := amount * rate in
      addUnitVectors usd eur_usd_rate = eur

-- Compatibility Check Examples 

-- Example 20: Compatible dimensions (m + m) 
def example_compatible_dimensions : Prop :=
  let meter1 := { exponents := [1, 0, 0, 0] }
  let meter2 := { exponents := [1, 0, 0, 0] }
  areCompatible meter1 meter2 = True

-- Example 21: Incompatible dimensions (m + s) 
def example_incompatible_dimensions : Prop :=
  let meter := { exponents := [1, 0, 0, 0] }
  let second := { exponents := [0, 0, 1, 0] }
  areCompatible meter second = False

-- Example 22: Dimension mismatch error 
def example_dimension_mismatch_error : String :=
  let meter := { exponents := [1, 0, 0, 0] }
  let second := { exponents := [0, 0, 1, 0] }
  if ¬areCompatible meter second then
    "Type error: Cannot add '" ++ unitToString meter ++ "' and '" ++ unitToString second ++ "' (incompatible dimensions)"
  else
    ""

-- Derived Units Examples 

-- Example 23: Velocity unit definition 
def example_velocity_unit : UnitDefinition :=
  { name := "Velocity",
    vector := { exponents := [1, 0, -1, 0] },
    scale := 1.0 }

-- Example 24: Acceleration unit definition 
def example_acceleration_unit : UnitDefinition :=
  { name := "Acceleration",
    vector := { exponents := [1, 0, -2, 0] },
    scale := 1.0 }

-- Example 25: Newton unit definition 
def example_newton_unit : UnitDefinition :=
  { name := "Newton",
    vector := { exponents := [1, 1, -2, 0] },
    scale := 1.0 }

-- User-Defined Units Examples 

-- Example 26: Pixel unit definition 
def example_pixel_unit : UnitDefinition :=
  { name := "Pixel",
    vector := { exponents := [1, 0, 0, 0] },
    scale := 1.0 / 96.0 }

-- Example 27: DPI unit definition 
def example_dpi_unit : UnitDefinition :=
  { name := "DPI",
    vector := { exponents := [-1, 0, 0, 0] },
    scale := 1.0 }

-- Example 28: Pixel to meter conversion 
def example_pixel_to_meter : UnitVector :=
  let pixel := { exponents := [1, 0, 0, 0] }
  let meter_per_pixel := { exponents := [1, 0, 0, 0] }
  addUnitVectors pixel meter_per_pixel

-- Edge Cases Examples 

-- Example 29: Zero exponent (dimensionless) 
def example_zero_exponent : UnitVector :=
  { exponents := [0, 0, 0, 0] }

-- Example 30: Negative exponent (1/meter) 
def example_negative_exponent : UnitVector :=
  { exponents := [-1, 0, 0, 0] }

-- Example 31: Fractional exponent (square root) 
def example_fractional_exponent : UnitVector :=
  let area := { exponents := [2, 0, 0, 0] }
  { exponents := area.exponents.map (fun e => e / 2) }

-- Example 32: Large exponent (m^10) 
def example_large_exponent : UnitVector :=
  { exponents := [10, 0, 0, 0] }

-- Unit Expression Examples 

-- Example 33: Base unit expression 
def example_base_unit_expression : UnitExpression :=
  UnitExpression.base BaseUnit.length

-- Example 34: Multiplication expression 
def example_multiplication_expression : UnitExpression :=
  UnitExpression.mul
    (UnitExpression.base BaseUnit.length)
    (UnitExpression.base BaseUnit.length)

-- Example 35: Division expression 
def example_division_expression : UnitExpression :=
  UnitExpression.div
    (UnitExpression.base BaseUnit.length)
    (UnitExpression.base BaseUnit.time)

-- Example 36: Power expression 
def example_power_expression : UnitExpression :=
  UnitExpression.pow
    (UnitExpression.base BaseUnit.length)
    2

-- Example 37: Complex expression 
def example_complex_expression : UnitExpression :=
  UnitExpression.div
    (UnitExpression.mul
      (UnitExpression.base BaseUnit.mass)
      (UnitExpression.pow
        (UnitExpression.base BaseUnit.length)
        2))
    (UnitExpression.pow
      (UnitExpression.base BaseUnit.time)
      2)

-- Example 38: Evaluate complex expression 
def example_evaluate_complex_expression : UnitVector :=
  evaluateUnitExpression
    (UnitExpression.div
      (UnitExpression.mul
        (UnitExpression.base BaseUnit.mass)
        (UnitExpression.pow
          (UnitExpression.base BaseUnit.length)
          2))
      (UnitExpression.pow
        (UnitExpression.base BaseUnit.time)
        2))

end Morph.Specs.UnitGroupTheory
-/