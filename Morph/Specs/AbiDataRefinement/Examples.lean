/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.AbiDataRefinement.Spec

/-!
# Examples: ABI Data Refinement

This module provides concrete examples and test cases for ABI data refinement specification.

## Overview

The AbiDataRefinement Examples module demonstrates:
- Type refinement from high-level ABI to memory layout
- Data transformation examples
- Layout compatibility verification
- ABI-specific optimization examples

## Key Concepts

- **Type Refinement:** Converting high-level ABI types to low-level memory layouts
- **Data Validation:** Ensuring data integrity during refinement
- **Layout Compatibility:** Verifying layout compatibility across ABI versions
-/

namespace Morph.Specs.AbiDataRefinement

/-!
## Example 1: Simple Type Refinement
Demonstrates basic type refinement from ABI to memory layout.
-/

/-- Example: Refine i32 ABI type to memory layout.
    This example shows a simple 32-bit integer type refinement.
-/
def exampleRefineI32 : MemoryLayout :=
  {
    abiType := { name := "i32", size := 32, align := 32 },
    size := 32,
    align := 32,
    offsets := [0]
  }

/-- Example: Verify type refinement for i32.
    Evaluates to show the refined layout.
-/
#eval exampleRefineI32

/-!
## Example 2: Struct Type Refinement
Demonstrates struct type refinement.
-/

/-- Example: Refine struct ABI type to memory layout.
    This example shows a struct with three fields.
-/
def exampleRefineStruct : MemoryLayout :=
  {
    abiType := { name := "struct", size := 16, align := 16 },
    size := 16,
    align := 16,
    offsets := [0, 4, 8]
  }

/-- Example: Verify struct refinement.
    Evaluates to show the refined struct layout.
-/
#eval exampleRefineStruct

/-!
## Example 3: Type Validation
Demonstrates data validation during refinement.
-/

/-- Example: Validate layout with correct size.
    This example shows a valid i32 layout.
-/
def exampleValidateLayout : Bool :=
  validateLayout
    { abiType := { name := "i32", size := 32, align := 32 },
      size := 32,
      align := 32,
      offsets := [0] }

/-- Example: Verify layout validation.
    Evaluates to show validation result.
-/
#eval exampleValidateLayout

/-!
## Example 4: Layout Compatibility
Demonstrates layout compatibility checking.
-/

/-- Example: Check compatibility between two identical layouts.
    This example shows that identical layouts are compatible.
-/
def exampleCompatibleLayouts : Bool :=
  compatibleLayouts
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }

/-- Example: Verify layout compatibility.
    Evaluates to show compatibility result.
-/
#eval exampleCompatibleLayouts

/-!
## Example 5: Incompatible Layouts
Demonstrates incompatible layouts.
-/

/-- Example: Check compatibility between different layouts.
    This example shows that layouts with different sizes are incompatible.
-/
def exampleIncompatibleLayouts : Bool :=
  compatibleLayouts
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 64,
          align := 32,
          offsets := [0] }

/-- Example: Verify layout incompatibility.
    Evaluates to show incompatibility result.
-/
#eval exampleIncompatibleLayouts

/-!
## Example 6: Complex Refinement
Demonstrates complex refinement scenarios.
-/

/-- Example: Refine nested struct layout.
    This example shows a nested struct with two fields.
-/
def exampleNestedRefinement : MemoryLayout :=
  {
    abiType := { name := "nested_struct", size := 32, align := 32 },
    size := 32,
    align := 32,
    offsets := [0, 16]
  }

/-- Example: Verify nested refinement.
    Evaluates to show the nested struct layout.
-/
#eval exampleNestedRefinement

/-!
## Example 7: Invalid Layout
Demonstrates invalid layout detection.
-/

/-- Example: Validate layout with incorrect size.
    This example shows an invalid layout where last offset doesn't match size.
-/
def exampleInvalidLayout : Bool :=
  validateLayout
    { abiType := { name := "i32", size := 32, align := 32 },
      size := 32,
      align := 32,
      offsets := [0, 4] }

/-- Example: Verify invalid layout detection.
    Evaluates to show invalid layout is detected.
-/
#eval exampleInvalidLayout

/-!
## Example 8: Empty Offsets
Demonstrates layout with no offsets.
-/

/-- Example: Validate layout with empty offsets.
    This example shows an invalid layout with no offsets.
-/
def exampleEmptyOffsets : Bool :=
  validateLayout
    { abiType := { name := "empty", size := 0, align := 1 },
      size := 0,
      align := 1,
      offsets := [] }

/-- Example: Verify empty offsets detection.
    Evaluates to show empty offsets are invalid.
-/
#eval exampleEmptyOffsets

/-!
## Example 9: Multiple Field Layout
Demonstrates layout with multiple fields.
-/

/-- Example: Layout with multiple fields.
    This example shows a struct with four fields.
-/
def exampleMultiFieldLayout : MemoryLayout :=
  {
    abiType := { name := "multi_field", size := 48, align := 32 },
    size := 48,
    align := 32,
    offsets := [0, 8, 16, 40]
  }

/-- Example: Verify multi-field layout.
    Evaluates to show the multi-field layout.
-/
#eval exampleMultiFieldLayout

/-!
## Example 10: Type Refinement Verification
Demonstrates verification of type refinement properties.
-/

/-- Example: Verify type refinement property.
    This example checks if a layout refines a type.
-/
def exampleVerifyTypeRefinement : Bool :=
  spec_type_refinement
    { name := "i32", size := 32, align := 32 }
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }

/-- Example: Verify type refinement result.
    Evaluates to show type refinement verification.
-/
#eval exampleVerifyTypeRefinement

/-!
## Example 11: Data Validation Verification
Demonstrates verification of data validation properties.
-/

/-- Example: Verify data validation property.
    This example checks if a layout validates correctly.
-/
def exampleVerifyDataValidation : Bool :=
  spec_data_validation
    { name := "i32", size := 32, align := 32 }
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }

/-- Example: Verify data validation result.
    Evaluates to show data validation verification.
-/
#eval exampleVerifyDataValidation

/-!
## Example 12: Layout Compatibility Verification
Demonstrates verification of layout compatibility properties.
-/

/-- Example: Verify layout compatibility property.
    This example checks if two layouts are compatible.
-/
def exampleVerifyLayoutCompatibility : Bool :=
  spec_layout_compatibility
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }

/-- Example: Verify layout compatibility result.
    Evaluates to show layout compatibility verification.
-/
#eval exampleVerifyLayoutCompatibility

/-!
## Example 13: Different ABI Types
Demonstrates layouts with different ABI types.
-/

/-- Example: Check compatibility between different ABI types.
    This example shows that different ABI types are incompatible.
-/
def exampleDifferentAbiTypes : Bool :=
  compatibleLayouts
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }
    { abiType := { name := "i64", size := 64, align := 64 },
          size := 64,
          align := 64,
          offsets := [0] }

/-- Example: Verify different ABI types incompatibility.
    Evaluates to show different types are incompatible.
-/
#eval exampleDifferentAbiTypes

/-!
## Example 14: Same Type Different Layout
Demonstrates same ABI type with different layouts.
-/

/-- Example: Check compatibility with same type, different offsets.
    This example shows that same type with different offsets is incompatible.
-/
def exampleSameTypeDifferentLayout : Bool :=
  compatibleLayouts
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0] }
    { abiType := { name := "i32", size := 32, align := 32 },
          size := 32,
          align := 32,
          offsets := [0, 4] }

/-- Example: Verify same type different layout incompatibility.
    Evaluates to show different layouts are incompatible.
-/
#eval exampleSameTypeDifferentLayout

/-!
## Example 15: Reflexive Compatibility
Demonstrates reflexive property of layout compatibility.
-/

/-- Example: Verify reflexive compatibility.
    This example shows that any layout is compatible with itself.
-/
def exampleReflexiveCompatibility : Bool :=
  compatibleLayouts exampleRefineI32 exampleRefineI32

/-- Example: Verify reflexive compatibility result.
    Evaluates to show reflexive compatibility.
-/
#eval exampleReflexiveCompatibility

/-!
## Example 16: Symmetric Compatibility
Demonstrates symmetric property of layout compatibility.
-/

/-- Example: Verify symmetric compatibility.
    This example shows that compatibility is symmetric.
-/
def exampleSymmetricCompatibility : Bool :=
  let L1 := exampleRefineI32
  let L2 := exampleRefineI32
  compatibleLayouts L1 L2 = compatibleLayouts L2 L1

/-- Example: Verify symmetric compatibility result.
    Evaluates to show symmetric compatibility.
-/
#eval exampleSymmetricCompatibility

/-!
## Example 17: Transitive Compatibility
Demonstrates transitive property of layout compatibility.
-/

/-- Example: Verify transitive compatibility.
    This example shows that compatibility is transitive.
-/
def exampleTransitiveCompatibility : Bool :=
  let L1 := exampleRefineI32
  let L2 := exampleRefineI32
  let L3 := exampleRefineI32
  compatibleLayouts L1 L2 ∧ compatibleLayouts L2 L3 → compatibleLayouts L1 L3

/-- Example: Verify transitive compatibility result.
    Evaluates to show transitive compatibility.
-/
#eval exampleTransitiveCompatibility

end Morph.Specs.AbiDataRefinement
