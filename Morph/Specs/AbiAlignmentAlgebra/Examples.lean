/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.AbiAlignmentAlgebra.Spec

/-!
# Examples: Alignment Algebra (ABI Layout)

This module provides concrete examples and test cases for ABI alignment algebra specification.

## Overview

The AbiAlignmentAlgebra Examples module demonstrates:
- Primitive type alignment properties
- Struct packing with alignment rules
- Offset calculation examples
- Total alignment and size computation
- C ABI compatibility verification

## Key Concepts

- **Primitive Alignment:** Primitive types have alignment equal to their width
- **Struct Packing:** Fields are packed according to alignment rules
- **Offset Calculation:** Field offsets are computed with proper alignment
- **Total Alignment:** Struct alignment is the maximum of field alignments
- **Total Size:** Struct size accounts for padding
-/

namespace Morph.Specs.AbiAlignmentAlgebra

/-!
## Example 1: Primitive Type Alignment
Demonstrates that primitive types have alignment equal to their width.
-/

/-- Example: Primitive type alignment for 32-bit integer.
    This example demonstrates that a 32-bit integer has size 32 and alignment 32.
-/
def examplePrimitiveI32Alignment : LayoutMetadata :=
  computePrimitiveLayout { width := 32 }

/-- Example: Verify primitive i32 alignment.
    Evaluates to show the computed layout for i32 type.
-/
#eval examplePrimitiveI32Alignment

/-- Example: Primitive type alignment for 64-bit integer.
    This example demonstrates that a 64-bit integer has size 64 and alignment 64.
-/
def examplePrimitiveI64Alignment : LayoutMetadata :=
  computePrimitiveLayout { width := 64 }

/-- Example: Verify primitive i64 alignment.
    Evaluates to show the computed layout for i64 type.
-/
#eval examplePrimitiveI64Alignment

/-- Example: Primitive type alignment for 8-bit boolean.
    This example demonstrates that a boolean has size 1 and alignment 1.
-/
def examplePrimitiveBoolAlignment : LayoutMetadata :=
  computePrimitiveLayout { width := 1 }

/-- Example: Verify primitive bool alignment.
    Evaluates to show the computed layout for bool type.
-/
#eval examplePrimitiveBoolAlignment

/-!
## Example 2: Single Field Struct
Demonstrates struct with a single field.
-/

/-- Example: Struct with single 32-bit integer field.
    This example shows a simple struct containing one i32 field.
-/
def exampleSingleFieldStruct : StructDef :=
  { fields := [{ fieldType := { width := 32 }, offset := 0, size := 32 }] }

/-- Example: Compute single field struct layout.
    Computes the layout metadata for the single field struct.
-/
def exampleSingleFieldLayout : LayoutMetadata :=
  computeStructLayout exampleSingleFieldStruct

/-- Example: Verify single field struct layout.
    Evaluates to show the computed layout for single field struct.
-/
#eval exampleSingleFieldLayout

/-!
## Example 3: Multiple Fields Struct
Demonstrates struct with multiple fields requiring padding.
-/

/-- Example: Struct with multiple fields of different alignments.
    This example shows a struct with i8, i32, and i16 fields.
-/
def exampleMultiFieldStruct : StructDef :=
  {
    fields := [
      { fieldType := { width := 8 }, offset := 0, size := 8 },
      { fieldType := { width := 32 }, offset := 8, size := 32 },
      { fieldType := { width := 16 }, offset := 40, size := 16 }
    ]
  }

/-- Example: Compute multi-field struct layout.
    Computes the layout metadata for the multi-field struct.
-/
def exampleMultiFieldLayout : LayoutMetadata :=
  computeStructLayout exampleMultiFieldStruct

/-- Example: Verify multi-field struct layout.
    Evaluates to show the computed layout for multi-field struct.
-/
#eval exampleMultiFieldLayout

/-!
## Example 4: Empty Struct
Demonstrates empty struct properties.
-/

/-- Example: Empty struct definition.
    This example shows a struct with no fields.
-/
def exampleEmptyStruct : StructDef :=
  { fields := [] }

/-- Example: Compute empty struct layout.
    Computes the layout metadata for the empty struct.
-/
def exampleEmptyLayout : LayoutMetadata :=
  computeStructLayout exampleEmptyStruct

/-- Example: Verify empty struct layout.
    Evaluates to show the computed layout for empty struct.
-/
#eval exampleEmptyLayout

/-!
## Example 5: Offset Calculation
Demonstrates offset calculation with alignment.
-/

/-- Example: Struct demonstrating offset calculation.
    This example shows a struct with fields at various offsets.
-/
def exampleOffsetCalcStruct : StructDef :=
  {
    fields := [
      { fieldType := { width := 8 }, offset := 0, size := 8 },
      { fieldType := { width := 32 }, offset := 8, size := 32 },
      { fieldType := { width := 8 }, offset := 40, size := 8 },
      { fieldType := { width := 64 }, offset := 48, size := 64 }
    ]
  }

/-- Example: Compute offsets for struct.
    Computes the list of field offsets.
-/
def exampleOffsetCalcOffsets : List Nat :=
  computeStructOffsets exampleOffsetCalcStruct.fields

/-- Example: Verify offset calculation.
    Evaluates to show the computed offsets.
-/
#eval exampleOffsetCalcOffsets

/-!
## Example 6: Total Alignment
Demonstrates total alignment computation.
-/

/-- Example: Struct with varying field alignments.
    This example shows a struct with fields of different alignments.
-/
def exampleAlignmentStruct : StructDef :=
  {
    fields := [
      { fieldType := { width := 8 }, offset := 0, size := 8 },
      { fieldType := { width := 32 }, offset := 8, size := 32 },
      { fieldType := { width := 64 }, offset := 40, size := 64 }
    ]
  }

/-- Example: Compute total alignment.
    Computes the alignment for the struct.
-/
def exampleAlignmentLayout : LayoutMetadata :=
  computeStructLayout exampleAlignmentStruct

/-- Example: Verify total alignment.
    Evaluates to show the computed alignment.
-/
#eval exampleAlignmentLayout

/-!
## Example 7: Total Size with Padding
Demonstrates total size computation with padding.
-/

/-- Example: Struct requiring end padding.
    This example shows a struct that needs padding at the end.
-/
def examplePaddingStruct : StructDef :=
  {
    fields := [
      { fieldType := { width := 8 }, offset := 0, size := 8 },
      { fieldType := { width := 32 }, offset := 8, size := 32 },
      { fieldType := { width := 8 }, offset := 40, size := 8 }
    ]
  }

/-- Example: Compute total size with padding.
    Computes the size for the struct including padding.
-/
def examplePaddingLayout : LayoutMetadata :=
  computeStructLayout examplePaddingStruct

/-- Example: Verify total size with padding.
    Evaluates to show the computed size including padding.
-/
#eval examplePaddingLayout

/-!
## Example 8: C ABI Compatibility
Demonstrates C ABI compatibility between layouts.
-/

/-- Example: Layout 1 - simple struct.
    This example shows a simple layout.
-/
def exampleLayout1 : LayoutMetadata :=
  { size := 32, align := { align := 32 }, offsets := [0] }

/-- Example: Layout 2 - equivalent layout.
    This example shows an equivalent layout.
-/
def exampleLayout2 : LayoutMetadata :=
  { size := 32, align := { align := 32 }, offsets := [0] }

/-- Example: Verify C ABI compatibility.
    Checks if two layouts are compatible.
-/
def exampleCabiCompatible : Bool :=
  exampleLayout1.size = exampleLayout2.size ∧
    exampleLayout1.align = exampleLayout2.align ∧
      exampleLayout1.offsets = exampleLayout2.offsets

/-- Example: Verify C ABI compatibility.
    Evaluates to check compatibility.
-/
#eval exampleCabiCompatible

/-!
## Example 9: Complex Nested Struct
Demonstrates struct with nested fields.
-/

/-- Example: Nested struct definition.
    This example shows a struct with fields at specific offsets.
-/
def exampleNestedStruct : StructDef :=
  {
    fields := [
      { fieldType := { width := 32 }, offset := 0, size := 32 },
      { fieldType := { width := 64 }, offset := 32, size := 64 }
    ]
  }

/-- Example: Compute nested struct layout.
    Computes the layout for the nested struct.
-/
def exampleNestedLayout : LayoutMetadata :=
  computeStructLayout exampleNestedStruct

/-- Example: Verify nested struct layout.
    Evaluates to show the computed layout.
-/
#eval exampleNestedLayout

/-!
## Example 10: Padding Calculation
Demonstrates padding calculation for alignment.
-/

/-- Example: Calculate padding for offset 3 with alignment 4.
    This example shows that offset 3 needs 1 byte of padding to align to 4.
-/
def examplePadding1 : Nat :=
  computePadding 3 4

/-- Example: Verify padding calculation.
    Evaluates to show the padding needed.
-/
#eval examplePadding1

/-- Example: Calculate padding for offset 5 with alignment 8.
    This example shows that offset 5 needs 3 bytes of padding to align to 8.
-/
def examplePadding2 : Nat :=
  computePadding 5 8

/-- Example: Verify padding calculation.
    Evaluates to show the padding needed.
-/
#eval examplePadding2

/-- Example: Calculate padding for offset 8 with alignment 8.
    This example shows that offset 8 needs 0 bytes of padding (already aligned).
-/
def examplePadding3 : Nat :=
  computePadding 8 8

/-- Example: Verify padding calculation.
    Evaluates to show the padding needed.
-/
#eval examplePadding3

/-!
## Example 11: Ceiling Division
Demonstrates ceiling division function.
-/

/-- Example: Ceiling division of 7 by 3.
    This example shows that ceil(7/3) = 3.
-/
def exampleCeilDiv1 : Nat :=
  ceilDiv 7 3

/-- Example: Verify ceiling division.
    Evaluates to show the result.
-/
#eval exampleCeilDiv1

/-- Example: Ceiling division of 8 by 4.
    This example shows that ceil(8/4) = 2 (exact division).
-/
def exampleCeilDiv2 : Nat :=
  ceilDiv 8 4

/-- Example: Verify ceiling division.
    Evaluates to show the result.
-/
#eval exampleCeilDiv2

/-- Example: Ceiling division of 10 by 3.
    This example shows that ceil(10/3) = 4.
-/
def exampleCeilDiv3 : Nat :=
  ceilDiv 10 3

/-- Example: Verify ceiling division.
    Evaluates to show the result.
-/
#eval exampleCeilDiv3

/-!
## Example 12: Field Offset Computation
Demonstrates field offset computation.
-/

/-- Example: Compute offset for first field.
    This example shows that the first field is always at offset 0.
-/
def exampleFieldOffset0 : Nat :=
  computeFieldOffset exampleMultiFieldStruct.fields 0

/-- Example: Verify field offset.
    Evaluates to show the first field offset.
-/
#eval exampleFieldOffset0

/-- Example: Compute offset for second field.
    This example shows the offset for the second field.
-/
def exampleFieldOffset1 : Nat :=
  computeFieldOffset exampleMultiFieldStruct.fields 1

/-- Example: Verify field offset.
    Evaluates to show the second field offset.
-/
#eval exampleFieldOffset1

/-- Example: Compute offset for third field.
    This example shows the offset for the third field.
-/
def exampleFieldOffset2 : Nat :=
  computeFieldOffset exampleMultiFieldStruct.fields 2

/-- Example: Verify field offset.
    Evaluates to show the third field offset.
-/
#eval exampleFieldOffset2

end Morph.Specs.AbiAlignmentAlgebra
