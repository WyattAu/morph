/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.AbiAlignmentAlgebra.Spec

namespace Morph.Specs.AbiAlignmentAlgebra

/-!
## Examples

Concrete examples demonstrating the AbiAlignmentAlgebra specification.
-/

def u8 : PrimitiveWidth := { width := 1 }

def u32 : PrimitiveWidth := { width := 4 }

def u64 : PrimitiveWidth := { width := 8 }

def u8Layout : LayoutMetadata := computePrimitiveLayout u8

example : u8Layout.size = 1 := rfl

example : u8Layout.align.align = 1 := rfl

def u64Layout : LayoutMetadata := computePrimitiveLayout u64

example : u64Layout.size = 8 := rfl

example : u64Layout.align.align = 8 := rfl

example : computePadding 3 4 = 1 := by
  unfold computePadding; simp

example : computePadding 4 4 = 0 := by
  unfold computePadding; simp

example : computePadding 7 8 = 1 := by
  unfold computePadding; simp

example : computePadding 0 1 = 0 := by
  unfold computePadding; simp

example : computeStructSize [] = 0 := rfl

example : computeStructAlign [] = { align := 1 } := rfl

example : computeFieldOffset [] 5 = 0 := by
  unfold computeFieldOffset computeFieldOffsetAux; simp

def singleFieldStruct : StructDef := {
  fields := [{ fieldType := u32, offset := 0, size := 4 }]
}

def singleFieldLayout : LayoutMetadata := computeStructLayout singleFieldStruct

example : ceilDiv 10 3 = 4 := by
  unfold ceilDiv; decide

example : ceilDiv 9 3 = 3 := by
  unfold ceilDiv; decide

end Morph.Specs.AbiAlignmentAlgebra
