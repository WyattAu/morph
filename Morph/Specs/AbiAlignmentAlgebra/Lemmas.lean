/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.AbiAlignmentAlgebra.Spec

namespace Morph.Specs.AbiAlignmentAlgebra

/-!
## Lemmas

Lemmas and auxiliary results for the AbiAlignmentAlgebra specification.
-/

theorem computePrimitiveLayout_size_eq_width (p : PrimitiveWidth) :
  (computePrimitiveLayout p).size = p.width := rfl

theorem computePrimitiveLayout_align_eq_width (p : PrimitiveWidth) :
  (computePrimitiveLayout p).align.align = p.width := rfl

theorem computePadding_aligned_zero (alignment : Nat) :
  computePadding (2 * alignment) alignment = 0 := by
  unfold computePadding
  simp [Nat.mul_comm]

theorem computePadding_unaligned (offset alignment : Nat) (hne : offset % alignment ≠ 0) :
  computePadding offset alignment = alignment - offset % alignment := by
  simp [computePadding, hne]

theorem computeStructAlign_empty : computeStructAlign [] = { align := 1 } := rfl

theorem computeStructSize_empty : computeStructSize [] = 0 := rfl

theorem computeFieldOffset_zero (fields : List FieldLayout) :
  computeFieldOffset fields 0 = 0 := by
  unfold computeFieldOffset computeFieldOffsetAux
  split <;> simp_all

theorem ceilDiv_exact (a b : Nat) (_h : b > 0) (h2 : a % b = 0) :
  ceilDiv a b = a / b := by
  simp [ceilDiv, h2]

theorem ceilDiv_round_up (a b : Nat) (_h : b > 0) (h2 : a % b > 0) :
  ceilDiv a b = a / b + 1 := by
  unfold ceilDiv
  have : a % b ≠ 0 := by omega
  split <;> simp_all

theorem defaultFieldLayout_eq :
  defaultFieldLayout = { fieldType := default, offset := 0, size := 0 } := rfl

end Morph.Specs.AbiAlignmentAlgebra
