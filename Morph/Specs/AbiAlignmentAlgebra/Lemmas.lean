/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.AbiAlignmentAlgebra.Spec

/-!
# Lemmas: Alignment Algebra (ABI Layout)

This module provides mathematical lemmas and proofs for ABI alignment algebra specification.

## Overview

The AbiAlignmentAlgebra Lemmas module formalizes:
- Primitive alignment correctness
- Struct packing algebra correctness
- Offset calculation correctness
- Total alignment correctness
- Total size correctness
- C ABI compatibility correctness

## Key Concepts

- **Primitive Alignment:** Primitive types have alignment equal to their width
- **Struct Packing:** Fields are packed according to alignment rules
- **Offset Calculation:** Field offsets are computed with proper alignment
- **Total Alignment:** Struct alignment is the maximum of field alignments
- **Total Size:** Struct size accounts for padding
- **C ABI Compatibility:** Layouts are compatible across dialects
-/

namespace Morph.Specs.AbiAlignmentAlgebra

/-!
## Primitive Alignment Lemmas
-/

/-- A layout for primitive type has size equal to type width.
    This lemma proves that primitive type size equals its width.
-/
theorem primitiveSizeEqualsWidth (p : PrimitiveWidth) :
    computePrimitiveLayout p.size = p.width := by
  unfold computePrimitiveLayout
  rfl

/-- A layout for primitive type has alignment equal to type width.
    This lemma proves that primitive type alignment equals its width.
-/
theorem primitiveAlignEqualsWidth (p : PrimitiveWidth) :
    computePrimitiveLayout p.align.align = p.width := by
  unfold computePrimitiveLayout
  rfl

/-- Primitive alignment specification holds for all primitive types.
    This theorem proves that primitive types have correct size and alignment.
-/
theorem spec_primitive_alignment_correct :
    spec_primitive_alignment := by
  intro p
  unfold spec_primitive_alignment
  constructor
  exact primitiveSizeEqualsWidth p
  exact primitiveAlignEqualsWidth p

/-!
## Struct Packing Lemmas
-/

/-- Empty struct has zero size and alignment 1.
    This lemma proves properties of empty structs.
-/
theorem emptyStructProperties :
    computeStructSize [] = 0 ∧
    computeStructAlign [] = { align := 1 } := by
  unfold computeStructSize computeStructAlign
  rfl

/-- Single field struct has size equal to field size.
    This lemma proves size property for single field structs.
-/
theorem singleFieldStructSize (f : FieldLayout) :
    let s := { fields := [f] } in
    computeStructSize s.fields = f.size := by
  unfold computeStructSize
  cases s.fields
  rfl

/-- Single field struct has alignment equal to field alignment.
    This lemma proves alignment property for single field structs.
-/
theorem singleFieldStructAlign (f : FieldLayout) :
    let s := { fields := [f] } in
    computeStructAlign s.fields = { align := f.fieldType.width } := by
  unfold computeStructAlign
  cases s.fields
  rfl

/-- Struct size is at least sum of field sizes.
    This lemma proves that struct size includes all field sizes.
-/
theorem structSizeAtLeastSum (s : StructDef) :
    computeStructSize s.fields ≥ s.fields.foldl (fun acc f => acc + f.size) 0 := by
  induction s.fields with
  | [] => rfl
  | f :: fs ih =>
    unfold computeStructSize
    have h_rest : computeStructSize fs ≥ fs.foldl (fun acc f => acc + f.size) 0 := by
      exact ih
    have h_padding : computePadding f.offset f.fieldType.width ≥ 0 := by
      unfold computePadding
      split
      rfl
      linarith
    linarith

/-- Struct alignment is maximum of field alignments.
    This lemma proves that struct alignment equals max field alignment.
-/
theorem structAlignIsMax (s : StructDef) :
    computeStructAlign s.fields.align = s.fields.foldl
      (fun acc f => Nat.max acc f.fieldType.width) 1 := by
  induction s.fields with
  | [] => rfl
  | f :: fs ih =>
    unfold computeStructAlign
    rw [ih]
    rfl

/-!
## Offset Calculation Lemmas
-/

/-- First field offset is zero.
    This lemma proves that first field starts at offset 0.
-/
theorem firstFieldOffsetZero (s : StructDef) :
    s.fields.length > 0 → computeFieldOffset s.fields 0 = 0 := by
  intro h_nonempty
  unfold computeFieldOffset
  rfl

/-- Offset calculation is monotonic.
    This lemma proves that offsets increase as we progress through fields.
-/
theorem offsetCalculationMonotonic (s : StructDef) (i j : Nat) :
    i < j → i < s.fields.length → j < s.fields.length →
      computeFieldOffset s.fields i ≤ computeFieldOffset s.fields j := by
  intros h_lt h_i_valid h_j_valid
  induction j with
  | zero =>
    intro h
    linarith
  | succ j ih =>
    intro h_i_lt_j
    by_cases h_eq : j = i
    case pos =>
      rw [h_eq]
      unfold computeFieldOffset
      have h_padding : computePadding _ _ ≥ 0 := by
        unfold computePadding
        split
        rfl
        linarith
      linarith
    case neg =>
      have h_i_lt_j : i < j := by
        linarith
      have h_j_valid : j < s.fields.length := by
        linarith
      have ih_result := ih h_i_lt_j (Nat.lt_of_lt_succ h_i_valid) h_j_valid
      unfold computeFieldOffset
      have h_padding : computePadding _ _ ≥ 0 := by
        unfold computePadding
        split
        rfl
        linarith
      linarith

/-- Padding is always non-negative.
    This lemma proves that padding calculation never produces negative values.
-/
theorem paddingNonNegative (offset alignment : Nat) :
    computePadding offset alignment ≥ 0 := by
  unfold computePadding
  split
  rfl
  linarith

/-!
## Total Alignment Lemmas
-/

/-- Total alignment is at least 1.
    This lemma proves minimum alignment requirement.
-/
theorem totalAlignmentAtLeastOne (s : StructDef) :
    computeStructAlign s.fields.align ≥ 1 := by
  cases s.fields with
  | [] => unfold computeStructAlign; rfl
  | f :: _ =>
    unfold computeStructAlign
    have h_max : Nat.max 1 f.fieldType.width ≥ 1 := by
      apply Nat.le_max_left
    exact h_max

/-- Total alignment equals maximum field alignment.
    This lemma provides explicit formula for struct alignment.
-/
theorem totalAlignmentEqualsMax (s : StructDef) :
    computeStructAlign s.fields.align = s.fields.foldl
      (fun acc f => Nat.max acc f.fieldType.width) 1 := by
  exact structAlignIsMax s

/-!
## Total Size Lemmas
-/

/-- Empty struct has size zero.
    This lemma proves empty struct size property.
-/
theorem emptyStructSizeZero :
    computeStructSize [] = 0 := by
  unfold computeStructSize
  rfl

/-- Total size accounts for padding.
    This lemma proves that struct size includes all padding.
-/
theorem totalSizeAccountsPadding (s : StructDef) :
    computeStructSize s.fields ≥ s.fields.foldl (fun acc f => acc + f.size) 0 := by
  exact structSizeAtLeastSum s

/-!
## C ABI Compatibility Lemmas
-/

/-- Layout compatibility is reflexive.
    This lemma proves that any layout is compatible with itself.
-/
theorem compatibleLayoutsReflexive (L : LayoutMetadata) :
    L.size = L.size ∧ L.align = L.align ∧ L.offsets = L.offsets := by
  constructor
  rfl
  constructor
  rfl
  rfl

/-!
## Correctness Theorems
-/

/-- Layout function specification holds.
    This theorem proves that layout function is well-defined.
-/
theorem spec_layout_function_correct :
    spec_layout_function := by
  intro T
  unfold spec_layout_function
  exists computePrimitiveLayout T.size, computePrimitiveLayout T.align
  constructor
  rfl
  rfl

/-- Struct packing algebra specification holds.
    This theorem proves that field offsets are correctly computed.
-/
theorem spec_struct_packing_algebra_correct :
    spec_struct_packing_algebra := by
  intro s i h_i_valid
  unfold spec_struct_packing_algebra
  unfold computeStructOffsets
  have h_index_eq : i = s.fields.length - 1 := by
    have h_len : i < s.fields.length := by
      exact h_i_valid
    have h_nonempty : s.fields.length > 0 := by
      linarith
    have h_le : i ≤ s.fields.length - 1 := by
      linarith
    by_cases h_eq : i = s.fields.length - 1
    case pos =>
      exact h_eq
    case neg =>
      have h_lt : i < s.fields.length - 1 := by
        linarith
      linarith
  rw [h_index_eq]
  have h_offset_eq : computeFieldOffset s.fields (s.fields.length - 1) =
                    (computeStructOffsets (s.fields.take (s.fields.length - 1))) ++
                    [computeFieldOffset s.fields (s.fields.length - 1)][s.fields.length - 1]! := by
    unfold computeStructOffsets
    cases s.fields with
    | [] =>
      have h_empty : s.fields.length = 0 := by
        rfl
      contradiction
    | f :: fs =>
      have h_len : s.fields.length = fs.length + 1 := by
        rfl
      rw [h_len]
      have h_take_len : (f :: fs).take (fs.length + 1) = f :: fs := by
        simp
      rw [h_take_len]
      rfl
  exact h_offset_eq

/-- Offset calculation specification holds.
    This theorem proves that offsets follow ceiling division formula.
-/
theorem spec_offset_calculation_correct :
    spec_offset_calculation := by
  intro s i h_i_valid
  unfold spec_offset_calculation
  split
  case inl h_zero =>
    rw [h_zero]
    unfold computeFieldOffset
    rfl
  case inr h_pos =>
    have h_i_pos : i > 0 := by
      linarith
    have h_i_minus_one_valid : i - 1 < s.fields.length := by
      linarith
    unfold computeFieldOffset
    have h_base_offset : computeFieldOffset s.fields (i - 1) + s.fields[i - 1]!.size =
                         computeFieldOffset s.fields (i - 1) + s.fields[i - 1]!.size := by
      rfl
    have h_ceil_div : ceilDiv (computeFieldOffset s.fields (i - 1) +
                              s.fields[i - 1]!.size)
                            s.fields[i]!.fieldType.width *
                            s.fields[i]!.fieldType.width =
                         ceilDiv (computeFieldOffset s.fields (i - 1) +
                              s.fields[i - 1]!.size)
                            s.fields[i]!.fieldType.width *
                            s.fields[i]!.fieldType.width := by
      unfold ceilDiv
      split
      rfl
      rfl
    rw [h_ceil_div]
    rfl

/-- Total alignment specification holds.
    This theorem proves that struct alignment equals maximum field alignment.
-/
theorem spec_total_alignment_correct :
    spec_total_alignment := by
  intro s
  unfold spec_total_alignment
  exact structAlignIsMax s

/-- Total size specification holds.
    This theorem proves that struct size accounts for all fields and padding.
-/
theorem spec_total_size_correct :
    spec_total_size := by
  intro s
  unfold spec_total_size
  by_cases h_empty : s.fields.length = 0
  case pos =>
    rw [h_empty]
    unfold computeStructSize
    have h_align : computeStructAlign [] = { align := 1 } := by
      unfold computeStructAlign
      rfl
    rw [h_align]
    unfold ceilDiv
    rfl
  case neg =>
    have h_nonempty : s.fields.length > 0 := by
      linarith
    have h_last_index : s.fields.length - 1 < s.fields.length := by
      linarith
    have h_last_offset : computeFieldOffset s.fields (s.fields.length - 1) =
                          (computeStructOffsets s.fields)[s.fields.length - 1]! := by
      have h_eq_index : s.fields.length - 1 = s.fields.length - 1 := by
        rfl
      rw [h_eq_index]
      unfold computeStructOffsets
      cases s.fields with
      | [] =>
        contradiction
      | f :: fs =>
        have h_len : s.fields.length = fs.length + 1 := by
          rfl
        rw [h_len]
        have h_take_eq : (f :: fs).take fs.length = fs := by
          simp
        rw [h_take_eq]
        rfl
    rw [h_last_offset]
    unfold computeStructSize
    have h_align_eq : computeStructAlign s.fields.align =
                       s.fields.foldl (fun acc f => Nat.max acc f.fieldType.width) 1 := by
      exact structAlignIsMax s
    rw [h_align_eq]
    unfold ceilDiv
    split
    rfl
    rfl

/-- C ABI compatibility specification holds.
    This theorem proves that identical layouts are compatible.
-/
theorem spec_c_abi_compatibility_correct :
    spec_c_abi_compatibility := by
  intro L1 L2
  unfold spec_c_abi_compatibility
  exact compatibleLayoutsReflexive L1

end Morph.Specs.AbiAlignmentAlgebra
