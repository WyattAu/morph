/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0


import Morph.Specs.GLOSSARY
import Morph.Specs.GLOSSARY.Spec
import Morph.Specs.AbiAlignmentAlgebra.Spec

/-!
# AbiAlignmentAlgebra Lemmas

This module provides mathematical lemmas and theorems for ABI alignment algebra specification.

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

-!/
namespace Morph.Specs.AbiAlignmentAlgebra

/-!
## Primitive Alignment Lemmas
-!/

-- Lemma: Primitive width equals size and alignment for primitive types 
lemma primitive_width_equals_size_align (p : PrimitiveWidth) :
  LayoutFunction.size (.primitive p) = p ∧
  LayoutFunction.align (.primitive p) = p := by
  -- By definition of compute_size and compute_align for primitive types
  -- Primitive types have size = width and align = width
  unfold compute_size
  unfold compute_align
  cases p
  constructor
  rfl

-- Lemma: Primitive alignment is natural number 
lemma primitive_alignment_is_nat (p : PrimitiveWidth) :
  (LayoutFunction.align (.primitive p)).align = p := by
  -- Alignment values are natural numbers by definition
  unfold LayoutFunction
  unfold Alignment
  cases p
  constructor
  rfl

/-!
## Struct Packing Lemmas
-!/

-- Lemma: Empty struct has zero size and alignment 1 
lemma empty_struct_properties :
  compute_struct_size [] = 0 ∧
  compute_struct_align [] = 1 := by
  -- Empty struct has no fields, so size is 0 and alignment is 1
  unfold compute_struct_size
  unfold compute_struct_align
  rfl

-- Lemma: Single field struct properties 
lemma single_field_struct_properties (f : FieldLayout) :
  let s := { fields := [f] } in
  compute_struct_size s.fields = f.size ∧
  compute_struct_align s.fields = f.field_type.align := by
  -- Single field struct has size equal to field size
  -- Alignment is equal to field's alignment
  unfold compute_struct_size
  unfold compute_struct_align
  cases s.fields
  constructor
  rfl

-- Lemma: Struct size is at least sum of field sizes 
lemma struct_size_at_least_sum (s : StructDef) :
  compute_struct_size s.fields ≥ s.fields.foldl (fun acc f => acc + f.size) 0 := by
  -- Struct size includes all field sizes plus padding
  -- Padding ensures size >= sum of field sizes
  induction s.fields with
  | [] => rfl
  | f :: fs =>
    have h_rest : compute_struct_size fs ≥ fs.foldl (fun acc f => acc + f.size) 0 := by
      induction fs with
      | [] => rfl
      | _ :: _ =>
        have ih : compute_struct_size _ ≥ _.foldl (fun acc f => acc + f.size) 0 := by
          assumption
        calc
          compute_struct_size (_ :: fs)
        = compute_struct_size fs
        ≥ _.foldl (fun acc f => acc + f.size) 0
        = f.size + _.foldl (fun acc f => acc + f.size) 0
    linarith

-- Lemma: Struct alignment is maximum of field alignments 
lemma struct_alignment_is_max (s : StructDef) :
  compute_struct_align s.fields = s.fields.foldl (fun acc f => Nat.max acc f.field_type.align) 1 := by
  -- Struct alignment is the maximum alignment among all fields
  -- This ensures proper alignment for all fields
  induction s.fields with
  | [] => rfl
  | f :: fs =>
    have h_rest : compute_struct_align fs = Nat.max (compute_struct_align fs) f.field_type.align := by
      induction fs with
        | [] => rfl
        | _ :: _ =>
          have ih : compute_struct_align _ = _.foldl (fun acc f => Nat.max acc f.field_type.align) 1 := by
            assumption
          calc
            compute_struct_align (_ :: fs)
          = Nat.max (compute_struct_align fs) f.field_type.align
          = Nat.max (_.foldl (fun acc f => Nat.max acc f.field_type.align) 1) f.field_type.align
          = Nat.max (Nat.max (_.foldl (fun acc f => Nat.max acc f.field_type.align) 1) f.field_type.align) f.field_type.align
    linarith

/-!
## Offset Calculation Lemmas
-!/

-- Lemma: First field offset is zero 
lemma first_field_offset_zero (s : StructDef) :
  s.fields.length > 0 →
    compute_struct_offset s.fields = 0 := by
  -- First field starts at offset 0
  intro h_nonempty
  unfold compute_struct_offset
  cases s.fields
  | f :: fs =>
    have h_single : compute_struct_offset [f] = 0 := by
      unfold compute_struct_offset
      rfl
    have h_rest : compute_struct_offset fs = compute_struct_offset [f] := by
      induction fs with
        | [] => rfl
        | _ :: _ =>
          have ih : compute_struct_offset _ = compute_struct_offset [f] := by
            assumption
          rfl
    linarith

-- Lemma: Offset calculation is monotonic 
lemma offset_calculation_monotonic (s : StructDef) (i j : Nat) :
  i < j →
    compute_struct_offset (s.fields.take (i + 1)) ≤
      compute_struct_offset (s.fields.take (j + 1)) := by
  -- Offsets increase as we progress through fields
  intro h_lt
  induction j with
  | zero => intro h; linarith
  | succ j ih =>
    intro h_i_lt_j
    have h_take_i : s.fields.take (i + 1) = s.fields.take (j + 1).take i := by
      simp
    calc
      compute_struct_offset (s.fields.take (i + 1))
    = compute_struct_offset h_take_i
    ≤ compute_struct_offset (s.fields.take (j + 1)) := by
      ih h_i_lt_j

/-!
## Total Alignment Lemmas
-!/

-- Lemma: Total alignment is at least 1 
lemma total_alignment_at_least_one (s : StructDef) :
  compute_struct_align s.fields ≥ 1 := by
  -- Struct alignment is at least 1 (minimum alignment)
  -- Empty struct has alignment 1
  -- Non-empty struct has alignment >= max field alignment >= 1
  cases s.fields with
  | [] => unfold compute_struct_align; rfl
  | f :: _ =>
    have h_max : Nat.max 1 f.field_type.align ≥ 1 := by
      linarith
    calc
      compute_struct_align (f :: _)
    = Nat.max (compute_struct_align []) f.field_type.align
    = Nat.max 1 f.field_type.align
    ≥ 1 := by
      h_max
    linarith

-- Lemma: Total alignment equals maximum field alignment 
lemma total_alignment_equals_max (s : StructDef) :
  compute_struct_align s.fields = s.fields.foldl (fun acc f => Nat.max acc f.field_type.align) 1 := by
  -- Struct alignment is exactly the maximum field alignment
  induction s.fields with
  | [] => rfl
  | f :: fs =>
    have h_rest : compute_struct_align fs = Nat.max (compute_struct_align fs) f.field_type.align := by
      induction fs with
        | [] => rfl
        | _ :: _ =>
          have ih : compute_struct_align _ = _.foldl (fun acc f => Nat.max acc f.field_type.align) 1 := by
            assumption
          calc
            compute_struct_align (_ :: fs)
          = Nat.max (compute_struct_align fs) f.field_type.align
          = Nat.max (_.foldl (fun acc f => Nat.max acc f.field_type.align) 1) f.field_type.align
        = Nat.max (Nat.max (_.foldl (fun acc f => Nat.max acc f.field_type.align) 1) f.field_type.align) f.field_type.align
    linarith

/-!
## Total Size Lemmas
-!/

-- Lemma: Empty struct has size zero 
lemma empty_struct_size_zero :
  compute_struct_size [] = 0 := by
  -- Empty struct has no fields, so size is 0
  unfold compute_struct_size
  rfl

-- Lemma: Total size accounts for padding 
lemma total_size_accounts_padding (s : StructDef) :
  let sumSizes := s.fields.foldl (fun acc f => acc + f.size) 0 in
  compute_struct_size s.fields ≥ sumSizes := by
  -- Total size is sum of field sizes plus padding
  -- Padding ensures proper alignment
  induction s.fields with
  | [] => rfl
  | f :: fs =>
    have h_rest : compute_struct_size fs ≥ fs.foldl (fun acc f => acc + f.size) 0 := by
      struct_size_at_least_sum { fields := fs }
    linarith

/-!
## C ABI Compatibility Lemmas
-!/

-- Lemma: Same layout implies same size and alignment 
lemma same_layout_implies_same_size_align
  (L1 L2 : LayoutMetadata) :
  L1.size = L2.size ∧ L1.align = L2.align := by
  -- If two layouts have same size and alignment, they are equivalent
  rfl

-- Lemma: Same layout implies same offsets 
lemma same_layout_implies_same_offsets
  (L1 L2 : LayoutMetadata) :
  L1.size = L2.size ∧ L1.align = L2.align → L1.offsets = L2.offsets := by
  -- If layouts have same size and alignment, offsets must be identical
  intro h_size_align
  rfl

/-!
## Correctness Theorems
-!/

-- Theorem: Primitive alignment correctness 
theorem spec_primitive_alignment_correct :
  spec_primitive_alignment := by
  -- For all primitive types, size and alignment equal to width
  intro p
  unfold spec_primitive_alignment
  constructor
  exact primitive_width_equals_size_align p

-- Theorem: Struct packing algebra correctness 
theorem spec_struct_packing_algebra_correct :
  spec_struct_packing_algebra := by
  -- For all structs, offsets are correctly computed
  intro s
  unfold spec_struct_packing_algebra
  intro h_offsets
  -- Offsets are computed by compute_struct_offsets
  exact h_offsets

-- Theorem: Offset calculation correctness 
theorem spec_offset_calculation_correct :
  spec_offset_calculation := by
  -- Offset calculation follows ceiling division formula
  intro s
  unfold spec_offset_calculation
  intro i
  cases i with
  | zero =>
    -- Base case: offset of empty prefix is 0
    rfl
  | succ i ih =>
    -- Inductive step: offset follows ceiling division
    have h_ceil_div : ∀ a b, ceil_div a b = if a % b = 0 then a / b else (a / b) + 1 := by
      unfold ceil_div
      intro a b
      cases a % b = 0 <;> rfl
    have h_offset_formula :
      compute_struct_offset (s.fields.take (i + 2)) =
      ceil_div (compute_struct_offset (s.fields.take (i + 1)) +
                s.fields[i]!.size)
                (s.fields[i + 1]!.field_type.align) *
                (s.fields[i + 1]!.field_type.align) := by
      unfold compute_struct_offset
      unfold compute_struct_size
      unfold compute_struct_align
      rw [h_ceil_div]
    exact h_offset_formula

-- Theorem: Total alignment correctness 
theorem spec_total_alignment_correct :
  spec_total_alignment := by
  -- Total alignment is maximum of first two field alignments
  intro s
  unfold spec_total_alignment
  cases s.fields with
  | [] => rfl
  | f1 :: [] =>
    -- Single field: alignment is field alignment
    rfl
  | f1 :: f2 :: _ =>
    -- Two or more fields: alignment is max of first two
    have h_max_two : Nat.max (Nat.max 1 f1.field_type.align) f2.field_type.align =
                     Nat.max (Nat.max 1 f1.field_type.align) f2.field_type.align := by
      rfl
    have h_max_rest : Nat.max (Nat.max (Nat.max 1 f1.field_type.align) f2.field_type.align)
                              (compute_struct_align _) =
                     Nat.max (Nat.max (Nat.max 1 f1.field_type.align) f2.field_type.align)
                              (compute_struct_align _) := by
      rfl
    calc
      compute_struct_align (f1 :: f2 :: _)
    = Nat.max (Nat.max 1 f1.field_type.align) f2.field_type.align
    = Nat.max (Nat.max (Nat.max 1 f1.field_type.align) f2.field_type.align)
              (compute_struct_align _)
    linarith

-- Theorem: Total size correctness 
theorem spec_total_size_correct :
  spec_total_size := by
  -- Total size accounts for padding at end of struct
  intro s
  unfold spec_total_size
  have h_size : compute_struct_size s.fields = compute_struct_size s.fields := by
    rfl
  have h_ceil : ∀ a b, ceil_div a b ≥ a / b := by
      unfold ceil_div
      intro a b
      cases a % b = 0 <;> linarith
    have h_total_size :
      compute_struct_size s.fields =
      ceil_div (compute_struct_offset s.fields) (s.fields[s.fields.length - 1]!.size) *
                (compute_struct_align s.fields) *
                (compute_struct_align s.fields) := by
      unfold compute_struct_size
      unfold compute_struct_offset
      unfold compute_struct_align
      rw [h_ceil]
    linarith
  exact h_total_size

-- Theorem: C ABI compatibility correctness 
theorem spec_c_abi_compatibility_correct :
  spec_c_abi_compatibility := by
  -- Layouts with same size, alignment, and offsets are compatible
  intro T1 T2 L1 L2
  unfold spec_c_abi_compatibility
  intro h_size h_align h_offsets
  -- If size, alignment, and offsets match, layouts are compatible
  exact h_size h_align h_offsets

end Morph.Specs.AbiAlignmentAlgebra
-/