/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.AbiDataRefinement.Spec

/-!
# Lemmas: ABI Data Refinement

This module contains mathematical lemmas and proofs for ABI data refinement specification.

## Overview

The AbiDataRefinement Lemmas module provides:
- Type refinement properties
- Data validation theorems
- Layout compatibility proofs
- Integration lemmas connecting refinement and validation

## Key Concepts

- **Type Refinement:** Converting high-level ABI types to low-level memory layouts
- **Data Validation:** Ensuring data integrity during refinement
- **Layout Compatibility:** Verifying layout compatibility across ABI versions
-/

namespace Morph.Specs.AbiDataRefinement

/-!
## Type Refinement Lemmas

These lemmas establish properties of type refinement from high-level ABI types to memory layouts.
-/

/-- A layout that refines a type preserves the type's size.
    This lemma proves that if a layout L refines a type T according to
    `spec_type_refinement`, then layout's size equals the type's size.
-/
theorem typeRefinementPreservesSize (T : AbiType) (L : MemoryLayout) :
    spec_type_refinement T L → L.size = T.size := by
  intro h
  unfold spec_type_refinement at h
  exact h.right.left

/-- A layout that refines a type preserves the type's alignment.
    This lemma proves that if a layout L refines a type T according to
    `spec_type_refinement`, then layout's alignment equals the type's alignment.
-/
theorem typeRefinementPreservesAlign (T : AbiType) (L : MemoryLayout) :
    spec_type_refinement T L → L.align = T.align := by
  intro h
  unfold spec_type_refinement at h
  exact h.right.right

/-- A layout that refines a type has a matching ABI type.
    This lemma proves that if a layout L refines a type T according to
    `spec_type_refinement`, then layout's `abiType` field equals T.
-/
theorem typeRefinementMatchesType (T : AbiType) (L : MemoryLayout) :
    spec_type_refinement T L → L.abiType = T := by
  intro h
  unfold spec_type_refinement at h
  exact h.left

/-- A layout with matching ABI type, size, and alignment satisfies type refinement.
    This lemma provides the converse direction: if a layout's ABI type matches T
    and size and alignment are preserved, then the layout refines the type.
-/
theorem typeRefinementFromProperties (T : AbiType) (L : MemoryLayout) :
    L.abiType = T → L.size = T.size → L.align = T.align →
      spec_type_refinement T L := by
  intro h1 h2 h3
  unfold spec_type_refinement
  constructor
  exact h1
  constructor
  exact h2
  exact h3

/-!
## Data Validation Lemmas

These lemmas establish properties of the layout validation predicate.
-/

/-- A singleton layout with offset [0] is valid if type size is 0.
    This lemma proves that a layout with a single offset [0] is valid when
    the ABI type size is 0.
-/
theorem singletonLayoutValid (T : AbiType) (L : MemoryLayout) :
    L.offsets = [0] → L.abiType = T → T.size = 0 →
      validateLayout L = true := by
  intro h1 h2 h3
  unfold validateLayout
  rw [h1, h2, h3]
  rfl

/-- A valid layout must have non-empty offsets.
    This lemma proves that if `validateLayout L` returns true, then the offsets
    list is non-empty.
-/
theorem layoutValidImpliesNonEmpty (L : MemoryLayout) :
    validateLayout L = true → L.offsets.length > 0 := by
  intro h
  unfold validateLayout at h
  exact h.left

/-- A valid layout has its last offset equal to the type size.
    This lemma proves that if `validateLayout L` returns true, then the last offset
    in the offsets list equals the ABI type's size.
-/
theorem layoutValidImpliesLastOffsetEqualsSize (L : MemoryLayout) :
    validateLayout L = true →
      match L.offsets.getLast? with
      | some lastOffset => lastOffset = L.abiType.size
      | none => True := by
  intro h
  unfold validateLayout at h
  cases h.right with
  case some lastOffset h_eq =>
    exact h_eq
  case none =>
    contradiction h.left

/-- A layout with non-empty offsets and correct final offset is valid.
    This lemma provides a constructive way to prove a layout is valid by
    checking two conditions directly.
-/
theorem layoutValidFromConditions (L : MemoryLayout) :
    L.offsets.length > 0 →
      match L.offsets.getLast? with
      | some lastOffset => lastOffset = L.abiType.size
      | none => True →
        validateLayout L = true := by
  intro h1 h2
  unfold validateLayout
  constructor
  exact h1
  exact h2

/-!
## Layout Compatibility Lemmas

These lemmas establish properties of the layout compatibility predicate.
-/

/-- Layout compatibility is reflexive.
    This lemma proves that any layout is compatible with itself.
-/
theorem compatibleLayoutsReflexive (L : MemoryLayout) :
    compatibleLayouts L L = true := by
  unfold compatibleLayouts
  constructor
  rfl
  constructor
  rfl
  constructor
  rfl
  rfl

/-- Layout compatibility is symmetric.
    This lemma proves that if layout L1 is compatible with L2, then L2 is
    compatible with L1.
-/
theorem compatibleLayoutsSymmetric (L1 L2 : MemoryLayout) :
    compatibleLayouts L1 L2 = true → compatibleLayouts L2 L1 = true := by
  intro h
  unfold compatibleLayouts at h
  unfold compatibleLayouts
  constructor
  exact Eq.symm h.left
  constructor
  exact Eq.symm h.right.left
  constructor
  exact Eq.symm h.right.right.left
  exact Eq.symm h.right.right.right

/-- Layout compatibility is transitive.
    This lemma proves that if L1 is compatible with L2 and L2 is compatible
    with L3, then L1 is compatible with L3.
-/
theorem compatibleLayoutsTransitive (L1 L2 L3 : MemoryLayout) :
    compatibleLayouts L1 L2 = true →
      compatibleLayouts L2 L3 = true →
        compatibleLayouts L1 L3 = true := by
  intro h1 h2
  unfold compatibleLayouts at h1 h2
  unfold compatibleLayouts
  constructor
  exact Eq.trans h1.left h2.left
  constructor
  exact Eq.trans h1.right.left h2.right.left
  constructor
  exact Eq.trans h1.right.right.left h2.right.right.left
  exact Eq.trans h1.right.right.right h2.right.right.right

/-- Compatible layouts have the same ABI type.
    This lemma proves that if two layouts are compatible, their ABI types are equal.
-/
theorem compatibleLayoutsSameType (L1 L2 : MemoryLayout) :
    compatibleLayouts L1 L2 = true → L1.abiType = L2.abiType := by
  intro h
  unfold compatibleLayouts at h
  exact h.left

/-- Compatible layouts have the same size.
    This lemma proves that if two layouts are compatible, their sizes are equal.
-/
theorem compatibleLayoutsSameSize (L1 L2 : MemoryLayout) :
    compatibleLayouts L1 L2 = true → L1.size = L2.size := by
  intro h
  unfold compatibleLayouts at h
  exact h.right.left

/-- Compatible layouts have the same alignment.
    This lemma proves that if two layouts are compatible, their alignments are equal.
-/
theorem compatibleLayoutsSameAlign (L1 L2 : MemoryLayout) :
    compatibleLayouts L1 L2 = true → L1.align = L2.align := by
  intro h
  unfold compatibleLayouts at h
  exact h.right.right.left

/-- Compatible layouts have identical offsets.
    This lemma proves that if two layouts are compatible, their offsets lists
    are identical.
-/
theorem compatibleLayoutsSameOffsets (L1 L2 : MemoryLayout) :
    compatibleLayouts L1 L2 = true → L1.offsets = L2.offsets := by
  intro h
  unfold compatibleLayouts at h
  exact h.right.right.right

/-- Layouts with identical fields are compatible.
    This lemma provides a constructive way to prove compatibility by showing all
    fields are equal.
-/
theorem compatibleLayoutsFromEqualFields (L1 L2 : MemoryLayout) :
    L1.abiType = L2.abiType →
      L1.size = L2.size →
        L1.align = L2.align →
          L1.offsets = L2.offsets →
            compatibleLayouts L1 L2 = true := by
  intro h1 h2 h3 h4
  unfold compatibleLayouts
  constructor
  exact h1
  constructor
  exact h2
  constructor
  exact h3
  exact h4

/-!
## Integration Lemmas

These lemmas connect type refinement, data validation, and layout compatibility.
-/

/-- A layout that refines a type and is valid satisfies data validation specification.
    This lemma proves that if a layout L refines type T and L is valid, then
    the data validation specification holds for T and L.
-/
theorem refinementImpliesValidation (T : AbiType) (L : MemoryLayout) :
    spec_type_refinement T L → validateLayout L = true →
      spec_data_validation T L := by
  intro h1 h2
  unfold spec_data_validation
  intro h3
  exact h2

/-- Compatible layouts have the same validation status.
    This lemma proves that if two layouts are compatible, they are either both
    valid or both invalid.
-/
theorem compatibleLayoutsSameValidation (L1 L2 : MemoryLayout) :
    compatibleLayouts L1 L2 = true →
      validateLayout L1 = validateLayout L2 := by
  intro h
  unfold compatibleLayouts at h
  unfold validateLayout validateLayout
  have h_abiType : L1.abiType = L2.abiType := by
    exact h.left
  have h_size : L1.size = L2.size := by
    exact h.right.left
  have h_align : L1.align = L2.align := by
    exact h.right.right.left
  have h_offsets : L1.offsets = L2.offsets := by
    exact h.right.right.right
  congr
  exact h_offsets
  rw [h_abiType]

/-- A layout that refines a type and has matching size and alignment is
    compatible with itself.
    This lemma shows the relationship between type refinement and self-compatibility.
-/
theorem refinementImpliesSelfCompatible (T : AbiType) (L : MemoryLayout) :
    spec_type_refinement T L → compatibleLayouts L L = true := by
  intro h
  exact compatibleLayoutsReflexive L

/-- Two layouts that both refine the same type are compatible if they have
    identical fields.
    This lemma connects type refinement to layout compatibility.
-/
theorem sameTypeRefinementImpliesCompatibility
    (T : AbiType) (L1 L2 : MemoryLayout) :
    spec_type_refinement T L1 →
      spec_type_refinement T L2 →
        L1.size = L2.size →
          L1.align = L2.align →
            L1.offsets = L2.offsets →
              compatibleLayouts L1 L2 = true := by
  intro h1 h2 h3 h4 h5
  unfold compatibleLayouts
  constructor
  exact Eq.trans (typeRefinementMatchesType T L1 h1)
                (Eq.symm (typeRefinementMatchesType T L2 h2))
  constructor
  exact h3
  constructor
  exact h4
  exact h5

/-- A valid layout that refines a type satisfies the layout compatibility
    specification.
    This lemma shows that a single valid refinement layout trivially satisfies
    the compatibility specification with itself.
-/
theorem validRefinementSatisfiesCompatibility (T : AbiType) (L : MemoryLayout) :
    spec_type_refinement T L → validateLayout L = true →
      ∃ L' : MemoryLayout, compatibleLayouts L L' = true := by
  intro h1 h2
  exists L
  exact compatibleLayoutsReflexive L

/-!
## Correctness Theorems
-/

/-- Type refinement specification holds for all valid layouts.
    This theorem proves that any valid layout that matches a type satisfies
    type refinement.
-/
theorem spec_type_refinement_correct :
    ∀ (T : AbiType) (L : MemoryLayout),
      L.abiType = T ∧ L.size = T.size ∧ L.align = T.align →
        spec_type_refinement T L := by
  intro T L h
  unfold spec_type_refinement
  exact h

/-- Data validation specification holds for all valid layouts.
    This theorem proves that data validation is satisfied when ABI types match.
-/
theorem spec_data_validation_correct :
    ∀ (T : AbiType) (L : MemoryLayout),
      L.abiType = T → validateLayout L = true →
        spec_data_validation T L := by
  intro T L h1 h2
  unfold spec_data_validation
  intro h3
  exact h2

/-- Layout compatibility specification holds for all identical layouts.
    This theorem proves that identical layouts are compatible.
-/
theorem spec_layout_compatibility_correct :
    ∀ (L1 L2 : MemoryLayout),
      L1.abiType = L2.abiType ∧
        L1.size = L2.size ∧
          L1.align = L2.align ∧
            L1.offsets = L2.offsets →
              compatibleLayouts L1 L2 = true := by
  intro L1 L2 h
  unfold compatibleLayouts
  exact h

end Morph.Specs.AbiDataRefinement
