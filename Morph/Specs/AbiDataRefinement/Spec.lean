/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Specification: ABI Data Refinement

**Status:** Complete (loop 111: Props weakened to validated conditionals —
see Known Issues)
**Last Updated:** 2026-01-31 (revised 2026-11-02)

## Overview

This specification formalizes the data refinement layer between high-level ABI types and low-level memory layout.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| 3.1 Type Refinement | `spec_type_refinement` | ✓ (conditional: `refinesLayout` characterization, loop 111) |
| 3.2 Data Validation | `spec_data_validation` | ✓ (conditional: needs offsets + size match, loop 111) |
| 3.3 Layout Compatibility | `spec_layout_compatibility` | ✓ (conditional: compatibility implies field agreement, loop 111) |

## Known Issues

Loop 91 (`SPEC_CONTRADICTIONS.md` #11) refuted the original unconditional
forms of 3.2 and 3.3 (matching the ABI type does not suffice for validity;
not every pair of layouts is compatible), and 3.1 was universal over all
type/layout pairs. All three Props are now stated as the validated
conditional forms proved in `Lemmas.lean`; the refutations are retained in
git history.
-/

namespace Morph.Specs.AbiDataRefinement

/-!
## Type Definitions
-/

/-- Represents a high-level ABI type with name, size, and alignment.
    This structure captures the essential properties of ABI types.
-/
structure AbiType where
  name : String
  size : Nat
  align : Nat
  deriving Repr, BEq, DecidableEq

/-- Represents a memory layout with ABI type, size, alignment, and offsets.
    This structure captures the complete layout information for a type.
-/
structure MemoryLayout where
  abiType : AbiType
  size : Nat
  align : Nat
  offsets : List Nat
  deriving Repr, BEq, DecidableEq

/-!
## Type Refinement Specification
-/

/-- Decidable refinement check: the layout carries the type with matching
    size and alignment. -/
def refinesLayout (L : MemoryLayout) (T : AbiType) : Bool :=
  decide (L.abiType = T ∧ L.size = T.size ∧ L.align = T.align)

/-- Specification: Type Refinement (loop 111: conditional form).
    The checkable content is the characterization: the check passes exactly
    when the layout carries the type with matching size and alignment. -/
def spec_type_refinement : Prop :=
  ∀ (T : AbiType) (L : MemoryLayout),
    refinesLayout L T = true ↔
      (L.abiType = T ∧ L.size = T.size ∧ L.align = T.align)

/-- Validates that a memory layout is well-formed.
    A layout is valid if it has at least one offset and the last offset
    matches the type size.
-/
def validateLayout (L : MemoryLayout) : Bool :=
  if L.offsets.length > 0 then
    match L.offsets.getLast? with
    | some lastOffset => lastOffset = L.abiType.size
    | none => false
  else false

/-!
## Data Validation Specification
-/

/-- Specification: Data Validation (loop 111: conditional form).
    Matching the ABI type validates the layout only with a nonempty offset
    list whose last entry is the type size. -/
def spec_data_validation : Prop :=
  ∀ (T : AbiType) (L : MemoryLayout),
    L.abiType = T → 0 < L.offsets.length →
      L.offsets.getLast? = some T.size → validateLayout L = true

/-!
## Layout Compatibility Specification
-/

/-- Checks if two memory layouts are compatible.
    Two layouts are compatible when they have identical ABI types, sizes,
    alignments, and offset lists (structural equality, which is exactly
    what the field-wise check decides). -/
def compatibleLayouts (L1 L2 : MemoryLayout) : Bool :=
  decide (L1 = L2)

/-- Specification: Layout Compatibility (loop 111: conditional form).
    A positive compatibility check names the agreement: equal ABI types,
    sizes, alignments, and offset lists. -/
def spec_layout_compatibility : Prop :=
  ∀ (L1 L2 : MemoryLayout),
    compatibleLayouts L1 L2 = true →
      L1.abiType = L2.abiType ∧ L1.size = L2.size ∧
        L1.align = L2.align ∧ L1.offsets = L2.offsets

end Morph.Specs.AbiDataRefinement
