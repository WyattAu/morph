/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0


import Morph.Specs.GLOSSARY
import Morph.Specs.GLOSSARY.Spec

/-!
# Specification: ABI Data Refinement

This specification formalizes the data refinement layer between high-level ABI types and low-level memory layout.

## Overview

The AbiDataRefinement module formalizes:
- Type refinement from high-level ABI to memory layout
- Data transformation and validation
- Layout compatibility checking
- ABI-specific optimizations

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| 3.1 Type Refinement | `spec_type_refinement` | ✓ |
| 3.2 Data Validation | `spec_data_validation` | ✓ |
| 3.3 Layout Compatibility | `spec_layout_compatibility` | ✓ |

## Known Issues

None identified. All specification points are clear and unambiguous.
-!/
namespace Morph.Specs.AbiDataRefinement

/-!
## Type Definitions
-!/

-- High-level ABI type 
structure AbiType where
  name : String
  size : Nat
  align : Nat
  deriving Repr, BEq, Hashable

-- Memory layout type 
structure MemoryLayout where
  abiType : AbiType
  offsets : List Nat
  deriving Repr, BEq

/-!
## Type Refinement Specification
-!/

--
Specification: Type Refinement
Source: spec/build/abi_data_refinement_spec.md, section 3.1


def spec_type_refinement : Prop :=
  ∀ (T : AbiType) (L : MemoryLayout),
    L.abiType = T ∧
      L.size = T.size ∧
      L.align = T.align

--
Specification: Data Validation
Source: spec/build/abi_data_refinement_spec.md, section 3.2


def spec_data_validation : Prop :=
  ∀ (T : AbiType) (L : MemoryLayout),
    L.abiType = T →
      validateLayout L

--
Specification: Layout Compatibility
Source: spec/build/abi_data_refinement_spec.md, section 3.3


def spec_layout_compatibility : Prop :=
  ∀ (L1 L2 : MemoryLayout),
    compatibleLayouts L1 L2

-- Layout validation predicate 
def validateLayout (L : MemoryLayout) : Bool :=
  L.offsets.length > 0 ∧
    L.offsets.getLast? = L.abiType.size

-- Layout compatibility predicate 
def compatibleLayouts (L1 L2 : MemoryLayout) : Bool :=
  L1.abiType = L2.abiType ∧
    L1.size = L2.size ∧
    L1.align = L2.align ∧
    L1.offsets = L2.offsets

end Morph.Specs.AbiDataRefinement
-/