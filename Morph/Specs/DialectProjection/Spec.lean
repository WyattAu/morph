/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Dialect Projection Specification

Multi-stage compilation dialect system for Morph.
Defines dialects, their capabilities, and inter-dialect projections (lowering).

## Overview

The compilation pipeline targets different dialects at each stage:
- **Core:** Safe, verifiable intermediate representation
- **Unsafe:** Low-level operations for trusted runtime code
- **FFI:** Foreign function interface bindings

Projections (lowerings) map terms from higher-level dialects to lower-level ones,
enabling staged compilation with verified transformations.

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Dialect variants | `Dialect` | Done |
| Dialect capabilities | `DialectCapability` | Done |
| Projection / lowering | `Projection` | Done |

## Known Issues

None.
-/

namespace Morph.Specs.DialectProjection

/-- Compilation dialect in the multi-stage pipeline -/
inductive Dialect where
  | core : Dialect
  | «unsafe» : Dialect
  | ffi : Dialect
  deriving Repr, BEq, Hashable

/-- Capability flags for a dialect -/
structure DialectCapability where
  supportsSideEffects : Bool
  supportsUnsafeOps : Bool
  supportsForeignCalls : Bool
  supportsHigherOrder : Bool
  supportsMutation : Bool
  deriving Repr

def coreCapabilities : DialectCapability :=
  { supportsSideEffects := false
    supportsUnsafeOps := false
    supportsForeignCalls := false
    supportsHigherOrder := true
    supportsMutation := false }

def unsafeCapabilities : DialectCapability :=
  { coreCapabilities with supportsSideEffects := true, supportsUnsafeOps := true, supportsMutation := true }

def ffiCapabilities : DialectCapability :=
  { coreCapabilities with supportsForeignCalls := true, supportsSideEffects := true }

/-- Retrieve capability set for a dialect -/
def dialectCapabilities (d : Dialect) : DialectCapability :=
  match d with
  | .core => coreCapabilities
  | .«unsafe» => unsafeCapabilities
  | .ffi => ffiCapabilities

/-- A projection lowers terms from one dialect to another -/
structure Projection where
  source : Dialect
  target : Dialect
  name : String

/-- A projection is valid when the target dialect has a superset of capabilities
    needed by the source. For now this is a simple ordering check. -/
def Projection.isValid (p : Projection) : Prop :=
  match p.source, p.target with
  | .core, .«unsafe» => True
  | .core, .ffi => True
  | .«unsafe», .ffi => True
  | _, _ => False

/-- A value that exists in a particular dialect -/
structure DialectValue where
  dialect : Dialect
  repr : Nat

end Morph.Specs.DialectProjection
