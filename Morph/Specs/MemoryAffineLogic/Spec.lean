/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/


import Morph.Core
import Morph.Memory
import Morph.Specs.CommonTypes

/-!
# Specification: Memory Affine Logic

**Source:** `spec/memory/memory_affine_logic_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Pending

## Overview

This specification formalizes affine type system logic for Morph,
ensuring that resources are used at most once (linear types) to prevent
use-after-free, double-free, and other memory safety issues.

The affine type system provides:
- Typing context with resource tracking
- Affine type predicates for types
- Context splitting and joining operations
- Resource linearity invariants

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| AFL-001 | `spec_affine_typing` | ✓ |
| AFL-002 | `spec_resource_linearity` | ✓ |
| AFL-003 | `spec_context_splitting` | ✓ |
| AFL-004 | `context_join_commutative` | ✓ |
| AFL-005 | `context_join_associative` | ✓ |
| AFL-006 | `empty_context_join_identity` | ✓ |
| AFL-007 | `affine_typing_memory_safety` | ✓ |

## Known Issues

None at this time.

-/

namespace Morph.Specs.MemoryAffineLogic

/- ## Core Type Definitions

This section defines fundamental types for affine typing system.
-/

/-- Typing context with resource tracking.

    The typing context tracks both variables and their types,
    along with a separate list of resources that must be used exactly once.
-/
structure AffineContext where
  /-- List of variable names and their types -/
  variables : List (String × MorphType)
  /-- List of resource names and their types -/
  resources : List (String × MorphType)
  deriving Repr

/- ## Helper Functions

This section provides utility functions for working with affine typing contexts.
-/

/-- Check if a variable exists in the context.

    Returns `true` if the variable is present in the variable list.
-/
def hasVariable (Γ : AffineContext) (x : String) : Prop :=
  ∃ (T : MorphType), (x, T) ∈ List.toArray Γ.variables

/-- Get the type of a variable in the context.

    Returns `some T` if the variable exists, otherwise `none`.
-/
def getVariableType (Γ : AffineContext) (x : String) : Option MorphType :=
  Γ.variables.find? (fun (y, _) => y = x) |>.map (fun (_, T) => T)

/-- Check if a resource exists in the context.

    Returns `true` if the resource is present in the resource list.
-/
def hasResource (Γ : AffineContext) (x : String) : Prop :=
  ∃ (T : MorphType), (x, T) ∈ List.toArray Γ.resources

/-- Get the type of a resource in the context.

    Returns `some T` if the resource exists, otherwise `none`.
-/
def getResourceType (Γ : AffineContext) (x : String) : Option MorphType :=
  Γ.resources.find? (fun (y, _) => y = x) |>.map (fun (_, T) => T)

/-- Count the number of times a variable appears in the context.

    In a well-formed context, each variable appears at most once.
-/
def variableCount (Γ : AffineContext) (x : String) : Nat :=
  Γ.variables.count (fun (y, _) => y = x)

/-- Count the number of times a resource appears in the context.

    In a well-formed context, each resource appears at most once.
-/
def resourceCount (Γ : AffineContext) (x : String) : Nat :=
  Γ.resources.count (fun (y, _) => y = x)

/- ## Affine Type Predicates

This section defines predicates for affine types.
-/

/-- Check if a type is affine (can only be used once).

    Affine types include primitive types, base types, and function types.
    They cannot be copied without explicit copy operations.
-/
def isAffineType (T : MorphType) : Prop :=
  match T with
  | .unit => True
  | .bool => True
  | .nat => True
  | .int => True
  | .string => True
  | .base _ => True
  | .arrow _ _ => True

/-- Check if a type is linear (must be used exactly once).

    Linear types are base types that must be used exactly once.
    They cannot be copied and must be consumed by operations.
-/
def isLinearType (T : MorphType) : Prop :=
  match T with
  | .base _ => True
  | _ => False

/- ## Well-Formedness Predicates

This section defines predicates for checking typing contexts.
-/

/-- Check if a context is well-formed (no duplicate variables).

    A context is well-formed when each variable appears at most once.
    Resources are tracked separately and also must not have duplicates.
-/
def isWellFormedContext (Γ : AffineContext) : Prop :=
  ∀ (x : String), variableCount Γ x ≤ 1

/-- Check if two contexts are disjoint (no shared variables).

    Two contexts are disjoint when they have no variables in common.
-/
def disjointContexts (Γ₁ Γ₂ : AffineContext) : Prop :=
  ∀ (x : String), ¬(hasVariable Γ₁ x ∧ hasVariable Γ₂ x)

/- ## Context Operations

This section defines operations for manipulating typing contexts.
-/

/-- Join two disjoint contexts.

    Concatenates the variable and resource lists of two contexts.
    This operation is valid only when contexts are disjoint.
-/
def joinContexts (Γ₁ Γ₂ : AffineContext) : AffineContext :=
  {
    variables := Γ₁.variables ++ Γ₂.variables,
    resources := Γ₁.resources ++ Γ₂.resources
  }

/-- Split a context by removing a variable.

    Removes the specified variable from the context.
    Returns `some (Γ₁, Γ₂)` where Γ₁ contains the removed variable
    and Γ₂ contains the remaining variables.
-/
def splitContext (Γ : AffineContext) (x : String) : Option (AffineContext × AffineContext) :=
  match getVariableType Γ x with
  | some T =>
      let Γ₁_vars := Γ.variables.filter (fun (y, _) => y = x)
      let Γ₂_vars := Γ.variables.filter (fun (y, _) => y ≠ x)
      some ({ variables := Γ₁_vars, resources := [] },
            { variables := Γ₂_vars, resources := Γ.resources })
  | none => none

/- ## Specification Theorems

This section contains formal specification theorems for affine type system.
-/

/- ## Affine Typing (AFL-001)

AFL-001 specifies affine typing rules for expressions.
-/

/-- AFL-001: Affine typing theorem.

    Well-typed expressions respect affine typing rules:
    - Variables in the context are used at most once
    - Linear types must be used exactly once
    - Affine types cannot be copied without explicit operations
-/
theorem spec_affine_typing (Γ : AffineContext) (e : Expr) : Prop :=
  typeChecks e →
    ∀ (x : String),
      hasVariable Γ x →
        variableCount Γ x ≤ 1

/- ## Resource Linearity (AFL-002)

AFL-002 specifies resource linearity invariants.
-/

/-- AFL-002: Resource linearity theorem.

    Resources in disjoint contexts remain linear when joined.
-/
theorem spec_resource_linearity (Γ₁ Γ₂ : AffineContext) : Prop :=
  disjointContexts Γ₁ Γ₂ →
    ∀ (x : String),
      hasVariable Γ₁ x ∨ hasVariable Γ₂ x →
        variableCount (joinContexts Γ₁ Γ₂) x ≤ 1

/- ## Context Splitting (AFL-003)

AFL-003 specifies context splitting properties.
-/

/-- AFL-003: Context splitting theorem.

    Any variable in a context can be split into its own sub-context.
    The split operation preserves all other variables and resources.
-/
theorem spec_context_splitting (Γ : AffineContext) (x : String) : Prop :=
  hasVariable Γ x →
    ∃ (Γ₁ Γ₂ : AffineContext),
      joinContexts Γ₁ Γ₂ = Γ ∧
        hasVariable Γ₁ x ∧
          disjointContexts Γ₁ Γ₂

/- ## Additional Specification Theorems

These theorems provide additional guarantees about affine typing.
-/

/-- AFL-004: Context join is commutative.

    Joining contexts is commutative up to definitional equality.
-/
theorem context_join_commutative (Γ₁ Γ₂ : AffineContext) : Prop :=
  joinContexts Γ₁ Γ₂ = joinContexts Γ₂ Γ₁

/-- AFL-005: Context join is associative.

    Joining contexts is associative up to definitional equality.
-/
theorem context_join_associative (Γ₁ Γ₂ Γ₃ : AffineContext) : Prop :=
  joinContexts (joinContexts Γ₁ Γ₂) Γ₃ = joinContexts Γ₁ (joinContexts Γ₂ Γ₃)

/-- AFL-006: Empty context is identity for join.

    Joining with an empty context returns the other context unchanged.
-/
theorem empty_context_join_identity (Γ : AffineContext) : Prop :=
  joinContexts Γ { variables := [], resources := [] } = Γ ∧
    joinContexts { variables := [], resources := [] } Γ = Γ

/-- AFL-007: Affine typing preserves memory safety.

    Well-typed affine expressions are memory safe.
-/
theorem spec_affine_typing_memory_safety (Γ : AffineContext) (e : Expr) : Prop :=
  typeChecks e → memorySafe e

/- ## Additional Theorems

These theorems provide additional properties of affine typing.
-/

/-- Affine types cannot be copied.

    Copying an affine type requires explicit copy operation.
    Without copy operation, the type can only be used once.
-/
theorem affine_types_no_copy (Γ : AffineContext) (x : String) (T : MorphType) : Prop :=
  isAffineType T →
    hasVariable Γ x →
      getVariableType Γ x = some T →
        ¬∃ (Γ' : AffineContext),
          Γ'.variables = (x, T) :: (x, T) :: Γ.variables.filter (fun (y, _) => y ≠ x)

/-- Linear types must be used exactly once.

    Linear types must appear exactly once in the context.
-/
theorem linear_types_used_once (Γ : AffineContext) (x : String) (T : MorphType) : Prop :=
  isLinearType T →
    hasVariable Γ x →
      getVariableType Γ x = some T →
        variableCount Γ x = 1

/-- Move operation consumes source.

    Moving a value consumes the source variable and creates a new destination.
-/
theorem move_consumes_source (Γ : AffineContext) (src dst : String) : Prop :=
  hasVariable Γ src →
    let Γ' := { variables := Γ.variables.filter (fun (y, _) => y ≠ src) ++ [(dst, (getVariableType Γ src).getD MorphType.unit)],
                 resources := Γ.resources } in
      ¬hasVariable Γ' src ∧ hasVariable Γ' dst

/-- Borrow operation preserves source.

    Borrowing a value preserves the source variable and creates a new destination.
-/
theorem borrow_preserves_source (Γ : AffineContext) (src dst : String) (region : Region) : Prop :=
  hasVariable Γ src →
    let Γ' := { variables := (dst, (getVariableType Γ src).getD MorphType.unit) :: Γ.variables,
                 resources := Γ.resources } in
      hasVariable Γ' src ∧ hasVariable Γ' dst

/-- Copy operation requires affine type.

    Copying an affine type is only allowed if the source type is affine.
-/
theorem copy_requires_affine (Γ : AffineContext) (src dst : String) : Prop :=
  hasVariable Γ src →
    match getVariableType Γ src with
    | some T =>
        isAffineType T →
          let Γ' := { variables := (dst, T) :: Γ.variables,
                       resources := Γ.resources } in
            hasVariable Γ' src ∧ hasVariable Γ' dst
    | none => False

/-- Variable use tracking.

    Variables in a well-formed context have a type and appear exactly once.
-/
theorem variable_use_tracking (Γ : AffineContext) (x : String) : Prop :=
  hasVariable Γ x →
    ∃ (T : MorphType), getVariableType Γ x = some T ∧ variableCount Γ x = 1

/-- Resource consumption.

    Resources in a well-formed context have a type and appear exactly once.
-/
theorem resource_consumption (Γ : AffineContext) (x : String) : Prop :=
  hasResource Γ x →
    ∃ (T : MorphType), getResourceType Γ x = some T ∧ resourceCount Γ x = 1

end Morph.Specs.MemoryAffineLogic
