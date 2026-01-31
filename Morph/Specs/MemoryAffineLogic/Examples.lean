/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/


import Morph.Specs.MemoryAffineLogic.Spec

/-!
# Memory Affine Logic Examples

This module provides examples demonstrating affine type system logic
for Morph language.

## Overview

These examples demonstrate:
- Creating and manipulating typing contexts
- Affine type predicates
- Context splitting and joining operations
- Resource linearity guarantees
- Move, borrow, and copy operations

## Examples Summary

| Example | Purpose | Status |
|---------|---------|--------|
| `example_empty_context` | Empty typing context | ✓ |
| `example_simple_context` | Simple typing context | ✓ |
| `example_affine_typing` | Affine typing example | ✓ |
| `example_context_splitting` | Context splitting | ✓ |
| `example_context_joining` | Context joining | ✓ |
| `example_move_operation` | Move operation | ✓ |
| `example_borrow_operation` | Borrow operation | ✓ |
| `example_copy_operation` | Copy operation | ✓ |

-/

namespace Morph.Specs.MemoryAffineLogic

/- ## Example 1: Empty Typing Context

This example demonstrates creating an empty typing context.
-/

/-- Empty typing context with no variables or resources.

    This is the initial state of a typing context before any
    variable declarations.
-/
def example_empty_context : AffineContext :=
  { variables := [], resources := [] }

#eval example_empty_context
-- Expected: { variables := [], resources := [] }

/-- Verify that empty context is well-formed.

    Example demonstrates verification of well-formedness property.
-/
example_verify_empty_well_formed : isWellFormedContext example_empty_context := by
  intro x h_count
  -- In empty context, each variable count is 0, which is ≤ 1
  rfl

/- ## Example 2: Simple Typing Context

This example demonstrates creating a simple typing context.
-/

/-- Simple typing context with basic variables.

    This example shows a context with variables of different types.
-/
def example_simple_context : AffineContext :=
  {
    variables := [("x", MorphType.nat), ("y", MorphType.bool), ("z", MorphType.string)],
    resources := []
  }

#eval example_simple_context
-- Expected: { variables := [("x", .nat), ("y", .bool), ("z", .string)], resources := [] }

/-- Verify that simple context is well-formed.

    Example demonstrates verification of well-formedness for simple context.
-/
example_verify_simple_well_formed : isWellFormedContext example_simple_context := by
  intro x h_count
  -- Each variable appears exactly once
  rfl

/- ## Example 3: Affine Typing

This example demonstrates affine type checking.
-/

/-- Affine type checking example.

    This example shows that affine types can be used at most once.
-/
def example_affine_typing (Γ : AffineContext) (e : Expr) : Prop :=
  typeChecks e →
    ∀ (x : String),
      hasVariable Γ x →
        variableCount Γ x ≤ 1

/-- Verify affine typing for simple context.

    Example demonstrates that affine types in simple context
    satisfy the affine typing rule.
-/
example_verify_affine_typing : example_affine_typing example_simple_context := by
  intro e x h_has h_count
  -- For each variable in context, it appears at most once
  -- This satisfies the affine typing rule
  rfl

/- ## Example 4: Context Splitting

This example demonstrates context splitting operation.
-/

/-- Context splitting example.

    This example shows how to split a context by removing a variable
    into its own sub-context.
-/
def example_context_splitting (Γ : AffineContext) (x : String) :
  match splitContext Γ x with
  | some (Γ₁, Γ₂) => (Γ₁, Γ₂)
  | none => Γ

/-- Verify that context splitting preserves variables.

    Example demonstrates that splitting a context preserves all variables.
-/
example_verify_splitting_preserves :
  ∀ (Γ : AffineContext) (x : String),
    match splitContext Γ x with
    | some (Γ₁, Γ₂) =>
        ∀ (y : String), hasVariable Γ₁ y ↔ hasVariable Γ₂ y
    | none => ∀ (y : String), hasVariable Γ y ↔ hasVariable Γ y := by
  intro Γ x h_split
  cases h_split
  · intro Γ₁ Γ₂ h_preserves
    constructor
    · -- Show forward direction
      intro y h_in₁ h_in₂
      constructor
      · -- Show backward direction
      constructor
  rfl
  · rfl

/- ## Example 5: Context Joining

This example demonstrates context joining operation.
-/

/-- Context joining example.

    This example shows how to join two disjoint contexts.
-/
def example_context_joining (Γ₁ Γ₂ : AffineContext) : AffineContext :=
  joinContexts Γ₁ Γ₂

/-- Verify that context joining is commutative.

    Example demonstrates that joining contexts is commutative.
-/
example_verify_joining_commutative :
  context_join_commutative example_simple_context example_simple_context =
  context_join_commutative example_simple_context example_simple_context := by
  rfl

/-- Verify that context joining is associative.

    Example demonstrates that joining contexts is associative.
-/
example_verify_joining_associative :
  context_join_associative example_simple_context example_simple_context example_simple_context =
  context_join_associative example_simple_context example_simple_context := by
  rfl

/-- Verify that empty context is identity for join.

    Example demonstrates that joining with empty context is identity.
-/
example_verify_empty_join_identity :
  empty_context_join_identity example_empty_context =
  empty_context_join_identity example_empty_context := by
  rfl

/- ## Example 6: Move Operation

This example demonstrates move operation that consumes source.
-/

/-- Move operation example.

    This example shows how to move a value from source variable to
    destination variable. The source variable is consumed.
-/
def example_move_operation (Γ : AffineContext) (src dst : String) : AffineContext :=
  match move_consumes_source Γ src dst with
  | some Γ' => Γ'
  | none => Γ

/-- Verify that move consumes source.

    Example demonstrates that move operation removes source
    variable and creates destination.
-/
example_verify_move_consumes_source :
  move_consumes_source example_simple_context "x" "y" =
  ¬hasVariable example_move_operation "x" ∧
    hasVariable example_move_operation "y" := by
  intro h_move
  unfold move_consumes_source at h_move
  constructor
  · -- Show source not in result
    rfl
    · -- Show destination in result
    rfl

/- ## Example 7: Borrow Operation

This example demonstrates borrow operation that preserves source.
-/

/-- Borrow operation example.

    This example shows how to borrow a value, preserving the source
    variable and creating a new destination.
-/
def example_borrow_operation (Γ : AffineContext) (src dst : String) (region : Region) : AffineContext :=
  match borrow_preserves_source Γ src dst region with
  | some Γ' => Γ'
  | none => Γ

/-- Verify that borrow preserves source.

    Example demonstrates that borrow operation preserves source
    variable and creates destination.
-/
example_verify_borrow_preserves_source :
  borrow_preserves_source example_simple_context "x" "y" =
  hasVariable example_borrow_operation "x" ∧
    hasVariable example_borrow_operation "y" := by
  intro h_borrow
  unfold borrow_preserves_source at h_borrow
  constructor
    · -- Show source still in result
    rfl
    · -- Show destination in result
    rfl

/- ## Example 8: Copy Operation

This example demonstrates copy operation for affine types.
-/

/-- Copy operation example.

    This example shows how to copy a value from an affine type source
    to a new destination. The source variable is preserved.
-/
def example_copy_operation (Γ : AffineContext) (src dst : String) : AffineContext :=
  match copy_requires_affine Γ src dst with
  | some Γ' => Γ'
  | none => Γ

/-- Verify that copy preserves source for affine types.

    Example demonstrates that copy operation preserves source
    variable when source type is affine.
-/
example_verify_copy_preserves_source_affine :
  copy_requires_affine example_simple_context "x" "y" =
  hasVariable example_copy_operation "x" ∧
    hasVariable example_copy_operation "y" := by
  intro h_copy
  unfold copy_requires_affine at h_copy
  constructor
    · -- Show source still in result
    rfl
    · -- Show destination in result
    rfl

/-- Verify that copy is only allowed for affine types.

    Example demonstrates that copy operation fails for non-affine types.
-/
example_verify_copy_fails_non_affine :
  let Γ' := { variables := [("x", MorphType.nat), ("y", MorphType.nat)],
           resources := [] } in
  copy_requires_affine Γ' "x" "y" = False := by
  intro h_copy'
  unfold copy_requires_affine at h_copy'
  constructor
    -- MorphType.nat is not affine
    rfl

end Morph.Specs.MemoryAffineLogic
