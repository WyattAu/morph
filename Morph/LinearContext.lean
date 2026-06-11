/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
open Morph.Core

namespace Morph

/-!
# Linear Context for Substructural Type Tracking

This module defines the linear usage context for tracking variable consumption
in the capability type system (ADR-010).

## Background

Standard type systems allow variables to be used any number of times (unrestricted).
Morph's capability types require substructural discipline:
- **iso** (isolated): Linear — must be used exactly once
- **val** (immutable value): Affine — may be used at most once
- **ref** (mutable reference): Borrowed — bounded by lifetime
- **Other types**: Unrestricted — may be used any number of times

## Design

The linear context tracks usage for each bound variable:
- `Usage.zero`: Not yet used
- `Usage.one`: Used exactly once (linear/affine: now consumed)
- `Usage.many`: Used multiple times (only valid for unrestricted types)

The typing judgment `HasType` will be extended to use `LinCtx` instead of
plain `bvs : List Typ`, enabling enforcement of linearity constraints.

## Migration Path

Phase 1 (current): Types defined, not yet integrated into HasType.
Phase 2: HasType signature changes from `bvs : List Typ` to `ctx : LinCtx`.
Phase 3: Consumption rules added for iso/val types.
Phase 4: Full linear soundness proof.

-/


/-! ## Usage Tracking -/

/-- Usage status for a bound variable.
    - `zero`: Not yet consumed (available for use)
    - `one`: Used exactly once (consumed — not available)
    - `many`: Used multiple times (unrestricted — always available) -/
inductive Usage where
  | zero : Usage
  | one : Usage
  | many : Usage
  deriving Repr, BEq, DecidableEq

namespace Usage

/-- Merge two usages (for branching control flow: if/else, match arms).
    In each branch, a variable may be used differently. The merge rule is:
    - zero + zero = zero (not used in either branch)
    - zero + one = zero (used in one branch — overall may not be used)
    - one + zero = zero (symmetric)
    - one + one = one (used in both branches — consumed)
    - many + _ = many (unrestricted stays unrestricted)
    - _ + many = many -/
def merge : Usage → Usage → Usage
  | zero, zero => zero
  | zero, one  => zero  -- affine: used in one branch, not both → not consumed
  | one,  zero => zero  -- symmetric
  | one,  one  => one   -- linear: used in both branches → consumed
  | many, _    => many
  | _,    many => many

/-- Check if a usage allows further access. -/
def isAvailable : Usage → Bool
  | zero => true
  | one  => false
  | many => true

end Usage

/-! ## Linear Context -/

/-- A linear context entry: a type paired with its usage status. -/
abbrev LinEntry := (Typ × Usage)

/-- The linear context: a list of (type × usage) entries.
    Index 0 is the most recently bound variable (de Bruijn convention).

    This replaces the plain `bvs : List Typ` in the current HasType judgment.
    Migration: `bvs = ctx.map Prod.fst` (project types from context). -/
abbrev LinCtx := List LinEntry

namespace LinCtx

/-! ## Context Operations -/

/-- Empty linear context. -/
def empty : LinCtx := []

/-- Get the type at a given index (if it exists). -/
def getType? (ctx : LinCtx) (idx : Nat) : Option Typ :=
  ctx[idx]?.map Prod.fst

/-- Get the usage at a given index (if it exists). -/
def getUsage? (ctx : LinCtx) (idx : Nat) : Option Usage :=
  ctx[idx]?.map Prod.snd

/-- Get the entry at a given index (if it exists). -/
def getEntry? (ctx : LinCtx) (idx : Nat) : Option LinEntry :=
  ctx[idx]?

/-- Set the usage at a given index (consumption). -/
def setUsage (ctx : LinCtx) (idx : Nat) (u : Usage) : LinCtx :=
  match ctx with
  | [] => []
  | entry :: rest =>
    if idx = 0 then (entry.fst, u) :: rest
    else entry :: setUsage rest (idx - 1) u

/-- Mark a variable as consumed (used once). -/
def consume (ctx : LinCtx) (idx : Nat) : LinCtx :=
  ctx.setUsage idx Usage.one

/-- Add a new binding to the context (push). -/
def push (ctx : LinCtx) (τ : Typ) (u : Usage := .zero) : LinCtx :=
  (τ, u) :: ctx

/-- Drop the most recent binding (pop). -/
def pop (ctx : LinCtx) : LinCtx :=
  ctx.drop 1

/-! ## Context Classification -/

/-- Check if a type requires substructural discipline. -/
def isLinear (τ : Typ) : Bool :=
  match τ with
  | .refType .iso _ => true   -- iso: linear
  | .refType .val _ => true   -- val: affine
  | .refType .ref _ => true   -- ref: borrowed
  | _ => false                 -- everything else: unrestricted

/-- Classify the required usage mode for a type.
    - Linear types start as `zero` and must become `one`
    - Unrestricted types start as `many` (no tracking needed) -/
def initialUsage (τ : Typ) : Usage :=
  if isLinear τ then Usage.zero else Usage.many

/-! ## Context Well-Formedness -/

/-- A linear context is well-formed if:
    1. Linear/affine types have usage zero or one (never many)
    2. Unrestricted types have usage many
    3. No usage contradictions -/
def WellFormed : LinCtx → Prop
  | [] => True
  | (τ, u) :: rest =>
    -- Linear types must not be marked as 'many'
    (isLinear τ → u ≠ Usage.many) ∧
    -- Unrestricted types should be marked as 'many'
    (¬isLinear τ → u = Usage.many) ∧
    WellFormed rest

/-! ## Context Merge (for Branching) -/

/-- Merge two contexts from different branches of a conditional or match.
    Each entry is merged pointwise using Usage.merge.
    
    This ensures that a variable consumed in one branch is not double-counted
    if it wasn't consumed in the other branch. -/
def merge (ctx1 ctx2 : LinCtx) : Option LinCtx :=
  if ctx1.length ≠ ctx2.length then none
  else some (ctx1.zipWith (fun (τ1, u1) (_, u2) => (τ1, u1.merge u2)) ctx2)

/-! ## Projection to Plain Type List -/

/-- Project the types from a linear context (for compatibility with existing HasType). -/
def types (ctx : LinCtx) : List Typ :=
  ctx.map Prod.fst

/-- Project the usages from a linear context. -/
def usages (ctx : LinCtx) : List Usage :=
  ctx.map Prod.snd

/-! ## Lemmas -/

theorem types_length (ctx : LinCtx) : (types ctx).length = ctx.length := by
  simp [types]

theorem push_type (ctx : LinCtx) (τ : Typ) (u : Usage) :
    types (push ctx τ u) = τ :: types ctx := by
  simp [push, types]

theorem consume_types_unchanged (ctx : LinCtx) (idx : Nat) :
    types (consume ctx idx) = types ctx := by
  induction ctx generalizing idx with
  | nil => rfl
  | cons entry tail ih =>
    simp only [consume, setUsage]
    cases idx with
    | zero => rfl
    | succ n =>
      simp only [types, List.map_cons]
      show entry.fst :: List.map Prod.fst (setUsage tail n Usage.one) = entry.fst :: List.map Prod.fst tail
      congr 1
      exact ih n

end LinCtx

end Morph
