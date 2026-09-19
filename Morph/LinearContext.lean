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

/-! ## Weakening Support -/

/-- Push a list of types onto the context (weakening support).
    Each type gets its initial usage (zero for linear, many for unrestricted). -/
def pushMany (ctx : LinCtx) (τs : List Typ) : LinCtx :=
  (τs.map (fun τ => (τ, initialUsage τ))) ++ ctx

theorem types_pushMany (ctx : LinCtx) (τs : List Typ) :
    types (pushMany ctx τs) = τs ++ types ctx := by
  have hmap : Prod.fst ∘ (fun τ => (τ, initialUsage τ)) = id := by
    funext x; rfl
  simp only [pushMany, types, List.map_append, List.map_map, hmap, List.map_id]

/-- Reassociation for nested context extension:
    pushing `xs` then `ys` equals pushing `xs ++ ys` in one go. -/
theorem pushMany_pushMany_append (ctx : LinCtx) (xs ys : List Typ) :
    pushMany (pushMany ctx ys) xs = pushMany ctx (xs ++ ys) := by
  simp only [pushMany, List.map_append, List.append_assoc]

/-! ## Index Bridges for Multi-Type Insertion -/

/-- Inserting entries for `σs` between prefix `pfx` and base `ctx` does not change
    the type seen at index `n < pfx.length` (both land inside the prefix). -/
theorem types_pushMany_pushMany_index_low (ctx : LinCtx) (pfx σs : List Typ) (n : Nat)
    (h : n < pfx.length) :
    (types (pushMany (pushMany ctx σs) pfx))[n]?
      = (types (pushMany ctx pfx))[n]? := by
  simp only [types_pushMany]
  rw [List.getElem?_append_left h, List.getElem?_append_left h]

/-- Inserting entries for `σs` between prefix `pfx` and base `ctx`: index
    `pfx.length + k` (for `k < σs.length`) reads the inserted type `σs[k]`. -/
theorem types_pushMany_pushMany_index_mid (ctx : LinCtx) (pfx σs : List Typ) (k : Nat)
    (h : k < σs.length) :
    (types (pushMany (pushMany ctx σs) pfx))[pfx.length + k]?
      = some (σs[k]'h) := by
  simp only [types_pushMany]
  rw [List.getElem?_append_right (by omega),
      show pfx.length + k - pfx.length = k from by omega]
  simp only [List.getElem?_append_left h]
  exact List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩

/-- Inserting entries for `σs` between prefix `pfx` and base `ctx`: index `n`
    (for `n ≥ pfx.length + σs.length`) in the extended context reads index
    `n - σs.length` of the unextended one. -/
theorem types_pushMany_pushMany_index_high (ctx : LinCtx) (pfx σs : List Typ) (n : Nat)
    (h : n ≥ pfx.length + σs.length) :
    (types (pushMany (pushMany ctx σs) pfx))[n]?
      = (types (pushMany ctx pfx))[n - σs.length]? := by
  simp only [types_pushMany]
  rw [List.getElem?_append_right (by omega)]
  rw [List.getElem?_append_right (by omega)]
  rw [List.getElem?_append_right (by omega)]
  rw [show n - pfx.length - σs.length = n - σs.length - pfx.length from by omega]

theorem types_pushMany_index_high (ctx : LinCtx) (τs : List Typ) (n : Nat)
    (h : n < ctx.length) :
    (types (pushMany ctx τs))[n + τs.length]'(by simp [types, pushMany]; omega)
        = (types ctx)[n]'(by rw [types_length]; exact h) := by
  simp [types_pushMany]

theorem types_pushMany_index_low (ctx : LinCtx) (τs : List Typ) (k : Nat)
    (h : k < τs.length) :
    (types (pushMany ctx τs))[k]'(by simp [types, pushMany]; omega) = τs[k]'h := by
  simp [types_pushMany, h]

/-- Index bridge for weakening: inserting `(σ, initialUsage σ)` between the pushed
    prefix `xs` and the base context does not change the type seen at index `n < xs.length`
    (both land inside the pushed prefix). -/
theorem types_pushMany_push_index_low (ctx : LinCtx) (xs : List Typ) (σ : Typ) (n : Nat)
    (h : n < xs.length) :
    (types (pushMany ((σ, initialUsage σ) :: ctx) xs))[n]'(by
        rw [types_pushMany]
        have h1 : types ((σ, initialUsage σ) :: ctx) = σ :: types ctx := rfl
        rw [h1]
        simp only [List.length_append, List.length_cons]
        omega)
      = (types (pushMany ctx xs))[n]'(by
        simp only [types_pushMany, List.length_append]
        omega) := by
  simp only [types_pushMany]
  exact (List.getElem_append_left h).trans (List.getElem_append_left h).symm

/-- Cast a `getElem` application along an equality of lists. -/
private theorem getElem_of_eq {α : Type _} {as bs : List α} {k : Nat}
    (e : as = bs) (p : k < as.length) :
    as[k]'p = bs[k]'(e ▸ p) := by
  subst e; rfl

/-- Index bridge for weakening (Option form): inserting `(σ, initialUsage σ)` between
    the pushed prefix `xs` and the base context shifts the base-context index by one
    (`n + 1` in the new context reads index `n` of the old context).
    Stated with `xs[i]?` to keep rewriting proof-free; recover the `getElem` form with
    `List.getElem?_of_lt` and `Option.some.inj`. -/
theorem types_pushMany_push_index_high (ctx : LinCtx) (xs : List Typ) (σ : Typ) (n : Nat)
    (hGe : n ≥ xs.length)
    (hCons : (n - xs.length) + 1 < (types ((σ, initialUsage σ) :: ctx)).length) :
    (types (pushMany ((σ, initialUsage σ) :: ctx) xs))[n + 1]?
      = (types (pushMany ctx xs))[n]? := by
  have hTyC : types ((σ, initialUsage σ) :: ctx) = σ :: types ctx := rfl
  simp only [types_pushMany]
  rw [hTyC] at hCons ⊢
  obtain ⟨i, rfl⟩ : ∃ i, n = i + xs.length := ⟨n - xs.length, by omega⟩
  rw [List.getElem?_append_right (l₁ := xs) (l₂ := σ :: types ctx) (by omega),
      show i + xs.length + 1 - xs.length = i + 1 from by omega,
      List.getElem?_cons_succ,
      List.getElem?_append_right (l₁ := xs) (l₂ := types ctx) (by omega),
      show i + xs.length - xs.length = i from by omega]

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
