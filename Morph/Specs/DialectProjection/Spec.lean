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
  deriving Repr, BEq

/-- A dialect expression: a term annotated with its source dialect. -/
inductive DialectExpr where
  | val : DialectValue → DialectExpr
  | op : String → List DialectExpr → DialectExpr
  | call : String → List DialectExpr → DialectExpr
  | block : List DialectExpr → DialectExpr
deriving Repr

/-- Lowering function: project an expression from source to target dialect.
    Currently a structural pass-through; full lowering is dialect-specific. -/
def lower (p : Projection) (e : DialectExpr) : DialectExpr :=
  match e with
  | .val v => .val { v with dialect := p.target }
  | .op name args => .op name (args.map (lower p))
  | .call name args => .call name (args.map (lower p))
  | .block exprs => .block (exprs.map (lower p))

/-- Projections are structurally equal if source and target match (ignore name metadata). -/
def Projection.equiv (p1 p2 : Projection) : Prop :=
  p1.source = p2.source ∧ p1.target = p2.target

/-- Projection composition: compose two projections.
    `p1` from A→B and `p2` from B→C yields a projection from A→C. -/
def compose (p1 p2 : Projection) : Projection :=
  { source := p1.source
  , target := p2.target
  , name := p2.name }

/-- The identity projection for each dialect (lowering to itself). -/
def identityProjection (d : Dialect) : Projection :=
  { source := d, target := d, name := "id" }

theorem compose_id_left_equiv (p : Projection) :
    Projection.equiv (compose (identityProjection p.source) p) p := by
  unfold compose identityProjection Projection.equiv
  simp

theorem compose_id_right_equiv (p : Projection) :
    Projection.equiv (compose p (identityProjection p.target)) p := by
  unfold compose identityProjection Projection.equiv
  simp

/-- Check whether all DialectValues in an expression belong to the given dialect. -/
def allInDialect : DialectExpr → Dialect → Prop
  | .val v, d => v.dialect = d
  | .op _ args, d => ∀ a ∈ args, allInDialect a d
  | .call _ args, d => ∀ a ∈ args, allInDialect a d
  | .block exprs, d => ∀ e ∈ exprs, allInDialect e d

theorem allInDialect_val (v : DialectValue) (d : Dialect) (h : v.dialect = d) :
    allInDialect (.val v) d := by
  simpa [allInDialect] using h

/-- Lowering through identity projection preserves the expression structure
    when the expression already belongs to the target dialect.
    The proof requires nested induction on `DialectExpr` (list subterms).
    This is a specification-level property; the structural argument is:
    `lower` replaces the dialect tag in values and recurses structurally,
    so lowering through identity is the identity on well-dialected expressions. -/
theorem lower_identity (d : Dialect) (e : DialectExpr) (hAll : allInDialect e d) :
    lower (identityProjection d) e = e := by
  exact DialectExpr.rec
    (motive_1 := fun e => allInDialect e d → lower (identityProjection d) e = e)
    (motive_2 := fun l => (∀ e ∈ l, allInDialect e d) → l.map (lower (identityProjection d)) = l)
    (val := fun v h => by
      simp only [lower, identityProjection]
      simp only [allInDialect] at h
      subst h; rfl)
    (op := fun name args ih h => by
      simp only [lower, identityProjection]
      simp only [allInDialect] at h
      congr 1; exact ih h)
    (call := fun name args ih h => by
      simp only [lower, identityProjection]
      simp only [allInDialect] at h
      congr 1; exact ih h)
    (block := fun exprs ih h => by
      simp only [lower, identityProjection]
      simp only [allInDialect] at h
      congr 1; exact ih h)
    (nil := fun _ => rfl)
    (cons := fun head tail ih_head ih_tail h => by
      simp only [List.map]
      congr 1
      · exact ih_head (h head (by simp))
      · exact ih_tail (fun e he => h e (by simp [List.mem_cons, he])))
    e hAll

end Morph.Specs.DialectProjection
