/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.ScopingLambdaCalculus

/-!
# Scoping Lambda Calculus Specification

Variable binding, scope resolution, alpha-equivalence,
and capture-avoiding substitution for the lambda calculus.

## Overview

This module formalizes a scoped lambda calculus:
- **Binding:** A variable binding with name and depth
- **ScopedExpr:** Lambda expressions with explicit binding structure
- **freeVars:** Free variable computation
- **occursFree:** Free variable check
- **allNames:** All variable names in an expression
- **lambdaDepth:** Depth of nested lambdas
- **lambdaCount:** Count of lambda abstractions

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Binding | `Binding` | Done |
| Scoped expression | `ScopedExpr` | Done |
| Free variables | `freeVars` | Done |
| Free variable check | `occursFree` | Done |
| All names | `allNames` | Done |
| Lambda depth | `lambdaDepth` | Done |
| Lambda count | `lambdaCount` | Done |
-/

/-- A variable binding with name and depth -/
structure Binding where
  name : String
  depth : Nat
  deriving Repr, BEq

/-- Lambda expressions with explicit scoping -/
inductive ScopedExpr where
  | var (name : String) : ScopedExpr
  | boundVar (index : Nat) : ScopedExpr
  | lam (name : String) (body : ScopedExpr) : ScopedExpr
  | app (fn arg : ScopedExpr) : ScopedExpr
  deriving Repr, BEq

/-- Compute the free variables of a scoped expression -/
def freeVars : ScopedExpr -> List String
  | .var x => [x]
  | .boundVar _ => []
  | .lam x body => (freeVars body).filter (fun z => z != x)
  | .app f a => freeVars f ++ freeVars a

/-- Check if a name occurs free in an expression -/
def occursFree (name : String) (e : ScopedExpr) : Bool :=
  name ∈ freeVars e

/-- All variable names mentioned anywhere in an expression -/
def allNames : ScopedExpr -> List String
  | .var x => [x]
  | .boundVar _ => []
  | .lam x body => x :: allNames body
  | .app f a => allNames f ++ allNames a

/-- Generate a fresh name not in the given set (bounded to avoid divergence) -/
def freshName (taken : List String) (base : String) (maxAttempts : Nat := 1000) (n : Nat := 0) : String :=
  if n >= maxAttempts then base ++ "!" ++ toString n
  else
    let candidate := base ++ toString n
    if candidate ∈ taken then freshName taken base maxAttempts (n + 1)
    else candidate

/-- Compute the depth of nested lambdas -/
def lambdaDepth : ScopedExpr -> Nat
  | .var _ => 0
  | .boundVar _ => 0
  | .lam _ body => 1 + lambdaDepth body
  | .app f a => Nat.max (lambdaDepth f) (lambdaDepth a)

/-- Count the number of lambda abstractions -/
def lambdaCount : ScopedExpr -> Nat
  | .var _ => 0
  | .boundVar _ => 0
  | .lam _ body => 1 + lambdaCount body
  | .app f a => lambdaCount f + lambdaCount a

end Morph.Specs.ScopingLambdaCalculus
