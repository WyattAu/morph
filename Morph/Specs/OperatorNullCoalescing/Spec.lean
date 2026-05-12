/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Null Coalescing Operator Specification

Defines the null coalescing operator (`??`) for the Morph language,
including its expression form and evaluation semantics.

## Overview

The null coalescing operator `a ?? b` evaluates to `a` when `a` is not null,
and to `b` otherwise. This is a right-associative binary operator with the
lowest precedence among logical operators.

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Expression form | `NullCoalesce` | Done |
| Evaluation semantics | `NullCoalesceSemantics` | Done |

## Known Issues

None.
-/

namespace Morph.Specs.OperatorNullCoalescing

/-- A nullable value for use in null coalescing -/
inductive Nullable where
  | null : Nullable
  | value : String → Nullable
  deriving Repr, BEq

/-- Check if a nullable is null -/
def Nullable.isNull : Nullable → Bool
  | .null => true
  | .value _ => false

/-- Get the value if present -/
def Nullable.getOrNull : Nullable → Option String
  | .null => none
  | .value s => some s

/-- Null coalescing expression: `left ?? right` -/
structure NullCoalesce where
  left : Nullable
  right : Nullable
  deriving Repr, BEq

/-- Evaluate a null coalescing expression: returns left if non-null, else right -/
def NullCoalesce.evaluate (nc : NullCoalesce) : Nullable :=
  if nc.left.isNull then nc.right else nc.left

/-- Flattened form: resolve a chain of null coalescing from left to right -/
def resolveChain (values : List Nullable) : Nullable :=
  match values with
  | [] => .null
  | [x] => x
  | x :: rest =>
      if x.isNull then resolveChain rest else x

/-- Semantics for null coalescing evaluation -/
structure NullCoalesceSemantics where
  shortCircuit : Bool
  chainLength : Nat
  deriving Repr, BEq

/-- Default semantics: short-circuit evaluation -/
def NullCoalesceSemantics.default : NullCoalesceSemantics :=
  { shortCircuit := true, chainLength := 1 }

/-- Check if evaluation uses short-circuit semantics -/
def NullCoalesceSemantics.isShortCircuit (s : NullCoalesceSemantics) : Bool :=
  s.shortCircuit

/-- Evaluate a null coalescing expression under given semantics -/
def evaluateWith (nc : NullCoalesce) (sem : NullCoalesceSemantics) : Nullable :=
  if sem.isShortCircuit then
    nc.evaluate
  else
    nc.right

end Morph.Specs.OperatorNullCoalescing
