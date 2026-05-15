/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Specs.TypeSystem

namespace Morph.TypeChecker

open Morph.Core
open Morph.Syntax
open Morph.Specs.TypeSystem

/-!
# Type Checker — Certified Executable Extraction

Extracts the type-checking algorithm from the formal `HasType` specification
in `Morph.Specs.TypeSystem.Spec` into executable functions.

## Components
- `synthType`: Bottom-up type synthesis (no annotations needed)
- `checkType`: Verify an expression against an expected type
- `unify`: Structural type unification for inference
- `typeCheckBlock`: Type-check an entire AST block (entry point)

See ADR-004 for bidirectional typing design.
-/

/-! ## Type Synthesis -/

/-- Synthesize the type of an expression in the given environment.
    Returns `none` if the expression is ill-typed or type cannot be determined
    (e.g., lambdas without annotations).

    For lambdas, bidirectional typing is needed; use `checkType` with an
    expected function type to infer lambda parameter types. -/
def synthType (bvs : List Typ) (env : TypEnv) (e : Expr) : Option Typ :=
  inferType bvs env e

/-! ## Type Checking -/

/-- Check that an expression has the expected type in the given environment.
    For lambdas, this performs bidirectional checking: given an expected
    function type, the parameter types are used to extend the de Bruijn
    context and check the body. -/
def checkType (bvs : List Typ) (env : TypEnv) (e : Expr) (expected : Typ) : Bool :=
  match e with
  | .lam n body =>
    match expected with
    | .functionType paramTys retTy =>
      if _h : n = paramTys.length then
        checkType (paramTys.reverse ++ bvs) env body retTy
      else false
    | _ => false
  | _ =>
    match synthType bvs env e with
    | some t => t == expected
    | none => false

/-! ## Type Unification -/

/-- Structural unification of two types. Returns the most general unifier
    or `none` if unification fails.

    Unification rules:
    - Identical types unify trivially.
    - Array types unify if their element types and sizes match.
    - Function types unify if their parameter lists and return types match.
    - All other cases fail.

    This is a simple structural unifier — no type variables are introduced
    in the current type system. If type variables are added (e.g., for
    polymorphism), extend this with substitution. -/
partial def unify (t1 t2 : Typ) : Option Typ :=
  if t1 == t2 then some t1
  else
    match t1, t2 with
    | .arrayType e1 s1, .arrayType e2 s2 =>
      if s1 == s2 then
        match unify e1 e2 with
        | some _ => some t1
        | none => none
      else none
    | .functionType ps1 r1, .functionType ps2 r2 =>
      if ps1.length == ps2.length then
        let paramOk := (ps1.zip ps2).all (fun (p1, p2) => (unify p1 p2).isSome)
        let retOk := (unify r1 r2).isSome
        if paramOk && retOk then some t1 else none
      else none
    | _, _ => none

/-! ## Block Type Checking -/

/-- Type-check an entire expression block. Returns `true` if every expression
    in the block is well-typed (i.e., `synthType` succeeds for each).

    The overall type of the block is the type of the last expression
    (or `unitType` if empty). -/
def typeCheckBlock (bvs : List Typ) (env : TypEnv) (exprs : List Expr) : Bool :=
  exprs.all (fun e => (synthType bvs env e).isSome)

/-! ## Error Reporting -/

/-- Produce a human-readable type error message when type checking fails. -/
def formatTypeError (bvs : List Typ) (env : TypEnv) (e : Expr) (expected : Typ) : String :=
  match synthType bvs env e with
  | some actual =>
    s!"Type mismatch: expected {repr expected}, found {repr actual} in {repr e}"
  | none =>
    s!"Cannot infer type for expression: {repr e}"

/-! ## Utility: Infer Type of List of Expressions -/

def inferTypes (bvs : List Typ) (env : TypEnv) (exprs : List Expr) : Option (List Typ) :=
  exprs.foldlM (init := []) (fun acc e =>
    match synthType bvs env e with
    | some t => some (acc ++ [t])
    | none => none)

end Morph.TypeChecker
