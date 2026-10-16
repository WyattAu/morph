/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Specs.TypeSystem.Spec

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

/-! Check that an expression has the expected type in the given environment.
    For lambdas, this performs bidirectional checking: given an expected
    function type, the parameter types are used to extend the de Bruijn
    context and check the body.

    For a `linearFunctionType` expectation (ADR-014) the parameters are pushed
    as plain types and each parameter must occur exactly once in the body
    (`countUses`).

    Checking mode also covers the *ambiguous constructs* whose synthesis is
    impossible by design (research loop 11, after Dunfield-Krishnaswami
    "Bidirectional Typing", ACM Computing Surveys 2021):
    - `.none_` accepts any `.optionType` expectation (rule `none_type`),
    - `.ok_ e` checks the body against the success component (rule `ok_type`),
    - `.err_ e` checks the body against the error component (rule `err_type`),
    - `.match_` synthesizes the scrutinee type and checks every arm against
      the expected result type (rules `match_type`/`ArmsTyped`).

    `.refCast` deliberately has NO checking rule: the judgment has no
    `refCast` rule either (capability casts are store-typed only, ADR-010
    amendment), so accepting one would be unsound.

    Soundness contract (proven as `Morph.Specs.TypeSystem.checkType_sound`,
    research program P13): `checkType bvs env e expected = true` implies
    `HasType bvs env e expected`. -/

mutual
/-- Check that an expression has the expected type in the given environment
    (bidirectional; see the module docstring above for the checking-mode
    coverage and the soundness contract). -/
def checkType (bvs : List Typ) (env : TypEnv) (e : Expr) (expected : Typ) : Bool :=
  match e with
  | .lam n body =>
    match expected with
    | .functionType paramTys retTy =>
      if _h : n = paramTys.length then
        checkType (paramTys.reverse ++ bvs) env body retTy
      else false
    | .linearFunctionType paramTys retTy =>
      if _h : n = paramTys.length then
        checkType (paramTys.reverse ++ bvs) env body retTy &&
          (List.range paramTys.length).all (fun i => countUses body i == 1)
      else false
    | _ => false
  | .none_ =>
    match expected with
    | .optionType _ => true
    | _ => false
  | .ok_ body =>
    match expected with
    | .resultType okTy _ => checkType bvs env body okTy
    | _ => false
  | .err_ body =>
    match expected with
    | .resultType _ errTy => checkType bvs env body errTy
    | _ => false
  | .match_ scrut arms =>
    match inferType bvs env scrut with
    | some tyScrut => checkArms bvs env tyScrut arms expected
    | none => false
  | _ =>
    match inferType bvs env e with
    | some t => decide (t = expected)
    | none => false
termination_by sizeOf e

/-- Check every `match_` arm against the expected result type, with the arm's
    pattern variables bound to the scrutinee type — the executable mirror of
    `ArmsTyped`. An empty arm list yields `unitType` (rule `ArmsTyped.nil`). -/
def checkArms (bvs : List Typ) (env : TypEnv) (tyScrut : Typ)
    (arms : List (List String × Expr)) (expected : Typ) : Bool :=
  match arms with
  | [] => decide (expected = .unitType)
  | (vars, body) :: rest =>
    checkType (List.replicate vars.length tyScrut ++ bvs) env body expected &&
    checkArms bvs env tyScrut rest expected
termination_by sizeOf arms
end

/-! ## Equations as rewrite rules

`checkType` and `checkArms` are defined by well-founded recursion (they call
each other on structurally smaller arguments), so `simp [checkType]` cannot
unfold them on its own: the equation compiler's lemmas are not simp rules by
default. Marking them `[simp]` makes both the definitional unfolding *and* the
side conditions (the "this constructor does not match" hypotheses) usable by
`simp`/`rw`, which is what every soundness proof and test here needs. -/
attribute [simp] TypeChecker.checkType.eq_1 TypeChecker.checkType.eq_2
  TypeChecker.checkType.eq_3 TypeChecker.checkType.eq_4 TypeChecker.checkType.eq_5
  TypeChecker.checkType.eq_6 TypeChecker.checkType.eq_7 TypeChecker.checkType.eq_8
  TypeChecker.checkType.eq_9 TypeChecker.checkType.eq_10 TypeChecker.checkType.eq_11
  TypeChecker.checkArms.eq_1 TypeChecker.checkArms.eq_2

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
