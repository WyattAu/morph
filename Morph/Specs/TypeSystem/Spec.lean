/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax

namespace Morph.Specs.TypeSystem

/-!
# Type System Specification (de Bruijn)

This module formalizes the type system for the Morph language specification
using de Bruijn indices for bound variables.

## Key Design Decisions

- `HasType bvs Γ e τ`: The first parameter `bvs : List Typ` tracks the types
  of currently-bound de Bruijn indices. `bvs[0]` is the type of bvar 0, etc.
- `TypEnv` maps free variable names to types (unchanged from named-variable system).
- `inferType bvs env e`: Executable type inference with bound-variable context.
- Weakening is trivial: just prepend a type to `bvs`.
- Substitution lemma is straightforward induction (no capture-avoidance needed).

## Overview

The TypeSystem module formalizes:
- **Type Environments:** Mapping variable names to types (for free variables)
- **Bound-variable context:** Stack of types for de Bruijn indices
- **Type Inference:** Computing types from expressions
- **Type Checking:** Verifying expressions against expected types
- **Type Well-Formedness:** Ensuring types are valid
- **Subtyping:** Type compatibility relationships
- **Type Safety:** Preservation of types under evaluation

-/

abbrev TypEnv := List (String × Morph.Core.Typ)

def lookupTyp (env : TypEnv) (name : String) : Option Morph.Core.Typ :=
  env.find? (fun (n, _) => n == name) |>.map Prod.snd

def extendTypEnv (env : TypEnv) (name : String) (typ : Morph.Core.Typ) : TypEnv :=
  (name, typ) :: env

/-!
## Type Well-Formedness
-/
inductive WellTyped : TypEnv -> Morph.Core.Typ -> Prop where
  | intType_wf : forall env, WellTyped env .intType
  | boolType_wf : forall env, WellTyped env .boolType
  | stringType_wf : forall env, WellTyped env .stringType
  | pointerType_wf : forall env, WellTyped env .pointerType
  | unitType_wf : forall env, WellTyped env .unitType
  | arrayType_wf : forall env elemTy sz,
      WellTyped env elemTy ->
      WellTyped env (.arrayType elemTy sz)
  | functionType_wf : forall env paramTys retTy,
      (forall paramTy, paramTy ∈ paramTys -> WellTyped env paramTy) ->
      WellTyped env retTy ->
      WellTyped env (.functionType paramTys retTy)

/-!
## Type Inference (Executable)

`inferType bvs env e` infers the type of expression `e` in:
- `bvs : List Typ` — types of bound de Bruijn indices (bvs[0] = type of bvar 0)
- `env : TypEnv` — types of free variables by name
-/
def inferType (bvs : List Morph.Core.Typ) (env : TypEnv) : Morph.Syntax.Expr -> Option Morph.Core.Typ
  | .bvar n => if h : n < bvs.length then some bvs[n] else none
  | .fvar name => lookupTyp env name
  | .lit (.int _) => some .intType
  | .lit (.bool _) => some .boolType
  | .lit (.string _) => some .stringType
  | .lit .unit => some .unitType
  | .lit (.pointer _) => some .pointerType
  | .lit .undef => none
  | .unop op e =>
    match op with
    | .not =>
      match inferType bvs env e with
      | some .boolType => some .boolType
      | _ => none
    | .notb =>
      match inferType bvs env e with
      | some .intType => some .intType
      | _ => none
    | _ => none
  | .binop op e1 e2 =>
    let typ1? := inferType bvs env e1
    let typ2? := inferType bvs env e2
    match typ1?, typ2? with
    | some .intType, some .intType =>
      match op with
      | .add | .sub | .mul | .div | .mod => some .intType
      | .eq | .neq | .lt | .leq | .gt | .geq => some .boolType
      | .andb | .orb | .xorb | .shl | .shr => some .intType
      | _ => none
    | some .boolType, some .boolType =>
      match op with
      | .and | .or => some .boolType
      | _ => none
    | _, _ => none
  | .app fn args =>
    match inferType bvs env fn with
    | some (.functionType paramTys retTy) =>
      if args.length == paramTys.length then
        let argTys := args.map (inferType bvs env)
        if argTys.all Option.isSome then
          let ok := (argTys.zip paramTys).all (fun (aTy?, pTy) =>
            match aTy? with
            | some aTy => aTy == pTy
            | none => false)
          if ok then some retTy else none
        else none
      else none
    | _ => none
  | .lam n _ => none  -- Lambdas need annotations for synthesis
  | .let_ e1 e2 =>
    match inferType bvs env e1 with
    | some τ1 => inferType (τ1 :: bvs) env e2
    | none => none
  | .ifThenElse c t f =>
    match inferType bvs env c with
    | some .boolType =>
      let typT := inferType bvs env t
      let typF := inferType bvs env f
      if typT == typF then typT else none
    | _ => none
  | .forLoop _ _ _ => some .unitType
  | .block [] => some .unitType
  | .block [e] => inferType bvs env e
  | .block (_ :: es) => inferType bvs env (.block es)
termination_by e => sizeOf e

def typeCheck (bvs : List Morph.Core.Typ) (env : TypEnv) (e : Morph.Syntax.Expr) (expected : Morph.Core.Typ) : Prop :=
  inferType bvs env e = some expected

/-!
## Subtyping
-/
inductive Subtype : Morph.Core.Typ -> Morph.Core.Typ -> Prop where
  | refl : forall typ, Subtype typ typ
  | trans : forall typ1 typ2 typ3,
      Subtype typ1 typ2 ->
      Subtype typ2 typ3 ->
      Subtype typ1 typ3

/-! ## Operator Classifications -/

def isArithOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .add | .sub | .mul | .div | .mod => True
  | _ => False

def isCompOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .eq | .neq | .lt | .leq | .gt | .geq => True
  | _ => False

def isLogicOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .and | .or => True
  | _ => False

def isBitwiseOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .andb | .orb | .xorb | .shl | .shr => True
  | _ => False

/-! ## Typing Judgments

`HasType bvs Γ e τ`:
- `bvs : List Typ` — types of bound de Bruijn indices
  (bvs[0] = type of bvar 0, the most recent binder)
- `Γ : TypEnv` — types of free variables by name
- `e : Expr` — the expression
- `τ : Typ` — the inferred type
-/

mutual

inductive HasType : List Morph.Core.Typ → TypEnv → Morph.Syntax.Expr → Morph.Core.Typ → Prop where
  | bvar_type : ∀ bvs Γ n,
      (h : n < bvs.length) →
      HasType bvs Γ (.bvar n) bvs[n]
  | fvar_type : ∀ bvs Γ name τ,
      lookupTyp Γ name = some τ →
      HasType bvs Γ (.fvar name) τ
  | lit_int : ∀ bvs Γ n, HasType bvs Γ (.lit (.int n)) .intType
  | lit_bool : ∀ bvs Γ b, HasType bvs Γ (.lit (.bool b)) .boolType
  | lit_string : ∀ bvs Γ s, HasType bvs Γ (.lit (.string s)) .stringType
  | lit_unit : ∀ bvs Γ, HasType bvs Γ (.lit .unit) .unitType
  | lit_pointer : ∀ bvs Γ p, HasType bvs Γ (.lit (.pointer p)) .pointerType
  | unop_not : ∀ bvs Γ e,
      HasType bvs Γ e .boolType →
      HasType bvs Γ (.unop .not e) .boolType
  | unop_notb : ∀ bvs Γ e,
      HasType bvs Γ e .intType →
      HasType bvs Γ (.unop .notb e) .intType
  | binop_arith : ∀ bvs Γ op e1 e2,
      isArithOp op →
      HasType bvs Γ e1 .intType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop op e1 e2) .intType
  | binop_comp : ∀ bvs Γ op e1 e2,
      isCompOp op →
      HasType bvs Γ e1 .intType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop op e1 e2) .boolType
  | binop_logic : ∀ bvs Γ op e1 e2,
      isLogicOp op →
      HasType bvs Γ e1 .boolType → HasType bvs Γ e2 .boolType →
      HasType bvs Γ (.binop op e1 e2) .boolType
  | binop_bitwise : ∀ bvs Γ op e1 e2,
      isBitwiseOp op →
      HasType bvs Γ e1 .intType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop op e1 e2) .intType
  | lam_type : ∀ bvs Γ n body paramTys retTy,
      n = paramTys.length →
      HasType (paramTys.reverse ++ bvs) Γ body retTy →
      HasType bvs Γ (.lam n body) (.functionType paramTys retTy)
  | app_type : ∀ bvs Γ fn args τs τ,
      HasType bvs Γ fn (.functionType τs τ) →
      HasTypeAll bvs Γ args τs →
      HasType bvs Γ (.app fn args) τ
  | let_type : ∀ bvs Γ e1 e2 τ1 τ2,
      HasType bvs Γ e1 τ1 →
      HasType (τ1 :: bvs) Γ e2 τ2 →
      HasType bvs Γ (.let_ e1 e2) τ2
  | if_type : ∀ bvs Γ c t f τ,
      HasType bvs Γ c .boolType →
      HasType bvs Γ t τ → HasType bvs Γ f τ →
      HasType bvs Γ (.ifThenElse c t f) τ
  | for_type : ∀ bvs Γ s e body,
      HasType bvs Γ s .intType → HasType bvs Γ e .intType →
      HasTypeAll (.intType :: bvs) Γ body [.unitType] →
      HasType bvs Γ (.forLoop s e body) .unitType
  | block_type : ∀ bvs Γ exprs τs τ,
      HasTypeAll bvs Γ exprs (τs ++ [τ]) →
      HasType bvs Γ (.block exprs) τ

inductive HasTypeAll : List Morph.Core.Typ → TypEnv → List Morph.Syntax.Expr → List Morph.Core.Typ → Prop where
  | nil : ∀ bvs Γ,
      HasTypeAll bvs Γ [] []
  | cons : ∀ bvs Γ e es τ τs,
      HasType bvs Γ e τ → HasTypeAll bvs Γ es τs →
      HasTypeAll bvs Γ (e :: es) (τ :: τs)

end

end Morph.Specs.TypeSystem
