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

/-! ## Struct Field Type Lookup

Look up the type of a named field in a struct's field list.
Returns `none` if the field name is not found.
-/
def structFieldType (fields : List (String × Morph.Core.Typ)) (name : String) : Option Morph.Core.Typ :=
  (fields.find? (fun (n, _) => n == name)).map Prod.snd

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
  | floatType_wf : forall env w, WellTyped env (.floatType w)
  | intWidthType_wf : forall env w, WellTyped env (.intWidthType w)
  | neverType_wf : forall env, WellTyped env .neverType
  | arrayType_wf : forall env elemTy sz,
      WellTyped env elemTy ->
      WellTyped env (.arrayType elemTy sz)
  | functionType_wf : forall env paramTys retTy,
      (forall paramTy, paramTy ∈ paramTys -> WellTyped env paramTy) ->
      WellTyped env retTy ->
      WellTyped env (.functionType paramTys retTy)
  | refType_wf : forall env cap innerTy,
      WellTyped env innerTy -> WellTyped env (.refType cap innerTy)
  | effectFunctionType_wf : forall env paramTys retTy effects,
      (forall paramTy, paramTy ∈ paramTys -> WellTyped env paramTy) ->
      WellTyped env retTy ->
      WellTyped env (.effectFunctionType paramTys retTy effects)
  | typeVar_wf : forall env n, WellTyped env (.typeVar n)
  | optionType_wf : forall env innerTy,
      WellTyped env innerTy → WellTyped env (.optionType innerTy)
  | resultType_wf : forall env okTy errTy,
      WellTyped env okTy → WellTyped env errTy → WellTyped env (.resultType okTy errTy)
  | tupleType_wf : forall env elemTys,
      (forall elemTy, elemTy ∈ elemTys → WellTyped env elemTy) →
      WellTyped env (.tupleType elemTys)
  | structType_wf : forall env name fields,
      (forall p, p ∈ fields → WellTyped env p.snd) →
      WellTyped env (.structType name fields)

/-!
## Type Inference (Executable)

`inferType bvs env e` infers the type of expression `e` in:
- `bvs : List Typ` — types of bound de Bruijn indices (bvs[0] = type of bvar 0)
- `env : TypEnv` — types of free variables by name
-/
mutual
def inferTypes (bvs : List Morph.Core.Typ) (env : TypEnv) : List Morph.Syntax.Expr -> Option (List Morph.Core.Typ)
  | [] => some []
  | e :: es =>
    match inferType bvs env e, inferTypes bvs env es with
    | some τ, some tys => some (τ :: tys)
    | _, _ => none
  termination_by es => sizeOf es

def inferType (bvs : List Morph.Core.Typ) (env : TypEnv) : Morph.Syntax.Expr -> Option Morph.Core.Typ
  | .bvar n => if h : n < bvs.length then some bvs[n] else none
  | .fvar name => lookupTyp env name
  | .lit (.int _) => some .intType
  | .lit (.bool _) => some .boolType
  | .lit (.string _) => some .stringType
  | .lit .unit => some .unitType
  | .lit (.pointer _) => some .pointerType
  | .lit (.float _) => some (.floatType .f64)
  | .lit .undef => none
  | .lit (.some v) =>
    match inferType bvs env (.lit v) with
    | some τ => some (.optionType τ)
    | none => none
  | .lit .none => none
  | .lit (.ok v) =>
    match inferType bvs env (.lit v) with
    | some τ => none
    | none => none
  | .lit (.err v) =>
    match inferType bvs env (.lit v) with
    | some τ => none
    | none => none
  | .lit (.tuple_ vs) =>
    let tys := vs.map (fun v => inferType bvs env (.lit v))
    if tys.all Option.isSome then
      some (.tupleType (tys.map Option.get!))
    else none
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
    | some .pointerType, some .intType =>
      match op with
      | .ptrAdd | .ptrSub => some .pointerType
      | _ => none
    | some .pointerType, some .unitType =>
      match op with
      | .ptrLoad => some .unitType
      | _ => none
    | some .pointerType, some _ =>
      match op with
      | .ptrStore => some .unitType
      | _ => none
    | some .stringType, some .stringType =>
      if op == .add then some .stringType else none
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
  | .match_ _ _ => none  -- match_ type inference is complex; typing via HasType.match_type
  | .field_ e name =>
    match inferType bvs env e with
    | some (.structType _ fields) =>
      match structFieldType fields name with
      | some τ => some τ
      | none => none
    | _ => none
  | .pipe e f =>
    match inferType bvs env e, inferType bvs env f with
    | some τ_e, some (.functionType [τ_arg] τ_ret) =>
      if τ_e == τ_arg then some τ_ret else none
    | _, _ => none
  | .some_ e =>
    match inferType bvs env e with
    | some τ => some (.optionType τ)
    | none => none
  | .none_ => none
  | .ok_ e =>
    match inferType bvs env e with
    | some τ => none
    | none => none
  | .err_ e =>
    match inferType bvs env e with
    | some τ => none
    | none => none
  | .nullCoalesce e1 e2 =>
    match inferType bvs env e1 with
    | some (.optionType τ) => some (.optionType τ)
    | _ => none
  | .typeAsc e τ => inferType bvs env e
  | .tuple_ elems =>
    match inferTypes bvs env elems with
    | some tys => some (.tupleType tys)
    | none => none
  termination_by e => sizeOf e
end

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

def isPtrArithOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .ptrAdd | .ptrSub => True
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
  | lit_float : ∀ bvs Γ w f, HasType bvs Γ (.lit (.float f)) (.floatType w)
  | lit_int_width : ∀ bvs Γ w n, HasType bvs Γ (.lit (.int n)) (.intWidthType w)
  | lit_some : ∀ bvs Γ v τ, HasType bvs Γ (.lit (.some v)) (.optionType τ)
  | lit_none : ∀ bvs Γ τ, HasType bvs Γ (.lit .none) (.optionType τ)
  | lit_ok : ∀ bvs Γ v τ_ok τ_err, HasType bvs Γ (.lit (.ok v)) (.resultType τ_ok τ_err)
  | lit_err : ∀ bvs Γ v τ_err τ_ok, HasType bvs Γ (.lit (.err v)) (.resultType τ_ok τ_err)
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
  | binop_ptr_arith : ∀ bvs Γ op e1 e2,
      isPtrArithOp op →
      HasType bvs Γ e1 .pointerType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop op e1 e2) .pointerType
  | binop_ptr_load : ∀ bvs Γ e1 e2,
      HasType bvs Γ e1 .pointerType → HasType bvs Γ e2 .unitType →
      HasType bvs Γ (.binop .ptrLoad e1 e2) .unitType
  | binop_ptr_store : ∀ bvs Γ e1 e2,
      HasType bvs Γ e1 .pointerType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop .ptrStore e1 e2) .unitType
  | binop_string_concat : ∀ bvs Γ op e1 e2,
      op = .add →
      HasType bvs Γ e1 .stringType → HasType bvs Γ e2 .stringType →
      HasType bvs Γ (.binop op e1 e2) .stringType
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
  | pipe_type : ∀ bvs Γ e f τ_arg τ_ret,
      HasType bvs Γ e τ_arg →
      HasType bvs Γ f (.functionType [τ_arg] τ_ret) →
      HasType bvs Γ (.pipe e f) τ_ret
  | typeAsc_type : ∀ bvs Γ e τ,
      HasType bvs Γ e τ →
      HasType bvs Γ (.typeAsc e τ) τ
  | some_type : ∀ bvs Γ e τ_inner,
      HasType bvs Γ e τ_inner →
      HasType bvs Γ (.some_ e) (.optionType τ_inner)
  | none_type : ∀ bvs Γ τ,
      HasType bvs Γ .none_ (.optionType τ)
  | ok_type : ∀ bvs Γ e τ_ok τ_err,
      HasType bvs Γ e τ_ok →
      HasType bvs Γ (.ok_ e) (.resultType τ_ok τ_err)
  | err_type : ∀ bvs Γ e τ_err τ_ok,
      HasType bvs Γ e τ_err →
      HasType bvs Γ (.err_ e) (.resultType τ_ok τ_err)
  | null_coalesce_type : ∀ bvs Γ e1 e2 τ,
      HasType bvs Γ e1 (.optionType τ) →
      HasType bvs Γ e2 (.optionType τ) →
      HasType bvs Γ (.nullCoalesce e1 e2) (.optionType τ)
  | tuple_type : ∀ bvs Γ elems tys,
      HasTypeAll bvs Γ elems tys →
      HasType bvs Γ (.tuple_ elems) (.tupleType tys)
  | field_access_type : ∀ bvs Γ e fname sname fields τ,
      HasType bvs Γ e (.structType sname fields) →
      structFieldType fields fname = some τ →
      HasType bvs Γ (.field_ e fname) τ
  | match_type : ∀ bvs Γ scrut arms τ_scrut τ_result,
      HasType bvs Γ scrut τ_scrut →
      ArmsTyped bvs Γ τ_scrut arms τ_result →
      HasType bvs Γ (.match_ scrut arms) τ_result

inductive HasTypeAll : List Morph.Core.Typ → TypEnv → List Morph.Syntax.Expr → List Morph.Core.Typ → Prop where
  | nil : ∀ bvs Γ,
      HasTypeAll bvs Γ [] []
  | cons : ∀ bvs Γ e es τ τs,
      HasType bvs Γ e τ → HasTypeAll bvs Γ es τs →
      HasTypeAll bvs Γ (e :: es) (τ :: τs)

inductive ArmsTyped : List Morph.Core.Typ → TypEnv → Morph.Core.Typ → List (List String × Morph.Syntax.Expr) → Morph.Core.Typ → Prop where
  | nil : ∀ bvs Γ τ_scrut,
      ArmsTyped bvs Γ τ_scrut [] .unitType
  | cons : ∀ bvs Γ vars body rest τ_scrut τ_result,
      HasType (List.replicate vars.length τ_scrut ++ bvs) Γ body τ_result →
      ArmsTyped bvs Γ τ_scrut rest τ_result →
      ArmsTyped bvs Γ τ_scrut ((vars, body) :: rest) τ_result

end

end Morph.Specs.TypeSystem
