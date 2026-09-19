/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.LinearContext

namespace Morph.Specs.TypeSystem

/-!
# Type System Specification (de Bruijn)

This module formalizes the type system for the Morph language specification
using de Bruijn indices for bound variables.

## Key Design Decisions

- `HasType ctx Γ e τ`: The first parameter `ctx : LinCtx` tracks the types
  and usages of currently-bound de Bruijn indices. `ctx.types[0]` is the
  type of bvar 0, etc.
- `TypEnv` maps free variable names to types (unchanged from named-variable system).
- `inferType ctx env e`: Executable type inference with bound-variable context.
- Weakening is trivial: just prepend entries via `LinCtx.pushMany`.
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

`inferType ctx env e` infers the type of expression `e` in:
- `ctx : LinCtx` — linear context of bound de Bruijn indices
  (ctx.types[0] = type of bvar 0)
- `env : TypEnv` — types of free variables by name
-/
mutual
def inferTypes (ctx : LinCtx) (env : TypEnv) : List Morph.Syntax.Expr -> Option (List Morph.Core.Typ)
  | [] => some []
  | e :: es =>
    match inferType ctx env e, inferTypes ctx env es with
    | some τ, some tys => some (τ :: tys)
    | _, _ => none
  termination_by es => sizeOf es

def inferType (ctx : LinCtx) (env : TypEnv) : Morph.Syntax.Expr -> Option Morph.Core.Typ
  | .bvar n => if h : n < ctx.types.length then some ctx.types[n] else none
  | .fvar name => lookupTyp env name
  | .lit (.int _) => some .intType
  | .lit (.bool _) => some .boolType
  | .lit (.string _) => some .stringType
  | .lit .unit => some .unitType
  | .lit (.pointer _) => some .pointerType
  | .lit (.float _) => some (.floatType .f64)
  | .lit .undef => none
  | .lit (.some v) =>
    match inferType ctx env (.lit v) with
    | some τ => some (.optionType τ)
    | none => none
  | .lit .none => none
  | .lit (.ok v) =>
    match inferType ctx env (.lit v) with
    | some τ => none
    | none => none
  | .lit (.err v) =>
    match inferType ctx env (.lit v) with
    | some τ => none
    | none => none
  | .lit (.tuple_ vs) =>
    let tys := vs.map (fun v => inferType ctx env (.lit v))
    if tys.all Option.isSome then
      some (.tupleType (tys.map Option.get!))
    else none
  | .lit (.array_ vs) =>
    let tys := vs.map (fun v => inferType ctx env (.lit v))
    match tys.head? with
    | some (some τ) =>
      if tys.all (fun t => t == some τ) && (vs.length > 0) then
        some (.arrayType τ vs.length)
      else none
    | _ => none
  | .lit (.loc _) => some .pointerType  -- locations are opaque pointers
  | .unop op e =>
    match op with
    | .not =>
      match inferType ctx env e with
      | some .boolType => some .boolType
      | _ => none
    | .notb =>
      match inferType ctx env e with
      | some .intType => some .intType
      | _ => none
    | _ => none
  | .binop op e1 e2 =>
    let typ1? := inferType ctx env e1
    let typ2? := inferType ctx env e2
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
    match inferType ctx env fn with
    | some (.functionType paramTys retTy) =>
      if args.length == paramTys.length then
        let argTys := args.map (inferType ctx env)
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
    match inferType ctx env e1 with
    | some τ1 => inferType ((τ1, LinCtx.initialUsage τ1) :: ctx) env e2
    | none => none
  | .ifThenElse c t f =>
    match inferType ctx env c with
    | some .boolType =>
      let typT := inferType ctx env t
      let typF := inferType ctx env f
      if typT == typF then typT else none
    | _ => none
  | .forLoop _ _ _ => some .unitType
  | .block [] => some .unitType
  | .block [e] => inferType ctx env e
  | .block (_ :: es) => inferType ctx env (.block es)
  | .match_ _ _ => none  -- match_ type inference is complex; typing via HasType.match_type
  | .field_ e name =>
    match inferType ctx env e with
    | some (.structType _ fields) =>
      match structFieldType fields name with
      | some τ => some τ
      | none => none
    | _ => none
  | .pipe e f =>
    match inferType ctx env e, inferType ctx env f with
    | some τ_e, some (.functionType [τ_arg] τ_ret) =>
      if τ_e == τ_arg then some τ_ret else none
    | _, _ => none
  | .some_ e =>
    match inferType ctx env e with
    | some τ => some (.optionType τ)
    | none => none
  | .none_ => none
  | .ok_ e =>
    match inferType ctx env e with
    | some τ => none
    | none => none
  | .err_ e =>
    match inferType ctx env e with
    | some τ => none
    | none => none
  | .nullCoalesce e1 e2 =>
    match inferType ctx env e1 with
    | some (.optionType τ) => some (.optionType τ)
    | _ => none
  | .typeAsc e τ => inferType ctx env e
  | .tuple_ elems =>
    match inferTypes ctx env elems with
    | some tys => some (.tupleType tys)
    | none => none
  | .arrayLit elems =>
    match inferTypes ctx env elems with
    | some tys =>
      match tys.head? with
      | some τ =>
        if tys.all (fun t => t == τ) && elems.length > 0 then
          some (.arrayType τ elems.length)
        else none
      | none => none
    | none => none
  | .arrayIndex arr idx =>
    match inferType ctx env arr, inferType ctx env idx with
    | some (.arrayType τ _), some .intType => some τ
    | _, _ => none
  | .refCreate e cap τ =>
    match inferType ctx env e with
    | some τ' => some (.refType cap τ)  -- annotate with capability
    | none => none
  | .refLoad e =>
    match inferType ctx env e with
    | some (.refType _ τ) => some τ
    | _ => none
  | .refStore e _ τ =>
    match inferType ctx env e with
    | some (.refType _ _) => some .unitType
    | _ => none
  | .refFree e =>
    match inferType ctx env e with
    | some (.refType .iso _) => some .unitType  -- only iso can free
    | _ => none
  termination_by e => sizeOf e
end

def typeCheck (ctx : LinCtx) (env : TypEnv) (e : Morph.Syntax.Expr) (expected : Morph.Core.Typ) : Prop :=
  inferType ctx env e = some expected

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

`HasType ctx Γ e τ`:
- `ctx : LinCtx` — linear context of bound de Bruijn indices
  (ctx.types[0] = type of bvar 0, the most recent binder)
- `Γ : TypEnv` — types of free variables by name
- `e : Expr` — the expression
 - `τ : Typ` — the inferred type
-/

mutual

inductive HasType : LinCtx → TypEnv → Morph.Syntax.Expr → Morph.Core.Typ → Prop where
  | bvar_type : ∀ ctx Γ n,
      (h : n < (ctx.types).length) →
      HasType ctx Γ (.bvar n) (ctx.types)[n]
  | fvar_type : ∀ ctx Γ name τ,
      lookupTyp Γ name = some τ →
      HasType ctx Γ (.fvar name) τ
  | lit_int : ∀ ctx Γ n, HasType ctx Γ (.lit (.int n)) .intType
  | lit_bool : ∀ ctx Γ b, HasType ctx Γ (.lit (.bool b)) .boolType
  | lit_string : ∀ ctx Γ s, HasType ctx Γ (.lit (.string s)) .stringType
  | lit_unit : ∀ ctx Γ, HasType ctx Γ (.lit .unit) .unitType
  | lit_pointer : ∀ ctx Γ p, HasType ctx Γ (.lit (.pointer p)) .pointerType
  | lit_float : ∀ ctx Γ w f, HasType ctx Γ (.lit (.float f)) (.floatType w)
  | lit_int_width : ∀ ctx Γ w n, HasType ctx Γ (.lit (.int n)) (.intWidthType w)
  | lit_some : ∀ ctx Γ v τ, HasType ctx Γ (.lit (.some v)) (.optionType τ)
  | lit_none : ∀ ctx Γ τ, HasType ctx Γ (.lit .none) (.optionType τ)
  | lit_ok : ∀ ctx Γ v τ_ok τ_err, HasType ctx Γ (.lit (.ok v)) (.resultType τ_ok τ_err)
  | lit_err : ∀ ctx Γ v τ_err τ_ok, HasType ctx Γ (.lit (.err v)) (.resultType τ_ok τ_err)
  | unop_not : ∀ ctx Γ e,
      HasType ctx Γ e .boolType →
      HasType ctx Γ (.unop .not e) .boolType
  | unop_notb : ∀ ctx Γ e,
      HasType ctx Γ e .intType →
      HasType ctx Γ (.unop .notb e) .intType
  | binop_arith : ∀ ctx Γ op e1 e2,
      isArithOp op →
      HasType ctx Γ e1 .intType → HasType ctx Γ e2 .intType →
      HasType ctx Γ (.binop op e1 e2) .intType
  | binop_comp : ∀ ctx Γ op e1 e2,
      isCompOp op →
      HasType ctx Γ e1 .intType → HasType ctx Γ e2 .intType →
      HasType ctx Γ (.binop op e1 e2) .boolType
  | binop_logic : ∀ ctx Γ op e1 e2,
      isLogicOp op →
      HasType ctx Γ e1 .boolType → HasType ctx Γ e2 .boolType →
      HasType ctx Γ (.binop op e1 e2) .boolType
  | binop_bitwise : ∀ ctx Γ op e1 e2,
      isBitwiseOp op →
      HasType ctx Γ e1 .intType → HasType ctx Γ e2 .intType →
      HasType ctx Γ (.binop op e1 e2) .intType
  | binop_ptr_arith : ∀ ctx Γ op e1 e2,
      isPtrArithOp op →
      HasType ctx Γ e1 .pointerType → HasType ctx Γ e2 .intType →
      HasType ctx Γ (.binop op e1 e2) .pointerType
  | binop_ptr_load : ∀ ctx Γ e1 e2,
      HasType ctx Γ e1 .pointerType → HasType ctx Γ e2 .unitType →
      HasType ctx Γ (.binop .ptrLoad e1 e2) .unitType
  | binop_ptr_store : ∀ ctx Γ e1 e2,
      HasType ctx Γ e1 .pointerType → HasType ctx Γ e2 .intType →
      HasType ctx Γ (.binop .ptrStore e1 e2) .unitType
  | binop_string_concat : ∀ ctx Γ op e1 e2,
      op = .add →
      HasType ctx Γ e1 .stringType → HasType ctx Γ e2 .stringType →
      HasType ctx Γ (.binop op e1 e2) .stringType
  | lam_type : ∀ ctx Γ n body paramTys retTy,
      n = paramTys.length →
      HasType (LinCtx.pushMany ctx paramTys.reverse) Γ body retTy →
      HasType ctx Γ (.lam n body) (.functionType paramTys retTy)
  | app_type : ∀ ctx Γ fn args τs τ,
      HasType ctx Γ fn (.functionType τs τ) →
      HasTypeAll ctx Γ args τs →
      HasType ctx Γ (.app fn args) τ
  | let_type : ∀ ctx Γ e1 e2 τ1 τ2,
      HasType ctx Γ e1 τ1 →
      HasType ((τ1, LinCtx.initialUsage τ1) :: ctx) Γ e2 τ2 →
      HasType ctx Γ (.let_ e1 e2) τ2
  | if_type : ∀ ctx Γ c t f τ,
      HasType ctx Γ c .boolType →
      HasType ctx Γ t τ → HasType ctx Γ f τ →
      HasType ctx Γ (.ifThenElse c t f) τ
  | for_type : ∀ ctx Γ s e body,
      HasType ctx Γ s .intType → HasType ctx Γ e .intType →
      HasTypeAll ((.intType, LinCtx.initialUsage .intType) :: ctx) Γ body [.unitType] →
      HasType ctx Γ (.forLoop s e body) .unitType
  | block_type : ∀ ctx Γ exprs τs τ,
      HasTypeAll ctx Γ exprs (τs ++ [τ]) →
      HasType ctx Γ (.block exprs) τ
  | pipe_type : ∀ ctx Γ e f τ_arg τ_ret,
      HasType ctx Γ e τ_arg →
      HasType ctx Γ f (.functionType [τ_arg] τ_ret) →
      HasType ctx Γ (.pipe e f) τ_ret
  | typeAsc_type : ∀ ctx Γ e τ,
      HasType ctx Γ e τ →
      HasType ctx Γ (.typeAsc e τ) τ
  | some_type : ∀ ctx Γ e τ_inner,
      HasType ctx Γ e τ_inner →
      HasType ctx Γ (.some_ e) (.optionType τ_inner)
  | none_type : ∀ ctx Γ τ,
      HasType ctx Γ .none_ (.optionType τ)
  | ok_type : ∀ ctx Γ e τ_ok τ_err,
      HasType ctx Γ e τ_ok →
      HasType ctx Γ (.ok_ e) (.resultType τ_ok τ_err)
  | err_type : ∀ ctx Γ e τ_err τ_ok,
      HasType ctx Γ e τ_err →
      HasType ctx Γ (.err_ e) (.resultType τ_ok τ_err)
  | null_coalesce_type : ∀ ctx Γ e1 e2 τ,
      HasType ctx Γ e1 (.optionType τ) →
      HasType ctx Γ e2 (.optionType τ) →
      HasType ctx Γ (.nullCoalesce e1 e2) (.optionType τ)
  | tuple_type : ∀ ctx Γ elems tys,
      HasTypeAll ctx Γ elems tys →
      HasType ctx Γ (.tuple_ elems) (.tupleType tys)
  | arrayLit_type : ∀ ctx Γ elems τ n,
      HasTypeAll ctx Γ elems (List.replicate n τ) →
      n = elems.length →
      n > 0 →
      HasType ctx Γ (.arrayLit elems) (.arrayType τ n)
  | arrayIndex_type : ∀ ctx Γ arr idx τ n,
      HasType ctx Γ arr (.arrayType τ n) →
      HasType ctx Γ idx .intType →
      HasType ctx Γ (.arrayIndex arr idx) τ
  -- Reference operations (storeless placeholders, ADR-010)
  | refCreate_type : ∀ ctx Γ e cap τ,
      HasType ctx Γ e τ →
      HasType ctx Γ (.refCreate e cap τ) (.refType cap τ)
  | refLoad_type : ∀ ctx Γ e cap τ,
      HasType ctx Γ e (.refType cap τ) →
      HasType ctx Γ (.refLoad e) τ
  | refStore_type : ∀ ctx Γ e v cap τ,
      HasType ctx Γ e (.refType cap τ) →
      HasType ctx Γ v τ →
      cap ≠ .val →  -- cannot store through immutable reference
      HasType ctx Γ (.refStore e v τ) .unitType
  | refFree_type : ∀ ctx Γ e τ,
      HasType ctx Γ e (.refType .iso τ) →
      HasType ctx Γ (.refFree e) .unitType
  | field_access_type : ∀ ctx Γ e fname sname fields τ,
      HasType ctx Γ e (.structType sname fields) →
      structFieldType fields fname = some τ →
      HasType ctx Γ (.field_ e fname) τ
  | match_type : ∀ ctx Γ scrut arms τ_scrut τ_result,
      HasType ctx Γ scrut τ_scrut →
      ArmsTyped ctx Γ τ_scrut arms τ_result →
      HasType ctx Γ (.match_ scrut arms) τ_result


inductive HasTypeAll : LinCtx → TypEnv → List Morph.Syntax.Expr → List Morph.Core.Typ → Prop where
  | nil : ∀ ctx Γ,
      HasTypeAll ctx Γ [] []
  | cons : ∀ ctx Γ e es τ τs,
      HasType ctx Γ e τ → HasTypeAll ctx Γ es τs →
      HasTypeAll ctx Γ (e :: es) (τ :: τs)

inductive ArmsTyped : LinCtx → TypEnv → Morph.Core.Typ → List (List String × Morph.Syntax.Expr) → Morph.Core.Typ → Prop where
  | nil : ∀ ctx Γ τ_scrut,
      ArmsTyped ctx Γ τ_scrut [] .unitType
  | cons : ∀ ctx Γ vars body rest τ_scrut τ_result,
      HasType (LinCtx.pushMany ctx (List.replicate vars.length τ_scrut)) Γ body τ_result →
      ArmsTyped ctx Γ τ_scrut rest τ_result →
      ArmsTyped ctx Γ τ_scrut ((vars, body) :: rest) τ_result

end

end Morph.Specs.TypeSystem
