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

- `HasType ctx Γ e τ ctx'`: The first parameter `ctx : LinCtx` tracks the types
  and usages of currently-bound de Bruijn indices. `ctx.types[0]` is the
  type of bvar 0, etc. The last parameter `ctx'` is the context *after*
  typing `e`. In ADR-010 Phase 1c-β-2 only `bvar_type` (consuming a linear slot)
  and the `binop_*` rules (threading a mid context) change it; the rest still
  return `ctx` unchanged.
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
## Linear Arrows (ADR-014 stage 1)

`linPushMany ctx τs` pushes the parameter types `τs` as *unrestricted* entries
(`Usage.many`). A `linearFunctionType` binder never consumes: the exactly-once
obligation for each parameter is discharged syntactically by `countUses` in the
`lam_linear_type` rule, mirroring Linear Haskell's design where the context is
never mutated during typing. -/
def linPushMany (ctx : LinCtx) (τs : List Morph.Core.Typ) : LinCtx :=
  (τs.map (fun τ => (τ, Usage.many))) ++ ctx

theorem types_linPushMany (ctx : LinCtx) (τs : List Morph.Core.Typ) :
    LinCtx.types (linPushMany ctx τs) = τs ++ LinCtx.types ctx := by
  have hmap : Prod.fst ∘ (fun (τ : Morph.Core.Typ) => (τ, Usage.many)) = id := by
    funext x; rfl
  simp [linPushMany, LinCtx.types, hmap]

/-- The entry at index `k < τs.length` of `linPushMany ctx τs` is `(τs[k], .many)`. -/
theorem entry_linPushMany_mid (ctx : LinCtx) (τs : List Morph.Core.Typ) (k : Nat)
    (h : k < τs.length) :
    (linPushMany ctx τs)[k]? = some (τs[k]'h, Usage.many) := by
  simp only [linPushMany]
  rw [List.getElem?_append_left (by simpa using h)]
  simp

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
  | linearFunctionType_wf : forall env paramTys retTy,
      (forall paramTy, paramTy ∈ paramTys -> WellTyped env paramTy) ->
      WellTyped env retTy ->
      WellTyped env (.linearFunctionType paramTys retTy)
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
    | some (.linearFunctionType paramTys retTy) =>
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
  | .refCast _ _ => none  -- capability casts are store-typed only (ADR-010 amendment)
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

`HasType ctx Γ e τ ctx'`:
- `ctx : LinCtx` — linear context of bound de Bruijn indices
  (ctx.types[0] = type of bvar 0, the most recent binder)
- `Γ : TypEnv` — types of free variables by name
- `e : Expr` — the expression
- `τ : Typ` — the inferred type
- `ctx' : LinCtx` — the linear context *after* typing `e` (ADR-010)

The judgment is a *state transformer on contexts*: it consumes the input
context `ctx` and produces the output context `ctx'`. Phase 1c-β-1 only installed
the plumbing (every rule returned the context it was given unchanged).

Phase 1c-β-2 (this increment) makes `Usage` matter in exactly two places, and
is deliberately partial elsewhere:
- `bvar_type` reads a linear slot (`ctx[n] = some (τ, .zero)`) and *consumes* it:
  its output context is `LinCtx.consume ctx n` (slot `n` advances to `.one`).
  `bvar_type_many` reads an unrestricted slot (`ctx[n] = some (τ, .many)`) and
  leaves the context unchanged.
- the `binop_*` rules *thread* the context: the second operand is typed in the
  first operand's **output** context, and the rule's own output context is that
  same mid context. This matches `HasTypeAll.cons`.

Every other rule still passes its input context through unchanged. That is
inconsistent with the consuming `bvar_type` but sound, and it is temporary: later
phases thread the remaining rules and merge contexts at branching points.
-/

mutual

inductive HasType : LinCtx → TypEnv → Morph.Syntax.Expr → Morph.Core.Typ → LinCtx → Prop where
  -- linear binding: consuming it advances the slot to .one
  | bvar_type : ∀ ctx Γ n τ (ctx' : LinCtx),
      (h : n < (ctx.types).length) →
      ctx[n]? = some (τ, Usage.zero) →
      ctx' = LinCtx.consume ctx n →
      HasType ctx Γ (.bvar n) τ ctx'
  -- unrestricted binding: available any number of times
  | bvar_type_many : ∀ ctx Γ n τ,
      (h : n < (ctx.types).length) →
      ctx[n]? = some (τ, Usage.many) →
      HasType ctx Γ (.bvar n) τ ctx
  | fvar_type : ∀ ctx Γ name τ,
      lookupTyp Γ name = some τ →
      HasType ctx Γ (.fvar name) τ ctx
  | lit_int : ∀ ctx Γ n, HasType ctx Γ (.lit (.int n)) .intType ctx
  | lit_bool : ∀ ctx Γ b, HasType ctx Γ (.lit (.bool b)) .boolType ctx
  | lit_string : ∀ ctx Γ s, HasType ctx Γ (.lit (.string s)) .stringType ctx
  | lit_unit : ∀ ctx Γ, HasType ctx Γ (.lit .unit) .unitType ctx
  | lit_pointer : ∀ ctx Γ p, HasType ctx Γ (.lit (.pointer p)) .pointerType ctx
  | lit_float : ∀ ctx Γ w f, HasType ctx Γ (.lit (.float f)) (.floatType w) ctx
  | lit_int_width : ∀ ctx Γ w n, HasType ctx Γ (.lit (.int n)) (.intWidthType w) ctx
  | lit_some : ∀ ctx Γ v τ, HasType ctx Γ (.lit (.some v)) (.optionType τ) ctx
  | lit_none : ∀ ctx Γ τ, HasType ctx Γ (.lit .none) (.optionType τ) ctx
  | lit_ok : ∀ ctx Γ v τ_ok τ_err, HasType ctx Γ (.lit (.ok v)) (.resultType τ_ok τ_err) ctx
  | lit_err : ∀ ctx Γ v τ_err τ_ok, HasType ctx Γ (.lit (.err v)) (.resultType τ_ok τ_err) ctx
  | unop_not : ∀ ctx Γ e,
      HasType ctx Γ e .boolType ctx →
      HasType ctx Γ (.unop .not e) .boolType ctx
  | unop_notb : ∀ ctx Γ e,
      HasType ctx Γ e .intType ctx →
      HasType ctx Γ (.unop .notb e) .intType ctx
  | binop_arith : ∀ ctx Γ op e1 e2 cmid,
      isArithOp op →
      HasType ctx Γ e1 .intType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop op e1 e2) .intType cmid
  | binop_comp : ∀ ctx Γ op e1 e2 cmid,
      isCompOp op →
      HasType ctx Γ e1 .intType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop op e1 e2) .boolType cmid
  | binop_logic : ∀ ctx Γ op e1 e2 cmid,
      isLogicOp op →
      HasType ctx Γ e1 .boolType cmid →
      HasType cmid Γ e2 .boolType cmid →
      HasType ctx Γ (.binop op e1 e2) .boolType cmid
  | binop_bitwise : ∀ ctx Γ op e1 e2 cmid,
      isBitwiseOp op →
      HasType ctx Γ e1 .intType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop op e1 e2) .intType cmid
  | binop_ptr_arith : ∀ ctx Γ op e1 e2 cmid,
      isPtrArithOp op →
      HasType ctx Γ e1 .pointerType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop op e1 e2) .pointerType cmid
  | binop_ptr_load : ∀ ctx Γ e1 e2 cmid,
      HasType ctx Γ e1 .pointerType cmid →
      HasType cmid Γ e2 .unitType cmid →
      HasType ctx Γ (.binop .ptrLoad e1 e2) .unitType cmid
  | binop_ptr_store : ∀ ctx Γ e1 e2 cmid,
      HasType ctx Γ e1 .pointerType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop .ptrStore e1 e2) .unitType cmid
  | binop_string_concat : ∀ ctx Γ op e1 e2 cmid,
      op = .add →
      HasType ctx Γ e1 .stringType cmid →
      HasType cmid Γ e2 .stringType cmid →
      HasType ctx Γ (.binop op e1 e2) .stringType cmid
  | lam_type : ∀ ctx Γ n body paramTys retTy,
      n = paramTys.length →
      HasType (LinCtx.pushMany ctx paramTys.reverse) Γ body retTy
          (LinCtx.pushMany ctx paramTys.reverse) →
      HasType ctx Γ (.lam n body) (.functionType paramTys retTy) ctx
  | app_type : ∀ ctx Γ fn args τs τ,
      HasType ctx Γ fn (.functionType τs τ) ctx →
      HasTypeAll ctx Γ args τs ctx →
      HasType ctx Γ (.app fn args) τ ctx
  -- linear arrow (ADR-014 stage 1): parameters are pushed as unrestricted
  -- entries (no consumption); the exactly-once obligation is discharged
  -- syntactically by `countUses`.
  | lam_linear_type : ∀ ctx Γ n body paramTys retTy,
      n = paramTys.length →
      HasType (linPushMany ctx paramTys.reverse) Γ body retTy
          (linPushMany ctx paramTys.reverse) →
      (∀ i, i < paramTys.length → Morph.Syntax.countUses body i = 1) →
      HasType ctx Γ (.lam n body) (.linearFunctionType paramTys retTy) ctx
  | app_linear_type : ∀ ctx Γ fn args τs τ,
      HasType ctx Γ fn (.linearFunctionType τs τ) ctx →
      HasTypeAll ctx Γ args τs ctx →
      HasType ctx Γ (.app fn args) τ ctx
  | let_type : ∀ ctx Γ e1 e2 τ1 τ2,
      HasType ctx Γ e1 τ1 ctx →
      HasType ((τ1, LinCtx.initialUsage τ1) :: ctx) Γ e2 τ2
          ((τ1, LinCtx.initialUsage τ1) :: ctx) →
      HasType ctx Γ (.let_ e1 e2) τ2 ctx
  | if_type : ∀ ctx Γ c t f τ,
      HasType ctx Γ c .boolType ctx →
      HasType ctx Γ t τ ctx → HasType ctx Γ f τ ctx →
      HasType ctx Γ (.ifThenElse c t f) τ ctx
  | for_type : ∀ ctx Γ s e body,
      HasType ctx Γ s .intType ctx → HasType ctx Γ e .intType ctx →
      HasTypeAll ((.intType, LinCtx.initialUsage .intType) :: ctx) Γ body [.unitType]
          ((.intType, LinCtx.initialUsage .intType) :: ctx) →
      HasType ctx Γ (.forLoop s e body) .unitType ctx
  | block_type : ∀ ctx Γ exprs τs τ,
      HasTypeAll ctx Γ exprs (τs ++ [τ]) ctx →
      HasType ctx Γ (.block exprs) τ ctx
  | pipe_type : ∀ ctx Γ e f τ_arg τ_ret,
      HasType ctx Γ e τ_arg ctx →
      HasType ctx Γ f (.functionType [τ_arg] τ_ret) ctx →
      HasType ctx Γ (.pipe e f) τ_ret ctx
  | typeAsc_type : ∀ ctx Γ e τ,
      HasType ctx Γ e τ ctx →
      HasType ctx Γ (.typeAsc e τ) τ ctx
  | some_type : ∀ ctx Γ e τ_inner,
      HasType ctx Γ e τ_inner ctx →
      HasType ctx Γ (.some_ e) (.optionType τ_inner) ctx
  | none_type : ∀ ctx Γ τ,
      HasType ctx Γ .none_ (.optionType τ) ctx
  | ok_type : ∀ ctx Γ e τ_ok τ_err,
      HasType ctx Γ e τ_ok ctx →
      HasType ctx Γ (.ok_ e) (.resultType τ_ok τ_err) ctx
  | err_type : ∀ ctx Γ e τ_err τ_ok,
      HasType ctx Γ e τ_err ctx →
      HasType ctx Γ (.err_ e) (.resultType τ_ok τ_err) ctx
  | null_coalesce_type : ∀ ctx Γ e1 e2 τ,
      HasType ctx Γ e1 (.optionType τ) ctx →
      HasType ctx Γ e2 (.optionType τ) ctx →
      HasType ctx Γ (.nullCoalesce e1 e2) (.optionType τ) ctx
  | tuple_type : ∀ ctx Γ elems tys,
      HasTypeAll ctx Γ elems tys ctx →
      HasType ctx Γ (.tuple_ elems) (.tupleType tys) ctx
  | arrayLit_type : ∀ ctx Γ elems τ n,
      HasTypeAll ctx Γ elems (List.replicate n τ) ctx →
      n = elems.length →
      n > 0 →
      HasType ctx Γ (.arrayLit elems) (.arrayType τ n) ctx
  | arrayIndex_type : ∀ ctx Γ arr idx τ n,
      HasType ctx Γ arr (.arrayType τ n) ctx →
      HasType ctx Γ idx .intType ctx →
      HasType ctx Γ (.arrayIndex arr idx) τ ctx
  -- Reference operations (storeless placeholders, ADR-010)
  | refCreate_type : ∀ ctx Γ e cap τ,
      HasType ctx Γ e τ ctx →
      HasType ctx Γ (.refCreate e cap τ) (.refType cap τ) ctx
  | refLoad_type : ∀ ctx Γ e cap τ,
      HasType ctx Γ e (.refType cap τ) ctx →
      HasType ctx Γ (.refLoad e) τ ctx
  | refStore_type : ∀ ctx Γ e v cap τ,
      HasType ctx Γ e (.refType cap τ) ctx →
      HasType ctx Γ v τ ctx →
      cap ≠ .val →  -- cannot store through immutable reference
      HasType ctx Γ (.refStore e v τ) .unitType ctx
  | refFree_type : ∀ ctx Γ e τ,
      HasType ctx Γ e (.refType .iso τ) ctx →
      HasType ctx Γ (.refFree e) .unitType ctx
  | field_access_type : ∀ ctx Γ e fname sname fields τ,
      HasType ctx Γ e (.structType sname fields) ctx →
      structFieldType fields fname = some τ →
      HasType ctx Γ (.field_ e fname) τ ctx
  | match_type : ∀ ctx Γ scrut arms τ_scrut τ_result,
      HasType ctx Γ scrut τ_scrut ctx →
      ArmsTyped ctx Γ τ_scrut arms τ_result ctx →
      HasType ctx Γ (.match_ scrut arms) τ_result ctx

/-- `HasTypeAll ctx Γ es τs ctx'`: a list is typable element by element, threading
    the context: each element consumes what it needs and hands the resulting
    context to the next one, with a single output context for the whole list. -/
inductive HasTypeAll : LinCtx → TypEnv → List Morph.Syntax.Expr → List Morph.Core.Typ → LinCtx → Prop where
  | nil : ∀ ctx Γ,
      HasTypeAll ctx Γ [] [] ctx
  | cons : ∀ ctx Γ cout e es τ τs,
      HasType ctx Γ e τ cout → HasTypeAll cout Γ es τs cout →
      HasTypeAll ctx Γ (e :: es) (τ :: τs) cout

/-- `ArmsTyped ctx Γ τ_scrut arms τ_result ctx'`: every arm body is typable in the
    scrutinee context extended with its pattern variables.

    Phase 1c-β-1: arms do not consume anything, so all arms keep the same
    context and the arms are *not* merged — a later phase (1c-β-2) will thread
    each arm's output context and merge them pointwise. -/
inductive ArmsTyped : LinCtx → TypEnv → Morph.Core.Typ → List (List String × Morph.Syntax.Expr) → Morph.Core.Typ → LinCtx → Prop where
  | nil : ∀ ctx Γ τ_scrut,
      ArmsTyped ctx Γ τ_scrut [] .unitType ctx
  | cons : ∀ ctx Γ vars body rest τ_scrut τ_result,
      HasType (LinCtx.pushMany ctx (List.replicate vars.length τ_scrut)) Γ body τ_result
          (LinCtx.pushMany ctx (List.replicate vars.length τ_scrut)) →
      ArmsTyped ctx Γ τ_scrut rest τ_result ctx →
      ArmsTyped ctx Γ τ_scrut ((vars, body) :: rest) τ_result ctx

end

end Morph.Specs.TypeSystem
