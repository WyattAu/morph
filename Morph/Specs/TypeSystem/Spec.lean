/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax

namespace Morph.Specs.TypeSystem

/-!
# Type System Specification

This module formalizes the type system for the Morph language specification.

## Overview

The TypeSystem module formalizes:
- **Type Environments:** Mapping variable names to types
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
## Type Inference
-/
def inferType (env : TypEnv) : Morph.Syntax.Expr -> Option Morph.Core.Typ
  | .var id => lookupTyp env id.name
  | .lit (.int _) => some .intType
  | .lit (.bool _) => some .boolType
  | .lit (.string _) => some .stringType
  | .lit .unit => some .unitType
  | .lit (.pointer _) => some .pointerType
  | .lit .undef => none
  | .unop _ _ => none
  | .binop _ _ _ => none
  | .app _ _ => none
  | .lam _ _ => none
  | .let _ _ _ => none
  | .ifThenElse _ _ _ => none
  | .forLoop _ _ _ _ => none
  | .block _ => none

def typeCheck (env : TypEnv) (e : Morph.Syntax.Expr) (expected : Morph.Core.Typ) : Prop :=
  inferType env e = some expected

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

/-! ## Typing Judgments -/

mutual

inductive HasType : TypEnv → Morph.Syntax.Expr → Morph.Core.Typ → Prop where
  | var_type : ∀ Γ id τ,
      lookupTyp Γ id.name = some τ →
      HasType Γ (.var id) τ
  | lit_int : ∀ Γ n, HasType Γ (.lit (.int n)) .intType
  | lit_bool : ∀ Γ b, HasType Γ (.lit (.bool b)) .boolType
  | lit_string : ∀ Γ s, HasType Γ (.lit (.string s)) .stringType
  | lit_unit : ∀ Γ, HasType Γ (.lit .unit) .unitType
  | lit_pointer : ∀ Γ p, HasType Γ (.lit (.pointer p)) .pointerType
  | unop_not : ∀ Γ e,
      HasType Γ e .boolType →
      HasType Γ (.unop .not e) .boolType
  | unop_notb : ∀ Γ e,
      HasType Γ e .intType →
      HasType Γ (.unop .notb e) .intType
  | binop_arith : ∀ Γ op e1 e2,
      isArithOp op →
      HasType Γ e1 .intType → HasType Γ e2 .intType →
      HasType Γ (.binop op e1 e2) .intType
  | binop_comp : ∀ Γ op e1 e2,
      isCompOp op →
      HasType Γ e1 .intType → HasType Γ e2 .intType →
      HasType Γ (.binop op e1 e2) .boolType
  | binop_logic : ∀ Γ op e1 e2,
      isLogicOp op →
      HasType Γ e1 .boolType → HasType Γ e2 .boolType →
      HasType Γ (.binop op e1 e2) .boolType
  | binop_bitwise : ∀ Γ op e1 e2,
      isBitwiseOp op →
      HasType Γ e1 .intType → HasType Γ e2 .intType →
      HasType Γ (.binop op e1 e2) .intType
  | lam_type : ∀ Γ x body τ1 τ2,
      HasType (extendTypEnv Γ x.name τ1) body τ2 →
      HasType Γ (.lam [x] body) (.functionType [τ1] τ2)
  | app_type : ∀ Γ fn args τs τ,
      HasType Γ fn (.functionType τs τ) →
      HasTypeAll Γ args τs →
      HasType Γ (.app fn args) τ
  | let_type : ∀ Γ id e1 e2 τ1 τ2,
      HasType Γ e1 τ1 →
      HasType (extendTypEnv Γ id.name τ1) e2 τ2 →
      HasType Γ (.let id e1 e2) τ2
  | if_type : ∀ Γ c t f τ,
      HasType Γ c .boolType →
      HasType Γ t τ → HasType Γ f τ →
      HasType Γ (.ifThenElse c t f) τ
  | for_type : ∀ Γ id s e body,
      HasType Γ s .intType → HasType Γ e .intType →
      HasTypeAll (extendTypEnv Γ id.name .intType) body [.unitType] →
      HasType Γ (.forLoop id s e body) .unitType
  | block_type : ∀ Γ exprs τs τ,
      HasTypeAll Γ exprs (τs ++ [τ]) →
      HasType Γ (.block exprs) τ

inductive HasTypeAll : TypEnv → List Morph.Syntax.Expr → List Morph.Core.Typ → Prop where
  | nil : ∀ Γ,
      HasTypeAll Γ [] []
  | cons : ∀ Γ e es τ τs,
      HasType Γ e τ → HasTypeAll Γ es τs →
      HasTypeAll Γ (e :: es) (τ :: τs)

end

end Morph.Specs.TypeSystem
