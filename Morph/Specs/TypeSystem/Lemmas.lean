/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem.Spec

namespace Morph.Specs.TypeSystem

open Morph.Core
open Morph.Syntax

/-! ## Inversion Lemmas -/

-- NOTE: bvar_type produces HasType bvs Γ (.bvar n) bvs[n], so any
-- HasType bvs Γ (.bvar n) τ must have τ = bvs[n] with n < bvs.length.
-- We split into two lemmas to avoid dependent indexing issues.
theorem HasType_bvar_has_length (bvs : List Typ) (Γ : TypEnv) (n : Nat) (τ : Typ) :
    HasType bvs Γ (.bvar n) τ → n < bvs.length := by
  intro h
  cases h with
  | bvar_type _ _ _ hLen => exact hLen

theorem HasType_fvar_inv (bvs : List Typ) (Γ : TypEnv) (name : String) (τ : Typ) :
    HasType bvs Γ (.fvar name) τ → lookupTyp Γ name = some τ := by
  intro h; cases h with | fvar_type => assumption

theorem HasType_lit_int_inv (bvs : List Typ) (Γ : TypEnv) (n : Int) (τ : Typ) :
    HasType bvs Γ (.lit (.int n)) τ → τ = .intType := by
  intro h; cases h with | lit_int => rfl

theorem HasType_lit_bool_inv (bvs : List Typ) (Γ : TypEnv) (b : Bool) (τ : Typ) :
    HasType bvs Γ (.lit (.bool b)) τ → τ = .boolType := by
  intro h; cases h with | lit_bool => rfl

theorem HasType_lit_string_inv (bvs : List Typ) (Γ : TypEnv) (s : String) (τ : Typ) :
    HasType bvs Γ (.lit (.string s)) τ → τ = .stringType := by
  intro h; cases h with | lit_string => rfl

theorem HasType_lit_unit_inv (bvs : List Typ) (Γ : TypEnv) (τ : Typ) :
    HasType bvs Γ (.lit .unit) τ → τ = .unitType := by
  intro h; cases h with | lit_unit => rfl

theorem HasType_lit_pointer_inv (bvs : List Typ) (Γ : TypEnv) (p : Pointer) (τ : Typ) :
    HasType bvs Γ (.lit (.pointer p)) τ → τ = .pointerType := by
  intro h; cases h with | lit_pointer => rfl

theorem HasType_unop_not_inv (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ) :
    HasType bvs Γ (.unop .not e) τ → τ = .boolType := by
  intro h; cases h with | unop_not => rfl

theorem HasType_unop_notb_inv (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ) :
    HasType bvs Γ (.unop .notb e) τ → τ = .intType := by
  intro h; cases h with | unop_notb => rfl

/-! ## Lift Simplification Lemmas

`liftUnder` is defined by well-founded recursion on a nested inductive type,
so Lean's kernel cannot unfold it definitionally. These lemmas provide
the necessary equalities for use in rewriting.
-/

@[simp] theorem lift_bvar (n k : Nat) : lift k (.bvar n) = .bvar (n + k) := by
  simp [lift, liftUnder]

@[simp] theorem lift_fvar (name : String) (k : Nat) : lift k (.fvar name) = .fvar name := by
  simp [lift, liftUnder]

@[simp] theorem lift_lit (v : Value) (k : Nat) : lift k (.lit v) = .lit v := by
  simp [lift, liftUnder]

@[simp] theorem lift_unop (op : Operator) (e : Expr) (k : Nat) :
    lift k (.unop op e) = .unop op (lift k e) := by
  simp [lift, liftUnder]

@[simp] theorem lift_binop (op : Operator) (e1 e2 : Expr) (k : Nat) :
    lift k (.binop op e1 e2) = .binop op (lift k e1) (lift k e2) := by
  simp [lift, liftUnder]

@[simp] theorem lift_lam (n : Nat) (body : Expr) (k : Nat) :
    lift k (.lam n body) = .lam n (liftUnder n k body) := by
  simp [lift, liftUnder]

@[simp] theorem lift_app (fn : Expr) (args : List Expr) (k : Nat) :
    lift k (.app fn args) = .app (lift k fn) (args.map (lift k)) := by
  simp [lift, liftUnder]

@[simp] theorem lift_let (e1 e2 : Expr) (k : Nat) :
    lift k (.let_ e1 e2) = .let_ (lift k e1) (liftUnder 1 k e2) := by
  simp [lift, liftUnder]

@[simp] theorem lift_if (c t f : Expr) (k : Nat) :
    lift k (.ifThenElse c t f) = .ifThenElse (lift k c) (lift k t) (lift k f) := by
  simp [lift, liftUnder]

@[simp] theorem lift_for (s e : Expr) (body : List Expr) (k : Nat) :
    lift k (.forLoop s e body) = .forLoop (lift k s) (lift k e) (body.map (liftUnder 1 k)) := by
  simp [lift, liftUnder]

@[simp] theorem lift_block (exprs : List Expr) (k : Nat) :
    lift k (.block exprs) = .block (exprs.map (lift k)) := by
  simp [lift, liftUnder]

/-! ## Weakening (Trivial with de Bruijn)

With de Bruijn indices, weakening is simply prepending a type to `bvs`.
No freshness predicate is needed — bound variables are identified by index,
not by name, so there is no possibility of capture.
-/

mutual

theorem weakening (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ) (σ : Typ) :
    HasType bvs Γ e τ → HasType (σ :: bvs) Γ (lift 1 e) τ := by
  intro h
  match h with
  | HasType.bvar_type bvs Γ n h =>
    have hLen' : n + 1 < (σ :: bvs).length := by simp; omega
    rw [lift_bvar]
    have : (σ :: bvs)[n + 1] = bvs[n] := by sorry
    exact this ▸ HasType.bvar_type (σ :: bvs) Γ (n + 1) hLen'
  | HasType.fvar_type bvs Γ name τ hLookup =>
    rw [lift_fvar]
    exact HasType.fvar_type (σ :: bvs) Γ name τ hLookup
  | HasType.lit_int bvs Γ n =>
    rw [lift_lit]
    exact HasType.lit_int (σ :: bvs) Γ n
  | HasType.lit_bool bvs Γ b =>
    rw [lift_lit]
    exact HasType.lit_bool (σ :: bvs) Γ b
  | HasType.lit_string bvs Γ s =>
    rw [lift_lit]
    exact HasType.lit_string (σ :: bvs) Γ s
  | HasType.lit_unit bvs Γ =>
    rw [lift_lit]
    exact HasType.lit_unit (σ :: bvs) Γ
  | HasType.lit_pointer bvs Γ p =>
    rw [lift_lit]
    exact HasType.lit_pointer (σ :: bvs) Γ p
  | HasType.unop_not bvs Γ e hE =>
    rw [lift_unop]
    exact HasType.unop_not (σ :: bvs) Γ (lift 1 e) (weakening _ _ _ _ σ hE)
  | HasType.unop_notb bvs Γ e hE =>
    rw [lift_unop]
    exact HasType.unop_notb (σ :: bvs) Γ (lift 1 e) (weakening _ _ _ _ σ hE)
  | HasType.binop_arith bvs Γ op e1 e2 hArith hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_arith (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hArith
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_comp bvs Γ op e1 e2 hComp hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_comp (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hComp
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_logic bvs Γ op e1 e2 hLogic hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_logic (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hLogic
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_bitwise bvs Γ op e1 e2 hBit hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_bitwise (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hBit
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.lam_type bvs Γ n body paramTys retTy hLen hBody =>
    rw [lift_lam]
    -- We have: HasType (paramTys.reverse ++ bvs) Γ body retTy
    -- Need: HasType (paramTys.reverse ++ σ :: bvs) Γ (liftUnder n 1 body) retTy
    -- Weakening at depth 0 gives: HasType (σ :: paramTys.reverse ++ bvs) Γ (lift 1 body) retTy
    -- These differ in both context and expression.
    sorry
  | HasType.app_type bvs Γ fn args τs τ hFn hArgs =>
    rw [lift_app]
    exact HasType.app_type (σ :: bvs) Γ (lift 1 fn) (List.map (lift 1) args) τs τ
      (weakening _ _ _ _ σ hFn) (weakening_all _ _ _ _ σ hArgs)
  | HasType.let_type bvs Γ e1 e2 τ1 τ2 hE1 hE2 =>
    rw [lift_let]
    -- lift 1 (.let_ e1 e2) = .let_ (lift 1 e1) (liftUnder 1 1 e2)
    -- For e2: typed in (τ1 :: bvs), need typing in (τ1 :: σ :: bvs) for (liftUnder 1 1 e2)
    sorry
  | HasType.if_type bvs Γ c t f τ hC hT hF =>
    rw [lift_if]
    exact HasType.if_type (σ :: bvs) Γ (lift 1 c) (lift 1 t) (lift 1 f) τ
      (weakening _ _ _ _ σ hC) (weakening _ _ _ _ σ hT) (weakening _ _ _ _ σ hF)
  | HasType.for_type bvs Γ s e body hS hE hBody =>
    rw [lift_for]
    -- Same issue as let_: body needs weakening at depth 1
    sorry
  | HasType.block_type bvs Γ exprs τs τ hExprs =>
    rw [lift_block]
    exact HasType.block_type (σ :: bvs) Γ (List.map (lift 1) exprs) τs τ
      (weakening_all _ _ _ _ σ hExprs)

theorem weakening_all (bvs : List Typ) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (σ : Typ) (h : HasTypeAll bvs Γ es τs) : HasTypeAll (σ :: bvs) Γ (es.map (lift 1)) τs := by
  match h with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _
      (weakening _ _ _ _ σ hE)
      (weakening_all _ _ _ _ σ hRest)

end

/-! ## Canonical Forms -/

def isFunctionValue (e : Expr) : Prop :=
  match e with
  | .lam _ _ => True
  | _ => False

/-! ## Evaluation Totality for Specific Operator Classes -/

theorem evalLogicOp_some_of_isLogicOp (op : Operator) (b1 b2 : Bool)
    (h : isLogicOp op) : ∃ r, Morph.Semantics.evalLogicOp op b1 b2 = some r := by
  cases op with
  | and => exact ⟨b1 && b2, rfl⟩
  | or => exact ⟨b1 || b2, rfl⟩
  | _ => unfold isLogicOp at h; exact h.elim

theorem evalBitwiseOp_some_of_isBitwiseOp (op : Operator) (n1 n2 : Int)
    (h : isBitwiseOp op) : ∃ r, Morph.Semantics.evalBitwiseOp op n1 n2 = some r := by
  cases op with
  | andb => exact ⟨if decide (n1 % 2 = 1) && decide (n2 % 2 = 1) then 1 else 0, rfl⟩
  | orb => exact ⟨if decide (n1 % 2 = 1) || decide (n2 % 2 = 1) then 1 else 0, rfl⟩
  | xorb => exact ⟨if decide (n1 % 2 = 1) != decide (n2 % 2 = 1) then 1 else 0, rfl⟩
  | shl => exact ⟨n1 * Int.pow 2 n2.toNat, rfl⟩
  | shr => exact ⟨Int.shiftRight n1 n2.toNat, rfl⟩
  | _ => unfold isBitwiseOp at h; exact h.elim

end Morph.Specs.TypeSystem
