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

private theorem nat_sub_lt_of_lt_add (a b c : Nat) (hGE : a ≥ c) (hLT : a < c + b) : a - c < b := by
  have h3 : (a - c) + c = a := Nat.sub_add_cancel hGE
  have h4 : (a - c) + c < b + c := by omega
  exact Nat.lt_of_add_lt_add_right h4

private theorem omega_list_len (as bs : List Typ) (n : Nat) (σ : Typ)
    (h : n < (as ++ bs).length) : n < (as ++ σ :: bs).length := by
  have h1 := @List.length_append Typ as bs
  have h2 := @List.length_append Typ as (σ :: bs)
  have h3 := @List.length_cons Typ σ bs
  have h4 := h2.trans (congrArg (as.length + ·) h3)
  omega

private theorem omega_list_len_succ (as bs : List Typ) (n : Nat) (σ : Typ)
    (h : n < (as ++ bs).length) : n + 1 < (as ++ σ :: bs).length := by
  have h1 := @List.length_append Typ as bs
  have h2 := @List.length_append Typ as (σ :: bs)
  have h3 := @List.length_cons Typ σ bs
  have h4 := h2.trans (congrArg (as.length + ·) h3)
  omega

mutual

private theorem weakening_at_depth (xs : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (e : Expr) (τ σ : Typ) :
    HasType (xs ++ bvs) Γ e τ → HasType (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) τ := by
  intro h
  cases h with
  | bvar_type _ _ n hLen =>
    simp only [liftUnder]
    split
    · rename_i hNlt
      have hLen2 := omega_list_len xs bvs n σ hLen
      have hBT := HasType.bvar_type (xs ++ σ :: bvs) Γ n hLen2
      have hEq := (@List.getElem_append_left Typ n xs (σ :: bvs) hNlt hLen2).trans
                 (@List.getElem_append_left Typ n xs bvs hNlt hLen).symm
      exact Eq.subst (motive := fun t => HasType (xs ++ σ :: bvs) Γ (.bvar n) t) hEq hBT
    · rename_i hNge
      have hLen2 := omega_list_len_succ xs bvs n σ hLen
      have hNge' : n ≥ xs.length := Nat.ge_of_not_lt hNge
      have hLIdx : n - xs.length < bvs.length := by
        have h1 := @List.length_append Typ xs bvs
        exact nat_sub_lt_of_lt_add n bvs.length xs.length hNge' (by omega)
      have hRIdx : (n - xs.length) + 1 < (σ :: bvs).length := by
        have h1 := @List.length_append Typ xs bvs
        have h2 := @List.length_cons Typ σ bvs
        omega
      have hBT := HasType.bvar_type (xs ++ σ :: bvs) Γ (n + 1) hLen2
      have h1 := @List.getElem_append_right Typ xs (σ :: bvs) (n + 1) (by omega) hLen2
      have h2 := @List.getElem_append_right Typ xs bvs n hNge' hLen
      have h3 := List.getElem_cons_succ σ bvs (n - xs.length) hRIdx
      have h4 : n + 1 - xs.length = (n - xs.length) + 1 := by omega
      have hBT1 := Eq.subst (motive := fun t => HasType (xs ++ σ :: bvs) Γ (.bvar (n + 1)) t) h1 hBT
      have h3' : (σ :: bvs)[n + 1 - xs.length] = bvs[n - xs.length] := by
        simp only [h4]; exact h3
      have hBT2 := Eq.subst (motive := fun t => HasType (xs ++ σ :: bvs) Γ (.bvar (n + 1)) t) h3' hBT1
      exact Eq.subst (motive := fun t => HasType (xs ++ σ :: bvs) Γ (.bvar (n + 1)) t) h2.symm hBT2
  | fvar_type _ _ name τ hLookup =>
    simp only [liftUnder]
    exact HasType.fvar_type (xs ++ σ :: bvs) Γ name τ hLookup
  | lit_int _ _ n => simp only [liftUnder]; exact HasType.lit_int (xs ++ σ :: bvs) Γ n
  | lit_bool _ _ b => simp only [liftUnder]; exact HasType.lit_bool (xs ++ σ :: bvs) Γ b
  | lit_string _ _ s => simp only [liftUnder]; exact HasType.lit_string (xs ++ σ :: bvs) Γ s
  | lit_unit _ _ => simp only [liftUnder]; exact HasType.lit_unit (xs ++ σ :: bvs) Γ
  | lit_pointer _ _ p => simp only [liftUnder]; exact HasType.lit_pointer (xs ++ σ :: bvs) Γ p
  | unop_not _ _ e' hE' =>
    simp only [liftUnder]
    exact HasType.unop_not (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e')
      (weakening_at_depth xs bvs Γ e' .boolType σ hE')
  | unop_notb _ _ e' hE' =>
    simp only [liftUnder]
    exact HasType.unop_notb (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e')
      (weakening_at_depth xs bvs Γ e' .intType σ hE')
  | binop_arith _ _ op e1 e2 hArith hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_arith (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hArith
      (weakening_at_depth xs bvs Γ e1 .intType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .intType σ hE2)
  | binop_comp _ _ op e1 e2 hComp hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_comp (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hComp
      (weakening_at_depth xs bvs Γ e1 .intType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .intType σ hE2)
  | binop_logic _ _ op e1 e2 hLogic hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_logic (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hLogic
      (weakening_at_depth xs bvs Γ e1 .boolType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .boolType σ hE2)
  | binop_bitwise _ _ op e1 e2 hBit hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_bitwise (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hBit
      (weakening_at_depth xs bvs Γ e1 .intType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .intType σ hE2)
  | lam_type _ _ n body paramTys retTy hLen hBody =>
    simp only [liftUnder, liftUnder]
    have hLenEq : (paramTys.reverse ++ xs).length = n + xs.length := by
      have h1 := @List.length_append Typ (paramTys.reverse) xs
      have h2 := @List.length_reverse Typ paramTys
      rw [h1, h2]; omega
    have hBody' := weakening_at_depth (paramTys.reverse ++ xs) bvs Γ body retTy σ
      (by rw [← List.append_assoc] at hBody; exact hBody)
    rw [hLenEq, Nat.add_comm] at hBody'
    exact HasType.lam_type (xs ++ σ :: bvs) Γ n (liftUnder (xs.length + n) 1 body) paramTys retTy hLen
      (Eq.subst (motive := fun ctx => HasType ctx Γ (liftUnder (xs.length + n) 1 body) retTy)
        (show paramTys.reverse ++ xs ++ σ :: bvs = paramTys.reverse ++ (xs ++ σ :: bvs) from
          by exact @List.append_assoc Typ (paramTys.reverse) xs (σ :: bvs)) hBody')
  | app_type _ _ fn args τs τ hFn hArgs =>
    simp only [liftUnder]
    exact HasType.app_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 fn)
      (List.map (liftUnder xs.length 1) args) τs τ
      (weakening_at_depth xs bvs Γ fn (.functionType τs τ) σ hFn)
      (weakening_at_depth_all xs bvs Γ args τs σ hArgs)
  | let_type _ _ e1 e2 τ1 _ hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.let_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e1)
      (liftUnder (xs.length + 1) 1 e2) τ1 τ
      (weakening_at_depth xs bvs Γ e1 τ1 σ hE1)
      (weakening_at_depth (τ1 :: xs) bvs Γ e2 τ σ hE2)
  | if_type _ _ c t f τ hC hT hF =>
    simp only [liftUnder]
    exact HasType.if_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 c)
      (liftUnder xs.length 1 t) (liftUnder xs.length 1 f) τ
      (weakening_at_depth xs bvs Γ c .boolType σ hC)
      (weakening_at_depth xs bvs Γ t τ σ hT)
      (weakening_at_depth xs bvs Γ f τ σ hF)
  | for_type _ _ s e body hS hE hBody =>
    simp only [liftUnder, liftUnder]
    exact HasType.for_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 s)
      (liftUnder xs.length 1 e) (List.map (liftUnder (xs.length + 1) 1) body)
      (weakening_at_depth xs bvs Γ s .intType σ hS)
      (weakening_at_depth xs bvs Γ e .intType σ hE)
      (weakening_at_depth_all (.intType :: xs) bvs Γ body [.unitType] σ hBody)
  | block_type _ _ exprs τs τ hExprs =>
    simp only [liftUnder]
    exact HasType.block_type (xs ++ σ :: bvs) Γ (List.map (liftUnder xs.length 1) exprs) τs τ
      (weakening_at_depth_all xs bvs Γ exprs (τs ++ [τ]) σ hExprs)

private theorem weakening_at_depth_all (xs : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (es : List Expr) (τs : List Typ) (σ : Typ)
    (h : HasTypeAll (xs ++ bvs) Γ es τs) :
    HasTypeAll (xs ++ σ :: bvs) Γ (es.map (liftUnder xs.length 1)) τs := by
  cases h with
  | nil _ _ => exact HasTypeAll.nil _ _
  | cons _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _
      (weakening_at_depth xs bvs Γ e τ σ hE)
      (weakening_at_depth_all xs bvs Γ es' τs' σ hRest)

end

mutual

theorem weakening (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ) (σ : Typ) :
    HasType bvs Γ e τ → HasType (σ :: bvs) Γ (lift 1 e) τ := by
  intro h
  match h with
  | HasType.bvar_type bvs Γ n h =>
    have hLen' : n + 1 < (σ :: bvs).length := by simp; omega
    rw [lift_bvar]
    have : (σ :: bvs)[n + 1]'hLen' = bvs[n]'h := by
      exact List.getElem_cons_succ σ bvs n hLen'
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
    have hLenEq1 := @List.length_reverse Typ paramTys
    have hLenEq2 : paramTys.reverse.length = n := hLenEq1.trans hLen.symm
    have hBody' := weakening_at_depth paramTys.reverse bvs Γ body retTy σ hBody
    exact HasType.lam_type (σ :: bvs) Γ n (liftUnder n 1 body) paramTys retTy hLen
      (Eq.subst (motive := fun i => HasType (paramTys.reverse ++ σ :: bvs) Γ (liftUnder i 1 body) retTy) hLenEq2 hBody')
  | HasType.app_type bvs Γ fn args τs τ hFn hArgs =>
    rw [lift_app]
    exact HasType.app_type (σ :: bvs) Γ (lift 1 fn) (List.map (lift 1) args) τs τ
      (weakening _ _ _ _ σ hFn) (weakening_all _ _ _ _ σ hArgs)
  | HasType.let_type bvs Γ e1 e2 τ1 τ2 hE1 hE2 =>
    rw [lift_let]
    exact HasType.let_type (σ :: bvs) Γ (lift 1 e1) (liftUnder 1 1 e2) τ1 τ2
      (weakening _ _ _ _ σ hE1) (weakening_at_depth [τ1] bvs Γ e2 τ2 σ hE2)
  | HasType.if_type bvs Γ c t f τ hC hT hF =>
    rw [lift_if]
    exact HasType.if_type (σ :: bvs) Γ (lift 1 c) (lift 1 t) (lift 1 f) τ
      (weakening _ _ _ _ σ hC) (weakening _ _ _ _ σ hT) (weakening _ _ _ _ σ hF)
  | HasType.for_type bvs Γ s e body hS hE hBody =>
    rw [lift_for]
    exact HasType.for_type (σ :: bvs) Γ (lift 1 s) (lift 1 e) (body.map (liftUnder 1 1))
      (weakening _ _ _ _ σ hS) (weakening _ _ _ _ σ hE)
      (weakening_at_depth_all [.intType] bvs Γ body [.unitType] σ hBody)
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
