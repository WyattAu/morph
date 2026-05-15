/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem.Spec
import Morph.Specs.TypeSystem.Lemmas

namespace Morph.Proofs.TypeSoundness

open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Step
open Morph.Specs.TypeSystem
open HasType

private theorem HasTypeAll_cons_head {bvs : List Typ} {Γ : TypEnv} {e : Expr} {es : List Expr}
    {τ : Typ} {τs : List Typ} (h : HasTypeAll bvs Γ (e :: es) (τ :: τs)) : HasType bvs Γ e τ := by
  match h with
  | HasTypeAll.cons _ _ _ _ _ _ hE _ => exact hE

private theorem HasTypeAll_cons_tail {bvs : List Typ} {Γ : TypEnv} {e : Expr} {es : List Expr}
    {τ : Typ} {τs : List Typ} (h : HasTypeAll bvs Γ (e :: es) (τ :: τs)) : HasTypeAll bvs Γ es τs := by
  match h with
  | HasTypeAll.cons _ _ _ _ _ _ _ hRest => exact hRest

private theorem HasTypeAll_nil_types {bvs : List Typ} {Γ : TypEnv} {τs : List Typ} :
    HasTypeAll bvs Γ [] τs -> τs = [] := by
  intro h; match h with | HasTypeAll.nil _ _ => rfl

private theorem append_singleton_ne_nil (τs : List Typ) (τ : Typ) : τs ++ [τ] ≠ [] := by
  intro h
  cases τs with
  | nil => exact absurd h (by contradiction)
  | cons _ _ => exact absurd h (by contradiction)

private theorem HasTypeAll_length (bvs : List Typ) (Γ : TypEnv) (es : List Expr) (τs : List Typ) :
    HasTypeAll bvs Γ es τs -> es.length = τs.length := by
  intro h
  cases es with
  | nil => match h with | HasTypeAll.nil _ _ => rfl
  | cons e es' =>
    cases τs with
    | nil => cases h
    | cons τ τs' =>
      simp only [List.length_cons]
      have ⟨_, hTail⟩ : HasType bvs Γ e τ ∧ HasTypeAll bvs Γ es' τs' := by
        match h with | HasTypeAll.cons _ _ _ _ _ _ hH hT => exact ⟨hH, hT⟩
      exact congrArg (· + 1) (HasTypeAll_length bvs Γ es' τs' hTail)

private theorem sem_isArithOp_not_spec_isCompOp (op : Operator) :
    Morph.Semantics.isArithOp op -> ¬Morph.Specs.TypeSystem.isCompOp op := by
  intro ha hc
  cases op <;> simp [Morph.Semantics.isArithOp, Morph.Specs.TypeSystem.isCompOp] at * <;> contradiction

private theorem sem_isCompOp_not_spec_isArithOp (op : Operator) :
    Morph.Semantics.isCompOp op -> ¬Morph.Specs.TypeSystem.isArithOp op := by
  intro hc ha
  cases op <;> simp [Morph.Semantics.isCompOp, Morph.Specs.TypeSystem.isArithOp] at * <;> contradiction

private theorem sem_isBitwiseOp_not_spec_isCompOp (op : Operator) :
    Morph.Semantics.isBitwiseOp op -> ¬Morph.Specs.TypeSystem.isCompOp op := by
  intro hb hc
  cases op <;> simp [Morph.Semantics.isBitwiseOp, Morph.Specs.TypeSystem.isCompOp] at * <;> contradiction

private theorem sem_isCompOp_not_spec_isBitwiseOp (op : Operator) :
    Morph.Semantics.isCompOp op -> ¬Morph.Specs.TypeSystem.isBitwiseOp op := by
  intro hc hb
  cases op <;> simp [Morph.Semantics.isCompOp, Morph.Specs.TypeSystem.isBitwiseOp] at * <;> contradiction

private theorem HasTypeAll_append {bvs : List Typ} {Γ : TypEnv} {es₁ es₂ : List Expr} {τs₁ τs₂ : List Typ}
    (h₁ : HasTypeAll bvs Γ es₁ τs₁) (h₂ : HasTypeAll bvs Γ es₂ τs₂) :
    HasTypeAll bvs Γ (es₁ ++ es₂) (τs₁ ++ τs₂) := by
  match h₁ with
  | HasTypeAll.nil _ _ => exact h₂
  | HasTypeAll.cons _ _ e es τ τs hE hRest =>
    exact HasTypeAll.cons _ _ e (es ++ es₂) τ (τs ++ τs₂) hE (HasTypeAll_append hRest h₂)

/-!
## Substitution Lemma (de Bruijn)

With de Bruijn indices, the substitution lemma is dramatically simpler.
No freshness predicate is needed — capture-avoidance is guaranteed by construction.

`HasType_subst`: If `e` has type `τ` in context `τ1 :: bvs`, and `v` has type `τ1` in `bvs`,
then `subst e v` has type `τ` in `bvs`.
-/

mutual

private theorem HasTypeAll_subst_all (bvs : List Typ) (Γ : TypEnv) (es : List Expr)
    (v : Expr) (τ1 : Typ) (τs : List Typ)
    (hArgs : HasTypeAll (τ1 :: bvs) Γ es τs)
    (hV : HasType bvs Γ v τ1) :
    HasTypeAll bvs Γ (es.map (fun e => Morph.Syntax.subst e v)) τs := by
  match hArgs with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ (Morph.Syntax.subst e v) (es'.map (fun e => Morph.Syntax.subst e v)) τ τs'
      (HasType_subst bvs Γ e v τ1 τ hE hV)
      (HasTypeAll_subst_all bvs Γ es' v τ1 τs' hRest hV)

-- Main substitution lemma: if e has type τ in (τ1 :: bvs) Γ,
-- and v has type τ1 in bvs Γ, then subst e v has type τ in bvs Γ.
private theorem HasType_subst (bvs : List Typ) (Γ : TypEnv) (e v : Expr) (τ1 τ : Typ)
    (hE : HasType (τ1 :: bvs) Γ e τ)
    (hV : HasType bvs Γ v τ1) :
    HasType bvs Γ (Morph.Syntax.subst e v) τ := by
  match hE with
  | HasType.bvar_type _ _ n hLen =>
    -- subst' 0 (.bvar n) v = if n = 0 then lift 0 v else .bvar (n - 1)
    -- Case n=0: needs lift_preserves_type lemma (lift 0 v has same type as v)
    -- Case n>0: (τ1::bvs)[n] = bvs[n-1], uses bvar_type with shifted index
    sorry
  | HasType.fvar_type _ _ name τ hLookup =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.fvar_type _ _ name τ hLookup
  | HasType.lit_int _ _ n => simp [Morph.Syntax.subst, Morph.Syntax.subst']; exact HasType.lit_int _ _ _
  | HasType.lit_bool _ _ b => simp [Morph.Syntax.subst, Morph.Syntax.subst']; exact HasType.lit_bool _ _ _
  | HasType.lit_string _ _ s => simp [Morph.Syntax.subst, Morph.Syntax.subst']; exact HasType.lit_string _ _ _
  | HasType.lit_unit _ _ => simp [Morph.Syntax.subst, Morph.Syntax.subst']; exact HasType.lit_unit _ _
  | HasType.lit_pointer _ _ p => simp [Morph.Syntax.subst, Morph.Syntax.subst']; exact HasType.lit_pointer _ _ _
  | HasType.unop_not _ _ e' hE' =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.unop_not _ _ (Morph.Syntax.subst e' v) (HasType_subst bvs Γ e' v τ1 .boolType hE' hV)
  | HasType.unop_notb _ _ e' hE' =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.unop_notb _ _ (Morph.Syntax.subst e' v) (HasType_subst bvs Γ e' v τ1 .intType hE' hV)
  | HasType.binop_arith _ _ op e1 e2 hArith hE1 hE2 =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.binop_arith _ _ op _ _ hArith
      (HasType_subst bvs Γ e1 v τ1 .intType hE1 hV)
      (HasType_subst bvs Γ e2 v τ1 .intType hE2 hV)
  | HasType.binop_comp _ _ op e1 e2 hComp hE1 hE2 =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.binop_comp _ _ op _ _ hComp
      (HasType_subst bvs Γ e1 v τ1 .intType hE1 hV)
      (HasType_subst bvs Γ e2 v τ1 .intType hE2 hV)
  | HasType.binop_logic _ _ op e1 e2 hLogic hE1 hE2 =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.binop_logic _ _ op _ _ hLogic
      (HasType_subst bvs Γ e1 v τ1 .boolType hE1 hV)
      (HasType_subst bvs Γ e2 v τ1 .boolType hE2 hV)
  | HasType.binop_bitwise _ _ op e1 e2 hBit hE1 hE2 =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.binop_bitwise _ _ op _ _ hBit
      (HasType_subst bvs Γ e1 v τ1 .intType hE1 hV)
      (HasType_subst bvs Γ e2 v τ1 .intType hE2 hV)
  | HasType.lam_type _ _ n body paramTys retTy _hLen hBody =>
    -- subst' 0 (.lam n body) v = .lam n (subst' (1+n) body v)
    -- hBody : HasType (paramTys.reverse ++ τ1 :: bvs) Γ body retTy
    -- Need: HasType (paramTys.reverse ++ bvs) Γ (subst' (1+n) body v) retTy
    -- Requires generalized substitution lemma for depth > 0
    sorry
  | HasType.app_type _ _ fn args τs τ hFn hArgs =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.app_type _ _ _ (args.map (fun e => Morph.Syntax.subst e v)) τs τ
      (HasType_subst bvs Γ fn v τ1 (.functionType τs τ) hFn hV)
      (HasTypeAll_subst_all bvs Γ args v τ1 τs hArgs hV)
  | HasType.if_type _ _ c t f τ hC hT hF =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.if_type _ _ _ _ _ τ
      (HasType_subst bvs Γ c v τ1 .boolType hC hV)
      (HasType_subst bvs Γ t v τ1 τ hT hV)
      (HasType_subst bvs Γ f v τ1 τ hF hV)
  | HasType.let_type _ _ e1 e2 τ1' τ2 hE1 hE2 =>
    -- subst' 0 (.let_ e1 e2) v = .let_ (subst e1 v) (subst' 1 e2 v)
    -- Requires substitution at depth 1 for e2
    sorry
  | HasType.for_type _ _ s e body hS hE hBody =>
    -- subst' 0 (.forLoop s e body) v = .forLoop (subst s v) (subst e v) (body.map (subst' 1 · v))
    -- Requires substitution at depth 1 for body elements
    sorry
  | HasType.block_type _ _ exprs τs τ hAll =>
    simp [Morph.Syntax.subst, Morph.Syntax.subst']
    exact HasType.block_type _ _ (exprs.map (fun e => Morph.Syntax.subst e v)) τs τ
      (HasTypeAll_subst_all bvs Γ exprs v τ1 (τs ++ [τ]) hAll hV)

end

mutual

theorem preservation : forall {e e' : Expr} {τ : Typ} {bvs : List Typ} {Γ : TypEnv},
    HasType bvs Γ e τ -> Step e e' -> HasType bvs Γ e' τ := by
  intro e e' τ bvs Γ hType hStep
  cases hStep with
  | binop_left op e1 e1' e2 hStep1 =>
    cases hType with
    | binop_arith => exact HasType.binop_arith _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_comp => exact HasType.binop_comp _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_logic => exact HasType.binop_logic _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_bitwise => exact HasType.binop_bitwise _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | _ => contradiction
  | binop_right op v1 e2 e2' _ hStep2 =>
    cases hType with
    | binop_arith => exact HasType.binop_arith _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | binop_comp => exact HasType.binop_comp _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | binop_logic => exact HasType.binop_logic _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | binop_bitwise => exact HasType.binop_bitwise _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | _ => contradiction
  | binop_arith _ _ _ r hArith _ =>
    cases hType with
    | binop_arith => exact HasType.lit_int _ _ r
    | binop_comp => exfalso; exact sem_isArithOp_not_spec_isCompOp _ hArith (by assumption)
    | binop_logic => cases (by assumption)
    | binop_bitwise => exact HasType.lit_int _ _ r
    | _ => contradiction
  | binop_comp _ _ _ hComp =>
    cases hType with
    | binop_arith => exfalso; exact sem_isCompOp_not_spec_isArithOp _ hComp (by assumption)
    | binop_comp => exact HasType.lit_bool _ _ (evalCompOp _ _ _)
    | binop_logic => cases (by assumption)
    | binop_bitwise => exfalso; exact sem_isCompOp_not_spec_isBitwiseOp _ hComp (by assumption)
    | _ => contradiction
  | binop_logic _ _ _ _ _ =>
    cases hType with
    | binop_logic => exact HasType.lit_bool _ _ (by assumption)
    | binop_arith => cases (by assumption)
    | binop_comp => cases (by assumption)
    | binop_bitwise => cases (by assumption)
    | _ => contradiction
  | binop_bitwise _ _ _ r hBit _ =>
    cases hType with
    | binop_arith => exact HasType.lit_int _ _ r
    | binop_comp => exfalso; exact sem_isBitwiseOp_not_spec_isCompOp _ hBit (by assumption)
    | binop_logic => cases (by assumption)
    | binop_bitwise => exact HasType.lit_int _ _ r
    | _ => contradiction
  | binop_div_zero _ =>
    cases hType with
    | binop_arith => exact HasType.lit_int _ _ 0
    | _ => contradiction
  | binop_mod_zero _ =>
    cases hType with
    | binop_arith => exact HasType.lit_int _ _ 0
    | _ => contradiction
  | unop_step op e e' hStep1 =>
    cases hType with
    | unop_not _ _ _ hSub => exact HasType.unop_not _ _ _ (preservation hSub hStep1)
    | unop_notb _ _ _ hSub => exact HasType.unop_notb _ _ _ (preservation hSub hStep1)
    | _ => contradiction
  | unop_not b =>
    cases hType with
    | unop_not => exact HasType.lit_bool _ _ (!b)
    | _ => contradiction
  | unop_notb n =>
    cases hType with
    | unop_notb => exact HasType.lit_int _ _ (-n - 1)
    | _ => contradiction
  | if_cond c c' t f hStep1 =>
    cases hType with
    | if_type _ _ _ _ _ _ hC hT hF => exact HasType.if_type _ _ c' t f τ (preservation hC hStep1) hT hF
    | _ => contradiction
  | if_true _ _ =>
    cases hType with
    | if_type _ _ _ _ _ _ hC hT hF => exact hT
    | _ => contradiction
  | if_false _ _ =>
    cases hType with
    | if_type _ _ _ _ _ _ hC hT hF => exact hF
    | _ => contradiction
  | let_step e1 e1' e2 hStep1 =>
    cases hType with
    | let_type _ _ _ _ _ _ hE1 hE2 => exact HasType.let_type _ _ e1' e2 (by assumption) τ (preservation hE1 hStep1) hE2
    | _ => contradiction
  | let_subst e1 e2 hVal =>
    cases hType with
    | let_type _ _ _ _ τ1' _ hE1 hE2 => exact HasType_subst bvs Γ e2 e1 τ1' τ hE2 hE1
    | _ => contradiction
  | for_start s s' e body hStep1 =>
    cases hType with
    | for_type _ _ _ _ _ hS hE hBody => exact HasType.for_type _ _ s' e body (preservation hS hStep1) hE hBody
    | _ => contradiction
  | for_end s e e' body _ hStep2 =>
    cases hType with
    | for_type _ _ _ _ _ hS hE hBody => exact HasType.for_type _ _ (.lit s) e' body hS (preservation hE hStep2) hBody
    | _ => contradiction
  | for_exec n m body _ =>
    cases hType with
    | for_type _ _ _ _ _ hS hE hBody =>
      -- After executing one loop iteration, we produce:
      -- let n = n in block (body ++ [forLoop (n+1) m body])
      -- The body needs simultaneous substitution of .lit (.int n) for index 1
      -- (index 0 is the loop counter .intType, index 1 is the bound var being .intType)
      -- This requires the simultaneous substitution lemma (substAll)
      sorry
    | _ => contradiction
  | for_done _ _ _ _ =>
    cases hType with
    | for_type _ _ => exact HasType.lit_unit _ _
    | _ => contradiction
  | block_head e' e'' rest hStep1 =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil =>
        exact HasType.block_type _ _ (e'' :: rest) [] τ
          (HasTypeAll.cons _ _ _ _ _ _ (preservation (HasTypeAll_cons_head hAll) hStep1) (HasTypeAll_cons_tail hAll))
      | cons τ' τs' =>
        exact HasType.block_type _ _ (e'' :: rest) (τ' :: τs') τ
          (HasTypeAll.cons _ _ _ _ _ _ (preservation (HasTypeAll_cons_head hAll) hStep1) (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_singleton v _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_lam_singleton n body =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_pop e_val head rest _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil =>
        exfalso
        have h := HasTypeAll_length _ _ _ _ hAll
        simp only [List.length_cons, List.length_append, List.length_nil] at h
        omega
      | cons τ' τs' =>
        exact HasType.block_type _ _ (head :: rest) τs' τ (HasTypeAll_cons_tail hAll)
    | _ => contradiction
  | app_fn fn fn' args hs =>
    match hType with
    | HasType.app_type _ _ _ _ τs τ hFn hArgs =>
      exact HasType.app_type _ _ fn' args τs τ (preservation hFn hs) hArgs
  | app_arg fn a a' rest _ hs =>
    match hType with
    | HasType.app_type _ _ _ _ τs _ hFn hAll =>
      cases τs with
      | nil =>
        exfalso
        have hLen := HasTypeAll_length _ _ _ _ hAll
        simp only [List.length_cons, List.length_nil] at hLen
        omega
      | cons τhead τtail =>
        exact HasType.app_type _ _ fn (a' :: rest) (τhead :: τtail) τ hFn
          (HasTypeAll.cons _ _ _ _ _ _ (preservation (HasTypeAll_cons_head hAll) hs) (HasTypeAll_cons_tail hAll))
  | app_lam n body args hLen =>
    match hType with
    | HasType.app_type _ _ _ _ _ _ hFn hAll =>
      cases hFn with
      | lam_type _ _ _ _ paramTys retTy hBodyP hLen' =>
        -- body has type retTy in (paramTys.reverse ++ bvs)
        -- We need to show substAll args.reverse body has type retTy in bvs
        -- This requires simultaneous substitution lemma
        sorry
        -- The simultaneous substitution lemma for substAll' needs to be proven:
        -- If HasType (paramTys.reverse ++ bvs) Γ body retTy
        -- and HasTypeAll bvs Γ args paramTys
        -- then HasType bvs Γ (substAll args.reverse body) retTy
        -- This is provable by induction on hBodyP, using the fact that
        -- args.reverse provides types for bvar 0..n-1

end

end Morph.Proofs.TypeSoundness
