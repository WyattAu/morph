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

private theorem getElem_cons_succ_of_pos {α : Type _} {a : α} {as : List α} {k : Nat}
    (hk1 : k ≥ 1) (hk_as : k < (a :: as).length) (hk_pred : k - 1 < as.length) :
    (a :: as)[k]'hk_as = as[k - 1]'hk_pred := by
  cases k with
  | zero => omega
  | succ n => simp [List.getElem_cons_succ]

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
## Lift-Zero Preserves Type for Values

`lift 0 e` has the same type as `e`. This follows from `lift_zero_eq : lift 0 e = e`.
-/

private theorem lift_zero_preserves_type (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ)
    (h : HasType bvs Γ e τ) : HasType bvs Γ (lift 0 e) τ := by
  rw [lift_zero_eq]; exact h

private theorem HasTypeAll_lift_zero (bvs : List Typ) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (h : HasTypeAll bvs Γ es τs) : HasTypeAll bvs Γ (es.map (lift 0)) τs := by
  rw [show es.map (lift 0) = es from liftUnder_zero_eq_list 0 es]; exact h

/-!
## Substitution Lemma (de Bruijn)

With de Bruijn indices, the substitution lemma is dramatically simpler.
No freshness predicate is needed — capture-avoidance is guaranteed by construction.

We prove the generalized form: substitution at arbitrary depth `pfx.length`.
`HasType_subst_depth`: If `e` has type `τ` in context `pfx ++ τ1 :: bvs`, and `v`
has type `τ1` in `bvs`, then `subst' pfx.length e v` has type `τ` in `pfx ++ bvs`.

The depth-0 specialization is `HasType_subst` (substituting the outermost binder).
-/

mutual

private theorem HasTypeAll_subst_depth (pfx : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (es : List Expr) (v : Expr) (τ1 : Typ) (τs : List Typ)
    (hArgs : HasTypeAll (pfx ++ τ1 :: bvs) Γ es τs)
    (hV : HasType bvs Γ v τ1) :
    HasTypeAll (pfx ++ bvs) Γ (es.map (fun e => subst' pfx.length e v)) τs := by
  match hArgs with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _
      (HasType_subst_depth pfx bvs Γ e v τ1 τ hE hV)
      (HasTypeAll_subst_depth pfx bvs Γ es' v τ1 τs' hRest hV)

private theorem HasType_subst_depth (pfx : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (e v : Expr) (τ1 τ : Typ)
    (hE : HasType (pfx ++ τ1 :: bvs) Γ e τ)
    (hV : HasType bvs Γ v τ1) :
    HasType (pfx ++ bvs) Γ (subst' pfx.length e v) τ := by
  match hE with
  | .bvar_type _ _ n hLen =>
    unfold subst'
    split
    · -- n < pfx.length: unchanged .bvar n
      next hNlt =>
      have hLen' : n < (pfx ++ bvs).length := by simp [List.length_append]; omega
      have hEq : (pfx ++ τ1 :: bvs)[n] = (pfx ++ bvs)[n] := by
        have h1 := @List.getElem_append_left Typ n pfx (τ1 :: bvs) hNlt hLen
        have h2 := @List.getElem_append_left Typ n pfx bvs hNlt hLen'
        exact h1.trans h2.symm
      exact hEq ▸ HasType.bvar_type _ _ n hLen'
    · split
      · -- n = pfx.length: substitute with lift pfx.length v
        next hEq =>
        subst hEq
        have hIdx : (pfx ++ τ1 :: bvs)[pfx.length] = τ1 := by
          rw [List.getElem_append_right (by omega)]; simp
        rw [hIdx]
        exact weaken_many_at_depth [] pfx bvs Γ v τ1 hV
      · -- n > pfx.length: shift to .bvar (n - 1)
        next hNeq =>
        have hNMinus1 : n - 1 < (pfx ++ bvs).length := by
          simp [List.length_append] at hLen ⊢; omega
        have hTypeEq : (pfx ++ τ1 :: bvs)[n] = (pfx ++ bvs)[n - 1] := by
          have hPfxLeN : pfx.length ≤ n := by omega
          have hPfxLeN1 : pfx.length ≤ n - 1 := by omega
          have h1 := @List.getElem_append_right Typ pfx (τ1 :: bvs) n hPfxLeN hLen
          have h2 := @List.getElem_append_right Typ pfx bvs (n - 1) hPfxLeN1 hNMinus1
          have hKPos : n - pfx.length ≥ 1 := by omega
          have hKLt : n - pfx.length < (τ1 :: bvs).length := by
            have : (τ1 :: bvs).length = bvs.length + 1 := rfl
            simp [List.length_append] at hLen; omega
          have hKPred : n - pfx.length - 1 < bvs.length := by
            simp [List.length_append] at hLen; omega
          have hSucc := getElem_cons_succ_of_pos hKPos hKLt hKPred
          calc (pfx ++ τ1 :: bvs)[n]
              = (τ1 :: bvs)[n - pfx.length] := h1
            _ = bvs[n - pfx.length - 1] := hSucc
            _ = bvs[n - 1 - pfx.length] := by congr 1; omega
            _ = (pfx ++ bvs)[n - 1] := h2.symm
        exact hTypeEq ▸ HasType.bvar_type _ _ (n - 1) hNMinus1
  | .fvar_type _ _ name τ hLookup =>
    simp only [subst']; exact HasType.fvar_type _ _ name τ hLookup
  | .lit_int _ _ _ => simp only [subst']; exact HasType.lit_int _ _ _
  | .lit_bool _ _ _ => simp only [subst']; exact HasType.lit_bool _ _ _
  | .lit_string _ _ _ => simp only [subst']; exact HasType.lit_string _ _ _
  | .lit_unit _ _ => simp only [subst']; exact HasType.lit_unit _ _
  | .lit_pointer _ _ _ => simp only [subst']; exact HasType.lit_pointer _ _ _
  | .unop_not _ _ e' hE' =>
    simp only [subst']
    exact HasType.unop_not _ _ _ (HasType_subst_depth pfx bvs Γ e' v τ1 .boolType hE' hV)
  | .unop_notb _ _ e' hE' =>
    simp only [subst']
    exact HasType.unop_notb _ _ _ (HasType_subst_depth pfx bvs Γ e' v τ1 .intType hE' hV)
  | .binop_arith _ _ op e1 e2 hArith hE1 hE2 =>
    simp only [subst']
    exact HasType.binop_arith _ _ op _ _ hArith
      (HasType_subst_depth pfx bvs Γ e1 v τ1 .intType hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 .intType hE2 hV)
  | .binop_comp _ _ op e1 e2 hComp hE1 hE2 =>
    simp only [subst']
    exact HasType.binop_comp _ _ op _ _ hComp
      (HasType_subst_depth pfx bvs Γ e1 v τ1 .intType hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 .intType hE2 hV)
  | .binop_logic _ _ op e1 e2 hLogic hE1 hE2 =>
    simp only [subst']
    exact HasType.binop_logic _ _ op _ _ hLogic
      (HasType_subst_depth pfx bvs Γ e1 v τ1 .boolType hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 .boolType hE2 hV)
  | .binop_bitwise _ _ op e1 e2 hBit hE1 hE2 =>
    simp only [subst']
    exact HasType.binop_bitwise _ _ op _ _ hBit
      (HasType_subst_depth pfx bvs Γ e1 v τ1 .intType hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 .intType hE2 hV)
  | .lam_type _ _ n body paramTys retTy hLen hBody =>
    -- subst' pfx.length (.lam n body) v = .lam n (subst' (pfx.length + n) body v)
    -- Body context: (paramTys.reverse ++ pfx) ++ τ1 :: bvs
    -- New prefix: paramTys.reverse ++ pfx
    -- Subst depth: (paramTys.reverse ++ pfx).length = n + pfx.length
    simp only [subst']
    have hBody' : HasType ((paramTys.reverse ++ pfx) ++ τ1 :: bvs) Γ body retTy := by
      rw [List.append_assoc]; exact hBody
    have hResult := HasType_subst_depth (paramTys.reverse ++ pfx) bvs Γ body v τ1 retTy hBody' hV
    simp only [List.length_append] at hResult
    have hLenEq : paramTys.reverse.length = n := by simp [← hLen]
    rw [hLenEq, Nat.add_comm n pfx.length] at hResult
    rw [List.append_assoc] at hResult
    exact HasType.lam_type (pfx ++ bvs) Γ n (subst' (pfx.length + n) body v) paramTys retTy hLen hResult
  | .app_type _ _ fn args τs τ hFn hArgs =>
    simp only [subst']
    exact HasType.app_type _ _ _ _ τs τ
      (HasType_subst_depth pfx bvs Γ fn v τ1 (.functionType τs τ) hFn hV)
      (HasTypeAll_subst_depth pfx bvs Γ args v τ1 τs hArgs hV)
  | .if_type _ _ c t f τ hC hT hF =>
    simp only [subst']
    exact HasType.if_type _ _ _ _ _ τ
      (HasType_subst_depth pfx bvs Γ c v τ1 .boolType hC hV)
      (HasType_subst_depth pfx bvs Γ t v τ1 τ hT hV)
      (HasType_subst_depth pfx bvs Γ f v τ1 τ hF hV)
  | .let_type _ _ e1 e2 τ1' τ2' hE1 hE2 =>
    -- subst' pfx (.let_ e1 e2) v = .let_ (subst' pfx e1 v) (subst' (pfx+1) e2 v)
    -- e2 context: [τ1'] ++ pfx ++ τ1 :: bvs = (τ1' :: pfx) ++ τ1 :: bvs
    simp only [subst']
    have hE2' : HasType (τ1' :: pfx ++ τ1 :: bvs) Γ e2 τ2' := by
      show HasType (τ1' :: pfx ++ τ1 :: bvs) Γ e2 τ2'; exact hE2
    have hResult := HasType_subst_depth (τ1' :: pfx) bvs Γ e2 v τ1 τ2' hE2' hV
    -- Depth: (τ1' :: pfx).length = 1 + pfx.length; simp normalizes to pfx.length + 1
    simp only [List.length_cons, List.length_nil, List.length_append] at hResult
    -- hResult : HasType (τ1' :: (pfx ++ bvs)) Γ (subst' (pfx.length + 1) e2 v) τ2'
    exact HasType.let_type (pfx ++ bvs) Γ (subst' pfx.length e1 v) (subst' (pfx.length + 1) e2 v) τ1' τ2'
      (HasType_subst_depth pfx bvs Γ e1 v τ1 τ1' hE1 hV)
      hResult
  | .for_type _ _ s e body hS hE hBody =>
    -- body context: [.intType] ++ pfx ++ τ1 :: bvs = (.intType :: pfx) ++ τ1 :: bvs
    simp only [subst']
    have hBody' : HasTypeAll (.intType :: pfx ++ τ1 :: bvs) Γ body [.unitType] := by
      show HasTypeAll (.intType :: pfx ++ τ1 :: bvs) Γ body [.unitType]; exact hBody
    have hBodyResult := HasTypeAll_subst_depth (.intType :: pfx) bvs Γ body v τ1 [.unitType] hBody' hV
    -- simp already normalizes the length to pfx.length + 1
    simp only [List.length_cons, List.length_nil] at hBodyResult
    exact HasType.for_type (pfx ++ bvs) Γ (subst' pfx.length s v) (subst' pfx.length e v) (List.map (fun x => subst' (pfx.length + 1) x v) body)
      (HasType_subst_depth pfx bvs Γ s v τ1 .intType hS hV)
      (HasType_subst_depth pfx bvs Γ e v τ1 .intType hE hV)
      hBodyResult
  | .block_type _ _ exprs τs τ hAll =>
    simp only [subst']
    exact HasType.block_type _ _ _ τs τ
      (HasTypeAll_subst_depth pfx bvs Γ exprs v τ1 (τs ++ [τ]) hAll hV)

end

-- Depth-0 specialization: HasType_subst
private theorem HasType_subst (bvs : List Typ) (Γ : TypEnv) (e v : Expr) (τ1 τ : Typ)
    (hE : HasType (τ1 :: bvs) Γ e τ)
    (hV : HasType bvs Γ v τ1) :
    HasType bvs Γ (Morph.Syntax.subst e v) τ :=
  HasType_subst_depth [] bvs Γ e v τ1 τ (by exact hE) hV

private theorem HasTypeAll_subst_all (bvs : List Typ) (Γ : TypEnv) (es : List Expr)
    (v : Expr) (τ1 : Typ) (τs : List Typ)
    (hArgs : HasTypeAll (τ1 :: bvs) Γ es τs)
    (hV : HasType bvs Γ v τ1) :
    HasTypeAll bvs Γ (es.map (fun e => Morph.Syntax.subst e v)) τs :=
  HasTypeAll_subst_depth [] bvs Γ es v τ1 τs (by exact hArgs) hV

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
