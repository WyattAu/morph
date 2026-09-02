/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Store
import Morph.Specs.TypeSystem.Spec
import Morph.Specs.TypeSystem.Lemmas
import Morph.Proofs.TypeSoundness.ExprDepth

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

private theorem sem_isArithOp_not_spec_isPtrArithOp (op : Operator) :
    Morph.Semantics.isArithOp op -> ¬Morph.Specs.TypeSystem.isPtrArithOp op := by
  intro ha hp
  cases op <;> simp [Morph.Semantics.isArithOp, Morph.Specs.TypeSystem.isPtrArithOp] at * <;> contradiction

private theorem sem_isCompOp_not_spec_isPtrArithOp (op : Operator) :
    Morph.Semantics.isCompOp op -> ¬Morph.Specs.TypeSystem.isPtrArithOp op := by
  intro hc hp
  cases op <;> simp [Morph.Semantics.isCompOp, Morph.Specs.TypeSystem.isPtrArithOp] at * <;> contradiction

private theorem sem_isLogicOp_not_spec_isPtrArithOp (op : Operator) :
    Morph.Semantics.isLogicOp op -> ¬Morph.Specs.TypeSystem.isPtrArithOp op := by
  intro hl hp
  cases op <;> simp [Morph.Semantics.isLogicOp, Morph.Specs.TypeSystem.isPtrArithOp] at * <;> contradiction

private theorem sem_isBitwiseOp_not_spec_isPtrArithOp (op : Operator) :
    Morph.Semantics.isBitwiseOp op -> ¬Morph.Specs.TypeSystem.isPtrArithOp op := by
  intro hb hp
  cases op <;> simp [Morph.Semantics.isBitwiseOp, Morph.Specs.TypeSystem.isPtrArithOp] at * <;> contradiction

/-!
## Lift-Zero Preserves Type for Values

`lift 0 e` has the same type as `e`. This follows from `lift_zero_eq : lift 0 e = e`.
-/

private theorem HasTypeAll_replicate (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ)
    (h : HasType bvs Γ e τ) : ∀ n, HasTypeAll bvs Γ (List.replicate n e) (List.replicate n τ)
  | 0 => by simp; constructor
  | n + 1 => by simp [List.replicate_succ]; constructor; exact h; exact HasTypeAll_replicate bvs Γ e τ h n

private theorem list_reverse_replicate (α : Type _) (a : α) (n : Nat) :
    (List.replicate n a).reverse = List.replicate n a := by
  induction n with
  | zero => simp
  | succ n IH =>
    simp only [List.replicate_succ, List.reverse_cons]
    rw [IH]
    induction n with
    | zero => simp
    | succ n IH2 => simp [List.replicate_succ, List.cons_append, IH2]

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
   | .lit_float _ _ _ _ => simp only [subst']; exact HasType.lit_float _ _ _ _
   | .lit_int_width _ _ _ _ => simp only [subst']; exact HasType.lit_int_width _ _ _ _
   | .lit_some _ _ _ τ => simp only [subst']; exact HasType.lit_some _ _ _ τ
   | .lit_none _ _ τ => simp only [subst']; exact HasType.lit_none _ _ τ
   | .lit_ok _ _ _ τ_ok τ_err => simp only [subst']; exact HasType.lit_ok _ _ _ τ_ok τ_err
   | .lit_err _ _ _ τ_err τ_ok => simp only [subst']; exact HasType.lit_err _ _ _ τ_err τ_ok
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
  | .binop_ptr_arith _ _ op e1 e2 hPtr hE1 hE2 =>
    simp only [subst']
    exact HasType.binop_ptr_arith _ _ op _ _ hPtr
      (HasType_subst_depth pfx bvs Γ e1 v τ1 .pointerType hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 .intType hE2 hV)
  | .binop_ptr_load _ _ e1 e2 hE1 hE2 =>
    simp only [subst']
    exact HasType.binop_ptr_load _ _ _ _
      (HasType_subst_depth pfx bvs Γ e1 v τ1 .pointerType hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 .unitType hE2 hV)
  | .binop_ptr_store _ _ e1 e2 hE1 hE2 =>
    simp only [subst']
    exact HasType.binop_ptr_store _ _ _ _
      (HasType_subst_depth pfx bvs Γ e1 v τ1 .pointerType hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 .intType hE2 hV)
  | .binop_string_concat _ _ op e1 e2 hOp hE1 hE2 =>
    simp only [subst']
    exact HasType.binop_string_concat (pfx ++ bvs) Γ op
      (subst' pfx.length e1 v) (subst' pfx.length e2 v)
      hOp
      (HasType_subst_depth pfx bvs Γ e1 v τ1 .stringType hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 .stringType hE2 hV)
  | .lam_type _ _ n body paramTys retTy hLen hBody =>
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
    simp only [subst']
    have hE2' : HasType (τ1' :: pfx ++ τ1 :: bvs) Γ e2 τ2' := by
      show HasType (τ1' :: pfx ++ τ1 :: bvs) Γ e2 τ2'; exact hE2
    have hResult := HasType_subst_depth (τ1' :: pfx) bvs Γ e2 v τ1 τ2' hE2' hV
    simp only [List.length_cons] at hResult
    exact HasType.let_type (pfx ++ bvs) Γ (subst' pfx.length e1 v) (subst' (pfx.length + 1) e2 v) τ1' τ2'
      (HasType_subst_depth pfx bvs Γ e1 v τ1 τ1' hE1 hV)
      hResult
  | .for_type _ _ s e body hS hE hBody =>
    simp only [subst']
    have hBody' : HasTypeAll (.intType :: pfx ++ τ1 :: bvs) Γ body [.unitType] := by
      show HasTypeAll (.intType :: pfx ++ τ1 :: bvs) Γ body [.unitType]; exact hBody
    have hBodyResult := HasTypeAll_subst_depth (.intType :: pfx) bvs Γ body v τ1 [.unitType] hBody' hV
    simp only [List.length_cons] at hBodyResult
    exact HasType.for_type (pfx ++ bvs) Γ (subst' pfx.length s v) (subst' pfx.length e v) (List.map (fun x => subst' (pfx.length + 1) x v) body)
      (HasType_subst_depth pfx bvs Γ s v τ1 .intType hS hV)
      (HasType_subst_depth pfx bvs Γ e v τ1 .intType hE hV)
      hBodyResult
   | .pipe_type _ _ e f τ_arg _ hE hF =>
    simp only [subst']
    exact HasType.pipe_type _ _ (subst' pfx.length e v) (subst' pfx.length f v) τ_arg _
      (HasType_subst_depth pfx bvs Γ e v τ1 τ_arg hE hV)
      (HasType_subst_depth pfx bvs Γ f v τ1 (.functionType [τ_arg] _ ) hF hV)
   | .typeAsc_type _ _ e τ hE =>
    simp only [subst']
    exact HasType.typeAsc_type _ _ (subst' pfx.length e v) τ
      (HasType_subst_depth pfx bvs Γ e v τ1 τ hE hV)
   | .some_type _ _ e τ_inner hE =>
    simp only [subst']
    exact HasType.some_type _ _ (subst' pfx.length e v) τ_inner
      (HasType_subst_depth pfx bvs Γ e v τ1 τ_inner hE hV)
   | .none_type _ _ τ =>
    simp only [subst']; exact HasType.none_type _ _ τ
   | .ok_type _ _ e τ_ok τ_err hE =>
    simp only [subst']
    exact HasType.ok_type _ _ (subst' pfx.length e v) τ_ok τ_err
      (HasType_subst_depth pfx bvs Γ e v τ1 τ_ok hE hV)
   | .err_type _ _ e τ_err τ_ok hE =>
    simp only [subst']
    exact HasType.err_type _ _ (subst' pfx.length e v) τ_err τ_ok
      (HasType_subst_depth pfx bvs Γ e v τ1 τ_err hE hV)
   | .null_coalesce_type _ _ e1 e2 τ hE1 hE2 =>
    simp only [subst']
    exact HasType.null_coalesce_type _ _ (subst' pfx.length e1 v) (subst' pfx.length e2 v) τ
      (HasType_subst_depth pfx bvs Γ e1 v τ1 (.optionType τ) hE1 hV)
      (HasType_subst_depth pfx bvs Γ e2 v τ1 (.optionType τ) hE2 hV)
   | .tuple_type _ _ elems tys hTys =>
     simp only [subst']
     exact HasType.tuple_type _ _ (elems.map (subst' pfx.length · v)) tys
       (HasTypeAll_subst_depth pfx bvs Γ elems v τ1 tys hTys hV)
   | .field_access_type _ _ e fname sname fields τ hE hField =>
     simp only [subst']
     exact HasType.field_access_type (pfx ++ bvs) Γ (subst' pfx.length e v) fname sname fields τ
       (HasType_subst_depth pfx bvs Γ e v τ1 (.structType sname fields) hE hV)
       hField
   | .match_type _ _ scrut arms ts tr hScrut hArms =>
      simp only [subst']
      exact HasType.match_type _ _ (subst' pfx.length scrut v) (substArms pfx.length v arms) _ _
        (HasType_subst_depth pfx bvs Γ scrut v τ1 ts hScrut hV)
        (ArmsTyped_subst_depth pfx bvs Γ arms v τ1 ts tr hArms hV)
   | .arrayLit_type _ _ elems τ' n hElems hLen hn =>
     simp only [subst']
     have hLen' : n = (List.map (fun e => subst' pfx.length e v) elems).length := by
       simp [List.length_map, hLen]
     exact HasType.arrayLit_type (pfx ++ bvs) Γ (elems.map (fun e => subst' pfx.length e v)) τ' n
       (HasTypeAll_subst_depth pfx bvs Γ elems v τ1 (List.replicate n τ') hElems hV)
       hLen' (by omega)
   | .arrayIndex_type _ _ arr idx τ' n hArr hIdx =>
     simp only [subst']
     exact HasType.arrayIndex_type (pfx ++ bvs) Γ (subst' pfx.length arr v) (subst' pfx.length idx v) τ' n
       (HasType_subst_depth pfx bvs Γ arr v τ1 (.arrayType τ' n) hArr hV)
       (HasType_subst_depth pfx bvs Γ idx v τ1 .intType hIdx hV)
   | .block_type _ _ exprs τs τ hAll =>
    simp only [subst']
    exact HasType.block_type _ _ _ τs τ
      (HasTypeAll_subst_depth pfx bvs Γ exprs v τ1 (τs ++ [τ]) hAll hV)
   | .refCreate_type _ _ e cap τ hE =>
     simp only [subst']
     exact HasType.refCreate_type _ _ _ cap τ (HasType_subst_depth pfx bvs Γ e v τ1 τ hE hV)
   | .refLoad_type _ _ e cap τ hE =>
     simp only [subst']
     exact HasType.refLoad_type _ _ _ cap τ (HasType_subst_depth pfx bvs Γ e v τ1 (.refType cap τ) hE hV)
   | .refStore_type _ _ e v' cap τ hE hV' hCap =>
     simp only [subst']
     exact HasType.refStore_type _ _ _ _ cap τ
       (HasType_subst_depth pfx bvs Γ e v τ1 (.refType cap τ) hE hV)
       (HasType_subst_depth pfx bvs Γ v' v τ1 τ hV' hV)
       hCap
   | .refFree_type _ _ e τ hE =>
     simp only [subst']
     exact HasType.refFree_type _ _ _ τ (HasType_subst_depth pfx bvs Γ e v τ1 (.refType .iso τ) hE hV)

private theorem ArmsTyped_subst_depth (pfx : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (arms : List (List String × Expr)) (v : Expr) (τ1 ts tr : Typ)
    (hArms : ArmsTyped (pfx ++ τ1 :: bvs) Γ ts arms tr)
    (hV : HasType bvs Γ v τ1) :
    ArmsTyped (pfx ++ bvs) Γ ts (substArms pfx.length v arms) tr := by
  cases hArms with
  | nil => simp only [substArms]; constructor
  | cons bvs Γ vars body rest ts tr hBody hRest =>
    simp only [substArms]
    constructor
    · have hBody' : HasType ((List.replicate vars.length ts ++ pfx) ++ τ1 :: bvs) Γ body tr := by
        show HasType ((List.replicate vars.length ts ++ pfx) ++ τ1 :: bvs) Γ body tr
        rw [List.append_assoc]; exact hBody
      have hResult := HasType_subst_depth (List.replicate vars.length ts ++ pfx) bvs Γ body v τ1 tr hBody' hV
      simp only [List.length_append, List.length_replicate] at hResult
      show HasType (List.replicate vars.length ts ++ (pfx ++ bvs)) Γ
          (subst' (pfx.length + vars.length) body v) tr
      rw [← List.append_assoc, Nat.add_comm]; exact hResult
    · exact ArmsTyped_subst_depth pfx bvs Γ rest v τ1 ts tr hRest hV

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

/-!
## Simultaneous Substitution Preserves Types

Direct mutual induction on `HasType`/`HasTypeAll` for `substAll'`.
`substAll'` is genuinely simultaneous (not decomposable into sequential `subst'`).

We prove the generalized form with a prefix `pfx` that tracks binders crossed.
When entering a `lam`/`let`/`for` binder, the prefix grows and the substitution
depth increases accordingly.
-/

mutual

private theorem HasTypeAll_substAll (pfx σs : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (vs : List Expr) (es : List Expr) (τs : List Typ)
    (hEs : HasTypeAll (pfx ++ σs ++ bvs) Γ es τs)
    (hVs : HasTypeAll bvs Γ vs σs.reverse)
    (hLen : vs.length = σs.length) :
    HasTypeAll (pfx ++ bvs) Γ (es.map (substAll' pfx.length vs.reverse)) τs := by
  match hEs with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _
      (HasType_substAll pfx σs bvs Γ vs e τ hE hVs hLen)
      (HasTypeAll_substAll pfx σs bvs Γ vs es' τs' hRest hVs hLen)

private theorem HasType_substAll (pfx σs : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (vs : List Expr) (e : Expr) (τ : Typ)
    (hE : HasType (pfx ++ σs ++ bvs) Γ e τ)
    (hVs : HasTypeAll bvs Γ vs σs.reverse)
    (hLen : vs.length = σs.length) :
    HasType (pfx ++ bvs) Γ (substAll' pfx.length vs.reverse e) τ := by
  match hE with
  | .bvar_type _ _ n hLenCtx =>
    unfold substAll'
    split
    · next hNlt =>
      have h1 := @List.length_append Typ pfx σs
      have h2 := @List.length_append Typ (pfx ++ σs) bvs
      have h3 := @List.length_append Typ pfx bvs
      have hLen' : n < (pfx ++ bvs).length := by have := h1; have := h2; have := h3; omega
      have hLenPfxσs' : n < (pfx ++ σs).length := by have := h1; have := h2; omega
      have hEq : (pfx ++ σs ++ bvs)[n] = (pfx ++ bvs)[n] := by
        calc (pfx ++ σs ++ bvs)[n]
            = (pfx ++ σs)[n] := @List.getElem_append_left Typ n (pfx ++ σs) bvs hLenPfxσs' hLenCtx
          _ = pfx[n] := @List.getElem_append_left Typ n pfx σs hNlt hLenPfxσs'
          _ = (pfx ++ bvs)[n] := (@List.getElem_append_left Typ n pfx bvs hNlt hLen').symm
      exact hEq ▸ HasType.bvar_type _ _ n hLen'
    · split
      · next hIn =>
        have hRevLen : vs.reverse.length = σs.length := by
          have := @List.length_reverse Expr vs; omega
        have h1 := @List.length_append Typ pfx σs
        have h2 := @List.length_append Typ σs bvs
        have h3 := @List.length_append Typ (pfx ++ σs) bvs
        have hNLePfx : pfx.length ≤ n := by have := hLenCtx; have := h1; have := h3; omega
        have hNltσs : n - pfx.length < σs.length := by have := h1; have := h3; have := hLenCtx; omega
        have hNltVs : n - pfx.length < vs.reverse.length := by omega
        have hNlt2 : n - pfx.length < (σs ++ bvs).length := by have := h1; have := h2; have := h3; omega
        have hVsRev : HasTypeAll bvs Γ vs.reverse σs := by
          have h := HasTypeAll_reverse bvs Γ vs σs.reverse hVs
          exact (List.reverse_reverse σs) ▸ h
        have hVal : HasType bvs Γ (vs.reverse[n - pfx.length]) σs[n - pfx.length] :=
          HasTypeAll_getElem bvs Γ vs.reverse σs (n - pfx.length) hVsRev hNltVs hNltσs
        have hIdx : (pfx ++ σs ++ bvs)[n] = σs[n - pfx.length] := by
          have hLenPfxσs := @List.length_append Typ pfx σs
          have hLenσsBvs := @List.length_append Typ σs bvs
          have hLenPfxσsBvs := @List.length_append Typ (pfx ++ σs) bvs
          have hLenPfxσsBvs2 := @List.length_append Typ pfx (σs ++ bvs)
          have hNltσsBvs : n - pfx.length < (σs ++ bvs).length := by
            have := hLenPfxσs; have := hLenPfxσsBvs; have := hLenσsBvs; have := hLenPfxσsBvs2; omega
          have hNltσs' : n - pfx.length < σs.length := hNltσs
          have hLenCtx2 : n < (pfx ++ (σs ++ bvs)).length := by
            have := hLenPfxσs; have := hLenPfxσsBvs; have := hLenPfxσsBvs2; omega
          have hStep1 := @List.getElem_append_right Typ pfx (σs ++ bvs) n hNLePfx hLenCtx2
          have hStep2 := @List.getElem_append_left Typ (n - pfx.length) σs bvs hNltσs' hNltσsBvs
          have hAssoc : pfx ++ σs ++ bvs = pfx ++ (σs ++ bvs) := List.append_assoc pfx σs bvs
          have hRw := @List.getElem_of_eq Typ (pfx ++ σs ++ bvs) (pfx ++ (σs ++ bvs)) hAssoc n hLenCtx
          exact hRw.trans (hStep1.trans hStep2)
        have hWeakened := weaken_many_at_depth [] pfx bvs Γ
          (vs.reverse[n - pfx.length]) σs[n - pfx.length] hVal
        exact hIdx.symm ▸ hWeakened
      · next hGe =>
        have hRevLen : vs.reverse.length = σs.length := by
          have := @List.length_reverse Expr vs; omega
        have h1 := @List.length_append Typ pfx σs
        have h2 := @List.length_append Typ (pfx ++ σs) bvs
        have h3 := @List.length_append Typ pfx bvs
        have hNLe2 : (pfx ++ σs).length ≤ n := by have := h1; have := h2; omega
        have hNFreeBvs : n - pfx.length - σs.length < bvs.length := by have := h1; have := h2; omega
        have hIdx : (pfx ++ σs ++ bvs)[n] = bvs[n - pfx.length - σs.length] := by
          calc (pfx ++ σs ++ bvs)[n]
              = bvs[n - (pfx ++ σs).length] :=
                @List.getElem_append_right Typ (pfx ++ σs) bvs n hNLe2 hLenCtx
            _ = bvs[n - pfx.length - σs.length] := by congr 1; have := h1; omega
        have hResLen : n - vs.reverse.length < (pfx ++ bvs).length := by
          have := h1; have := h2; have := h3; have := hRevLen; have := hLen; have := hGe; omega
        have hResIdx : (pfx ++ bvs)[n - vs.reverse.length] = bvs[n - pfx.length - σs.length] := by
          have hNLeRes : pfx.length ≤ n - vs.reverse.length := by
            have := hRevLen; have := hLen; have := hGe; omega
          have hLenCtx' : n - vs.reverse.length < (pfx ++ bvs).length := by
            have := h1; have := h2; have := h3; have := hRevLen; have := hLen; have := hGe; omega
          have h3 := @List.getElem_append_right Typ pfx bvs (n - vs.reverse.length) hNLeRes hLenCtx'
          calc (pfx ++ bvs)[n - vs.reverse.length]
              = bvs[n - vs.reverse.length - pfx.length] := h3
            _ = bvs[n - pfx.length - σs.length] := by
              have := hRevLen; have := hLen; have := hGe
              congr 1; omega
        have hResType : (pfx ++ bvs)[n - vs.reverse.length] = (pfx ++ σs ++ bvs)[n] :=
          hResIdx.trans hIdx.symm
        exact hResType.symm ▸ HasType.bvar_type (pfx ++ bvs) Γ (n - vs.reverse.length) hResLen
  | .fvar_type _ _ name τ hLookup =>
    unfold substAll'; exact HasType.fvar_type _ _ name τ hLookup
  | .lit_int _ _ _ => unfold substAll'; exact HasType.lit_int _ _ _
  | .lit_bool _ _ _ => unfold substAll'; exact HasType.lit_bool _ _ _
  | .lit_string _ _ _ => unfold substAll'; exact HasType.lit_string _ _ _
  | .lit_unit _ _ => unfold substAll'; exact HasType.lit_unit _ _
  | .lit_pointer _ _ _ => unfold substAll'; exact HasType.lit_pointer _ _ _
  | .lit_float _ _ _ _ => unfold substAll'; exact HasType.lit_float _ _ _ _
  | .lit_int_width _ _ _ _ => unfold substAll'; exact HasType.lit_int_width _ _ _ _
  | .lit_some _ _ _ τ => unfold substAll'; exact HasType.lit_some _ _ _ τ
  | .lit_none _ _ τ => unfold substAll'; exact HasType.lit_none _ _ τ
  | .lit_ok _ _ _ τ_ok τ_err => unfold substAll'; exact HasType.lit_ok _ _ _ τ_ok τ_err
  | .lit_err _ _ _ τ_err τ_ok => unfold substAll'; exact HasType.lit_err _ _ _ τ_err τ_ok
  | .unop_not _ _ e' hE' =>
    unfold substAll'
    exact HasType.unop_not _ _ _ (HasType_substAll pfx σs bvs Γ vs e' .boolType hE' hVs hLen)
  | .unop_notb _ _ e' hE' =>
    unfold substAll'
    exact HasType.unop_notb _ _ _ (HasType_substAll pfx σs bvs Γ vs e' .intType hE' hVs hLen)
  | .binop_arith _ _ op e1 e2 hArith hE1 hE2 =>
    unfold substAll'
    exact HasType.binop_arith _ _ op _ _ hArith
      (HasType_substAll pfx σs bvs Γ vs e1 .intType hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 .intType hE2 hVs hLen)
  | .binop_comp _ _ op e1 e2 hComp hE1 hE2 =>
    unfold substAll'
    exact HasType.binop_comp _ _ op _ _ hComp
      (HasType_substAll pfx σs bvs Γ vs e1 .intType hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 .intType hE2 hVs hLen)
  | .binop_logic _ _ op e1 e2 hLogic hE1 hE2 =>
    unfold substAll'
    exact HasType.binop_logic _ _ op _ _ hLogic
      (HasType_substAll pfx σs bvs Γ vs e1 .boolType hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 .boolType hE2 hVs hLen)
  | .binop_bitwise _ _ op e1 e2 hBit hE1 hE2 =>
    unfold substAll'
    exact HasType.binop_bitwise _ _ op _ _ hBit
      (HasType_substAll pfx σs bvs Γ vs e1 .intType hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 .intType hE2 hVs hLen)
  | .binop_ptr_arith _ _ op e1 e2 hPtr hE1 hE2 =>
    unfold substAll'
    exact HasType.binop_ptr_arith _ _ op _ _ hPtr
      (HasType_substAll pfx σs bvs Γ vs e1 .pointerType hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 .intType hE2 hVs hLen)
  | .binop_ptr_load _ _ e1 e2 hE1 hE2 =>
    unfold substAll'
    exact HasType.binop_ptr_load _ _ _ _
      (HasType_substAll pfx σs bvs Γ vs e1 .pointerType hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 .unitType hE2 hVs hLen)
  | .binop_ptr_store _ _ e1 e2 hE1 hE2 =>
    unfold substAll'
    exact HasType.binop_ptr_store _ _ _ _
      (HasType_substAll pfx σs bvs Γ vs e1 .pointerType hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 .intType hE2 hVs hLen)
  | .binop_string_concat _ _ op e1 e2 hOp hE1 hE2 =>
    unfold substAll'
    exact HasType.binop_string_concat (pfx ++ bvs) Γ op
      (substAll' pfx.length vs.reverse e1) (substAll' pfx.length vs.reverse e2)
      hOp
      (HasType_substAll pfx σs bvs Γ vs e1 .stringType hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 .stringType hE2 hVs hLen)
  | .lam_type _ _ m body paramTys retTy hLenM hBody =>
    unfold substAll'
    have hAssoc1 : paramTys.reverse ++ (pfx ++ σs ++ bvs) = paramTys.reverse ++ pfx ++ σs ++ bvs := by
      rw [← List.append_assoc, ← List.append_assoc]
    have hBody' : HasType (paramTys.reverse ++ pfx ++ σs ++ bvs) Γ body retTy :=
      hAssoc1 ▸ hBody
    have hResult := HasType_substAll (paramTys.reverse ++ pfx) σs bvs Γ vs body retTy
      hBody' hVs hLen
    have hDepth : pfx.length + m = (paramTys.reverse ++ pfx).length := by
      have h1 : (paramTys.reverse ++ pfx).length = paramTys.reverse.length + pfx.length :=
        @List.length_append Typ paramTys.reverse pfx
      have h2 : paramTys.reverse.length = paramTys.length := @List.length_reverse Typ paramTys
      omega
    have hResult' : HasType (paramTys.reverse ++ (pfx ++ bvs)) Γ
        (substAll' (pfx.length + m) vs.reverse body) retTy := by
      have hAssoc : (paramTys.reverse ++ pfx) ++ bvs = paramTys.reverse ++ (pfx ++ bvs) :=
        List.append_assoc paramTys.reverse pfx bvs
      exact hAssoc ▸ hDepth.symm ▸ hResult
    exact HasType.lam_type (pfx ++ bvs) Γ m (substAll' (pfx.length + m) vs.reverse body)
      paramTys retTy hLenM hResult'
  | .app_type _ _ fn args τs τ hFn hArgs =>
    unfold substAll'
    exact HasType.app_type _ _ _ _ τs τ
      (HasType_substAll pfx σs bvs Γ vs fn (.functionType τs τ) hFn hVs hLen)
      (HasTypeAll_substAll pfx σs bvs Γ vs args τs hArgs hVs hLen)
  | .if_type _ _ c t f τ hC hT hF =>
    unfold substAll'
    exact HasType.if_type _ _ _ _ _ τ
      (HasType_substAll pfx σs bvs Γ vs c .boolType hC hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs t τ hT hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs f τ hF hVs hLen)
  | .let_type _ _ e1 e2 τ1' τ2' hE1 hE2 =>
    unfold substAll'
    have hE2' : HasType ((τ1' :: pfx) ++ σs ++ bvs) Γ e2 τ2' := by
      have hEq : τ1' :: (pfx ++ σs ++ bvs) = (τ1' :: pfx) ++ σs ++ bvs := by
        simp [List.cons_append, List.append_assoc]
      exact hEq ▸ hE2
    have hResult := HasType_substAll (τ1' :: pfx) σs bvs Γ vs e2 τ2' hE2' hVs hLen
    simp only [List.length_cons] at hResult
    have hResult' : HasType (pfx ++ bvs) Γ
        ((substAll' pfx.length vs.reverse e1).let_ (substAll' (pfx.length + 1) vs.reverse e2)) τ2' :=
      HasType.let_type (pfx ++ bvs) Γ (substAll' pfx.length vs.reverse e1)
        (substAll' (pfx.length + 1) vs.reverse e2) τ1' τ2'
        (HasType_substAll pfx σs bvs Γ vs e1 τ1' hE1 hVs hLen)
        hResult
    exact hResult'
  | .for_type _ _ s e body hS hE hBody =>
    unfold substAll'
    have hBody' : HasTypeAll ((.intType :: pfx) ++ σs ++ bvs) Γ body [.unitType] := by
      have hEq : .intType :: (pfx ++ σs ++ bvs) = (.intType :: pfx) ++ σs ++ bvs := by
        simp [List.cons_append, List.append_assoc]
      exact hEq ▸ hBody
    have hBodyResult := HasTypeAll_substAll (.intType :: pfx) σs bvs Γ vs body [.unitType]
      hBody' hVs hLen
    simp only [List.length_cons] at hBodyResult
    have hResult' : HasType (pfx ++ bvs) Γ
        (.forLoop (substAll' pfx.length vs.reverse s) (substAll' pfx.length vs.reverse e)
          (body.map (substAll' (pfx.length + 1) vs.reverse))) Typ.unitType :=
      HasType.for_type (pfx ++ bvs) Γ (substAll' pfx.length vs.reverse s)
        (substAll' pfx.length vs.reverse e) (body.map (substAll' (pfx.length + 1) vs.reverse))
        (HasType_substAll pfx σs bvs Γ vs s .intType hS hVs hLen)
        (HasType_substAll pfx σs bvs Γ vs e .intType hE hVs hLen)
        hBodyResult
    exact hResult'
  | .pipe_type _ _ e f τ_arg _ hE hF =>
    unfold substAll'
    exact HasType.pipe_type _ _ (substAll' pfx.length vs.reverse e) (substAll' pfx.length vs.reverse f) τ_arg _
      (HasType_substAll pfx σs bvs Γ vs e τ_arg hE hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs f (.functionType [τ_arg] _ ) hF hVs hLen)
  | .typeAsc_type _ _ e τ hE =>
    unfold substAll'
    exact HasType.typeAsc_type _ _ (substAll' pfx.length vs.reverse e) τ
      (HasType_substAll pfx σs bvs Γ vs e τ hE hVs hLen)
  | .some_type _ _ e τ_inner hE =>
    unfold substAll'
    exact HasType.some_type _ _ (substAll' pfx.length vs.reverse e) τ_inner
      (HasType_substAll pfx σs bvs Γ vs e τ_inner hE hVs hLen)
  | .none_type _ _ τ =>
    unfold substAll'; exact HasType.none_type _ _ τ
  | .ok_type _ _ e τ_ok τ_err hE =>
    unfold substAll'
    exact HasType.ok_type _ _ (substAll' pfx.length vs.reverse e) τ_ok τ_err
      (HasType_substAll pfx σs bvs Γ vs e τ_ok hE hVs hLen)
  | .err_type _ _ e τ_err τ_ok hE =>
    unfold substAll'
    exact HasType.err_type _ _ (substAll' pfx.length vs.reverse e) τ_err τ_ok
      (HasType_substAll pfx σs bvs Γ vs e τ_err hE hVs hLen)
  | .null_coalesce_type _ _ e1 e2 τ hE1 hE2 =>
    unfold substAll'
    exact HasType.null_coalesce_type _ _
      (substAll' pfx.length vs.reverse e1) (substAll' pfx.length vs.reverse e2) τ
      (HasType_substAll pfx σs bvs Γ vs e1 (.optionType τ) hE1 hVs hLen)
      (HasType_substAll pfx σs bvs Γ vs e2 (.optionType τ) hE2 hVs hLen)
   | .tuple_type _ _ elems tys hTys =>
     unfold substAll'
     exact HasType.tuple_type _ _ (elems.map (substAll' pfx.length vs.reverse)) tys
       (HasTypeAll_substAll pfx σs bvs Γ vs elems tys hTys hVs hLen)
    | .field_access_type _ _ e fname sname fields τ hE hField =>
      unfold substAll'
      exact HasType.field_access_type (pfx ++ bvs) Γ (substAll' pfx.length vs.reverse e) fname sname fields τ
        (HasType_substAll pfx σs bvs Γ vs e (.structType sname fields) hE hVs hLen)
        hField
     | .match_type _ _ scrut arms ts tr hScrut hArms =>
       unfold substAll'
       exact HasType.match_type _ _ (substAll' pfx.length vs.reverse scrut) (substAllArms pfx.length vs.reverse arms) ts tr
         (HasType_substAll pfx σs bvs Γ vs scrut ts hScrut hVs hLen)
                   (ArmsTyped_substAll pfx σs bvs Γ vs arms ts tr hArms hVs hLen)
     | .arrayLit_type _ _ elems τ' n hElems hLen' hn =>
       unfold substAll'
       have hLen'' : n = (List.map (fun e => substAll' pfx.length vs.reverse e) elems).length := by
         simp [List.length_map, hLen']
       exact HasType.arrayLit_type (pfx ++ bvs) Γ (elems.map (fun e => substAll' pfx.length vs.reverse e)) τ' n
         (HasTypeAll_substAll pfx σs bvs Γ vs elems (List.replicate n τ') hElems hVs hLen)
         hLen'' (by omega)
     | .arrayIndex_type _ _ arr idx τ' n hArr hIdx =>
       unfold substAll'
       exact HasType.arrayIndex_type (pfx ++ bvs) Γ (substAll' pfx.length vs.reverse arr) (substAll' pfx.length vs.reverse idx) τ' n
         (HasType_substAll pfx σs bvs Γ vs arr (.arrayType τ' n) hArr hVs hLen)
         (HasType_substAll pfx σs bvs Γ vs idx .intType hIdx hVs hLen)
     | .block_type _ _ exprs τs' τ hAll =>
     unfold substAll'
     exact HasType.block_type _ _ _ τs' τ
       (HasTypeAll_substAll pfx σs bvs Γ vs exprs (τs' ++ [τ]) hAll hVs hLen)
     | .refCreate_type _ _ e cap τ hE =>
       unfold substAll'
       exact HasType.refCreate_type _ _ _ cap τ (HasType_substAll pfx σs bvs Γ vs e τ hE hVs hLen)
     | .refLoad_type _ _ e cap τ hE =>
       unfold substAll'
       exact HasType.refLoad_type _ _ _ cap τ (HasType_substAll pfx σs bvs Γ vs e (.refType cap τ) hE hVs hLen)
     | .refStore_type _ _ e v' cap τ hE hV' hCap =>
       unfold substAll'
       exact HasType.refStore_type _ _ _ _ cap τ
         (HasType_substAll pfx σs bvs Γ vs e (.refType cap τ) hE hVs hLen)
         (HasType_substAll pfx σs bvs Γ vs v' τ hV' hVs hLen)
         hCap
     | .refFree_type _ _ e τ hE =>
       unfold substAll'
       exact HasType.refFree_type _ _ _ τ (HasType_substAll pfx σs bvs Γ vs e (.refType .iso τ) hE hVs hLen)

private theorem ArmsTyped_substAll (pfx σs : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (vs : List Expr) (arms : List (List String × Expr)) (ts tr : Typ)
    (hArms : ArmsTyped (pfx ++ σs ++ bvs) Γ ts arms tr)
    (hVs : HasTypeAll bvs Γ vs σs.reverse)
    (hLen : vs.length = σs.length) :
    ArmsTyped (pfx ++ bvs) Γ ts (substAllArms pfx.length vs.reverse arms) tr := by
  cases hArms with
  | nil => simp only [substAllArms]; constructor
  | cons bvs Γ vars body rest ts tr hBody hRest =>
    simp only [substAllArms]
    constructor
    · have hBody' : HasType ((List.replicate vars.length ts ++ pfx) ++ σs ++ bvs) Γ body tr := by
        simp only [List.append_assoc] at hBody ⊢
        exact hBody
      have hResult := HasType_substAll (List.replicate vars.length ts ++ pfx) σs bvs Γ vs body tr hBody' hVs hLen
      simp only [List.length_append, List.length_replicate] at hResult
      show HasType (List.replicate vars.length ts ++ (pfx ++ bvs)) Γ
          (substAll' (pfx.length + vars.length) vs.reverse body) tr
      rw [← List.append_assoc, Nat.add_comm]; exact hResult
    · exact ArmsTyped_substAll pfx σs bvs Γ vs rest ts tr hRest hVs hLen

end

-- Depth-0 wrapper for app_lam
private theorem HasType_iterSubst (σs : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (vs : List Expr) (e : Expr) (τ : Typ)
    (hE : HasType (σs ++ bvs) Γ e τ)
    (hVs : HasTypeAll bvs Γ vs σs.reverse)
    (hLen : vs.length = σs.length) :
    HasType bvs Γ (substAll' 0 vs.reverse e) τ :=
  HasType_substAll [] σs bvs Γ vs e τ hE hVs hLen

/-!
## Type Preservation (Main Theorem)
-/

private theorem HasType_tuple_inv {bvs : List Typ} {Γ : TypEnv} {rest : List Expr} {τs : List Typ} :
    HasType bvs Γ (.tuple_ rest) (.tupleType τs) → HasTypeAll bvs Γ rest τs := by
  intro h
  cases h with
  | tuple_type _ _ _ _ hAll => exact hAll
  | _ => contradiction

set_option maxHeartbeats 1000000 in
mutual

theorem preservation : forall {σ σ' : Store} {e e' : Expr} {τ : Typ} {bvs : List Typ} {Γ : TypEnv},
    HasType bvs Γ e τ -> Step σ e σ' e' -> HasType bvs Γ e' τ := by
  intro σ σ' e e' τ bvs Γ hType hStep
  cases hStep with
  | binop_left op e1 e1' e2 hStep1 =>
    cases hType with
    | binop_arith => exact HasType.binop_arith _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_comp => exact HasType.binop_comp _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_logic => exact HasType.binop_logic _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_bitwise => exact HasType.binop_bitwise _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_ptr_arith => exact HasType.binop_ptr_arith _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_ptr_load => exact HasType.binop_ptr_load _ _ e1' e2 (preservation (by assumption) hStep1) (by assumption)
    | binop_ptr_store => exact HasType.binop_ptr_store _ _ e1' e2 (preservation (by assumption) hStep1) (by assumption)
    | binop_string_concat => exact HasType.binop_string_concat _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | _ => contradiction
  | binop_right op v1 e2 e2' _ hStep2 =>
    cases hType with
    | binop_arith => exact HasType.binop_arith _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | binop_comp => exact HasType.binop_comp _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | binop_logic => exact HasType.binop_logic _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | binop_bitwise => exact HasType.binop_bitwise _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | binop_ptr_arith => exact HasType.binop_ptr_arith _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | binop_ptr_load => exact HasType.binop_ptr_load _ _ (.lit v1) e2' (by assumption) (preservation (by assumption) hStep2)
    | binop_ptr_store => exact HasType.binop_ptr_store _ _ (.lit v1) e2' (by assumption) (preservation (by assumption) hStep2)
    | binop_string_concat => exact HasType.binop_string_concat _ _ op (.lit v1) e2' (by assumption) (by assumption) (preservation (by assumption) hStep2)
    | _ => contradiction
  | binop_arith _ _ _ r hArith _ =>
    cases hType with
    | binop_arith => exact HasType.lit_int _ _ r
    | binop_comp => exfalso; exact sem_isArithOp_not_spec_isCompOp _ hArith (by assumption)
    | binop_bitwise => exact HasType.lit_int _ _ r
    | binop_ptr_arith _ _ _ _ _ hOp _ _ => exfalso; exact sem_isArithOp_not_spec_isPtrArithOp _ hArith hOp
    | binop_ptr_load _ _ _ _ hE1 _ => cases hE1
    | binop_ptr_store _ _ _ _ hE1 _ => cases hE1
    | _ => contradiction
  | binop_comp _ _ _ hComp =>
    cases hType with
    | binop_arith => exfalso; exact sem_isCompOp_not_spec_isArithOp _ hComp (by assumption)
    | binop_comp => exact HasType.lit_bool _ _ (evalCompOp _ _ _)
    | binop_bitwise => exfalso; exact sem_isCompOp_not_spec_isBitwiseOp _ hComp (by assumption)
    | binop_ptr_arith _ _ _ _ _ hOp _ _ => exfalso; exact sem_isCompOp_not_spec_isPtrArithOp _ hComp hOp
    | binop_ptr_load _ _ _ _ hE1 _ => cases hE1
    | binop_ptr_store _ _ _ _ hE1 _ => cases hE1
    | _ => contradiction
  | binop_logic _ _ _ _ _ =>
    cases hType with
    | binop_logic => exact HasType.lit_bool _ _ (by assumption)
    | binop_ptr_arith _ _ _ _ _ hOp _ _ => exfalso; exact sem_isLogicOp_not_spec_isPtrArithOp _ (by assumption) hOp
    | _ => contradiction
  | binop_bitwise _ _ _ r hBit _ =>
    cases hType with
    | binop_arith => exact HasType.lit_int _ _ r
    | binop_comp => exfalso; exact sem_isBitwiseOp_not_spec_isCompOp _ hBit (by assumption)
    | binop_bitwise => exact HasType.lit_int _ _ r
    | binop_ptr_arith _ _ _ _ _ hOp _ _ => exfalso; exact sem_isBitwiseOp_not_spec_isPtrArithOp _ hBit hOp
    | binop_ptr_load _ _ _ _ hE1 _ => cases hE1
    | binop_ptr_store _ _ _ _ hE1 _ => cases hE1
    | _ => contradiction
  | binop_ptr_arith _ _ _ r hPtr _ =>
    cases hType with
    | binop_ptr_arith => exact HasType.lit_pointer _ _ r
    | _ => contradiction
  | binop_ptr_load _ =>
    cases hType with
    | binop_ptr_load => exact HasType.lit_unit _ _
    | _ => contradiction
  | binop_ptr_store _ _ =>
    cases hType with
    | binop_ptr_store => exact HasType.lit_unit _ _
    | _ => contradiction
  | binop_string_concat s1 s2 =>
    cases hType with
    | binop_string_concat => exact HasType.lit_string _ _ (s1 ++ s2)
    | _ => contradiction
  | binop_div_zero _ =>
    cases hType with
    | binop_arith => exact HasType.lit_int _ _ 0
    | binop_ptr_arith _ _ _ _ _ hOp _ _ => exfalso; cases hOp
    | _ => contradiction
  | binop_mod_zero _ =>
    cases hType with
    | binop_arith => exact HasType.lit_int _ _ 0
    | binop_ptr_arith _ _ _ _ _ hOp _ _ => exfalso; cases hOp
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
      have hInnerBody : HasTypeAll (.intType :: .intType :: bvs) Γ (body.map (lift 1)) [.unitType] :=
        weakening_all (.intType :: bvs) Γ body [.unitType] .intType hBody
      have hInnerFor : HasType (.intType :: bvs) Γ
          (.forLoop (.lit (.int (n + 1))) (.lit (.int m)) (body.map (lift 1))) .unitType :=
        HasType.for_type (.intType :: bvs) Γ (.lit (.int (n + 1))) (.lit (.int m))
          (body.map (lift 1))
          (HasType.lit_int _ _ (n + 1))
          (HasType.lit_int _ _ m)
          hInnerBody
      have hBlockAll : HasTypeAll (.intType :: bvs) Γ
          (body ++ [.forLoop (.lit (.int (n + 1))) (.lit (.int m)) (body.map (lift 1))])
          [.unitType, .unitType] :=
        HasTypeAll_append hBody
          (HasTypeAll.cons _ _ _ _ _ _ hInnerFor (HasTypeAll.nil _ _))
      exact HasType.let_type bvs Γ (.lit (.int n))
        (.block (body ++ [.forLoop (.lit (.int (n + 1))) (.lit (.int m)) (body.map (lift 1))]))
        .intType .unitType hS
        (HasType.block_type (.intType :: bvs) Γ
          (body ++ [.forLoop (.lit (.int (n + 1))) (.lit (.int m)) (body.map (lift 1))])
          [.unitType] .unitType hBlockAll)
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
  | block_none_singleton =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_err_singleton e _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_ok_singleton e _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_some_singleton e _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_tuple_singleton elems =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_array_singleton elems =>
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
  | block_refCreate_singleton e cap τ_param _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_refLoad_singleton e _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_refStore_singleton e v τ_param _ _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_refFree_singleton e _ =>
    cases hType with
    | block_type _ _ _ τs _ hAll =>
      cases τs with
      | nil => exact HasTypeAll_cons_head hAll
      | cons τ' τs' =>
        exfalso
        exact append_singleton_ne_nil τs' τ (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
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
      match hFn with
      | HasType.lam_type _ _ _ _ paramTys retTy hLen' hBodyP =>
        have hLenEq : args.length = paramTys.reverse.length := by
          rw [List.length_reverse]; exact hLen ▸ hLen'
        have hVs : HasTypeAll bvs Γ args (paramTys.reverse).reverse := by
          simp [List.reverse_reverse]; exact hAll
        exact HasType_iterSubst paramTys.reverse bvs Γ args body retTy
          hBodyP hVs hLenEq
  | pipe_left e e' f hStep1 =>
    cases hType with
    | pipe_type => exact HasType.pipe_type _ _ e' f _ _ (preservation (by assumption) hStep1) (by assumption)
    | _ => contradiction
  | pipe_right v f f' hIsVal hStep2 =>
    cases hType with
    | pipe_type => exact HasType.pipe_type _ _ v f' _ _ (by assumption) (preservation (by assumption) hStep2)
    | _ => contradiction
  | pipe_done v f hIsVal =>
    cases hType with
    | pipe_type =>
      exact HasType.app_type _ _ f [v] [_] _ (by assumption)
        (HasTypeAll.cons _ _ _ _ _ _ (by assumption) (HasTypeAll.nil _ _))
    | _ => contradiction
  | typeAsc_step e e' τ hStep1 =>
    cases hType with
    | typeAsc_type => exact HasType.typeAsc_type _ _ e' _ (preservation (by assumption) hStep1)
    | _ => contradiction
  | typeAsc_done valExpr τAsc =>
    cases hType with
    | typeAsc_type => exact (by assumption)
    | _ => contradiction
  | match_scrut_step scrut scrut' arms hStep1 =>
    cases hType with
    | match_type _ _ _ _ _ _ hScrut hArms =>
      exact HasType.match_type _ _ scrut' arms _ _ (preservation hScrut hStep1) hArms
    | _ => contradiction
  | match_arm e vars body rest hIsVal =>
    cases hType with
    | match_type _ _ _ _ τ_scrut τ_result hScrut hArms =>
      match hArms with
      | .cons _ _ _ body2 _ ts tr hBody2 _ =>
        have hRepLen : (List.replicate vars.length e).length = (List.replicate vars.length ts).length := by
          simp [List.length_replicate]
        have hRepVs : HasTypeAll bvs Γ (List.replicate vars.length e) (List.replicate vars.length ts).reverse := by
          rw [list_reverse_replicate]
          exact HasTypeAll_replicate bvs Γ e ts hScrut vars.length
        have hResult := HasType_iterSubst (List.replicate vars.length ts) bvs Γ
          (List.replicate vars.length e) body2 tr hBody2 hRepVs hRepLen
        show HasType bvs Γ (substAll' 0 (List.replicate vars.length e) body2) tr
        rw [list_reverse_replicate] at hResult
        exact hResult
    | _ => contradiction
  | match_empty e hIsVal =>
    cases hType with
    | match_type _ _ _ _ _ _ hScrut hArms =>
      cases hArms
      exact HasType.lit_unit _ _
    | _ => contradiction
  | some_step e e' hStep1 =>
    cases hType with
    | some_type _ _ _ τ_inner hE =>
      exact HasType.some_type _ _ e' τ_inner (preservation hE hStep1)
    | _ => contradiction
  | some_done v =>
    cases hType with
    | some_type _ _ _ τ_inner hE => exact HasType.lit_some _ _ v τ_inner
    | _ => contradiction
  | some_none_done =>
    cases hType with
    | some_type bvs Γ _ τ_inner hE => exact HasType.lit_some bvs Γ Value.none τ_inner
    | _ => contradiction
  | none_step =>
    cases hType with
    | none_type _ _ τ => exact HasType.lit_none _ _ τ
    | _ => contradiction
  | ok_step e e' hStep1 =>
    cases hType with
    | ok_type _ _ _ τ_ok _ hE =>
      exact HasType.ok_type _ _ e' τ_ok _ (preservation hE hStep1)
    | _ => contradiction
  | ok_done v =>
    cases hType with
    | ok_type _ _ _ τ_ok τ_err hE => exact HasType.lit_ok _ _ v τ_ok τ_err
    | _ => contradiction
  | ok_none_done =>
    cases hType with
    | ok_type bvs Γ _ τ_ok τ_err hE => exact HasType.lit_ok bvs Γ Value.none τ_ok τ_err
    | _ => contradiction
  | err_step e e' hStep1 =>
    cases hType with
    | err_type _ _ _ τ_err _ hE =>
      exact HasType.err_type _ _ e' τ_err _ (preservation hE hStep1)
    | _ => contradiction
  | err_done v =>
    cases hType with
    | err_type _ _ _ τ_err τ_ok hE => exact HasType.lit_err _ _ v τ_err τ_ok
    | _ => contradiction
  | err_none_done =>
    cases hType with
    | err_type bvs Γ _ τ_err τ_ok hE => exact HasType.lit_err bvs Γ Value.none τ_err τ_ok
    | _ => contradiction
  | null_coalesce_step_e1 e1 e1' e2 hStep1 =>
    cases hType with
    | null_coalesce_type _ _ _ _ _ hE1 hE2 =>
      exact HasType.null_coalesce_type _ _ e1' e2 _ (preservation hE1 hStep1) hE2
    | _ => contradiction
  | null_coalesce_some v e2 =>
    cases hType with
    | null_coalesce_type _ _ _ _ _ hE1 _ => exact hE1
    | _ => contradiction
  | null_coalesce_none e2 =>
    cases hType with
    | null_coalesce_type _ _ _ _ _ _ hE2 => exact hE2
    | _ => contradiction
  | null_coalesce_lit_some v e2 =>
    cases hType with
    | null_coalesce_type _ _ _ _ _ hE1 _ => exact hE1
    | _ => contradiction
   | null_coalesce_lit_none e2 =>
     cases hType with
     | null_coalesce_type _ _ _ _ _ _ hE2 => exact hE2
     | _ => contradiction
    | field_step e e' name hs =>
      cases hType with
      | field_access_type _ _ _ _ _ _ _ hE hField =>
        exact HasType.field_access_type _ _ e' name _ _ _ (preservation hE hs) hField
      | _ => contradiction
    | tuple_step_head head head' rest hs =>
      cases hType with
      | tuple_type _ _ _ _ hAll =>
        cases hAll with
        | cons _ _ _ _ _ _ hE_head hAll_rest =>
          exact HasType.tuple_type _ _ _ _
            (HasTypeAll.cons _ _ _ _ _ _ (preservation hE_head hs) hAll_rest)
      | _ => contradiction
    | tuple_step_rest head rest rest' hv hs =>
      cases hType with
      | tuple_type _ _ _ _ hAll =>
        cases hAll with
        | cons _ _ _ _ _ _ hE_head hAll_rest =>
          have hAll_rest' := HasType_tuple_inv (preservation (HasType.tuple_type _ _ _ _ hAll_rest) hs)
          exact HasType.tuple_type _ _ _ _
            (HasTypeAll.cons _ _ _ _ _ _ hE_head hAll_rest')
      | _ => contradiction
    | array_step_head head head' rest hs =>
      cases hType with
      | arrayLit_type _ _ _ τ n hAll hLen hn =>
        cases n with
        | zero => exfalso; omega
        | succ n' =>
          simp only [List.replicate_succ] at hAll ⊢
          cases hAll with
          | cons _ _ _ _ _ _ hE_head hAll_rest =>
            exact HasType.arrayLit_type _ _ (head' :: rest) τ (Nat.succ n')
              (HasTypeAll.cons _ _ _ _ _ _ (preservation hE_head hs) hAll_rest)
              (by simp only [List.length_cons] at hLen ⊢; omega) (by omega)
      | _ => contradiction
    | array_step_rest head rest rest' hv hs =>
      cases hType with
      | arrayLit_type _ _ _ τ n hAll hLen hn =>
        cases n with
        | zero => exfalso; omega
        | succ n' =>
          simp only [List.replicate_succ] at hAll ⊢
          cases hAll with
          | cons _ _ _ _ _ _ hE_head hAll_rest =>
            cases n' with
            | zero =>
              have : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj hLen).symm
              subst this
              cases hs
            | succ n'' =>
              have hRestType : HasType bvs Γ (.arrayLit rest) (.arrayType τ (Nat.succ n'')) :=
                HasType.arrayLit_type _ _ rest τ (Nat.succ n'') hAll_rest
                  (Nat.succ.inj hLen) (Nat.succ_pos n'')
              have hRestType' := preservation hRestType hs
              cases hRestType' with
              | arrayLit_type _ _ _ _ _ hAll_rest' hLen' hn' =>
                exact HasType.arrayLit_type _ _ (head :: rest') τ (Nat.succ (Nat.succ n''))
                  (HasTypeAll.cons _ _ _ _ _ _ hE_head hAll_rest')
                  (congrArg Nat.succ hLen') (Nat.succ_pos _)
              | _ => contradiction
      | _ => contradiction
    | array_index_array arr arr' idx hs =>
      cases hType with
      | arrayIndex_type _ _ _ _ τ n hArr hIdx =>
        exact HasType.arrayIndex_type _ _ arr' idx τ n (preservation hArr hs) hIdx
      | _ => contradiction
    | array_index_idx arr idx idx' hv hs =>
      cases hType with
      | arrayIndex_type _ _ _ _ τ n hArr hIdx =>
        exact HasType.arrayIndex_type _ _ arr idx' τ n hArr (preservation hIdx hs)
      | _ => contradiction
    | array_index_hit elems hvs idx hLt =>
      cases hType with
      | arrayIndex_type _ _ _ _ τ m hArr hIdx =>
        cases hArr with
        | arrayLit_type _ _ _ _ _ hAll hLen hn =>
          have hGet : ∀ es n, HasTypeAll bvs Γ es (List.replicate n τ) →
            ∀ i (_ : i < es.length), HasType bvs Γ (es.getD i (.lit .unit)) τ := by
            intro es n hAll'
            induction es generalizing n with
            | nil => intro i h; simp at h
            | cons head tail ih =>
              cases n with
              | zero => intro i h; cases hAll'
              | succ n' =>
                intro i h
                cases hAll' with
                | cons _ _ _ _ _ _ hE_head hE_tail =>
                  cases i with
                  | zero => simp [List.getD]; exact hE_head
                  | succ i' => simp only [List.getD_cons_succ]; exact ih n' hE_tail i' (by simp at h; omega)
          exact hGet elems m hAll idx (by omega)
        | _ => contradiction
      | _ => contradiction
    | array_index_oob elems hvs idx hPos hGe =>
      cases hType with
      | arrayIndex_type _ _ _ _ τ m hArr hIdx =>
        cases hArr with
        | arrayLit_type _ _ _ _ _ hAll hLen hn =>
          cases m with
          | zero => exfalso; omega
          | succ m' =>
            simp only [List.replicate_succ] at hAll
            cases hAll with
            | cons _ _ _ _ _ _ hE_head _ => simp [List.getD]; exact hE_head
        | _ => contradiction
      | _ => contradiction
     | array_index_neg elems hvs m hPos =>
       cases hType with
       | arrayIndex_type _ _ _ _ τ n hArr hIdx =>
         cases hArr with
         | arrayLit_type _ _ _ _ _ hAll hLen hn =>
           cases n with
           | zero => exfalso; omega
           | succ n' =>
             simp only [List.replicate_succ] at hAll
             cases hAll with
             | cons _ _ _ _ _ _ hE_head _ => simp [List.getD]; exact hE_head
         | _ => contradiction
       | _ => contradiction
    | ref_create_step e e' cap τ hStep1 =>
      cases hType with
      | refCreate_type _ _ _ cap τ hE =>
        exact HasType.refCreate_type _ _ _ cap τ (preservation hE hStep1)
      | _ => contradiction
    | ref_load_step e e' hStep1 =>
      cases hType with
      | refLoad_type _ _ _ cap τ hE =>
        exact HasType.refLoad_type _ _ _ cap τ (preservation hE hStep1)
      | _ => contradiction
    | ref_store_step_arr e e' v τ hStep1 =>
      cases hType with
      | refStore_type _ _ _ _ cap τ hE hV' hCap =>
        exact HasType.refStore_type _ _ _ _ cap τ (preservation hE hStep1) hV' hCap
      | _ => contradiction
    | ref_store_step_val e e' v τ hVal hStep1 =>
      cases hType with
      | refStore_type _ _ _ _ cap τ hE hV' hCap =>
        exact HasType.refStore_type _ _ _ _ cap τ hE (preservation hV' hStep1) hCap
      | _ => contradiction
    | ref_free_step e e' hStep1 =>
      cases hType with
      | refFree_type _ _ _ τ hE =>
        exact HasType.refFree_type _ _ _ τ (preservation hE hStep1)
      | _ => contradiction
    | ref_load_eval e cap τ_val _ =>
      cases hType with
      | refLoad_type _ _ _ cap τ_inner hE =>
        cases hE with
        | refCreate_type _ _ _ _ _ hE' => exact hE'
        | _ => contradiction
      | _ => contradiction
    | ref_store_eval e v cap τ_val _ _ _ =>
      cases hType with
      | refStore_type => exact HasType.lit_unit _ _
      | _ => contradiction
    | ref_free_eval e τ_val _ =>
      cases hType with
      | refFree_type => exact HasType.lit_unit _ _
      | _ => contradiction
    | ref_load_done loc τ_val v hLoad =>
      cases hType with
      | refLoad_type _ _ _ cap τ' hE => cases hE
      | _ => contradiction
    | ref_store_done loc v τ σ' hStore =>
      cases hType with
      | refStore_type _ _ _ _ cap τ' hE hV hCap => cases hE
      | _ => contradiction
    | ref_free_done loc σ' hFree =>
      cases hType with
      | refFree_type _ _ _ τ' hE => cases hE
      | _ => contradiction

end

end Morph.Proofs.TypeSoundness
