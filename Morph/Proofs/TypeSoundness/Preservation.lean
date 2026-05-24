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
    simp only [List.length_cons] at hResult
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
    simp only [List.length_cons] at hBodyResult
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
    · -- n < pfx.length: shadowed by prefix, unchanged .bvar n
      next hNlt =>
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
      · -- pfx.length ≤ n < pfx.length + σs.length: substitute
        next hIn =>
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
      · -- n ≥ pfx.length + σs.length: free bvar, shift down by vs.reverse.length
        next hGe =>
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
  | .lam_type _ _ m body paramTys retTy hLenM hBody =>
    -- substAll' pfx.length vs.reverse (.lam m body) = .lam m (substAll' (pfx.length + m) vs.reverse body)
    -- Body context: paramTys.reverse ++ pfx ++ σs ++ bvs = (paramTys.reverse ++ pfx) ++ σs ++ bvs
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
    -- e2 context: τ1' :: pfx ++ σs ++ bvs = (τ1' :: pfx) ++ σs ++ bvs
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
    -- body context: .intType :: pfx ++ σs ++ bvs = (.intType :: pfx) ++ σs ++ bvs
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
  | .block_type _ _ exprs τs' τ hAll =>
    unfold substAll'
    exact HasType.block_type _ _ _ τs' τ
      (HasTypeAll_substAll pfx σs bvs Γ vs exprs (τs' ++ [τ]) hAll hVs hLen)

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
    | binop_ptr_arith => exact HasType.binop_ptr_arith _ _ op e1' e2 (by assumption) (preservation (by assumption) hStep1) (by assumption)
    | binop_ptr_load => exact HasType.binop_ptr_load _ _ e1' e2 (preservation (by assumption) hStep1) (by assumption)
    | binop_ptr_store => exact HasType.binop_ptr_store _ _ e1' e2 (preservation (by assumption) hStep1) (by assumption)
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
      -- Step produces: .let_ (.lit (.int n)) (.block (body ++ [forLoop ... (body.map (lift 1))]))
      -- Under let_, context is (.intType :: bvs). Body was typed at (.intType :: bvs) — matches.
      -- Inner forLoop body (body.map (lift 1)) needs type at (.intType :: .intType :: bvs):
      -- use weakening_all to insert the extra .intType layer.
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
      match hFn with
      | HasType.lam_type _ _ _ _ paramTys retTy hLen' hBodyP =>
        have hLenEq : args.length = paramTys.reverse.length := by
          rw [List.length_reverse]; exact hLen ▸ hLen'
        have hVs : HasTypeAll bvs Γ args (paramTys.reverse).reverse := by
          simp [List.reverse_reverse]; exact hAll
        exact HasType_iterSubst paramTys.reverse bvs Γ args body retTy
          hBodyP hVs hLenEq

end

end Morph.Proofs.TypeSoundness
