/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem

namespace Morph.Proofs.TypeSoundness

open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Step
open Morph.Specs.TypeSystem
open HasType

private theorem HasTypeAll_cons_head {Gamma : TypEnv} {e : Expr} {es : List Expr}
    {tau : Typ} {taus : List Typ} (h : HasTypeAll Gamma (e :: es) (tau :: taus)) : HasType Gamma e tau := by
  match h with
  | HasTypeAll.cons _ _ _ _ _ hE _ => exact hE

private theorem HasTypeAll_cons_tail {Gamma : TypEnv} {e : Expr} {es : List Expr}
    {tau : Typ} {taus : List Typ} (h : HasTypeAll Gamma (e :: es) (tau :: taus)) : HasTypeAll Gamma es taus := by
  match h with
  | HasTypeAll.cons _ _ _ _ _ _ hRest => exact hRest

private theorem HasTypeAll_nil_types {Gamma : TypEnv} {taus : List Typ} :
    HasTypeAll Gamma [] taus -> taus = [] := by
  intro h; match h with | HasTypeAll.nil _ => rfl

private theorem append_singleton_ne_nil (taus : List Typ) (tau : Typ) : taus ++ [tau] ≠ [] := by
  intro h
  cases taus with
  | nil => exact absurd h (by contradiction)
  | cons _ _ => exact absurd h (by contradiction)

private theorem HasTypeAll_length (Gamma : TypEnv) (es : List Expr) (taus : List Typ) :
    HasTypeAll Gamma es taus -> es.length = taus.length := by
  intro h
  cases es with
  | nil => match h with | HasTypeAll.nil _ => rfl
  | cons e es' =>
    cases taus with
    | nil => cases h
    | cons tau taus' =>
      simp only [List.length_cons]
      have ⟨_, hTail⟩ : HasType Gamma e tau ∧ HasTypeAll Gamma es' taus' := by
        match h with | HasTypeAll.cons _ _ _ _ _ hH hT => exact ⟨hH, hT⟩
      exact congrArg (· + 1) (HasTypeAll_length Gamma es' taus' hTail)

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

private theorem lookupTyp_extend_eq {Γ : TypEnv} {name : String} {typ : Typ} :
    lookupTyp (extendTypEnv Γ name typ) name = some typ := by
  unfold extendTypEnv lookupTyp
  simp only [List.find?_cons, beq_self_eq_true]
  simp [Option.map]

private theorem lookupTyp_extend_ne {Γ : TypEnv} {name y : String} {typ : Typ} (hne : name ≠ y) :
    lookupTyp (extendTypEnv Γ name typ) y = lookupTyp Γ y := by
  unfold extendTypEnv lookupTyp
  simp only [List.find?_cons]
  split
  · next h => exact absurd (eq_of_beq h) hne
  · rfl

private theorem HasTypeAll_append {Γ : TypEnv} {es₁ es₂ : List Expr} {τs₁ τs₂ : List Typ}
    (h₁ : HasTypeAll Γ es₁ τs₁) (h₂ : HasTypeAll Γ es₂ τs₂) :
    HasTypeAll Γ (es₁ ++ es₂) (τs₁ ++ τs₂) := by
  match h₁ with
  | HasTypeAll.nil _ => exact h₂
  | HasTypeAll.cons _ e es τ τs hE hRest =>
    exact HasTypeAll.cons _ e (es ++ es₂) τ (τs ++ τs₂) hE (HasTypeAll_append hRest h₂)

private theorem extendTypEnv_lookup_eq {Γ : TypEnv} {name : String} {typ : Typ} {Γ' : TypEnv}
    (hEq : ∀ x, lookupTyp Γ x = lookupTyp Γ' x) (y : String) :
    lookupTyp (extendTypEnv Γ name typ) y = lookupTyp (extendTypEnv Γ' name typ) y := by
  cases Decidable.em (name = y) with
  | inl hEq' => rw [hEq', lookupTyp_extend_eq, lookupTyp_extend_eq]
  | inr hNe => rw [lookupTyp_extend_ne hNe, lookupTyp_extend_ne hNe]; exact hEq y

private theorem extendTypEnv_shadow_eq {Γ : TypEnv} {name : String} {typ : Typ} :
    ∀ x, lookupTyp (extendTypEnv Γ name typ) x = lookupTyp (extendTypEnv (extendTypEnv Γ name typ) name typ) x := by
  intro x
  cases Decidable.em (name = x) with
  | inl hEq => rw [hEq, lookupTyp_extend_eq, lookupTyp_extend_eq]
  | inr hNe => rw [lookupTyp_extend_ne hNe, lookupTyp_extend_ne hNe]; exact (lookupTyp_extend_ne hNe).symm

mutual
private theorem HasType_lookup_eq {Γ Γ' : TypEnv} {e : Expr} {τ : Typ}
    (h : HasType Γ e τ) (hEq : ∀ x, lookupTyp Γ x = lookupTyp Γ' x) : HasType Γ' e τ := by
  match h with
  | HasType.var_type _ id τ hLookup =>
    exact HasType.var_type Γ' id τ (Eq.trans (Eq.symm (hEq id.name)) hLookup)
  | HasType.lit_int _ n => exact HasType.lit_int Γ' n
  | HasType.lit_bool _ b => exact HasType.lit_bool Γ' b
  | HasType.lit_string _ s => exact HasType.lit_string Γ' s
  | HasType.lit_unit _ => exact HasType.lit_unit Γ'
  | HasType.lit_pointer _ p => exact HasType.lit_pointer Γ' p
  | HasType.unop_not _ e' hE' => exact HasType.unop_not Γ' e' (HasType_lookup_eq hE' hEq)
  | HasType.unop_notb _ e' hE' => exact HasType.unop_notb Γ' e' (HasType_lookup_eq hE' hEq)
  | HasType.binop_arith _ op e1 e2 hArith hE1 hE2 => exact HasType.binop_arith Γ' op e1 e2 hArith (HasType_lookup_eq hE1 hEq) (HasType_lookup_eq hE2 hEq)
  | HasType.binop_comp _ op e1 e2 hComp hE1 hE2 => exact HasType.binop_comp Γ' op e1 e2 hComp (HasType_lookup_eq hE1 hEq) (HasType_lookup_eq hE2 hEq)
  | HasType.binop_logic _ op e1 e2 hLogic hE1 hE2 => exact HasType.binop_logic Γ' op e1 e2 hLogic (HasType_lookup_eq hE1 hEq) (HasType_lookup_eq hE2 hEq)
  | HasType.binop_bitwise _ op e1 e2 hBit hE1 hE2 => exact HasType.binop_bitwise Γ' op e1 e2 hBit (HasType_lookup_eq hE1 hEq) (HasType_lookup_eq hE2 hEq)
  | HasType.lam_type _ x body τ1 τ2 hBody => exact HasType.lam_type Γ' x body τ1 τ2 (HasType_lookup_eq hBody (extendTypEnv_lookup_eq hEq))
  | HasType.app_type _ fn args τs τ hFn hArgs => exact HasType.app_type Γ' fn args τs τ (HasType_lookup_eq hFn hEq) (HasTypeAll_lookup_eq hArgs hEq)
  | HasType.let_type _ _ _ _ _ _ hE1' hE2' => exact HasType.let_type _ _ _ _ _ _ (HasType_lookup_eq hE1' hEq) (HasType_lookup_eq hE2' (extendTypEnv_lookup_eq hEq))
  | HasType.if_type _ c t f τ hC hT hF => exact HasType.if_type Γ' c t f τ (HasType_lookup_eq hC hEq) (HasType_lookup_eq hT hEq) (HasType_lookup_eq hF hEq)
  | HasType.for_type _ id' s e body hS hE hBody => exact HasType.for_type Γ' id' s e body (HasType_lookup_eq hS hEq) (HasType_lookup_eq hE hEq) (HasTypeAll_lookup_eq hBody (extendTypEnv_lookup_eq hEq))
  | HasType.block_type _ exprs τs τ hAll => exact HasType.block_type Γ' exprs τs τ (HasTypeAll_lookup_eq hAll hEq)

private theorem HasTypeAll_lookup_eq {Γ Γ' : TypEnv} {es : List Expr} {τs : List Typ}
    (h : HasTypeAll Γ es τs) (hEq : ∀ x, lookupTyp Γ x = lookupTyp Γ' x) : HasTypeAll Γ' es τs := by
  match h with
  | HasTypeAll.nil _ => exact HasTypeAll.nil Γ'
  | HasTypeAll.cons _ e es τ τs hE hRest =>
    exact HasTypeAll.cons _ e es τ τs (HasType_lookup_eq hE hEq) (HasTypeAll_lookup_eq hRest hEq)

private theorem extendTypEnv_lookup_eq_inner {Γ : TypEnv} {name : String} {typ : Typ} {Γ' : TypEnv}
    (hEq : ∀ x, lookupTyp Γ x = lookupTyp Γ' x) (y : String) :
    lookupTyp (extendTypEnv Γ name typ) y = lookupTyp (extendTypEnv Γ' name typ) y := by
  cases Decidable.em (name = y) with
  | inl hEq' => rw [hEq', lookupTyp_extend_eq, lookupTyp_extend_eq]
  | inr hNe => rw [lookupTyp_extend_ne hNe, lookupTyp_extend_ne hNe]; exact hEq y

private theorem extendTypEnv_shadow_eq_inner {Γ : TypEnv} {name : String} {typ : Typ} :
    ∀ x, lookupTyp (extendTypEnv Γ name typ) x = lookupTyp (extendTypEnv (extendTypEnv Γ name typ) name typ) x := by
  intro x
  cases Decidable.em (name = x) with
  | inl hEq => rw [hEq, lookupTyp_extend_eq, lookupTyp_extend_eq]
  | inr hNe => rw [lookupTyp_extend_ne hNe, lookupTyp_extend_ne hNe]; exact (lookupTyp_extend_ne hNe).symm
end

/-- When the inner binding shadows the outer one (same name), the outer binding is irrelevant for lookups. -/
private theorem lookupTyp_drop_shadowed {Γ : TypEnv} {x : String} {τ₁ : Typ} (y : Id) (τ' : Typ)
    (hEq : y.name = x) :
    ∀ z, lookupTyp (extendTypEnv (extendTypEnv Γ x τ₁) y τ') z = lookupTyp (extendTypEnv Γ y τ') z := by
  intro z
  unfold extendTypEnv lookupTyp
  simp only [List.find?_cons]
  cases Decidable.em (y.name = z) with
  | inl h => simp [h]
  | inr h =>
    simp only [h, ↓reduceIte]
    cases Decidable.em (x = z) with
    | inl h2 => exfalso; exact h (hEq ▸ h2)
    | inr _ => rfl

private theorem substList_preserves_type_all (Gamma : TypEnv) (es : List Expr) (x : String) (v : Expr) (tau1 : Typ) (taus : List Typ)
    (hArgs : HasTypeAll (extendTypEnv Gamma x tau1) es taus)
    (hV : HasType Gamma v tau1) : HasTypeAll Gamma (substList es x v) taus := by
  match hArgs with
  | HasTypeAll.nil _ => exact HasTypeAll.nil Gamma
  | HasTypeAll.cons _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons Gamma (subst e x v) (substList es' x v) τ τs'
      (subst_preserves_type Gamma e x v tau1 τ hE hV)
      (substList_preserves_type_all Gamma es' x v tau1 τs' hRest hV)

private theorem subst_preserves_type (Gamma : TypEnv) (e : Expr) (x : String) (v : Expr) (tau1 tau : Typ)
    (hE : HasType (extendTypEnv Gamma x tau1) e tau)
    (hV : HasType Gamma v tau1) : HasType Gamma (subst e x v) tau := by
  match hE with
  | HasType.var_type _ id τ hLookup =>
    unfold subst
    split
    · next hEq =>
      have hNameEq : id.name = x := eq_of_beq hEq
      rw [hNameEq, lookupTyp_extend_eq] at hLookup
      injection hLookup with hτ
      rw [hτ]; exact hV
    · next hNe =>
      have hNe' : id.name ≠ x := fun h => by
        rw [h] at hNe
        exact Bool.false_ne_true (hNe ▸ beq_self_eq_true)
      exact HasType.var_type Gamma id τ (lookupTyp_extend_ne hNe')
  | HasType.lit_int _ _ => unfold subst; exact HasType.lit_int Gamma _
  | HasType.lit_bool _ _ => unfold subst; exact HasType.lit_bool Gamma _
  | HasType.lit_string _ _ => unfold subst; exact HasType.lit_string Gamma _
  | HasType.lit_unit _ => unfold subst; exact HasType.lit_unit Gamma
  | HasType.lit_pointer _ _ => unfold subst; exact HasType.lit_pointer Gamma _
  | HasType.unop_not _ e' hE' =>
    unfold subst
    exact HasType.unop_not Gamma (subst e' x v) (subst_preserves_type Gamma e' x v tau1 .boolType hE' hV)
  | HasType.unop_notb _ e' hE' =>
    unfold subst
    exact HasType.unop_notb Gamma (subst e' x v) (subst_preserves_type Gamma e' x v tau1 .intType hE' hV)
  | HasType.binop_arith _ op e1 e2 hArith hE1 hE2 =>
    unfold subst
    exact HasType.binop_arith Gamma op (subst e1 x v) (subst e2 x v) hArith
      (subst_preserves_type Gamma e1 x v tau1 .intType hE1 hV)
      (subst_preserves_type Gamma e2 x v tau1 .intType hE2 hV)
  | HasType.binop_comp _ op e1 e2 hComp hE1 hE2 =>
    unfold subst
    exact HasType.binop_comp Gamma op (subst e1 x v) (subst e2 x v) hComp
      (subst_preserves_type Gamma e1 x v tau1 .intType hE1 hV)
      (subst_preserves_type Gamma e2 x v tau1 .intType hE2 hV)
  | HasType.binop_logic _ op e1 e2 hLogic hE1 hE2 =>
    unfold subst
    exact HasType.binop_logic Gamma op (subst e1 x v) (subst e2 x v) hLogic
      (subst_preserves_type Gamma e1 x v tau1 .boolType hE1 hV)
      (subst_preserves_type Gamma e2 x v tau1 .boolType hE2 hV)
  | HasType.binop_bitwise _ op e1 e2 hBit hE1 hE2 =>
    unfold subst
    exact HasType.binop_bitwise Gamma op (subst e1 x v) (subst e2 x v) hBit
      (subst_preserves_type Gamma e1 x v tau1 .intType hE1 hV)
      (subst_preserves_type Gamma e2 x v tau1 .intType hE2 hV)
  | HasType.app_type _ fn args τs τ hFn hArgs =>
    unfold subst
    exact HasType.app_type Gamma (subst fn x v) (substList args x v) τs τ
      (subst_preserves_type Gamma fn x v tau1 (.functionType τs τ) hFn hV)
      (substList_preserves_type_all Gamma args x v tau1 τs hArgs hV)
  | HasType.if_type _ c t f τ hC hT hF =>
    unfold subst
    exact HasType.if_type Gamma (subst c x v) (subst t x v) (subst f x v) τ
      (subst_preserves_type Gamma c x v tau1 .boolType hC hV)
      (subst_preserves_type Gamma t x v tau1 τ hT hV)
      (subst_preserves_type Gamma f x v tau1 τ hF hV)
  | HasType.block_type _ exprs τs τ hAll =>
    unfold subst
    exact HasType.block_type Gamma (substList exprs x v) τs τ
      (substList_preserves_type_all Gamma exprs x v tau1 (τs ++ [τ]) hAll hV)
  | HasType.lam_type _ x' body τ1' τ2 hBody =>
    unfold subst
    split
    · next hCap =>
      have hNameEq : x'.name = x := by
        simp only [List.any_cons, List.any_nil, decide_eq_true] at hCap
        exact eq_of_beq hCap
      exact HasType.lam_type Gamma x' body τ1' τ2
        (HasType_lookup_eq hBody (lookupTyp_drop_shadowed x' τ1' hNameEq))
    · next _ =>
      exact HasType.lam_type Gamma x' (subst body x v) τ1' τ2
        (subst_preserves_type Gamma body x v tau1 τ2 hBody hV)
  | HasType.let_type _ id e1 e2 τ1 τ2 hE1 hE2 =>
    unfold subst
    split
    · next hCap =>
      exact HasType.let_type Gamma id (subst e1 x v) e2 τ1 τ2
        (subst_preserves_type Gamma e1 x v tau1 τ1 hE1 hV)
        (HasType_lookup_eq hE2 (lookupTyp_drop_shadowed id τ1 (eq_of_beq hCap)))
    · next _ =>
      exact HasType.let_type Gamma id (subst e1 x v) (subst e2 x v) τ1 τ2
        (subst_preserves_type Gamma e1 x v tau1 τ1 hE1 hV)
        (subst_preserves_type Gamma e2 x v tau1 τ2 hE2 hV)
  | HasType.for_type _ id s e body hS hE hBody =>
    unfold subst
    split
    · next hCap =>
      exact HasType.for_type Gamma id (subst s x v) (subst e x v) body
        (subst_preserves_type Gamma s x v tau1 .intType hS hV)
        (subst_preserves_type Gamma e x v tau1 .intType hE hV)
        (HasTypeAll_lookup_eq hBody (lookupTyp_drop_shadowed id .intType (eq_of_beq hCap)))
    · next _ =>
      exact HasType.for_type Gamma id (subst s x v) (subst e x v) (substList body x v)
        (subst_preserves_type Gamma s x v tau1 .intType hS hV)
        (subst_preserves_type Gamma e x v tau1 .intType hE hV)
        (substList_preserves_type_all Gamma body x v tau1 [.unitType] hBody hV)

theorem preservation : forall {e e' : Expr} {tau : Typ} {Gamma : TypEnv},
    HasType Gamma e tau -> Step e e' -> HasType Gamma e' tau := by
  intro e e' tau Gamma hType hStep
  cases hStep with
  | binop_left op e1 e1' e2 hStep1 =>
    cases hType with
    | binop_arith =>
      rename_i hArith hE1 hE2
      exact HasType.binop_arith Gamma op e1' e2 hArith (preservation hE1 hStep1) hE2
    | binop_comp =>
      rename_i hComp hE1 hE2
      exact HasType.binop_comp Gamma op e1' e2 hComp (preservation hE1 hStep1) hE2
    | binop_logic =>
      rename_i hLogic hE1 hE2
      exact HasType.binop_logic Gamma op e1' e2 hLogic (preservation hE1 hStep1) hE2
    | binop_bitwise =>
      rename_i hBit hE1 hE2
      exact HasType.binop_bitwise Gamma op e1' e2 hBit (preservation hE1 hStep1) hE2
    | _ => contradiction
  | binop_right op v1 e2 e2' _ hStep2 =>
    cases hType with
    | binop_arith =>
      rename_i hArith hE1 hE2
      exact HasType.binop_arith Gamma op (.lit v1) e2' hArith hE1 (preservation hE2 hStep2)
    | binop_comp =>
      rename_i hComp hE1 hE2
      exact HasType.binop_comp Gamma op (.lit v1) e2' hComp hE1 (preservation hE2 hStep2)
    | binop_logic =>
      rename_i hLogic hE1 hE2
      exact HasType.binop_logic Gamma op (.lit v1) e2' hLogic hE1 (preservation hE2 hStep2)
    | binop_bitwise =>
      rename_i hBit hE1 hE2
      exact HasType.binop_bitwise Gamma op (.lit v1) e2' hBit hE1 (preservation hE2 hStep2)
    | _ => contradiction
  | binop_arith op n1 n2 r hArith _ =>
    cases hType with
    | binop_arith =>
      exact HasType.lit_int Gamma r
    | binop_comp =>
      rename_i hComp hE1 hE2
      exfalso; exact sem_isArithOp_not_spec_isCompOp op hArith hComp
    | binop_logic =>
      rename_i hLogic hE1 hE2
      cases hE1
    | binop_bitwise =>
      rename_i hBit hE1 hE2
      exact HasType.lit_int Gamma r
    | _ => contradiction
  | binop_comp op n1 n2 hComp =>
    cases hType with
    | binop_arith =>
      rename_i hArith hE1 hE2
      exfalso; exact sem_isCompOp_not_spec_isArithOp op hComp hArith
    | binop_comp =>
      exact HasType.lit_bool Gamma (Morph.Semantics.evalCompOp op n1 n2)
    | binop_logic =>
      rename_i hLogic hE1 hE2
      cases hE1
    | binop_bitwise =>
      rename_i hBit hE1 hE2
      exfalso; exact sem_isCompOp_not_spec_isBitwiseOp op hComp hBit
    | _ => contradiction
  | binop_logic _ b1 b2 r _ _ =>
    cases hType with
    | binop_arith =>
      rename_i hArith hE1 hE2
      cases hE1
    | binop_comp =>
      rename_i hComp hE1 hE2
      cases hE1
    | binop_logic =>
      exact HasType.lit_bool Gamma r
    | binop_bitwise =>
      rename_i hBit hE1 hE2
      cases hE1
    | _ => contradiction
  | binop_bitwise op n1 n2 r hBit _ =>
    cases hType with
    | binop_arith =>
      rename_i hArith hE1 hE2
      exact HasType.lit_int Gamma r
    | binop_comp =>
      rename_i hComp hE1 hE2
      exfalso; exact sem_isBitwiseOp_not_spec_isCompOp op hBit hComp
    | binop_logic =>
      rename_i hLogic hE1 hE2
      cases hE1
    | binop_bitwise =>
      exact HasType.lit_int Gamma r
    | _ => contradiction
  | binop_div_zero _ =>
    cases hType with
    | binop_arith =>
      exact HasType.lit_int Gamma 0
    | _ => contradiction
  | binop_mod_zero _ =>
    cases hType with
    | binop_arith =>
      exact HasType.lit_int Gamma 0
    | _ => contradiction
  | unop_step op e e' hStep1 =>
    cases hType with
    | unop_not =>
      rename_i hE
      exact HasType.unop_not Gamma e' (preservation hE hStep1)
    | unop_notb =>
      rename_i hE
      exact HasType.unop_notb Gamma e' (preservation hE hStep1)
    | _ => contradiction
  | unop_not b =>
    cases hType with
    | unop_not =>
      exact HasType.lit_bool Gamma (!b)
    | _ => contradiction
  | unop_notb n =>
    cases hType with
    | unop_notb =>
      exact HasType.lit_int Gamma (-n - 1)
    | _ => contradiction
  | if_cond c c' t f hStep1 =>
    cases hType with
    | if_type =>
      rename_i hC hT hF
      exact HasType.if_type Gamma c' t f tau (preservation hC hStep1) hT hF
    | _ => contradiction
  | if_true _ _ =>
    cases hType with
    | if_type =>
      rename_i hC hT hF
      exact hT
    | _ => contradiction
  | if_false _ _ =>
    cases hType with
    | if_type =>
      rename_i hC hT hF
      exact hF
    | _ => contradiction
  | let_step id e1 e1' e2 hStep1 =>
    cases hType with
    | let_type =>
      rename_i tau1 hE1 hE2
      exact HasType.let_type Gamma id e1' e2 tau1 tau (preservation hE1 hStep1) hE2
    | _ => contradiction
  | let_subst id e1 e2 _ =>
    cases hType with
    | let_type =>
      rename_i tau1 hE1 hE2
      exact subst_preserves_type Gamma e2 id.name e1 tau1 tau hE2 hE1
    | _ => contradiction
  | for_start id s s' e body hStep1 =>
    cases hType with
    | for_type =>
      rename_i hS hE hBody
      exact HasType.for_type Gamma id s' e body (preservation hS hStep1) hE hBody
    | _ => contradiction
  | for_end id s e e' body _ hStep2 =>
    cases hType with
    | for_type =>
      rename_i hS hE hBody
      exact HasType.for_type Gamma id (.lit s) e' body hS (preservation hE hStep2) hBody
    | _ => contradiction
  | for_exec id n m body _ =>
    cases hType with
    | for_type =>
      rename_i hS hE hBody
      exact HasType.let_type Gamma id (.lit (.int n))
        (.block (body ++ [.forLoop id (.lit (.int (n + 1))) (.lit (.int m)) body]))
        .intType .unitType (HasType.lit_int Gamma n)
        (HasType.block_type (extendTypEnv Gamma id.name .intType)
          (body ++ [.forLoop id (.lit (.int (n + 1))) (.lit (.int m)) body])
          [.unitType] .unitType
          (HasTypeAll_append hBody
            (HasTypeAll.cons (extendTypEnv Gamma id.name .intType)
              (.forLoop id (.lit (.int (n + 1))) (.lit (.int m)) body)
              [] .unitType []
              (HasType.for_type (extendTypEnv Gamma id.name .intType) id
                (.lit (.int (n + 1))) (.lit (.int m)) body
                (HasType.lit_int (extendTypEnv Gamma id.name .intType) (n + 1))
                (HasType.lit_int (extendTypEnv Gamma id.name .intType) m)
                (HasTypeAll_lookup_eq hBody extendTypEnv_shadow_eq))
              (HasTypeAll.nil (extendTypEnv Gamma id.name .intType)))))
    | _ => contradiction
  | for_done _ _ _ _ _ =>
    cases hType with
    | for_type =>
      exact HasType.lit_unit Gamma
    | _ => contradiction
  | block_head e' e'' rest hStep1 =>
    cases hType with
    | block_type =>
      rename_i taus hAll
      cases taus with
      | nil =>
        exact HasType.block_type Gamma (e'' :: rest) [] tau
          (HasTypeAll.cons Gamma e'' rest tau [] (preservation (HasTypeAll_cons_head hAll) hStep1) (HasTypeAll_cons_tail hAll))
      | cons tau' taus' =>
        exact HasType.block_type Gamma (e'' :: rest) (tau' :: taus') tau
          (HasTypeAll.cons Gamma e'' rest tau' (taus' ++ [tau]) (preservation (HasTypeAll_cons_head hAll) hStep1) (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_singleton v _ =>
    cases hType with
    | block_type =>
      rename_i taus hAll
      cases taus with
      | nil => exact HasTypeAll_cons_head hAll
      | cons tau' taus' =>
        exfalso
        exact append_singleton_ne_nil taus' tau (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_lam_singleton xs body =>
    cases hType with
    | block_type =>
      rename_i taus hAll
      cases taus with
      | nil => exact HasTypeAll_cons_head hAll
      | cons tau' taus' =>
        exfalso
        exact append_singleton_ne_nil taus' tau (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_pop e_val head rest _ =>
    cases hType with
    | block_type =>
      rename_i taus hAll
      cases taus with
      | nil =>
        exfalso
        have h := HasTypeAll_length Gamma (e_val :: head :: rest) ([] ++ [tau]) hAll
        simp only [List.length_cons, List.length_append, List.length_nil] at h
        omega
      | cons tau' taus' =>
        exact HasType.block_type Gamma (head :: rest) taus' tau (HasTypeAll_cons_tail hAll)
    | _ => contradiction
  | app_fn fn fn' args hs =>
    cases hType with
    | app_type =>
      rename_i τs' τ' hFn hArgs'
      exact HasType.app_type Gamma fn' args τs' τ' (preservation hFn hs) hArgs'
    | _ => contradiction
  | app_arg fn a a' rest _ hs =>
    cases hType with
    | app_type =>
      rename_i τs' τ' hFn hArgs'
      have hHead := HasTypeAll_cons_head hArgs'
      have hTail := HasTypeAll_cons_tail hArgs'
      exact HasType.app_type Gamma fn (a' :: rest) τs' τ' hFn
        (HasTypeAll.cons Gamma a' rest _ _ (preservation hHead hs) hTail)
    | _ => contradiction
  | app_lam xs body args _ =>
    cases hType with
    | app_type =>
      rename_i τs' τ' hFn hArgs'
      have hLam : HasType Gamma (.lam xs body) (.functionType τs' τ') := by
        cases hFn with
        | lam_type => rfl
        | _ => contradiction
      have hBody : HasType (extendTypEnv Gamma xs.head.name τs'.head) body τ' := by
        cases hLam with
        | lam_type _ _ _ _ hBody => exact hBody
        | _ => contradiction
      have hArg : HasType Gamma args.head τs'.head := by
        cases hArgs' with
        | cons _ _ _ _ hHead _ => exact hHead
        | nil => contradiction
      exact subst_preserves_type Gamma body xs.head.name args.head τs'.head τ' hBody hArg
    | _ => contradiction

end Morph.Proofs.TypeSoundness
