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

theorem HasType_var_inv (Γ : TypEnv) (id : Id) (τ : Typ) :
    HasType Γ (.var id) τ → lookupTyp Γ id.name = some τ := by
  intro h; cases h with | var_type => assumption

theorem HasType_lit_int_inv (Γ : TypEnv) (n : Int) (τ : Typ) :
    HasType Γ (.lit (.int n)) τ → τ = .intType := by
  intro h; cases h with | lit_int => rfl

theorem HasType_lit_bool_inv (Γ : TypEnv) (b : Bool) (τ : Typ) :
    HasType Γ (.lit (.bool b)) τ → τ = .boolType := by
  intro h; cases h with | lit_bool => rfl

theorem HasType_lit_string_inv (Γ : TypEnv) (s : String) (τ : Typ) :
    HasType Γ (.lit (.string s)) τ → τ = .stringType := by
  intro h; cases h with | lit_string => rfl

theorem HasType_lit_unit_inv (Γ : TypEnv) (τ : Typ) :
    HasType Γ (.lit .unit) τ → τ = .unitType := by
  intro h; cases h with | lit_unit => rfl

theorem HasType_lit_pointer_inv (Γ : TypEnv) (p : Pointer) (τ : Typ) :
    HasType Γ (.lit (.pointer p)) τ → τ = .pointerType := by
  intro h; cases h with | lit_pointer => rfl

theorem HasType_unop_not_inv (Γ : TypEnv) (e : Expr) (τ : Typ) :
    HasType Γ (.unop .not e) τ → τ = .boolType := by
  intro h; cases h with | unop_not => rfl

theorem HasType_unop_notb_inv (Γ : TypEnv) (e : Expr) (τ : Typ) :
    HasType Γ (.unop .notb e) τ → τ = .intType := by
  intro h; cases h with | unop_notb => rfl

/-! ## Weakening
    NOTE: Correct weakening requires freshness precondition: x ∉ freeVars(e).
    Without it, the lemma is unsound (see ADR-006). -/

private theorem lookupTyp_extend_ne' {Γ : TypEnv} {name y : String} {typ : Typ} (hne : name ≠ y) :
    lookupTyp (extendTypEnv Γ name typ) y = lookupTyp Γ y := by
  unfold extendTypEnv lookupTyp
  simp only [List.find?_cons]
  split
  · next h => exact absurd (eq_of_beq h) hne
  · rfl

private theorem lookupTyp_extend_eq' {Γ : TypEnv} {name : String} {typ : Typ} :
    lookupTyp (extendTypEnv Γ name typ) name = some typ := by
  unfold extendTypEnv lookupTyp
  simp only [List.find?_cons, beq_self_eq_true]
  simp [Option.map]

private theorem extendTypEnv_swap' {Γ : TypEnv} {x y : String} {τx τy : Typ} (hne : x ≠ y) (z : String) :
    lookupTyp (extendTypEnv (extendTypEnv Γ x τx) y τy) z =
    lookupTyp (extendTypEnv (extendTypEnv Γ y τy) x τx) z := by
  unfold extendTypEnv lookupTyp
  simp only [List.find?_cons]
  cases Decidable.em (z = x) with
  | inl hz =>
    cases Decidable.em (z = y) with
    | inl hz2 => exfalso; exact hne (hz ▸ hz2)
    | inr hz2 =>
      have h1 : ¬(y == x) := fun h => hne (eq_of_beq h).symm
      have h2 : ¬(y == z) := fun h => hz2 (eq_of_beq h).symm
      simp only [h2]
  | inr hz =>
    cases Decidable.em (z = y) with
    | inl hz' =>
      have h1 : ¬(x == y) := fun h => hne (eq_of_beq h)
      have h2 : ¬(x == z) := fun h => hz (eq_of_beq h).symm
      simp only [h2]
    | inr hz' =>
      have h1 : ¬(y == z) := fun h => hz' (eq_of_beq h).symm
      have h2 : ¬(x == z) := fun h => hz (eq_of_beq h).symm
      simp only [h1, h2]

private theorem extendTypEnv_lookup_eq' {Γ Γ' : TypEnv} {name : String} {typ : Typ}
    (hEq : ∀ x, lookupTyp Γ x = lookupTyp Γ' x) (y : String) :
    lookupTyp (extendTypEnv Γ name typ) y = lookupTyp (extendTypEnv Γ' name typ) y := by
  cases Decidable.em (name = y) with
  | inl hEq' => rw [hEq', lookupTyp_extend_eq', lookupTyp_extend_eq']
  | inr hNe => rw [lookupTyp_extend_ne' hNe, lookupTyp_extend_ne' hNe]; exact hEq y

mutual

private theorem HasType_lookup_eq' {Γ Γ' : TypEnv} {e : Expr} {τ : Typ}
    (h : HasType Γ e τ) (hEq : ∀ x, lookupTyp Γ x = lookupTyp Γ' x) : HasType Γ' e τ := by
  match h with
  | HasType.var_type _ id τ hLookup =>
    exact HasType.var_type Γ' id τ (Eq.trans (Eq.symm (hEq id.name)) hLookup)
  | HasType.lit_int _ n => exact HasType.lit_int Γ' n
  | HasType.lit_bool _ b => exact HasType.lit_bool Γ' b
  | HasType.lit_string _ s => exact HasType.lit_string Γ' s
  | HasType.lit_unit _ => exact HasType.lit_unit Γ'
  | HasType.lit_pointer _ p => exact HasType.lit_pointer Γ' p
  | HasType.unop_not _ e' hE' => exact HasType.unop_not Γ' e' (HasType_lookup_eq' hE' hEq)
  | HasType.unop_notb _ e' hE' => exact HasType.unop_notb Γ' e' (HasType_lookup_eq' hE' hEq)
  | HasType.binop_arith _ op e1 e2 hArith hE1 hE2 =>
    exact HasType.binop_arith Γ' op e1 e2 hArith (HasType_lookup_eq' hE1 hEq) (HasType_lookup_eq' hE2 hEq)
  | HasType.binop_comp _ op e1 e2 hComp hE1 hE2 =>
    exact HasType.binop_comp Γ' op e1 e2 hComp (HasType_lookup_eq' hE1 hEq) (HasType_lookup_eq' hE2 hEq)
  | HasType.binop_logic _ op e1 e2 hLogic hE1 hE2 =>
    exact HasType.binop_logic Γ' op e1 e2 hLogic (HasType_lookup_eq' hE1 hEq) (HasType_lookup_eq' hE2 hEq)
  | HasType.binop_bitwise _ op e1 e2 hBit hE1 hE2 =>
    exact HasType.binop_bitwise Γ' op e1 e2 hBit (HasType_lookup_eq' hE1 hEq) (HasType_lookup_eq' hE2 hEq)
  | HasType.lam_type _ x body τ1 τ2 hBody =>
    exact HasType.lam_type Γ' x body τ1 τ2 (HasType_lookup_eq' hBody (extendTypEnv_lookup_eq' hEq))
  | HasType.app_type _ fn args τs τ hFn hArgs =>
    exact HasType.app_type Γ' fn args τs τ (HasType_lookup_eq' hFn hEq) (HasTypeAll_lookup_eq' hArgs hEq)
  | HasType.let_type _ id e1 e2 τ1 τ2 hE1 hE2 =>
    exact HasType.let_type _ _ _ _ _ _
      (HasType_lookup_eq' hE1 hEq)
      (HasType_lookup_eq' hE2 (extendTypEnv_lookup_eq' hEq))
  | HasType.if_type _ c t f τ hC hT hF =>
    exact HasType.if_type Γ' c t f τ (HasType_lookup_eq' hC hEq) (HasType_lookup_eq' hT hEq) (HasType_lookup_eq' hF hEq)
  | HasType.for_type _ id' s e body hS hE hBody =>
    exact HasType.for_type Γ' id' s e body
      (HasType_lookup_eq' hS hEq) (HasType_lookup_eq' hE hEq)
      (HasTypeAll_lookup_eq' hBody (extendTypEnv_lookup_eq' hEq))
  | HasType.block_type _ exprs τs τ hAll =>
    exact HasType.block_type Γ' exprs τs τ (HasTypeAll_lookup_eq' hAll hEq)

private theorem HasTypeAll_lookup_eq' {Γ Γ' : TypEnv} {es : List Expr} {τs : List Typ}
    (h : HasTypeAll Γ es τs) (hEq : ∀ x, lookupTyp Γ x = lookupTyp Γ' x) : HasTypeAll Γ' es τs := by
  match h with
  | HasTypeAll.nil _ => exact HasTypeAll.nil Γ'
  | HasTypeAll.cons _ e es τ τs hE hRest =>
    exact HasTypeAll.cons _ e es τ τs (HasType_lookup_eq' hE hEq) (HasTypeAll_lookup_eq' hRest hEq)

end

mutual

private theorem weakening_hasType (Γ : TypEnv) (e : Expr) (τ : Typ) (x : String) (σ : Typ)
    (hFresh : x ∉ freeVars e) (h : HasType Γ e τ) : HasType (extendTypEnv Γ x σ) e τ := by
  match h with
  | HasType.var_type _ id τ hL =>
    cases Decidable.em (x = id.name) with
    | inl hEq =>
      exfalso; exact hFresh (by rw [hEq]; simp only [freeVars]; exact List.mem_cons_self)
    | inr hNe =>
      exact HasType.var_type (extendTypEnv Γ x σ) id τ
        (by rw [lookupTyp_extend_ne' hNe]; exact hL)
  | HasType.lit_int _ _ => exact HasType.lit_int _ _
  | HasType.lit_bool _ _ => exact HasType.lit_bool _ _
  | HasType.lit_string _ _ => exact HasType.lit_string _ _
  | HasType.lit_unit _ => exact HasType.lit_unit _
  | HasType.lit_pointer _ _ => exact HasType.lit_pointer _ _
  | HasType.unop_not _ e' hE =>
    exact HasType.unop_not _ _ (weakening_hasType _ _ .boolType x σ
      (fun h => by simp only [freeVars] at hFresh; exact hFresh h) hE)
  | HasType.unop_notb _ e' hE =>
    exact HasType.unop_notb _ _ (weakening_hasType _ _ .intType x σ
      (fun h => by simp only [freeVars] at hFresh; exact hFresh h) hE)
  | HasType.binop_arith _ op e1 e2 hA hE1 hE2 =>
    exact HasType.binop_arith _ op _ _ hA
      (weakening_hasType _ _ .intType x σ
        (fun (h : x ∈ freeVars e1) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (freeVars e2) h)) hE1)
      (weakening_hasType _ _ .intType x σ
        (fun (h : x ∈ freeVars e2) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_right (freeVars e1) h)) hE2)
  | HasType.binop_comp _ op e1 e2 hC hE1 hE2 =>
    exact HasType.binop_comp _ op _ _ hC
      (weakening_hasType _ _ .intType x σ
        (fun (h : x ∈ freeVars e1) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (freeVars e2) h)) hE1)
      (weakening_hasType _ _ .intType x σ
        (fun (h : x ∈ freeVars e2) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_right (freeVars e1) h)) hE2)
  | HasType.binop_logic _ op e1 e2 hL hE1 hE2 =>
    exact HasType.binop_logic _ op _ _ hL
      (weakening_hasType _ _ .boolType x σ
        (fun (h : x ∈ freeVars e1) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (freeVars e2) h)) hE1)
      (weakening_hasType _ _ .boolType x σ
        (fun (h : x ∈ freeVars e2) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_right (freeVars e1) h)) hE2)
  | HasType.binop_bitwise _ op e1 e2 hB hE1 hE2 =>
    exact HasType.binop_bitwise _ op _ _ hB
      (weakening_hasType _ _ .intType x σ
        (fun (h : x ∈ freeVars e1) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (freeVars e2) h)) hE1)
      (weakening_hasType _ _ .intType x σ
        (fun (h : x ∈ freeVars e2) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_right (freeVars e1) h)) hE2)
  | HasType.lam_type _ x' body τ1 τ2 hB =>
    have hNe : x'.name ≠ x := by
      intro hEq; exfalso
      simp only [freeVars] at hFresh
      exact hFresh (hEq ▸ @List.mem_cons_self String x'.name (freeVars body))
    have hW : HasType (extendTypEnv (extendTypEnv Γ x'.name τ1) x σ) body τ2 :=
      weakening_hasType (extendTypEnv Γ x'.name τ1) body τ2 x σ
        (fun (h : x ∈ freeVars body) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_right [x'.name] h)) hB
    exact HasType.lam_type _ x' body τ1 τ2
      (HasType_lookup_eq' hW (extendTypEnv_swap' hNe))
  | HasType.app_type _ fn args τs τ hF hA =>
    exact HasType.app_type _ fn args τs τ
      (weakening_hasType _ _ (.functionType τs τ) x σ
        (fun (h : x ∈ freeVars fn) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (args.flatMap freeVars) h)) hF)
      (weakening_hasType_all Γ args τs x σ
        (fun (h : x ∈ args.flatMap freeVars) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_right (freeVars fn) h)) hA)
  | HasType.let_type _ id e1 e2 τ1 τ2 hE1 hE2 =>
    have hNe : id.name ≠ x := by
      intro hEq; exfalso
      simp only [freeVars] at hFresh
      exact hFresh (hEq ▸ List.mem_append_left (freeVars e2)
        (List.mem_append_right (freeVars e1) (@List.mem_cons_self String id.name [])))
    exact HasType.let_type _ _ _ _ _ _
      (weakening_hasType _ _ τ1 x σ
        (fun (h : x ∈ freeVars e1) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (freeVars e2)
            (List.mem_append_left [id.name] h))) hE1)
      (HasType_lookup_eq'
        (weakening_hasType (extendTypEnv Γ id.name τ1) e2 τ2 x σ
          (fun (h : x ∈ freeVars e2) => by
            simp only [freeVars] at hFresh
            exact hFresh (List.mem_append_right (freeVars e1 ++ [id.name]) h)) hE2)
        (extendTypEnv_swap' hNe))
  | HasType.if_type _ c t f τ hC hT hF =>
    exact HasType.if_type _ _ _ _ τ
      (weakening_hasType _ _ .boolType x σ
        (fun (h : x ∈ freeVars c) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (freeVars f)
            (List.mem_append_left (freeVars t) h))) hC)
      (weakening_hasType _ _ τ x σ
        (fun (h : x ∈ freeVars t) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (freeVars f)
            (List.mem_append_right (freeVars c) h))) hT)
      (weakening_hasType _ _ τ x σ
        (fun (h : x ∈ freeVars f) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_right (freeVars c ++ freeVars t) h)) hF)
  | HasType.for_type _ id s e' body hS hE hB =>
    have hNe : id.name ≠ x := by
      intro hEq; exfalso
      simp only [freeVars] at hFresh
      exact hFresh (hEq ▸ List.mem_append_left (body.flatMap freeVars)
        (List.mem_append_right (freeVars s ++ freeVars e')
          (@List.mem_cons_self String id.name [])))
    have hW : HasTypeAll (extendTypEnv (extendTypEnv Γ id.name .intType) x σ) body [.unitType] :=
      weakening_hasType_all (extendTypEnv Γ id.name .intType) body [.unitType] x σ
        (fun (h : x ∈ body.flatMap freeVars) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_right (freeVars s ++ freeVars e' ++ [id.name]) h)) hB
    exact HasType.for_type _ id s e' body
      (weakening_hasType _ _ .intType x σ
        (fun (h : x ∈ freeVars s) => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (body.flatMap freeVars)
            (List.mem_append_left [id.name]
              (List.mem_append_left (freeVars e') h)))) hS)
      (weakening_hasType _ _ .intType x σ
        (fun (h : x ∈ freeVars e') => by
          simp only [freeVars] at hFresh
          exact hFresh (List.mem_append_left (body.flatMap freeVars)
            (List.mem_append_left [id.name]
              (List.mem_append_right (freeVars s) h)))) hE)
      (@HasTypeAll_lookup_eq'
        (extendTypEnv (extendTypEnv Γ id.name .intType) x σ)
        (extendTypEnv (extendTypEnv Γ x σ) id.name .intType)
        body [.unitType] hW (extendTypEnv_swap' hNe))
  | HasType.block_type _ exprs τs τ hA =>
    exact HasType.block_type _ exprs τs τ
      (weakening_hasType_all Γ exprs (τs ++ [τ]) x σ
        (fun h => by simp only [freeVars] at hFresh; exact hFresh h) hA)

private theorem weakening_hasType_all (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (x : String) (σ : Typ) (hFresh : x ∉ List.flatMap freeVars es)
    (h : HasTypeAll Γ es τs) : HasTypeAll (extendTypEnv Γ x σ) es τs := by
  match h with
  | HasTypeAll.nil _ => exact HasTypeAll.nil _
  | HasTypeAll.cons _ e es' τ τs' hE hR =>
    exact HasTypeAll.cons _ _ _ _ _
      (weakening_hasType _ _ _ x σ (fun h => hFresh (List.mem_append_left _ h)) hE)
      (weakening_hasType_all _ es' _ x σ (fun h => hFresh (List.mem_append_right (freeVars e) h)) hR)

end

theorem weakening (Γ : TypEnv) (e : Expr) (τ : Typ) (x : String) (σ : Typ)
    (hFresh : x ∉ freeVars e) :
    HasType Γ e τ → HasType (extendTypEnv Γ x σ) e τ :=
  weakening_hasType Γ e τ x σ hFresh

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
