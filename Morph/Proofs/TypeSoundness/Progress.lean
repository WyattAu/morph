/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem
import Morph.Specs.TypeSystem.Lemmas
import Morph.Proofs.TypeSoundness.ExprDepth

namespace Morph.Proofs.TypeSoundness

open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Morph.Specs.TypeSystem
open HasType

/-! # Progress Theorem

Every well-typed closed term is either a value or can take a step.
-/

/-! ## Canonical Forms -/

theorem canonical_bool : forall {e : Expr},
    IsValue e -> HasType [] e .boolType -> exists b, e = .lit (.bool b) := by
  intro e hv ht
  cases hv with
  | lit v => cases v with
    | bool b => exact ⟨b, rfl⟩
    | _ => cases ht
  | lam _ _ => cases ht

theorem canonical_int : forall {e : Expr},
    IsValue e -> HasType [] e .intType -> exists n, e = .lit (.int n) := by
  intro e hv ht
  cases hv with
  | lit v => cases v with
    | int n => exact ⟨n, rfl⟩
    | _ => cases ht
  | lam _ _ => cases ht

/-! ## Helpers -/

private theorem lookupTyp_nil (name : String) : lookupTyp [] name = none := by
  unfold lookupTyp; simp

private theorem sub_lt_d (d : Nat) {sub parent : Expr}
    (hSub : exprDepth sub < exprDepth parent)
    (hDepth : exprDepth parent < d + 1) : exprDepth sub < d :=
  Nat.lt_of_lt_of_le hSub (Nat.le_of_lt_succ hDepth)

private theorem depth_unop (op : Operator) {e : Expr} :
    exprDepth e < exprDepth (.unop op e) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_binop_l (op : Operator) {e1 e2 : Expr} :
    exprDepth e1 < exprDepth (.binop op e1 e2) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_binop_r (op : Operator) {e1 e2 : Expr} :
    exprDepth e2 < exprDepth (.binop op e1 e2) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (Nat.lt_succ_self _)

private theorem depth_let_l {id : Id} {e1 e2 : Expr} :
    exprDepth e1 < exprDepth (.let id e1 e2) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_if_c {c t f : Expr} :
    exprDepth c < exprDepth (.ifThenElse c t f) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_for_s {id : Id} {s e : Expr} {body : List Expr} :
    exprDepth s < exprDepth (.forLoop id s e body) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left (exprDepth s) _) (Nat.lt_succ_self _)

private theorem depth_for_e {id : Id} {s e : Expr} {body : List Expr} :
    exprDepth e < exprDepth (.forLoop id s e body) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.le_max_left (exprDepth e) (listExprDepth body))
      (Nat.le_max_right (exprDepth s) ((exprDepth e).max (listExprDepth body))))
    (Nat.lt_succ_self _)

private theorem depth_block_head {e : Expr} {rest : List Expr} :

private theorem depth_app_fn {fn : Expr} {args : List Expr} :
    exprDepth fn < exprDepth (.app fn args) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)
    exprDepth e < exprDepth (.block (e :: rest)) := by
  simp only [exprDepth, listExprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left (exprDepth e) (listExprDepth rest)) (Nat.lt_succ_self _)

private theorem HasTypeAll_nil_types {Γ : TypEnv} {tys : List Typ} :
    HasTypeAll Γ [] tys → tys = [] := by
  intro h
  cases h with
  | nil => rfl

private theorem HasTypeAll_length (Γ : TypEnv) (es : List Expr) (taus : List Typ) :
    HasTypeAll Γ es taus → es.length = taus.length := by
  intro h
  cases es with
  | nil => cases taus with | nil => cases h with | nil => rfl | cons => cases h
  | cons e es' =>
    cases taus with
    | nil => cases h
    | cons tau taus' =>
      simp only [List.length_cons]
      match h with
      | HasTypeAll.cons _ _ _ _ _ _ hRest =>
        exact congrArg (· + 1) (HasTypeAll_length Γ es' taus' hRest)

private theorem HasTypeAll_append_cons_head {Γ : TypEnv} {e : Expr} {es : List Expr}
    {τs : List Typ} {τ : Typ} (h : HasTypeAll Γ (e :: es) (τs ++ [τ])) :
    ∃ τ_h, HasType Γ e τ_h := by
  cases τs with
  | nil =>
    change HasTypeAll Γ (e :: es) [τ] at h
    cases h with
    | cons _ _ _ _ _ hE _ => exact ⟨_, hE⟩
  | cons τ' τs' =>
    change HasTypeAll Γ (e :: es) (τ' :: (τs' ++ [τ])) at h
    cases h with
    | cons _ _ _ _ _ hE _ => exact ⟨_, hE⟩

/-! ## Progress (strong induction on depth) -/

private theorem progress_strong :
    forall (d : Nat) (e : Expr), exprDepth e < d ->
    forall (tau : Typ), HasType [] e tau -> IsValue e \/ exists e', Step e e' := by
  intro d
  induction d with
  | zero =>
    intro e hDepth _ _
    exact absurd hDepth (Nat.not_lt_zero _)
  | succ d ih =>
    intro e hDepth tau hType
    cases hType with
    | var_type _ id _ hLookup =>
      exfalso
      exact absurd (lookupTyp_nil id.name |>.symm.trans hLookup) (by contradiction)
    | lit_int _ n => left; exact IsValue.lit (Value.int n)
    | lit_bool _ b => left; exact IsValue.lit (Value.bool b)
    | lit_string _ s => left; exact IsValue.lit (Value.string s)
    | lit_unit => left; exact IsValue.lit Value.unit
    | lit_pointer _ p => left; exact IsValue.lit (Value.pointer p)
    | unop_not _ eSub hSub =>
      have hRes := ih eSub (sub_lt_d d (depth_unop .not) hDepth) .boolType hSub
      cases hRes with
      | inl hv =>
        obtain ⟨b, hb⟩ := canonical_bool hv hSub
        rw [hb]; right; exact ⟨.lit (.bool (!b)), Step.unop_not b⟩
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.unop .not e', Step.unop_step .not eSub e' hs⟩
    | unop_notb _ eSub hSub =>
      have hRes := ih eSub (sub_lt_d d (depth_unop .notb) hDepth) .intType hSub
      cases hRes with
      | inl hv =>
        obtain ⟨k, hk⟩ := canonical_int hv hSub
        rw [hk]; right; exact ⟨.lit (.int (-k - 1)), Step.unop_notb k⟩
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.unop .notb e', Step.unop_step .notb eSub e' hs⟩
    | binop_arith _ op e1 e2 hArith hSub1 hSub2 =>
      have h1 := ih e1 (sub_lt_d d (depth_binop_l op) hDepth) .intType hSub1
      have h2 := ih e2 (sub_lt_d d (depth_binop_r op) hDepth) .intType hSub2
      cases h1 with
      | inl hv1 =>
        obtain ⟨k1, hk1⟩ := canonical_int hv1 hSub1
        rw [hk1]
        cases h2 with
        | inl hv2 =>
          obtain ⟨k2, hk2⟩ := canonical_int hv2 hSub2
          rw [hk2]
          match hRes : evalArithOp op k1 k2 with
          | some r =>
            right; exact ⟨.lit (.int r), Step.binop_arith op k1 k2 r hArith hRes⟩
          | none =>
            cases op with
            | add | sub | mul =>
              exfalso; unfold evalArithOp at hRes; contradiction
            | div =>
              cases k2 with
              | ofNat n =>
                cases n with
                | zero => right; exact ⟨.lit (.int 0), Step.binop_div_zero k1⟩
                | succ _ => exfalso; unfold evalArithOp at hRes; contradiction
              | negSucc _ => exfalso; unfold evalArithOp at hRes; contradiction
            | mod =>
              cases k2 with
              | ofNat n =>
                cases n with
                | zero => right; exact ⟨.lit (.int 0), Step.binop_mod_zero k1⟩
                | succ _ => exfalso; unfold evalArithOp at hRes; contradiction
              | negSucc _ => exfalso; unfold evalArithOp at hRes; contradiction
            | _ => exfalso; unfold Morph.Specs.TypeSystem.isArithOp at hArith; exact hArith.elim
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop op (.lit (.int k1)) e2',
            Step.binop_right op (.int k1) e2 e2' (IsValue.lit (.int k1)) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop op e1' e2, Step.binop_left op e1 e1' e2 hs⟩
    | binop_comp _ op e1 e2 hComp hSub1 hSub2 =>
      have h1 := ih e1 (sub_lt_d d (depth_binop_l op) hDepth) .intType hSub1
      have h2 := ih e2 (sub_lt_d d (depth_binop_r op) hDepth) .intType hSub2
      cases h1 with
      | inl hv1 =>
        obtain ⟨k1, hk1⟩ := canonical_int hv1 hSub1
        rw [hk1]
        cases h2 with
        | inl hv2 =>
          obtain ⟨k2, hk2⟩ := canonical_int hv2 hSub2
          rw [hk2]
          right; exact ⟨.lit (.bool (evalCompOp op k1 k2)),
            Step.binop_comp op k1 k2 hComp⟩
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop op (.lit (.int k1)) e2',
            Step.binop_right op (.int k1) e2 e2' (IsValue.lit (.int k1)) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop op e1' e2, Step.binop_left op e1 e1' e2 hs⟩
    | binop_logic _ op e1 e2 hLogic hSub1 hSub2 =>
      have h1 := ih e1 (sub_lt_d d (depth_binop_l op) hDepth) .boolType hSub1
      have h2 := ih e2 (sub_lt_d d (depth_binop_r op) hDepth) .boolType hSub2
      cases h1 with
      | inl hv1 =>
        obtain ⟨b1, hb1⟩ := canonical_bool hv1 hSub1
        rw [hb1]
        cases h2 with
        | inl hv2 =>
          obtain ⟨b2, hb2⟩ := canonical_bool hv2 hSub2
          rw [hb2]
          match hRes : evalLogicOp op b1 b2 with
          | some r =>
            right; exact ⟨.lit (.bool r), Step.binop_logic op b1 b2 r hLogic hRes⟩
          | none =>
            exfalso
            obtain ⟨r, hr⟩ := evalLogicOp_some_of_isLogicOp op b1 b2 hLogic
            rw [hr] at hRes
            exact absurd hRes (by contradiction)
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop op (.lit (.bool b1)) e2',
            Step.binop_right op (.bool b1) e2 e2' (IsValue.lit (.bool b1)) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop op e1' e2, Step.binop_left op e1 e1' e2 hs⟩
    | binop_bitwise _ op e1 e2 hBitwise hSub1 hSub2 =>
      have h1 := ih e1 (sub_lt_d d (depth_binop_l op) hDepth) .intType hSub1
      have h2 := ih e2 (sub_lt_d d (depth_binop_r op) hDepth) .intType hSub2
      cases h1 with
      | inl hv1 =>
        obtain ⟨k1, hk1⟩ := canonical_int hv1 hSub1
        rw [hk1]
        cases h2 with
        | inl hv2 =>
          obtain ⟨k2, hk2⟩ := canonical_int hv2 hSub2
          rw [hk2]
          match hRes : evalBitwiseOp op k1 k2 with
          | some r =>
            right; exact ⟨.lit (.int r), Step.binop_bitwise op k1 k2 r hBitwise hRes⟩
          | none =>
            exfalso
            obtain ⟨r, hr⟩ := evalBitwiseOp_some_of_isBitwiseOp op k1 k2 hBitwise
            rw [hr] at hRes
            exact absurd hRes (by contradiction)
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop op (.lit (.int k1)) e2',
            Step.binop_right op (.int k1) e2 e2' (IsValue.lit (.int k1)) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop op e1' e2, Step.binop_left op e1 e1' e2 hs⟩
    | lam_type _ x body _ _ _ => left; exact IsValue.lam [x] body
    | app_type _ fn args τs τ hFn hArgs =>
      have ih_fn := ih fn (sub_lt_d d depth_app_fn hDepth) (.functionType τs τ) hFn
      cases ih_fn with
      | inl hv =>
        cases hv with
        | lit _ => exfalso; cases hFn with <;> contradiction
        | lam xs body =>
          cases hFn with
          | lam_type _ x' body' τ1 τ2 _ =>
            right
            have hArgsLen : args.length = [x'].length := by
              have h1 := HasTypeAll_length [] args [τ1] hArgs
              simp only [List.length_cons, List.length_nil] at h1
              simp only [List.length_cons, List.length_nil]
              exact h1
            exact ⟨substAll body' [x'] args, Step.app_lam [x'] body' args hArgsLen⟩
          | _ => contradiction
      | inr hStep_fn =>
        obtain ⟨fn', hs⟩ := hStep_fn
        right; exact ⟨.app fn' args, Step.app_fn fn fn' args hs⟩
    | let_type _ id e1 e2 tau1 tau2 hSub1 hSub2 =>
      have h1 := ih e1 (sub_lt_d d depth_let_l hDepth) tau1 hSub1
      cases h1 with
      | inl hv =>
        cases hv with
        | lit v =>
          right; exact ⟨subst e2 id.name (.lit v), Step.let_subst id (.lit v) e2 (IsValue.lit v)⟩
        | lam xs body =>
          right; exact ⟨subst e2 id.name (.lam xs body), Step.let_subst id (.lam xs body) e2 (IsValue.lam xs body)⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.let id e1' e2, Step.let_step id e1 e1' e2 hs⟩
    | if_type _ c t f tau hCond _ _ =>
      have hc := ih c (sub_lt_d d depth_if_c hDepth) .boolType hCond
      cases hc with
      | inl hv =>
        obtain ⟨b, hb⟩ := canonical_bool hv hCond
        rw [hb]
        cases b with
        | true => right; exact ⟨t, Step.if_true t f⟩
        | false => right; exact ⟨f, Step.if_false t f⟩
      | inr hStep =>
        obtain ⟨c', hs⟩ := hStep
        right; exact ⟨.ifThenElse c' t f, Step.if_cond c c' t f hs⟩
    | for_type _ id s e body hStart hEnd hBody =>
      have hResS := ih s (sub_lt_d d depth_for_s hDepth) .intType hStart
      cases hResS with
      | inl hv =>
        obtain ⟨k1, hk1⟩ := canonical_int hv hStart
        rw [hk1]
        have hResE := ih e (sub_lt_d d depth_for_e hDepth) .intType hEnd
        cases hResE with
        | inl hv2 =>
          obtain ⟨k2, hk2⟩ := canonical_int hv2 hEnd
          rw [hk2]
          exact dite (k1 < k2)
            (fun hLt => Or.inr ⟨_, Step.for_exec id k1 k2 body hLt⟩)
            (fun hNlt => Or.inr ⟨_, Step.for_done id k1 k2 body (by omega)⟩)
        | inr hStep2 =>
          obtain ⟨e', hs⟩ := hStep2
          right; exact ⟨_, Step.for_end id (.int k1) e e' body (IsValue.lit (.int k1)) hs⟩
      | inr hStep1 =>
        obtain ⟨s', hs⟩ := hStep1
        right; exact ⟨_, Step.for_start id s s' e body hs⟩
    | block_type _ exprs τs τ hAll =>
      cases exprs with
      | nil =>
        exfalso
        have hLen := congrArg List.length (HasTypeAll_nil_types hAll)
        rw [List.length_append, List.length_cons, List.length_nil] at hLen
        omega
      | cons head rest =>
        obtain ⟨τ_h, hHead⟩ := HasTypeAll_append_cons_head hAll
        have hRes := ih head (sub_lt_d d depth_block_head hDepth) τ_h hHead
        cases hRes with
        | inr hStep =>
          obtain ⟨head', hs⟩ := hStep
          right; exact ⟨_, Step.block_head head head' rest hs⟩
        | inl hv =>
          cases rest with
          | nil =>
            cases hv with
            | lit v => right; exact ⟨_, Step.block_singleton v (IsValue.lit v)⟩
            | lam xs body => right; exact ⟨_, Step.block_lam_singleton xs body⟩
          | cons head2 rest2 =>
            right; exact ⟨_, Step.block_pop head head2 rest2 hv⟩

/-! ## Main Theorem -/

theorem progress : forall {e : Expr} {tau : Typ},
    HasType [] e tau -> IsValue e \/ exists e', Step e e' := by
  intro e tau h
  exact progress_strong (exprDepth e + 1) e (Nat.lt_succ_self _) tau h

end Morph.Proofs.TypeSoundness
