/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

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
open Morph.Specs.TypeSystem
open HasType

/-! # Progress Theorem

Every well-typed closed term is either a value or can take a step.
Closed means: empty bound-variable context (bvs = []) and empty free-variable env (Γ = []).
-/

/-! ## Canonical Forms -/

theorem canonical_bool : forall {e : Expr},
    IsValue e -> HasType [] [] e .boolType -> exists b, e = .lit (.bool b) := by
  intro e hv ht
  cases hv with
  | lit v => cases v with
    | bool b => exact ⟨b, rfl⟩
    | _ => cases ht
  | lam _ _ => cases ht
  | none_ => cases ht
  | err_ _ _ => cases ht
  | ok_ _ _ => cases ht
  | some_ _ _ => cases ht
  | tuple_ _ _ => cases ht
  | array_ _ _ => cases ht
  | refCreate _ _ _ _ => cases ht

theorem canonical_int : forall {e : Expr},
    IsValue e -> HasType [] [] e .intType -> exists n, e = .lit (.int n) := by
  intro e hv ht
  cases hv with
  | lit v => cases v with
    | int n => exact ⟨n, rfl⟩
    | _ => cases ht
  | lam _ _ => cases ht
  | none_ => cases ht
  | err_ _ _ => cases ht
  | ok_ _ _ => cases ht
  | some_ _ _ => cases ht
  | tuple_ _ _ => cases ht
  | array_ _ _ => cases ht
  | refCreate _ _ _ _ => cases ht

theorem canonical_string : forall {e : Expr},
    IsValue e -> HasType [] [] e .stringType -> exists s, e = .lit (.string s) := by
  intro e hv ht
  cases hv with
  | lit v => cases v with
    | string s => exact ⟨s, rfl⟩
    | _ => cases ht
  | lam _ _ => cases ht
  | none_ => cases ht
  | err_ _ _ => cases ht
  | ok_ _ _ => cases ht
  | some_ _ _ => cases ht
  | tuple_ _ _ => cases ht
  | array_ _ _ => cases ht
  | refCreate _ _ _ _ => cases ht

theorem canonical_float : forall {e : Expr} {w : FloatWidth},
    IsValue e -> HasType [] [] e (.floatType w) -> exists f, e = .lit (.float f) := by
  intro e w hv ht
  cases hv with
  | lit v => cases v with
    | float f => exact ⟨f, rfl⟩
    | _ => cases ht
  | lam _ _ => cases ht
  | none_ => cases ht
  | err_ _ _ => cases ht
  | ok_ _ _ => cases ht
  | some_ _ _ => cases ht
  | tuple_ _ _ => cases ht
  | array_ _ _ => cases ht
  | refCreate _ _ _ _ => cases ht

theorem canonical_intWidth : forall {e : Expr} {w : IntWidth},
    IsValue e -> HasType [] [] e (.intWidthType w) -> exists n, e = .lit (.int n) := by
  intro e w hv ht
  cases hv with
  | lit v => cases v with
    | int n => exact ⟨n, rfl⟩
    | _ => cases ht
  | lam _ _ => cases ht
  | none_ => cases ht
  | err_ _ _ => cases ht
  | ok_ _ _ => cases ht
  | some_ _ _ => cases ht
  | tuple_ _ _ => cases ht
  | array_ _ _ => cases ht
  | refCreate _ _ _ _ => cases ht

theorem canonical_ref : forall {e : Expr} {cap τ},
    IsValue e -> HasType [] [] e (.refType cap τ) ->
    ∃ e', e = .refCreate e' cap τ ∧ HasType [] [] e' τ ∧ IsValue e' := by
  intro e cap τ hv ht
  cases hv with
  | lit v => cases ht
  | lam _ _ => cases ht
  | none_ => cases ht
  | err_ _ _ => cases ht
  | ok_ _ _ => cases ht
  | some_ _ _ => cases ht
  | tuple_ _ _ => cases ht
  | array_ _ _ => cases ht
  | refCreate e' cap' τ' hv' =>
    cases ht with
    | refCreate_type _ _ _ cap2 τ2 hE =>
      exact ⟨e', rfl, hE, hv'⟩

/-! ## Helpers -/

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

private theorem depth_let_l {e1 e2 : Expr} :
    exprDepth e1 < exprDepth (.let_ e1 e2) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_if_c {c t f : Expr} :
    exprDepth c < exprDepth (.ifThenElse c t f) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_for_s {s e : Expr} {body : List Expr} :
    exprDepth s < exprDepth (.forLoop s e body) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left (exprDepth s) _) (Nat.lt_succ_self _)

private theorem depth_for_e {s e : Expr} {body : List Expr} :
    exprDepth e < exprDepth (.forLoop s e body) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.le_max_left (exprDepth e) (listExprDepth body))
      (Nat.le_max_right (exprDepth s) ((exprDepth e).max (listExprDepth body))))
    (Nat.lt_succ_self _)

private theorem depth_block_head {e : Expr} {rest : List Expr} :
    exprDepth e < exprDepth (.block (e :: rest)) := by
  simp only [exprDepth, listExprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left (exprDepth e) (listExprDepth rest)) (Nat.lt_succ_self _)

private theorem depth_app_fn {fn : Expr} {args : List Expr} :
    exprDepth fn < exprDepth (.app fn args) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_field {e : Expr} {name : String} :
    exprDepth e < exprDepth (.field_ e name) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_match_scrut {scrut : Expr} {arms : List (List String × Expr)} :
    exprDepth scrut < exprDepth (.match_ scrut arms) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_pipe_l {e : Expr} {f : Expr} :
    exprDepth e < exprDepth (.pipe e f) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_pipe_r {e : Expr} {f : Expr} :
    exprDepth f < exprDepth (.pipe e f) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (Nat.lt_succ_self _)

private theorem depth_typeAsc {e : Expr} {τ : Typ} :
    exprDepth e < exprDepth (.typeAsc e τ) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_some {e : Expr} :
    exprDepth e < exprDepth (.some_ e) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_none : exprDepth .none_ = 0 := by simp only [exprDepth]

private theorem depth_ok {e : Expr} :
    exprDepth e < exprDepth (.ok_ e) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_err {e : Expr} :
    exprDepth e < exprDepth (.err_ e) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_null_coalesce_e1 {e1 e2 : Expr} :
    exprDepth e1 < exprDepth (.nullCoalesce e1 e2) := by
  simp only [exprDepth]; exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_refCreate {e cap τ} :
    exprDepth e < exprDepth (.refCreate e cap τ) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_refLoad {e} :
    exprDepth e < exprDepth (.refLoad e) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem depth_refStore {e v τ} :
    exprDepth e < exprDepth (.refStore e v τ) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

private theorem depth_refStore_v {e v τ} :
    exprDepth v < exprDepth (.refStore e v τ) := by
  simp only [exprDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (Nat.lt_succ_self _)

private theorem depth_refFree {e} :
    exprDepth e < exprDepth (.refFree e) := by
  simp only [exprDepth]; exact Nat.lt_succ_self _

private theorem HasTypeAll_nil_types {bvs : List Typ} {Γ : TypEnv} {tys : List Typ} :
    HasTypeAll bvs Γ [] tys → tys = [] := by
  intro h
  cases h with
  | nil => rfl

private theorem HasTypeAll_length (bvs : List Typ) (Γ : TypEnv) (es : List Expr) (τs : List Typ) :
    HasTypeAll bvs Γ es τs → es.length = τs.length := by
  intro h
  cases es with
  | nil =>
    match h with
    | HasTypeAll.nil _ _ =>
      cases τs with
      | nil => rfl
      | cons => contradiction
  | cons e es' =>
    cases τs with
    | nil => cases h
    | cons τ τs' =>
      simp only [List.length_cons]
      match h with
      | HasTypeAll.cons _ _ _ _ _ _ _ hRest =>
        exact congrArg (· + 1) (HasTypeAll_length bvs Γ es' τs' hRest)

private theorem HasTypeAll_append_cons_head {bvs : List Typ} {Γ : TypEnv} {e : Expr} {es : List Expr}
    {τs : List Typ} {τ : Typ} (h : HasTypeAll bvs Γ (e :: es) (τs ++ [τ])) :
    ∃ τ_h, HasType bvs Γ e τ_h := by
  cases τs with
  | nil =>
    change HasTypeAll bvs Γ (e :: es) [τ] at h
    cases h with
    | cons _ _ _ _ _ _ hE _ => exact ⟨_, hE⟩
  | cons τ' τs' =>
    change HasTypeAll bvs Γ (e :: es) (τ' :: (τs' ++ [τ])) at h
    cases h with
     | cons _ _ _ _ _ _ hE _ => exact ⟨_, hE⟩

private theorem HasTypeAll_mem {bvs : List Typ} {Γ : TypEnv} {es : List Expr}
    {τs : List Typ} (hAll : HasTypeAll bvs Γ es τs) (e : Expr) (he : e ∈ es) :
    ∃ τ, HasType bvs Γ e τ := by
  cases es with
  | nil => cases he
  | cons head rest =>
    match hAll with
    | HasTypeAll.cons _ _ _ _ _ _ hE hRest =>
      cases he with
      | head _ => exact ⟨_, hE⟩
      | tail _ h => exact HasTypeAll_mem hRest e h

private theorem tuple_find_step_rest {rest : List Expr} {e e' : Expr}
    (he : e ∈ rest) (hs : Step σ e σ e') :
    ∃ (n : Nat) (hn : n < rest.length), Step σ (rest.get ⟨n, hn⟩) σ e' := by
  induction rest with
  | nil => cases he
  | cons head rest ih =>
    cases he with
    | head _ =>
      exact ⟨0, Nat.zero_lt_succ _, hs⟩
    | tail _ h =>
      obtain ⟨n, hn, hget⟩ := ih h
      exact ⟨n + 1, Nat.succ_lt_succ hn, hget⟩

private theorem list_exists_step_or_all_values {rest : List Expr}
    (h : ∀ e ∈ rest, IsValue e ∨ ∃ e', Step σ e σ e') :
    (∀ e ∈ rest, IsValue e) ∨ ∃ e e', e ∈ rest ∧ Step σ e σ e' := by
  induction rest with
  | nil => left; intro _ h; cases h
  | cons head rest ih =>
    have hh : IsValue head ∨ ∃ e', Step σ head σ e' := h head (List.Mem.head rest)
    have hRest : ∀ x ∈ rest, IsValue x ∨ ∃ e', Step σ x σ e' := fun x hx => h x (List.Mem.tail head hx)
    cases hh with
    | inl hv =>
      cases ih hRest with
      | inl hAll =>
        left; intro x hx
        cases hx with
        | head _ => exact hv
        | tail _ h => exact hAll x h
      | inr hStep2 =>
        obtain ⟨e, e', he, hs⟩ := hStep2
        right; exact ⟨e, e', List.Mem.tail head he, hs⟩
    | inr hStep =>
      obtain ⟨e', hs⟩ := hStep
      right; exact ⟨head, e', List.Mem.head rest, hs⟩

private theorem listExprDepth_mem {e : Expr} {rest : List Expr} (he : e ∈ rest) :
    exprDepth e ≤ listExprDepth rest := by
  induction rest with
  | nil => cases he
  | cons head rest ih =>
    cases he with
    | head _ => simp only [listExprDepth]; exact Nat.le_max_left _ _
    | tail _ h => simp only [listExprDepth]; exact Nat.le_trans (ih h) (Nat.le_max_right (exprDepth head) (listExprDepth rest))

private theorem tuple_progress_list {d : Nat}
    (ih : ∀ (e : Expr), exprDepth e < d → ∀ (τ : Typ), HasType [] [] e τ → IsValue e ∨ (∃ e', Step σ e σ e'))
    (elems : List Expr) (τs : List Typ)
    (hAll : HasTypeAll [] [] elems τs)
    (hd : ∀ e ∈ elems, exprDepth e < d) :
    (∃ elems', Step σ (.tuple_ elems) σ (.tuple_ elems')) ∨ (∀ e ∈ elems, IsValue e) := by
  revert τs hAll hd
  induction elems with
  | nil => intro τs hAll _; right; intro _ h; cases h
  | cons head rest ih_elems =>
    intro τs hAll hd
    cases hAll with
    | cons _ _ _ _ τ_h τs' hE_head hAll_rest =>
      have hRes := ih head (hd head (List.Mem.head rest)) τ_h hE_head
      cases hRes with
      | inr hStep =>
        left
        obtain ⟨head', hs⟩ := hStep
        exact ⟨head' :: rest, Step.tuple_step_head σ head head' rest hs⟩
      | inl hv =>
        have hd_rest : ∀ e ∈ rest, exprDepth e < d := fun e' he' => hd e' (List.Mem.tail head he')
        have hRest := ih_elems τs' hAll_rest hd_rest
        cases hRest with
        | inl hStepRest =>
          left
          obtain ⟨elems'', hs⟩ := hStepRest
          exact ⟨head :: elems'', Step.tuple_step_rest σ head rest elems'' hv hs⟩
        | inr hVals =>
          right
          intro x hx
          cases hx with
          | head _ => exact hv
          | tail _ h => exact hVals x h

private theorem array_progress_list {d : Nat}
    (ih : ∀ (e : Expr), exprDepth e < d → ∀ (τ : Typ), HasType [] [] e τ → IsValue e ∨ (∃ e', Step σ e σ e'))
    (elems : List Expr) (τs : List Typ)
    (hAll : HasTypeAll [] [] elems τs)
    (hd : ∀ e ∈ elems, exprDepth e < d) :
    (∃ elems', Step σ (.arrayLit elems) σ (.arrayLit elems')) ∨ (∀ e ∈ elems, IsValue e) := by
  revert τs hAll hd
  induction elems with
  | nil => intro τs hAll _; right; intro _ h; cases h
  | cons head rest ih_elems =>
    intro τs hAll hd
    cases hAll with
    | cons _ _ _ _ τ_h τs' hE_head hAll_rest =>
      have hRes := ih head (hd head (List.Mem.head rest)) τ_h hE_head
      cases hRes with
      | inr hStep =>
        left
        obtain ⟨head', hs⟩ := hStep
        exact ⟨head' :: rest, Step.array_step_head σ head head' rest hs⟩
      | inl hv =>
        have hd_rest : ∀ e ∈ rest, exprDepth e < d := fun e' he' => hd e' (List.Mem.tail head he')
        have hRest := ih_elems τs' hAll_rest hd_rest
        cases hRest with
        | inl hStepRest =>
          left
          obtain ⟨elems'', hs⟩ := hStepRest
          exact ⟨head :: elems'', Step.array_step_rest σ head rest elems'' hv hs⟩
        | inr hVals =>
          right
          intro x hx
          cases hx with
          | head _ => exact hv
          | tail _ h => exact hVals x h

private theorem progress_strong :
    forall {σ : Store} (d : Nat) (e : Expr), exprDepth e < d ->
    forall (τ : Typ), HasType [] [] e τ -> IsValue e \/ exists e', Step σ e σ e' := by
  intro σ d
  induction d with
  | zero =>
    intro e hDepth _ _
    exact absurd hDepth (Nat.not_lt_zero _)
  | succ d ih =>
    intro e hDepth τ hType
    cases hType with
    | bvar_type _ _ n hLen =>
      exfalso
      exact absurd hLen (Nat.not_lt_zero _)
    | fvar_type _ _ name τ_val hLookup =>
      exfalso
      have h_eq : lookupTyp [] name = none := rfl
      rw [h_eq] at hLookup
      cases hLookup
    | lit_int _ _ n => left; exact IsValue.lit (Value.int n)
    | lit_bool _ _ b => left; exact IsValue.lit (Value.bool b)
    | lit_string _ _ s => left; exact IsValue.lit (Value.string s)
    | lit_unit _ _ => left; exact IsValue.lit Value.unit
    | lit_pointer _ _ p => left; exact IsValue.lit (Value.pointer p)
    | lit_float _ _ w f => left; exact IsValue.lit (Value.float f)
    | lit_int_width _ _ w n => left; exact IsValue.lit (Value.int n)
    | unop_not _ _ eSub hSub =>
      have hRes := ih eSub (Nat.lt_of_lt_of_le (depth_unop .not) (Nat.le_of_lt_succ hDepth)) .boolType hSub
      cases hRes with
      | inl hv =>
        obtain ⟨b, hb⟩ := canonical_bool hv hSub
        rw [hb]; right; exact ⟨.lit (.bool (!b)), Step.unop_not σ b⟩
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.unop .not e', Step.unop_step σ .not eSub e' hs⟩
    | unop_notb _ _ eSub hSub =>
      have hRes := ih eSub (Nat.lt_of_lt_of_le (depth_unop .notb) (Nat.le_of_lt_succ hDepth)) .intType hSub
      cases hRes with
      | inl hv =>
        obtain ⟨k, hk⟩ := canonical_int hv hSub
        rw [hk]; right; exact ⟨.lit (.int (-k - 1)), Step.unop_notb σ k⟩
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.unop .notb e', Step.unop_step σ .notb eSub e' hs⟩
    | binop_arith _ _ op e1 e2 hArith hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le (depth_binop_l op) (Nat.le_of_lt_succ hDepth)) .intType hSub1
      have h2 := ih e2 (Nat.lt_of_lt_of_le (depth_binop_r op) (Nat.le_of_lt_succ hDepth)) .intType hSub2
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
            right; exact ⟨.lit (.int r), Step.binop_arith σ op k1 k2 r hArith hRes⟩
          | none =>
            cases op with
            | add | sub | mul =>
              exfalso; unfold evalArithOp at hRes; contradiction
            | div =>
              cases k2 with
              | ofNat n =>
                cases n with
                | zero => right; exact ⟨.lit (.int 0), Step.binop_div_zero σ k1⟩
                | succ _ => exfalso; unfold evalArithOp at hRes; contradiction
              | negSucc _ => exfalso; unfold evalArithOp at hRes; contradiction
            | mod =>
              cases k2 with
              | ofNat n =>
                cases n with
                | zero => right; exact ⟨.lit (.int 0), Step.binop_mod_zero σ k1⟩
                | succ _ => exfalso; unfold evalArithOp at hRes; contradiction
              | negSucc _ => exfalso; unfold evalArithOp at hRes; contradiction
            | _ => exfalso; unfold Morph.Specs.TypeSystem.isArithOp at hArith; exact hArith.elim
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop op (.lit (.int k1)) e2',
            Step.binop_right σ op (.int k1) e2 e2' (IsValue.lit (.int k1)) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop op e1' e2, Step.binop_left σ op e1 e1' e2 hs⟩
    | binop_comp _ _ op e1 e2 hComp hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le (depth_binop_l op) (Nat.le_of_lt_succ hDepth)) .intType hSub1
      have h2 := ih e2 (Nat.lt_of_lt_of_le (depth_binop_r op) (Nat.le_of_lt_succ hDepth)) .intType hSub2
      cases h1 with
      | inl hv1 =>
        obtain ⟨k1, hk1⟩ := canonical_int hv1 hSub1
        rw [hk1]
        cases h2 with
        | inl hv2 =>
          obtain ⟨k2, hk2⟩ := canonical_int hv2 hSub2
          rw [hk2]
          right; exact ⟨.lit (.bool (evalCompOp op k1 k2)),
            Step.binop_comp σ op k1 k2 hComp⟩
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop op (.lit (.int k1)) e2',
            Step.binop_right σ op (.int k1) e2 e2' (IsValue.lit (.int k1)) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop op e1' e2, Step.binop_left σ op e1 e1' e2 hs⟩
    | binop_logic _ _ op e1 e2 hLogic hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le (depth_binop_l op) (Nat.le_of_lt_succ hDepth)) .boolType hSub1
      have h2 := ih e2 (Nat.lt_of_lt_of_le (depth_binop_r op) (Nat.le_of_lt_succ hDepth)) .boolType hSub2
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
            right; exact ⟨.lit (.bool r), Step.binop_logic σ op b1 b2 r hLogic hRes⟩
          | none =>
            exfalso
            obtain ⟨r, hr⟩ := evalLogicOp_some_of_isLogicOp op b1 b2 hLogic
            rw [hr] at hRes
            exact absurd hRes (by contradiction)
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop op (.lit (.bool b1)) e2',
            Step.binop_right σ op (.bool b1) e2 e2' (IsValue.lit (.bool b1)) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop op e1' e2, Step.binop_left σ op e1 e1' e2 hs⟩
    | binop_bitwise _ _ op e1 e2 hBitwise hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le (depth_binop_l op) (Nat.le_of_lt_succ hDepth)) .intType hSub1
      have h2 := ih e2 (Nat.lt_of_lt_of_le (depth_binop_r op) (Nat.le_of_lt_succ hDepth)) .intType hSub2
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
            right; exact ⟨.lit (.int r), Step.binop_bitwise σ op k1 k2 r hBitwise hRes⟩
          | none =>
            exfalso
            obtain ⟨r, hr⟩ := evalBitwiseOp_some_of_isBitwiseOp op k1 k2 hBitwise
            rw [hr] at hRes
            exact absurd hRes (by contradiction)
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop op (.lit (.int k1)) e2',
            Step.binop_right σ op (.int k1) e2 e2' (IsValue.lit (.int k1)) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop op e1' e2, Step.binop_left σ op e1 e1' e2 hs⟩
    | binop_ptr_arith _ _ op e1 e2 hPtr hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le (depth_binop_l op) (Nat.le_of_lt_succ hDepth)) .pointerType hSub1
      have h2 := ih e2 (Nat.lt_of_lt_of_le (depth_binop_r op) (Nat.le_of_lt_succ hDepth)) .intType hSub2
      cases h1 with
      | inl hv1 =>
        cases hv1 with
        | lit v =>
          cases v with
          | pointer p =>
            cases h2 with
            | inl hv2 =>
              obtain ⟨k2, hk2⟩ := canonical_int hv2 hSub2
              rw [hk2]
              match hRes : evalPtrArithOp op p k2 with
              | some r =>
                right; exact ⟨.lit (.pointer r), Step.binop_ptr_arith σ op p k2 r hPtr hRes⟩
              | none =>
                exfalso
                cases op with
                | ptrAdd =>
                  unfold evalPtrArithOp at hRes; contradiction
                | ptrSub =>
                  unfold evalPtrArithOp at hRes; contradiction
                | _ => unfold Morph.Specs.TypeSystem.isPtrArithOp at hPtr; exact hPtr.elim
            | inr hStep2 =>
              obtain ⟨e2', hs⟩ := hStep2
              right; exact ⟨.binop op (.lit (.pointer p)) e2',
                Step.binop_right σ op (.pointer p) e2 e2' (IsValue.lit (.pointer p)) hs⟩
           | _ => exfalso; cases hSub1
         | lam _ _ => exfalso; cases hSub1
         | none_ => exfalso; cases hSub1
         | err_ _ _ => exfalso; cases hSub1
         | ok_ _ _ => exfalso; cases hSub1
          | some_ _ _ => exfalso; cases hSub1
          | tuple_ _ _ => exfalso; cases hSub1
         | array_ _ _ => exfalso; cases hSub1
          | refCreate _ _ _ _ => exfalso; cases hSub1
       | inr hStep1 =>
         obtain ⟨e1', hs⟩ := hStep1
         right; exact ⟨.binop op e1' e2, Step.binop_left σ op e1 e1' e2 hs⟩
     | binop_ptr_load _ _ e1 e2 hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le (depth_binop_l .ptrLoad) (Nat.le_of_lt_succ hDepth)) .pointerType hSub1
      cases h1 with
      | inl hv1 =>
        cases hv1 with
        | lit v =>
          cases v with
          | pointer p =>
            have h2 := ih e2 (Nat.lt_of_lt_of_le (depth_binop_r .ptrLoad) (Nat.le_of_lt_succ hDepth)) .unitType hSub2
            cases h2 with
            | inl hv2 =>
              cases hv2 with
              | lit v2 =>
                cases hSub2 with
                | lit_unit => right; exact ⟨.lit .unit, Step.binop_ptr_load σ p⟩
                | _ => contradiction
              | lam _ _ => exfalso; cases hSub2
              | none_ => exfalso; cases hSub2
              | err_ _ _ => exfalso; cases hSub2
              | ok_ _ _ => exfalso; cases hSub2
              | some_ _ _ => exfalso; cases hSub2
               | tuple_ _ _ => exfalso; cases hSub2
              | array_ _ _ => exfalso; cases hSub2
              | refCreate _ _ _ _ => exfalso; cases hSub2
             | inr hStep2 =>
              obtain ⟨e2', hs⟩ := hStep2
              right; exact ⟨.binop .ptrLoad (.lit (.pointer p)) e2',
                Step.binop_right σ .ptrLoad (.pointer p) e2 e2' (IsValue.lit (.pointer p)) hs⟩
          | _ => exfalso; cases hSub1
        | lam _ _ => exfalso; cases hSub1
        | none_ => exfalso; cases hSub1
        | err_ _ _ => exfalso; cases hSub1
        | ok_ _ _ => exfalso; cases hSub1
         | some_ _ _ => exfalso; cases hSub1
         | tuple_ _ _ => exfalso; cases hSub1
        | array_ _ _ => exfalso; cases hSub1
        | refCreate _ _ _ _ => exfalso; cases hSub1
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop .ptrLoad e1' e2, Step.binop_left σ .ptrLoad e1 e1' e2 hs⟩
     | binop_ptr_store _ _ e1 e2 hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le (depth_binop_l .ptrStore) (Nat.le_of_lt_succ hDepth)) .pointerType hSub1
      cases h1 with
      | inl hv1 =>
        cases hv1 with
        | lit v =>
          cases v with
          | pointer p =>
            have h2 := ih e2 (Nat.lt_of_lt_of_le (depth_binop_r .ptrStore) (Nat.le_of_lt_succ hDepth)) .intType hSub2
            cases h2 with
            | inl hv2 =>
              obtain ⟨k2, hk2⟩ := canonical_int hv2 hSub2
              rw [hk2]
              right; exact ⟨.lit .unit, Step.binop_ptr_store σ p (Value.int k2)⟩
            | inr hStep2 =>
              obtain ⟨e2', hs⟩ := hStep2
              right; exact ⟨.binop .ptrStore (.lit (.pointer p)) e2',
                Step.binop_right σ .ptrStore (.pointer p) e2 e2' (IsValue.lit (.pointer p)) hs⟩
          | _ => exfalso; cases hSub1
        | lam _ _ => exfalso; cases hSub1
        | none_ => exfalso; cases hSub1
        | err_ _ _ => exfalso; cases hSub1
        | ok_ _ _ => exfalso; cases hSub1
         | some_ _ _ => exfalso; cases hSub1
        | tuple_ _ _ => exfalso; cases hSub1
        | array_ _ _ => exfalso; cases hSub1
         | refCreate _ _ _ _ => exfalso; cases hSub1
       | inr hStep1 =>
         obtain ⟨e1', hs⟩ := hStep1
         right; exact ⟨.binop .ptrStore e1' e2, Step.binop_left σ .ptrStore e1 e1' e2 hs⟩
     | binop_string_concat _ _ op e1 e2 hOp hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le (depth_binop_l op) (Nat.le_of_lt_succ hDepth)) .stringType hSub1
      have h2 := ih e2 (Nat.lt_of_lt_of_le (depth_binop_r op) (Nat.le_of_lt_succ hDepth)) .stringType hSub2
      subst hOp
      cases h1 with
      | inl hv1 =>
        obtain ⟨s1, hs1⟩ := canonical_string hv1 hSub1
        rw [hs1]
        cases h2 with
        | inl hv2 =>
          obtain ⟨s2, hs2⟩ := canonical_string hv2 hSub2
          rw [hs2]
          right; exact ⟨.lit (.string (s1 ++ s2)), Step.binop_string_concat σ s1 s2⟩
        | inr hStep2 =>
          obtain ⟨e2', hs⟩ := hStep2
          right; exact ⟨.binop .add (.lit (.string s1)) e2', Step.binop_right σ .add (.string s1) e2 e2' (IsValue.lit _) hs⟩
      | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.binop .add e1' e2, Step.binop_left σ .add e1 e1' e2 hs⟩
     | lam_type _ _ n body paramTys retTy hLen hBody =>
      left; exact IsValue.lam n body
    | app_type _ _ fnE argsE τs _ hFnE hArgsE =>
      have ih_fn := ih fnE (Nat.lt_of_lt_of_le depth_app_fn (Nat.le_of_lt_succ hDepth)) (.functionType τs τ) hFnE
      cases ih_fn with
      | inl hv =>
        cases hv with
        | lit _ =>
          exfalso
          cases hFnE with <;> contradiction
        | lam n body =>
          have hArgsLen : argsE.length = n := by
            have h := HasTypeAll_length [] [] argsE τs hArgsE
            cases hFnE with
            | lam_type _ _ _ _ paramTys _ hLen _ =>
              simp at *
              omega
            | _ => contradiction
          right
          exact ⟨substAll argsE.reverse body, Step.app_lam σ n body argsE hArgsLen⟩
        | none_ => exfalso; cases hFnE with <;> contradiction
        | err_ _ _ => exfalso; cases hFnE with <;> contradiction
        | ok_ _ _ => exfalso; cases hFnE with <;> contradiction
        | some_ _ _ => exfalso; cases hFnE with <;> contradiction
        | tuple_ _ _ => exfalso; cases hFnE with <;> contradiction
        | array_ _ _ => exfalso; cases hFnE with <;> contradiction
         | refCreate _ _ _ _ => exfalso; cases hFnE with <;> contradiction
      | inr hStep_fn =>
        obtain ⟨fnE', hs⟩ := hStep_fn
        right; exact ⟨.app fnE' argsE, Step.app_fn σ fnE fnE' argsE hs⟩
    | let_type _ _ e1 e2 τ1 τ2 hSub1 hSub2 =>
      have h1 := ih e1 (Nat.lt_of_lt_of_le depth_let_l (Nat.le_of_lt_succ hDepth)) τ1 hSub1
      cases h1 with
      | inl hv =>
        cases hv with
        | lit v =>
          right; exact ⟨subst e2 (.lit v), Step.let_subst σ (.lit v) e2 (IsValue.lit v)⟩
        | lam n body =>
          right; exact ⟨subst e2 (.lam n body), Step.let_subst σ (.lam n body) e2 (IsValue.lam n body)⟩
        | none_ =>
          right; exact ⟨subst e2 .none_, Step.let_subst σ .none_ e2 IsValue.none_⟩
        | err_ e hv =>
          right; exact ⟨subst e2 (.err_ e), Step.let_subst σ (.err_ e) e2 (IsValue.err_ e hv)⟩
        | ok_ e hv =>
          right; exact ⟨subst e2 (.ok_ e), Step.let_subst σ (.ok_ e) e2 (IsValue.ok_ e hv)⟩
         | some_ e hv =>
            right; exact ⟨subst e2 (.some_ e), Step.let_subst σ (.some_ e) e2 (IsValue.some_ e hv)⟩
         | tuple_ elems hvs =>
           right; exact ⟨subst e2 (.tuple_ elems), Step.let_subst σ (.tuple_ elems) e2 (IsValue.tuple_ elems hvs)⟩
         | array_ elems hvs =>
           right; exact ⟨subst e2 (.arrayLit elems), Step.let_subst σ (.arrayLit elems) e2 (IsValue.array_ elems hvs)⟩
          | refCreate e cap τ hv =>
            right; exact ⟨subst e2 (.refCreate e cap τ), Step.let_subst σ (.refCreate e cap τ) e2 (IsValue.refCreate e cap τ hv)⟩
       | inr hStep1 =>
        obtain ⟨e1', hs⟩ := hStep1
        right; exact ⟨.let_ e1' e2, Step.let_step σ e1 e1' e2 hs⟩
    | if_type _ _ c t f τ_if hCond hT hF =>
      have hc := ih c (Nat.lt_of_lt_of_le depth_if_c (Nat.le_of_lt_succ hDepth)) .boolType hCond
      cases hc with
      | inl hv =>
        obtain ⟨b, hb⟩ := canonical_bool hv hCond
        rw [hb]
        cases b with
        | true => right; exact ⟨t, Step.if_true σ t f⟩
        | false => right; exact ⟨f, Step.if_false σ t f⟩
      | inr hStep =>
        obtain ⟨c', hs⟩ := hStep
        right; exact ⟨.ifThenElse c' t f, Step.if_cond σ c c' t f hs⟩
    | for_type _ _ s e body hStart hEnd hBody =>
      have hResS := ih s (Nat.lt_of_lt_of_le depth_for_s (Nat.le_of_lt_succ hDepth)) .intType hStart
      cases hResS with
      | inl hv =>
        obtain ⟨k1, hk1⟩ := canonical_int hv hStart
        rw [hk1]
        have hResE := ih e (Nat.lt_of_lt_of_le depth_for_e (Nat.le_of_lt_succ hDepth)) .intType hEnd
        cases hResE with
        | inl hv2 =>
          obtain ⟨k2, hk2⟩ := canonical_int hv2 hEnd
          rw [hk2]
          exact dite (k1 < k2)
            (fun hLt => Or.inr ⟨_, Step.for_exec σ k1 k2 body hLt⟩)
            (fun hNlt => Or.inr ⟨_, Step.for_done σ k1 k2 body (by omega)⟩)
        | inr hStep2 =>
          obtain ⟨e', hs⟩ := hStep2
          right; exact ⟨_, Step.for_end σ (.int k1) e e' body (IsValue.lit (.int k1)) hs⟩
      | inr hStep1 =>
        obtain ⟨s', hs⟩ := hStep1
        right; exact ⟨_, Step.for_start σ s s' e body hs⟩
    | pipe_type _ _ ePipe fPipe τArg _ hE1 hE2 =>
      have hResE := ih ePipe (Nat.lt_of_lt_of_le depth_pipe_l (Nat.le_of_lt_succ hDepth)) τArg hE1
      match hResE with
      | Or.inr ⟨e', hs⟩ =>
        right; exact ⟨.pipe e' fPipe, Step.pipe_left σ ePipe e' fPipe hs⟩
      | Or.inl hvE =>
        have hResF := ih fPipe (Nat.lt_of_lt_of_le depth_pipe_r (Nat.le_of_lt_succ hDepth)) (.functionType [τArg] τ) hE2
        match hResF with
        | Or.inr ⟨f', hs⟩ =>
          right; exact ⟨.pipe ePipe f', Step.pipe_right σ ePipe fPipe f' hvE hs⟩
        | Or.inl _ =>
          right; exact ⟨.app fPipe [ePipe], Step.pipe_done σ ePipe fPipe hvE⟩
    | typeAsc_type _ _ eAsc _ hE =>
      have hRes := ih eAsc (Nat.lt_of_lt_of_le depth_typeAsc (Nat.le_of_lt_succ hDepth)) τ hE
      cases hRes with
      | inl hv =>
        right; exact ⟨eAsc, Step.typeAsc_done σ eAsc τ hv⟩
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.typeAsc e' τ, Step.typeAsc_step σ eAsc e' τ hs⟩
    | block_type _ _ exprs τs τ hAll =>
      cases exprs with
      | nil =>
        exfalso
        have hLen := congrArg List.length (HasTypeAll_nil_types hAll)
        rw [List.length_append, List.length_cons, List.length_nil] at hLen
        omega
      | cons head rest =>
        obtain ⟨τ_h, hHead⟩ := HasTypeAll_append_cons_head hAll
        have hRes := ih head (Nat.lt_of_lt_of_le depth_block_head (Nat.le_of_lt_succ hDepth)) τ_h hHead
        cases hRes with
        | inr hStep =>
          obtain ⟨head', hs⟩ := hStep
          right; exact ⟨_, Step.block_head σ head head' rest hs⟩
        | inl hv =>
          cases rest with
          | nil =>
            cases hv with
            | lit v => right; exact ⟨_, Step.block_singleton σ v (IsValue.lit v)⟩
            | lam n body => right; exact ⟨_, Step.block_lam_singleton σ n body⟩
            | none_ => right; exact ⟨_, Step.block_none_singleton σ⟩
            | err_ e hv' => right; exact ⟨_, Step.block_err_singleton σ e hv'⟩
            | ok_ e hv' => right; exact ⟨_, Step.block_ok_singleton σ e hv'⟩
             | some_ e hv' => right; exact ⟨_, Step.block_some_singleton σ e hv'⟩
             | tuple_ elems hvs => right; exact ⟨_, Step.block_tuple_singleton σ elems hvs⟩
             | array_ elems hvs => right; exact ⟨_, Step.block_array_singleton σ elems hvs⟩
             | refCreate e cap τ hv => right; exact ⟨_, Step.block_refCreate_singleton σ e cap τ hv⟩
           | cons head2 rest2 =>
            right; exact ⟨_, Step.block_pop σ head head2 rest2 hv⟩
    | some_type _ _ eSome τ_inner hE =>
      have hRes := ih eSome (Nat.lt_of_lt_of_le depth_some (Nat.le_of_lt_succ hDepth)) τ_inner hE
      cases hRes with
      | inl hv =>
         cases hv with
        | lit v => right; exact ⟨.lit (.some v), Step.some_done σ v⟩
        | none_ => right; exact ⟨.lit (.some Value.none), Step.some_none_done σ⟩
        | lam n body => left; exact IsValue.some_ (.lam n body) (IsValue.lam n body)
        | err_ e2 hv2 => left; exact IsValue.some_ (.err_ e2) (IsValue.err_ e2 hv2)
        | ok_ e2 hv2 => left; exact IsValue.some_ (.ok_ e2) (IsValue.ok_ e2 hv2)
         | some_ e2 hv2 => left; exact IsValue.some_ (.some_ e2) (IsValue.some_ e2 hv2)
         | tuple_ elems hvs => left; exact IsValue.some_ (.tuple_ elems) (IsValue.tuple_ elems hvs)
         | array_ elems hvs => left; exact IsValue.some_ (.arrayLit elems) (IsValue.array_ elems hvs)
          | refCreate e cap τ hv => left; exact IsValue.some_ (.refCreate e cap τ) (IsValue.refCreate e cap τ hv)
       | inr hStep =>
         obtain ⟨e', hs⟩ := hStep
         right; exact ⟨.some_ e', Step.some_step σ eSome e' hs⟩
     | none_type _ _ _ => right; exact ⟨.lit Value.none, Step.none_step σ⟩
     | ok_type _ _ eOk τ_ok _ hE =>
      have hRes := ih eOk (Nat.lt_of_lt_of_le depth_ok (Nat.le_of_lt_succ hDepth)) τ_ok hE
      cases hRes with
      | inl hv =>
         cases hv with
        | lit v => right; exact ⟨.lit (.ok v), Step.ok_done σ v⟩
        | none_ => right; exact ⟨.lit (.ok Value.none), Step.ok_none_done σ⟩
        | lam n body => left; exact IsValue.ok_ (.lam n body) (IsValue.lam n body)
        | err_ e2 hv2 => left; exact IsValue.ok_ (.err_ e2) (IsValue.err_ e2 hv2)
          | ok_ e2 hv2 => left; exact IsValue.ok_ (.ok_ e2) (IsValue.ok_ e2 hv2)
          | some_ e2 hv2 => left; exact IsValue.ok_ (.some_ e2) (IsValue.some_ e2 hv2)
          | tuple_ elems hvs => left; exact IsValue.ok_ (.tuple_ elems) (IsValue.tuple_ elems hvs)
          | array_ elems hvs => left; exact IsValue.ok_ (.arrayLit elems) (IsValue.array_ elems hvs)
          | refCreate e cap τ hv => left; exact IsValue.ok_ (.refCreate e cap τ) (IsValue.refCreate e cap τ hv)
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.ok_ e', Step.ok_step σ eOk e' hs⟩
    | err_type _ _ eErr τ_err _ hE =>
      have hRes := ih eErr (Nat.lt_of_lt_of_le depth_err (Nat.le_of_lt_succ hDepth)) τ_err hE
      cases hRes with
      | inl hv =>
         cases hv with
        | lit v => right; exact ⟨.lit (.err v), Step.err_done σ v⟩
        | none_ => right; exact ⟨.lit (.err Value.none), Step.err_none_done σ⟩
        | lam n body => left; exact IsValue.err_ (.lam n body) (IsValue.lam n body)
        | err_ e2 hv2 => left; exact IsValue.err_ (.err_ e2) (IsValue.err_ e2 hv2)
        | ok_ e2 hv2 => left; exact IsValue.err_ (.ok_ e2) (IsValue.ok_ e2 hv2)
          | some_ e2 hv2 => left; exact IsValue.err_ (.some_ e2) (IsValue.some_ e2 hv2)
          | tuple_ elems hvs => left; exact IsValue.err_ (.tuple_ elems) (IsValue.tuple_ elems hvs)
          | array_ elems hvs => left; exact IsValue.err_ (.arrayLit elems) (IsValue.array_ elems hvs)
          | refCreate e cap τ hv => left; exact IsValue.err_ (.refCreate e cap τ) (IsValue.refCreate e cap τ hv)
       | inr hStep =>
         obtain ⟨e', hs⟩ := hStep
         right; exact ⟨.err_ e', Step.err_step σ eErr e' hs⟩
    | lit_some _ _ _ _ => left; exact IsValue.lit _
    | lit_none _ _ _ => left; exact IsValue.lit _
    | lit_ok _ _ _ τ_ok _ => left; exact IsValue.lit _
    | lit_err _ _ _ τ_err _ => left; exact IsValue.lit _
    | null_coalesce_type _ _ e1 e2 τ hE1 hE2 =>
      have hRes := ih e1 (Nat.lt_of_lt_of_le depth_null_coalesce_e1 (Nat.le_of_lt_succ hDepth)) (.optionType τ) hE1
      cases hRes with
      | inl hv =>
        right
        cases e1 with
        | lit v =>
          cases v with
          | some inner => exact ⟨.lit (.some inner), Step.null_coalesce_lit_some σ inner e2⟩
          | none => exact ⟨e2, Step.null_coalesce_lit_none σ e2⟩
          | _ => contradiction
        | some_ e => exact ⟨.some_ e, Step.null_coalesce_some σ e e2⟩
        | none_ => exact ⟨e2, Step.null_coalesce_none σ e2⟩
        | _ => contradiction
      | inr hStep =>
        obtain ⟨e1', hs⟩ := hStep
        right; exact ⟨.nullCoalesce e1' e2, Step.null_coalesce_step_e1 σ e1 e1' e2 hs⟩
    | tuple_type _ _ elems τs hAll =>
      have hd : ∀ e ∈ elems, exprDepth e < d := by
        intro e he
        have h₁ : exprDepth e ≤ listExprDepth elems := listExprDepth_mem he
        have h₂ : listExprDepth elems + 1 < d + 1 := hDepth
        omega
      have hTuple := tuple_progress_list ih elems τs hAll hd
      cases hTuple with
      | inl hStep =>
        obtain ⟨elems', hs⟩ := hStep
        right; exact ⟨.tuple_ elems', hs⟩
      | inr hVals => left; exact IsValue.tuple_ elems hVals
    | arrayLit_type _ _ elems τ n hElems hLen hn =>
      have hd : ∀ e ∈ elems, exprDepth e < d := by
        intro e he
        have h₁ : exprDepth e ≤ listExprDepth elems := listExprDepth_mem he
        have h₂ : listExprDepth elems + 1 < d + 1 := hDepth
        omega
      have hArr := array_progress_list ih elems (List.replicate n τ) hElems hd
      cases hArr with
      | inl hStep =>
        obtain ⟨elems', hs⟩ := hStep
        right; exact ⟨.arrayLit elems', hs⟩
      | inr hVals => left; exact IsValue.array_ elems hVals
    | arrayIndex_type _ _ arr idx τ n hArr hIdx =>
      have hArrRes := ih arr (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_max_left (exprDepth arr) (exprDepth idx)) (Nat.lt_succ_self _)) (Nat.le_of_lt_succ hDepth)) (.arrayType τ n) hArr
      cases hArrRes with
      | inr hStep =>
        obtain ⟨arr', hs⟩ := hStep
        right; exact ⟨.arrayIndex arr' idx, Step.array_index_array σ arr arr' idx hs⟩
      | inl hvArr =>
        have hIdxRes := ih idx (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_max_right (exprDepth arr) (exprDepth idx)) (Nat.lt_succ_self _)) (Nat.le_of_lt_succ hDepth)) .intType hIdx
        cases hIdxRes with
        | inr hStep =>
          obtain ⟨idx', hs⟩ := hStep
          right; exact ⟨.arrayIndex arr idx', Step.array_index_idx σ arr idx idx' hvArr hs⟩
        | inl hvIdx =>
          right
          cases hvArr with
          | array_ elems hvs =>
            obtain ⟨k, hk⟩ := canonical_int hvIdx hIdx
            rw [hk]
            have hPos : elems.length > 0 := by
              cases hArr with
              | arrayLit_type _ _ _ _ _ _ hEq hPos => rw [← hEq]; exact hPos
              | _ => contradiction
            exact match k with
            | Int.ofNat m =>
              if hLt : m < elems.length then
                ⟨elems.getD m (.lit .unit), Step.array_index_hit σ elems hvs m hLt⟩
              else
                ⟨elems.getD 0 (.lit .unit), Step.array_index_oob σ elems hvs m hPos (by omega)⟩
            | Int.negSucc m =>
              ⟨elems.getD 0 (.lit .unit), Step.array_index_neg σ elems hvs m hPos⟩
          | _ => exfalso; cases hArr
    | field_access_type _ _ e_base fname sname fields τ hE_base hField =>
      have hRes := ih e_base (Nat.lt_of_lt_of_le depth_field (Nat.le_of_lt_succ hDepth))
        (.structType sname fields) hE_base
      cases hRes with
      | inr hStep =>
        obtain ⟨e_base', hs⟩ := hStep
        right; exact ⟨.field_ e_base' fname, Step.field_step σ e_base e_base' fname hs⟩
      | inl hv =>
        exfalso
        cases hv with
        | lit _ => cases hE_base
        | lam _ _ => cases hE_base
        | none_ => cases hE_base
        | err_ _ _ => cases hE_base
        | ok_ _ _ => cases hE_base
        | some_ _ _ => cases hE_base
        | tuple_ _ _ => cases hE_base
                 | array_ _ _ => cases hE_base
         | refCreate _ _ _ _ => cases hE_base
    | match_type _ _ scrut arms ts tr hScrut hArms =>
      have hRes := ih scrut (Nat.lt_of_lt_of_le depth_match_scrut (Nat.le_of_lt_succ hDepth))
        ts hScrut
      cases hRes with
      | inr hStep =>
        obtain ⟨scrut', hs⟩ := hStep
        right; exact ⟨.match_ scrut' arms, Step.match_scrut_step σ scrut scrut' arms hs⟩
      | inl hv =>
        right
        match arms with
        | [] => exact ⟨.lit .unit, Step.match_empty σ scrut hv⟩
        | (vars, body) :: rest => exact ⟨substAll (List.replicate vars.length scrut) body, Step.match_arm σ scrut vars body rest hv⟩
    | refCreate_type _ _ e cap τ hE =>
      have hRes := ih e (Nat.lt_of_lt_of_le depth_refCreate (Nat.le_of_lt_succ hDepth)) τ hE
      cases hRes with
      | inl hv =>
        left; exact IsValue.refCreate e cap τ hv
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.refCreate e' cap τ, Step.ref_create_step σ e e' cap τ hs⟩
    | refLoad_type _ _ e cap τ hE =>
      have hRes := ih e (Nat.lt_of_lt_of_le depth_refLoad (Nat.le_of_lt_succ hDepth)) (.refType cap τ) hE
      cases hRes with
      | inl hv =>
        obtain ⟨e', he', hE', hv'⟩ := canonical_ref hv hE
        right; exact ⟨e', by rw [he']; exact Step.ref_load_eval σ e' cap τ hv'⟩
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.refLoad e', Step.ref_load_step σ e e' hs⟩
    | refStore_type _ _ e v cap τ hE hV hCap =>
      have hResE := ih e (Nat.lt_of_lt_of_le depth_refStore (Nat.le_of_lt_succ hDepth)) (.refType cap τ) hE
      cases hResE with
      | inl hvE =>
        obtain ⟨e', he', hE', hv'⟩ := canonical_ref hvE hE
        have hResV := ih v (Nat.lt_of_lt_of_le depth_refStore_v (Nat.le_of_lt_succ hDepth)) τ hV
        cases hResV with
        | inl hvV =>
          right; exact ⟨.lit .unit, by rw [he']; exact Step.ref_store_eval σ e' v cap τ hv' hvV hCap⟩
        | inr hStepV =>
          obtain ⟨v', hs⟩ := hStepV
          right; exact ⟨.refStore e v' τ,
            Step.ref_store_step_val σ e v' v τ hvE hs⟩
      | inr hStepE =>
        obtain ⟨e', hs⟩ := hStepE
        right; exact ⟨.refStore e' v τ, Step.ref_store_step_arr σ e e' v τ hs⟩
    | refFree_type _ _ e τ hE =>
      have hRes := ih e (Nat.lt_of_lt_of_le depth_refFree (Nat.le_of_lt_succ hDepth)) (.refType .iso τ) hE
      cases hRes with
      | inl hv =>
        obtain ⟨e', he', hE', hv'⟩ := canonical_ref hv hE
        right; exact ⟨.lit .unit, by rw [he']; exact Step.ref_free_eval σ e' τ hv'⟩
      | inr hStep =>
        obtain ⟨e', hs⟩ := hStep
        right; exact ⟨.refFree e', Step.ref_free_step σ e e' hs⟩

/-! ## Main Theorem -/

theorem progress : forall {σ : Store} {e : Expr} {τ : Typ},
    HasType [] [] e τ -> IsValue e \/ exists e', Step σ e σ e' := by
  intro σ e τ h
  exact progress_strong (exprDepth e + 1) e (Nat.lt_succ_self _) τ h

end Morph.Proofs.TypeSoundness
