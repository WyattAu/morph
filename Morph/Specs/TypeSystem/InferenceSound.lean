/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TypeSystem.Spec
import Morph.TypeChecker

/-!
# Inference Soundness (research program P13, CakeML frontend-2 discipline)

The executable checker `inferType`/`inferTypes` (defined in the executable
section of `Morph.Specs.TypeSystem.Spec`) is proven sound against the
declarative judgment `HasType`/`HasTypeAll`:

* `inferType_sound`: every `some τ` answer is a real derivation
  `HasType bvs Γ e τ`.
* `inferTypes_sound`, `synthType_sound`: the list-level and entry-point
  projections.
* `checkType_sound` / `checkType_sound_true`: the bidirectional checker,
  including both lambda cases (`lam_type` and `lam_linear_type` via the
  `countUses` side condition, ADR-014).
* `typeCheckBlock_sound`: the block-level entry point.

Completeness is *not* claimed (and is false): `match_`, `none_`, `.ok_`,
`.err_`, `refCast` and lambda synthesis all return `none`.
-/

namespace Morph.Specs.TypeSystem

open Morph.Syntax

/-! ## Size measure for the mutual induction

`inferType` and `inferTypes` are mutually recursive; the induction below is
strong induction on this measure (the built-in `induction` tactic refuses
`Expr` because it is a nested inductive). `mLit` makes the literal recursion
`.lit (.some v) ↝ .lit v` measure-decreasing. -/

mutual
/-- Expression size, fine-grained enough for the checker's recursions. -/
def mE : Expr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .lit v => 1 + mLit v
  | .unop _ e => 1 + mE e
  | .binop _ e1 e2 => 1 + mE e1 + mE e2
  | .app fn args => 1 + mE fn + mL args
  | .lam _ b => 1 + mE b
  | .let_ a b => 1 + mE a + mE b
  | .ifThenElse c t f => 1 + mE c + mE t + mE f
  | .forLoop s e b => 1 + mE s + mE e + mL b
  | .block es => 1 + mL es
  | .match_ scrut _ => 1 + mE scrut
  | .field_ e _ => 1 + mE e
  | .pipe e f => 1 + mE e + mE f
  | .typeAsc e _ => 1 + mE e
  | .some_ e => 1 + mE e
  | .none_ => 1
  | .ok_ e => 1 + mE e
  | .err_ e => 1 + mE e
  | .nullCoalesce e1 e2 => 1 + mE e1 + mE e2
  | .tuple_ es => 1 + mL es
  | .arrayLit es => 1 + mL es
  | .arrayIndex a i => 1 + mE a + mE i
  | .refCreate e _ _ => 1 + mE e
  | .refLoad e => 1 + mE e
  | .refStore e v _ => 1 + mE e + mE v
  | .refFree e => 1 + mE e
  | .refCast e _ => 1 + mE e
termination_by e => sizeOf e

/-- List size companion of `mE`. -/
def mL : List Expr → Nat
  | [] => 0
  | e :: es => 1 + mE e + mL es
termination_by es => sizeOf es

/-- Literal size companion of `mE`. -/
def mLit : Morph.Core.Value → Nat
  | .some v => 1 + mLit v
  | .ok v => 1 + mLit v
  | .err v => 1 + mLit v
  | _ => 1
termination_by v => sizeOf v
end

theorem mE_lit_some (v : Morph.Core.Value) :
    mE (.lit v) < mE (.lit (Morph.Core.Value.some v)) := by
  simp only [mE, mLit]; omega

theorem mE_unop  (op : Morph.Core.Operator) (e : Expr) :
    mE e < mE (.unop op e) := by
  simp only [mE]; omega

theorem mE_binop_l  (op : Morph.Core.Operator) (e1 e2 : Expr) :
    mE e1 < mE (.binop op e1 e2) := by
  simp only [mE]; omega

theorem mE_binop_r  (op : Morph.Core.Operator) (e1 e2 : Expr) :
    mE e2 < mE (.binop op e1 e2) := by
  simp only [mE]; omega

theorem mE_app_fn  (fn : Expr) (args : List Expr) :
    mE fn < mE (.app fn args) := by
  simp only [mE]; omega

theorem mE_app_args  (fn : Expr) (args : List Expr) :
    mL args < mE (.app fn args) := by
  simp only [mE]; omega

theorem mE_lam  (k : Nat) (b : Expr) :
    mE b < mE (.lam k b) := by
  simp only [mE]; omega

theorem mE_let_l (a b : Expr) :
    mE a < mE (.let_ a b) := by
  simp only [mE]; omega

theorem mE_let_r (a b : Expr) :
    mE b < mE (.let_ a b) := by
  simp only [mE]; omega

theorem mE_if_c (c t f : Expr) :
    mE c < mE (.ifThenElse c t f) := by
  simp only [mE]; omega

theorem mE_if_t (c t f : Expr) :
    mE t < mE (.ifThenElse c t f) := by
  simp only [mE]; omega

theorem mE_if_f (c t f : Expr) :
    mE f < mE (.ifThenElse c t f) := by
  simp only [mE]; omega

theorem mE_for_s  (s e : Expr) (body : List Expr) :
    mE s < mE (.forLoop s e body) := by
  simp only [mE]; omega

theorem mE_for_e  (s e : Expr) (body : List Expr) :
    mE e < mE (.forLoop s e body) := by
  simp only [mE]; omega

theorem mE_for_body  (s e : Expr) (body : List Expr) :
    mL body < mE (.forLoop s e body) := by
  simp only [mE]; omega

theorem mE_block (es : List Expr) :
    mL es < mE (.block es) := by
  simp only [mE]; omega

theorem mE_field  (e : Expr) (name : String) :
    mE e < mE (.field_ e name) := by
  simp only [mE]; omega

theorem mE_pipe_l (e f : Expr) :
    mE e < mE (.pipe e f) := by
  simp only [mE]; omega

theorem mE_pipe_r (e f : Expr) :
    mE f < mE (.pipe e f) := by
  simp only [mE]; omega

theorem mE_some (e : Expr) :
    mE e < mE (.some_ e) := by
  simp only [mE]; omega

theorem mE_null_l (e1 e2 : Expr) :
    mE e1 < mE (.nullCoalesce e1 e2) := by
  simp only [mE]; omega

theorem mE_null_r (e1 e2 : Expr) :
    mE e2 < mE (.nullCoalesce e1 e2) := by
  simp only [mE]; omega

theorem mE_typeAsc  (e : Expr) (τ : Morph.Core.Typ) :
    mE e < mE (.typeAsc e τ) := by
  simp only [mE]; omega

theorem mE_tuple (es : List Expr) :
    mL es < mE (.tuple_ es) := by
  simp only [mE]; omega

theorem mE_arrayLit (es : List Expr) :
    mL es < mE (.arrayLit es) := by
  simp only [mE]; omega

theorem mE_index_l (arr idx : Expr) :
    mE arr < mE (.arrayIndex arr idx) := by
  simp only [mE]; omega

theorem mE_index_r (arr idx : Expr) :
    mE idx < mE (.arrayIndex arr idx) := by
  simp only [mE]; omega

theorem mE_refCreate  (e : Expr) (cap : Morph.Core.Capability) (τ : Morph.Core.Typ) :
    mE e < mE (.refCreate e cap τ) := by
  simp only [mE]; omega

theorem mE_refLoad (e : Expr) :
    mE e < mE (.refLoad e) := by
  simp only [mE]; omega

theorem mE_refStore_l  (e v : Expr) (τ : Morph.Core.Typ) :
    mE e < mE (.refStore e v τ) := by
  simp only [mE]; omega

theorem mE_refStore_r  (e v : Expr) (τ : Morph.Core.Typ) :
    mE v < mE (.refStore e v τ) := by
  simp only [mE]; omega

theorem mE_refFree (e : Expr) :
    mE e < mE (.refFree e) := by
  simp only [mE]; omega

theorem mL_cons_l  (e : Expr) (es : List Expr) :
    mE e < mL (e :: es) := by
  simp only [mL]; omega

theorem mL_cons_r  (e : Expr) (es : List Expr) :
    mL es < mL (e :: es) := by
  simp only [mL]; omega
/-! ## Helper lemmas -/

/-- `inferTypes` produces exactly one type per list element. -/
theorem inferTypes_length (es : List Expr) :
    ∀ (bvs : List Morph.Core.Typ) (Γ : TypEnv) (tys : List Morph.Core.Typ),
      inferTypes bvs Γ es = some tys → tys.length = es.length := by
  induction es with
  | nil =>
    intro bvs Γ tys h
    simp only [inferTypes] at h
    simp at h
    subst h
    simp
  | cons e es' ih =>
    intro bvs Γ tys h
    simp only [inferTypes] at h
    cases hin : inferType bvs Γ e with
    | none =>
      rw [hin] at h
      simp at h
    | some t =>
      cases hrest : inferTypes bvs Γ es' with
      | none =>
        rw [hin, hrest] at h
        simp at h
      | some ts =>
        rw [hin, hrest] at h
        simp at h
        obtain ⟨rfl⟩ := h
        simp [ih bvs Γ ts hrest]

/-- If every element of `xs` is (decidably) equal to `a`, then `xs` is a
`replicate`. Used for `arrayLit_type`'s premise. -/
theorem eq_all_replicate (xs : List Morph.Core.Typ) (a : Morph.Core.Typ)
    (h : xs.all (fun x => decide (x = a)) = true) :
    xs = List.replicate xs.length a := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hx, hxs⟩ := h
    rw [ih hxs, hx]
    simp [List.replicate_succ]

/-! ## Soundness of the `binop` dispatch -/

/-- `binopResult` only accepts operator/type combinations that the `binop_*`
rules of the judgment accept. -/
theorem binopResult_sound (op : Morph.Core.Operator) (t1 t2 : Morph.Core.Typ) (bvs : List Morph.Core.Typ)
    (Γ : TypEnv) (e1 e2 : Expr) (τ : Morph.Core.Typ)
    (hres : binopResult op t1 t2 = some τ) :
    HasType bvs Γ e1 t1 → HasType bvs Γ e2 t2 →
    HasType bvs Γ (.binop op e1 e2) τ := by
  intro h1 h2
  cases op with
  | add =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2
             | exact HasType.binop_string_concat _ _ _ _ _ rfl h1 h2)
        | simp at hres
  | sub =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | mul =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | div =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | mod =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | eq =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | neq =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | lt =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | leq =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | gt =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | geq =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | and =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_logic _ _ _ _ _ (by unfold isLogicOp; trivial) h1 h2)
        | simp at hres
  | or =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_logic _ _ _ _ _ (by unfold isLogicOp; trivial) h1 h2)
        | simp at hres
  | andb =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | orb =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | xorb =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | shl =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | shr =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | ptrAdd =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_ptr_arith _ _ _ _ _ (by unfold isPtrArithOp; trivial) h1 h2)
        | simp at hres
  | ptrSub =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_ptr_arith _ _ _ _ _ (by unfold isPtrArithOp; trivial) h1 h2)
        | simp at hres
  | ptrLoad =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_ptr_load _ _ _ _ h1 h2)
        | simp at hres
  | ptrStore =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_ptr_store _ _ _ _ h1 h2)
        | simp at hres
  | not =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | notb =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq] at hres
           obtain ⟨rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
/-! ## The mutual soundness theorem -/

/-- Combined soundness statement for the checker, by strong induction on the
size measure. -/
theorem sound_mutual (n : Nat) :
    (∀ (e : Expr) (bvs : List Morph.Core.Typ) (Γ : TypEnv) (τ : Morph.Core.Typ),
        mE e < n → inferType bvs Γ e = some τ → HasType bvs Γ e τ) ∧
    (∀ (es : List Expr) (bvs : List Morph.Core.Typ) (Γ : TypEnv) (τs : List Morph.Core.Typ),
        mL es < n → inferTypes bvs Γ es = some τs →
        HasTypeAll bvs Γ es τs) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro e _ _ _ hn _
      exact absurd hn (Nat.not_lt_zero _)
    · intro es _ _ _ hn _
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    obtain ⟨ihE, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro e bvs Γ τ hn h
      cases e with
      | bvar k =>
        simp only [inferType] at h
        split at h
        · rename_i hLt
          simp at h
          subst h
          exact HasType.bvar_type bvs Γ k hLt
        · simp at h
      | fvar name =>
        simp only [inferType] at h
        exact HasType.fvar_type bvs Γ name τ h
      | lit v =>
        cases v with
        | int z =>
          simp only [inferType] at h
          simp at h
          subst h
          exact HasType.lit_int bvs Γ z
        | bool b =>
          simp only [inferType] at h
          simp at h
          subst h
          exact HasType.lit_bool bvs Γ b
        | string str =>
          simp only [inferType] at h
          simp at h
          subst h
          exact HasType.lit_string bvs Γ str
        | unit =>
          simp only [inferType] at h
          simp at h
          subst h
          exact HasType.lit_unit bvs Γ
        | pointer p =>
          simp only [inferType] at h
          simp at h
          subst h
          exact HasType.lit_pointer bvs Γ p
        | float f =>
          simp only [inferType] at h
          simp at h
          subst h
          exact HasType.lit_float bvs Γ .f64 f
        | some v' =>
          simp only [inferType] at h
          split at h
          · rename_i t hin
            simp at h
            subst h
            exact HasType.lit_some bvs Γ v' t
          · simp at h
        | none => simp only [inferType] at h; simp at h
        | undef => simp only [inferType] at h; simp at h
        | ok _ => simp only [inferType] at h; simp at h
        | err _ => simp only [inferType] at h; simp at h
        | loc _ => simp only [inferType] at h; simp at h
        | tuple_ _ => simp only [inferType] at h; simp at h
        | array_ _ => simp only [inferType] at h; simp at h
        | closure _ _ => simp only [inferType] at h; simp at h
      | unop op e =>
        cases op with
        | not =>
          simp only [inferType] at h
          split at h
          · rename_i t hin
            simp at h
            subst h
            exact HasType.unop_not bvs Γ e
              (ihE e bvs Γ .boolType
                (Nat.lt_of_lt_of_le (mE_unop .not e) (Nat.le_of_lt_succ hn)) hin)
          · simp at h
        | notb =>
          simp only [inferType] at h
          split at h
          · rename_i t hin
            simp at h
            subst h
            exact HasType.unop_notb bvs Γ e
              (ihE e bvs Γ .intType
                (Nat.lt_of_lt_of_le (mE_unop .notb e) (Nat.le_of_lt_succ hn)) hin)
          · simp at h
        | _ => simp only [inferType] at h; simp at h
      | binop op e1 e2 =>
        simp only [inferType] at h
        split at h
        · rename_i t1 h1eq
          split at h
          · rename_i t2 h2eq
            cases hres : binopResult op t1 t2 with
            | none => rw [hres] at h; simp at h
            | some r =>
              rw [hres] at h
              simp at h
              subst h
              exact binopResult_sound op t1 t2 bvs Γ e1 e2 r hres
                (ihE e1 bvs Γ t1
                  (Nat.lt_of_lt_of_le (mE_binop_l op e1 e2) (Nat.le_of_lt_succ hn)) h1eq)
                (ihE e2 bvs Γ t2
                  (Nat.lt_of_lt_of_le (mE_binop_r op e1 e2) (Nat.le_of_lt_succ hn)) h2eq)
          · simp at h
        · simp at h
      | app fn args =>
        simp only [inferType] at h
        split at h
        · rename_i ps rt hfn
          split at h
          · rename_i ats hargs
            split at h
            · rename_i hps
              simp at h
              subst h
              have hHA := ihL args bvs Γ ats
                (Nat.lt_of_lt_of_le (mE_app_args fn args) (Nat.le_of_lt_succ hn)) hargs
              rw [hps] at hHA
              exact HasType.app_type bvs Γ fn args ps rt
                (ihE fn bvs Γ (.functionType ps rt)
                  (Nat.lt_of_lt_of_le (mE_app_fn fn args) (Nat.le_of_lt_succ hn)) hfn)
                hHA
            · simp at h
          · simp at h
        · rename_i ps rt hfn
          split at h
          · rename_i ats hargs
            split at h
            · rename_i hps
              simp at h
              subst h
              have hHA := ihL args bvs Γ ats
                (Nat.lt_of_lt_of_le (mE_app_args fn args) (Nat.le_of_lt_succ hn)) hargs
              rw [hps] at hHA
              exact HasType.app_linear_type bvs Γ fn args ps rt
                (ihE fn bvs Γ (.linearFunctionType ps rt)
                  (Nat.lt_of_lt_of_le (mE_app_fn fn args) (Nat.le_of_lt_succ hn)) hfn)
                hHA
            · simp at h
          · simp at h
        · simp at h
      | lam _ _ => simp only [inferType] at h; simp at h
      | let_ e1 e2 =>
        simp only [inferType] at h
        split at h
        · rename_i t1 h1eq
          exact HasType.let_type bvs Γ e1 e2 t1 τ
            (ihE e1 bvs Γ t1
              (Nat.lt_of_lt_of_le (mE_let_l e1 e2) (Nat.le_of_lt_succ hn)) h1eq)
            (ihE e2 (t1 :: bvs) Γ τ
              (Nat.lt_of_lt_of_le (mE_let_r e1 e2) (Nat.le_of_lt_succ hn)) h)
        · simp at h
      | ifThenElse c t f =>
        simp only [inferType] at h
        split at h
        · rename_i hc
          split at h
          · rename_i typT ht
            split at h
            · rename_i typF hf
              split at h
              · rename_i htf
                simp at h
                subst h
                exact HasType.if_type bvs Γ c t f typT
                  (ihE c bvs Γ .boolType
                    (Nat.lt_of_lt_of_le (mE_if_c c t f) (Nat.le_of_lt_succ hn)) hc)
                  (ihE t bvs Γ typT
                    (Nat.lt_of_lt_of_le (mE_if_t c t f) (Nat.le_of_lt_succ hn)) ht)
                  (by
                    have hHF := ihE f bvs Γ typF
                      (Nat.lt_of_lt_of_le (mE_if_f c t f) (Nat.le_of_lt_succ hn)) hf
                    rw [← htf] at hHF
                    exact hHF)
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | forLoop s e body =>
        simp only [inferType] at h
        split at h
        · rename_i hs
          split at h
          · rename_i he
            split at h
            · rename_i hinfer
              simp at h
              subst h
              exact HasType.for_type bvs Γ s e body
                (ihE s bvs Γ .intType
                  (Nat.lt_of_lt_of_le (mE_for_s s e body) (Nat.le_of_lt_succ hn)) hs)
                (ihE e bvs Γ .intType
                  (Nat.lt_of_lt_of_le (mE_for_e s e body) (Nat.le_of_lt_succ hn)) he)
                (ihL body (.intType :: bvs) Γ [.unitType]
                  (Nat.lt_of_lt_of_le (mE_for_body s e body) (Nat.le_of_lt_succ hn)) hinfer)
            · simp at h
          · simp at h
        · simp at h
      | block exprs =>
        simp only [inferType] at h
        split at h
        · rename_i tys hlist
          split at h
          · rename_i t rest hrev
            simp at h
            subst h
            have hHA := ihL exprs bvs Γ tys
              (Nat.lt_of_lt_of_le (mE_block exprs) (Nat.le_of_lt_succ hn)) hlist
            have htys : tys = rest.reverse ++ [t] := by
              have h2 := congrArg List.reverse hrev
              rw [List.reverse_reverse, List.reverse_cons] at h2
              exact h2
            rw [htys] at hHA
            exact HasType.block_type bvs Γ exprs rest.reverse t hHA
          · simp at h
        · simp at h
      | match_ _ _ => simp only [inferType] at h; simp at h
      | field_ e name =>
        simp only [inferType] at h
        split at h
        · rename_i sname fields he_eq
          split at h
          · rename_i t hfield
            simp at h
            subst h
            exact HasType.field_access_type bvs Γ e name sname fields t
              (ihE e bvs Γ (.structType sname fields)
                (Nat.lt_of_lt_of_le (mE_field e name) (Nat.le_of_lt_succ hn)) he_eq)
                hfield
          · simp at h
        · simp at h
      | pipe e f =>
        simp only [inferType] at h
        split at h
        · rename_i te he_eq
          split at h
          · rename_i targ tret hf_eq
            split at h
            · rename_i hta
              simp at h
              subst h
              have hHE := ihE e bvs Γ te
                (Nat.lt_of_lt_of_le (mE_pipe_l e f) (Nat.le_of_lt_succ hn)) he_eq
              rw [hta] at hHE
              exact HasType.pipe_type bvs Γ e f targ tret hHE
                (ihE f bvs Γ (.functionType [targ] tret)
                  (Nat.lt_of_lt_of_le (mE_pipe_r e f) (Nat.le_of_lt_succ hn)) hf_eq)
            · simp at h
          · simp at h
        · simp at h
      | some_ e =>
        simp only [inferType] at h
        split at h
        · rename_i t he_eq
          simp at h
          subst h
          exact HasType.some_type bvs Γ e t
            (ihE e bvs Γ t (Nat.lt_of_lt_of_le (mE_some e) (Nat.le_of_lt_succ hn)) he_eq)
        · simp at h
      | none_ => simp only [inferType] at h; simp at h
      | ok_ _ => simp only [inferType] at h; simp at h
      | err_ _ => simp only [inferType] at h; simp at h
      | nullCoalesce e1 e2 =>
        simp only [inferType] at h
        split at h
        · rename_i t1 h1eq
          split at h
          · rename_i t2 h2eq
            split at h
            · rename_i hteq
              simp at h
              obtain ⟨rfl⟩ := h
              have hH2 := ihE e2 bvs Γ (.optionType t2)
                (Nat.lt_of_lt_of_le (mE_null_r e1 e2) (Nat.le_of_lt_succ hn)) h2eq
              rw [← hteq] at hH2
              exact HasType.null_coalesce_type bvs Γ e1 e2 t1
                (ihE e1 bvs Γ (.optionType t1)
                  (Nat.lt_of_lt_of_le (mE_null_l e1 e2) (Nat.le_of_lt_succ hn)) h1eq)
                hH2
            · simp at h
          · simp at h
        · simp at h
      | typeAsc e tAnn =>
        simp only [inferType] at h
        split at h
        · rename_i t he_eq
          split at h
          · rename_i hta
            simp at h
            subst h
            have hHE := ihE e bvs Γ t
              (Nat.lt_of_lt_of_le (mE_typeAsc e tAnn) (Nat.le_of_lt_succ hn)) he_eq
            rw [hta] at hHE
            exact HasType.typeAsc_type bvs Γ e tAnn hHE
          · simp at h
        · simp at h
      | tuple_ elems =>
        simp only [inferType] at h
        split at h
        · rename_i tys hlist
          simp at h
          obtain ⟨rfl⟩ := h
          exact HasType.tuple_type bvs Γ elems tys
            (ihL elems bvs Γ tys (Nat.lt_of_lt_of_le (mE_tuple elems) (Nat.le_of_lt_succ hn)) hlist)
        · simp at h
      | arrayLit elems =>
        simp only [inferType] at h
        split at h
        · rename_i tys hlist
          split at h
          · rename_i t headeq
            split at h
            · rename_i hcond
              simp at h
              obtain ⟨rfl⟩ := h
              rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
              obtain ⟨hall, hpos⟩ := hcond
              have htys := eq_all_replicate tys t hall
              have hlen := inferTypes_length elems bvs Γ tys hlist
              have hHA := ihL elems bvs Γ tys
                (Nat.lt_of_lt_of_le (mE_arrayLit elems) (Nat.le_of_lt_succ hn)) hlist
              rw [htys, hlen] at hHA
              exact HasType.arrayLit_type bvs Γ elems t elems.length hHA rfl hpos
            · simp at h
          · simp at h
        · simp at h
      | arrayIndex arr idx =>
        simp only [inferType] at h
        split at h
        · rename_i t sz heq
          split at h
          · rename_i hieq
            simp at h
            subst h
            exact HasType.arrayIndex_type bvs Γ arr idx t sz
              (ihE arr bvs Γ (.arrayType t sz)
                (Nat.lt_of_lt_of_le (mE_index_l arr idx) (Nat.le_of_lt_succ hn)) heq)
              (ihE idx bvs Γ .intType
                (Nat.lt_of_lt_of_le (mE_index_r arr idx) (Nat.le_of_lt_succ hn)) hieq)
          · simp at h
        · simp at h
      | refCreate e cap tAnn =>
        simp only [inferType] at h
        split at h
        · rename_i t he_eq
          split at h
          · rename_i hta
            simp at h
            subst h
            have hHE := ihE e bvs Γ t
              (Nat.lt_of_lt_of_le (mE_refCreate e cap tAnn) (Nat.le_of_lt_succ hn)) he_eq
            rw [hta] at hHE
            exact HasType.refCreate_type bvs Γ e cap tAnn hHE
          · simp at h
        · simp at h
      | refLoad e =>
        simp only [inferType] at h
        split at h
        · rename_i cap t he_eq
          simp at h
          subst h
          exact HasType.refLoad_type bvs Γ e cap _
            (ihE e bvs Γ (.refType cap _)
              (Nat.lt_of_lt_of_le (mE_refLoad e) (Nat.le_of_lt_succ hn)) he_eq)
        · simp at h
      | refStore e v tAnn =>
        simp only [inferType] at h
        split at h
        · rename_i cap t he_eq
          split at h
          · rename_i hcap
            split at h
            · rename_i hte
              split at h
              · rename_i tv hveq
                split at h
                · rename_i htv
                  simp at h
                  subst h
                  have hHE := ihE e bvs Γ (.refType cap t)
                    (Nat.lt_of_lt_of_le (mE_refStore_l e v tAnn) (Nat.le_of_lt_succ hn)) he_eq
                  rw [hte] at hHE
                  have hHV := ihE v bvs Γ tv
                    (Nat.lt_of_lt_of_le (mE_refStore_r e v tAnn) (Nat.le_of_lt_succ hn)) hveq
                  rw [htv] at hHV
                  exact HasType.refStore_type bvs Γ e v cap tAnn hHE hHV hcap
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | refFree e =>
        simp only [inferType] at h
        split at h
        · rename_i cap t he_eq
          split at h
          · rename_i hcap
            simp at h
            obtain ⟨rfl⟩ := h
            have hHE := ihE e bvs Γ (.refType cap t)
              (Nat.lt_of_lt_of_le (mE_refFree e) (Nat.le_of_lt_succ hn)) he_eq
            rw [hcap] at hHE
            exact HasType.refFree_type bvs Γ e t hHE
          · simp at h
        · simp at h
      | refCast _ _ => simp only [inferType] at h; simp at h
    · intro es bvs Γ τs hn h
      cases es with
      | nil =>
        simp only [inferTypes] at h
        simp at h
        obtain ⟨rfl⟩ := h
        exact HasTypeAll.nil bvs Γ
      | cons e es' =>
        simp only [inferTypes] at h
        cases hin : inferType bvs Γ e with
        | none =>
          rw [hin] at h
          simp at h
        | some t =>
          cases hrest : inferTypes bvs Γ es' with
          | none =>
            rw [hin, hrest] at h
            simp at h
          | some ts =>
            rw [hin, hrest] at h
            simp at h
            obtain ⟨rfl⟩ := h
            exact HasTypeAll.cons bvs Γ e es' t ts
              (ihE e bvs Γ t (Nat.lt_of_lt_of_le (mL_cons_l e es') (Nat.le_of_lt_succ hn)) hin)
              (ihL es' bvs Γ ts (Nat.lt_of_lt_of_le (mL_cons_r e es') (Nat.le_of_lt_succ hn)) hrest)

/-! ## Soundness corollaries -/

/-- **P13 main theorem.** The checker is sound: every `some τ` answer
corresponds to a derivation of the declarative judgment. -/
theorem inferType_sound (bvs : List Morph.Core.Typ) (Γ : TypEnv) (e : Expr) (τ : Morph.Core.Typ)
    (h : inferType bvs Γ e = some τ) : HasType bvs Γ e τ :=
  (sound_mutual (mE e + 1)).1 e bvs Γ τ (Nat.lt_succ_self _) h

/-- List-level analogue of `inferType_sound`. -/
theorem inferTypes_sound (bvs : List Morph.Core.Typ) (Γ : TypEnv) (es : List Expr) (τs : List Morph.Core.Typ)
    (h : inferTypes bvs Γ es = some τs) : HasTypeAll bvs Γ es τs :=
  (sound_mutual (mL es + 1)).2 es bvs Γ τs (Nat.lt_succ_self _) h

/-- `synthType` is definitionally `inferType`, so it is sound too. -/
theorem synthType_sound (bvs : List Morph.Core.Typ) (Γ : TypEnv) (e : Expr) (τ : Morph.Core.Typ)
    (h : Morph.TypeChecker.synthType bvs Γ e = some τ) :
    HasType bvs Γ e τ :=
  inferType_sound bvs Γ e τ h

/-- `checkType` on a lambda checked against a `functionType`: the recursive
call on the body (with the `lam_type` push) succeeds. -/
theorem checkType_lam_fun (k : Nat) (body : Expr) (bvs : List Morph.Core.Typ) (Γ : TypEnv)
    (ps : List Morph.Core.Typ) (rt : Morph.Core.Typ)
    (h : Morph.TypeChecker.checkType bvs Γ (.lam k body) (.functionType ps rt) = true) :
    k = ps.length ∧
      Morph.TypeChecker.checkType (ps.reverse ++ bvs) Γ body rt = true := by
  simp only [Morph.TypeChecker.checkType] at h
  split at h
  · rename_i hdec
    exact ⟨hdec, h⟩
  · simp at h

/-- `checkType` on a lambda checked against a `linearFunctionType`: the
recursive call on the body succeeds and every parameter occurs exactly once
(`countUses`, ADR-014). -/
theorem checkType_lam_lin (k : Nat) (body : Expr) (bvs : List Morph.Core.Typ) (Γ : TypEnv)
    (ps : List Morph.Core.Typ) (rt : Morph.Core.Typ)
    (h : Morph.TypeChecker.checkType bvs Γ (.lam k body) (.linearFunctionType ps rt) = true) :
    k = ps.length ∧
      Morph.TypeChecker.checkType (ps.reverse ++ bvs) Γ body rt = true ∧
      (∀ i, i < ps.length → countUses body i = 1) := by
  simp only [Morph.TypeChecker.checkType] at h
  split at h
  · rename_i hdec
    rw [Bool.and_eq_true] at h
    obtain ⟨hb, huses⟩ := h
    refine ⟨hdec, hb, ?_⟩
    intro i hi
    have hmem : i ∈ List.range ps.length := List.mem_range.mpr hi
    have huse := List.all_eq_true.mp huses i hmem
    simpa using huse
  · simp at h

/-- The bidirectional checker is sound: `checkType bvs Γ e expected = true`
implies `HasType bvs Γ e expected` (P13, with the ADR-014 linear-arrow case). -/
theorem checkType_sound (n : Nat) :
    ∀ (e : Expr) (bvs : List Morph.Core.Typ) (Γ : TypEnv) (expected : Morph.Core.Typ),
      mE e < n → Morph.TypeChecker.checkType bvs Γ e expected = true →
      HasType bvs Γ e expected := by
  induction n with
  | zero =>
    intro e _ _ _ hn _
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro e bvs Γ expected hn h
    cases heq : e with
    | lam k body =>
      subst heq
      cases heq2 : expected with
      | functionType ps rt =>
        rw [heq2] at h
        obtain ⟨hlen, hb⟩ := checkType_lam_fun k body bvs Γ ps rt h
        exact HasType.lam_type bvs Γ k body ps rt hlen
          (ih body (ps.reverse ++ bvs) Γ rt (by simp only [mE] at hn; omega) hb)
      | linearFunctionType ps rt =>
        rw [heq2] at h
        obtain ⟨hlen, hb, huses⟩ := checkType_lam_lin k body bvs Γ ps rt h
        exact HasType.lam_linear_type bvs Γ k body ps rt hlen
          (ih body (ps.reverse ++ bvs) Γ rt (by simp only [mE] at hn; omega) hb) huses
      | _ =>
        rw [heq2] at h
        simp [Morph.TypeChecker.checkType] at h
    | _ =>
      subst heq
      simp only [Morph.TypeChecker.checkType] at h
      split at h
      · rename_i t hin
        simp only [decide_eq_true_eq] at h
        subst h
        exact inferType_sound bvs Γ _ t hin
      · simp at h

/-- Contract-level corollary of `checkType_sound` without the measure
bookkeeping. -/
theorem checkType_sound_true (bvs : List Morph.Core.Typ) (Γ : TypEnv) (e : Expr) (expected : Morph.Core.Typ)
    (h : Morph.TypeChecker.checkType bvs Γ e expected = true) :
    HasType bvs Γ e expected :=
  checkType_sound (mE e + 1) e bvs Γ expected (Nat.lt_succ_self _) h

/-- `typeCheckBlock` is sound: every expression in the block is typable
(independently) by the judgment. -/
theorem typeCheckBlock_sound (bvs : List Morph.Core.Typ) (Γ : TypEnv) (exprs : List Expr)
    (h : Morph.TypeChecker.typeCheckBlock bvs Γ exprs = true) :
    ∀ e ∈ exprs, ∃ τ, HasType bvs Γ e τ := by
  intro e he
  have hall : (inferType bvs Γ e).isSome = true :=
    List.all_eq_true.mp h e he
  cases hs : inferType bvs Γ e with
  | none =>
    rw [hs] at hall
    simp at hall
  | some t =>
    exact ⟨t, inferType_sound bvs Γ e t hs⟩

end Morph.Specs.TypeSystem
