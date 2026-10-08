/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TypeSystem.Spec
import Morph.TypeChecker

/-!
# Inference Soundness (research program P13, CakeML frontend-2 discipline)

The executable checker `inferTypeC`/`inferTypesC` (defined in the executable
section of `Morph.Specs.TypeSystem.Spec`) is proven sound against the
declarative judgment `HasType`/`HasTypeAll`:

* `inferTypeC_sound`: every `some (τ, cout)` answer is a real derivation
  `HasType ctx Γ e τ cout`.
* `inferType_sound`, `inferTypes_sound`, `synthType_sound`: the type-only
  projections used across the code base.
* `checkType_sound`: the bidirectional checker, including both lambda cases
  (`lam_type` via `linPushMany`, `lam_linear_type` via `linPushMany` and
  the `countUses` side condition).
* `typeCheckBlock_sound`: the block-level entry point.

Completeness is *not* claimed (and is false): `match_`, `none_`, `.ok_`,
`.err_`, `refCast` and lambda synthesis all return `none`.
-/

namespace Morph.Specs.TypeSystem

open Morph.Syntax

/-! ## Size measure for the mutual induction

`inferTypeC` and `inferTypesC` are mutually recursive; the induction below is
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

/-- `inferTypesC` produces exactly one type per list element. -/
theorem inferTypesC_length (es : List Expr) :
    ∀ (ctx : LinCtx) (Γ : TypEnv) (tys : List Morph.Core.Typ) (cout : LinCtx),
      inferTypesC ctx Γ es = some (tys, cout) → tys.length = es.length := by
  induction es with
  | nil =>
    intro ctx Γ tys cout h
    simp only [inferTypesC] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons e es' ih =>
    intro ctx Γ tys cout h
    simp only [inferTypesC] at h
    split at h
    · rename_i t c he
      split at h
      · rename_i rest cout' hrest
        simp at h
        obtain ⟨-, hty, -⟩ := h
        rw [← hty]
        simp [ih c Γ rest cout' hrest]
      · simp at h
    · simp at h

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
rules of the judgment accept, threading the mid context `cmid`. -/
theorem binopResult_sound (op : Morph.Core.Operator) (t1 t2 : Morph.Core.Typ) (cmid ctx : LinCtx)
    (Γ : TypEnv) (e1 e2 : Expr) (τ : Morph.Core.Typ) (cout : LinCtx)
    (hres : binopResult op t1 t2 cmid = some (τ, cout)) :
    HasType ctx Γ e1 t1 cmid → HasType cmid Γ e2 t2 cmid →
    HasType ctx Γ (.binop op e1 e2) τ cout := by
  intro h1 h2
  cases op with
  | add =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2
             | exact HasType.binop_string_concat _ _ _ _ _ _ rfl h1 h2)
        | simp at hres
  | sub =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | mul =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | div =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | mod =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | eq =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | neq =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | lt =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | leq =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | gt =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | geq =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_comp _ _ _ _ _ _ (by unfold isCompOp; trivial) h1 h2)
        | simp at hres
  | and =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_logic _ _ _ _ _ _ (by unfold isLogicOp; trivial) h1 h2)
        | simp at hres
  | or =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_logic _ _ _ _ _ _ (by unfold isLogicOp; trivial) h1 h2)
        | simp at hres
  | andb =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | orb =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | xorb =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | shl =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | shr =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_bitwise _ _ _ _ _ _ (by unfold isBitwiseOp; trivial) h1 h2)
        | simp at hres
  | ptrAdd =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_ptr_arith _ _ _ _ _ _ (by unfold isPtrArithOp; trivial) h1 h2)
        | simp at hres
  | ptrSub =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_ptr_arith _ _ _ _ _ _ (by unfold isPtrArithOp; trivial) h1 h2)
        | simp at hres
  | ptrLoad =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_ptr_load _ _ _ _ _ h1 h2)
        | simp at hres
  | ptrStore =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_ptr_store _ _ _ _ _ h1 h2)
        | simp at hres
  | not =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres
  | notb =>
    simp only [binopResult] at hres
    split at hres
    all_goals
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hres
           obtain ⟨rfl, rfl⟩ := hres
           first
             | exact HasType.binop_arith _ _ _ _ _ _ (by unfold isArithOp; trivial) h1 h2)
        | simp at hres

/-! ## The mutual soundness theorem -/

/-- Combined soundness statement for the mutually recursive checker, by strong
induction on the size measure. -/
theorem sound_mutual (n : Nat) :
    (∀ (e : Expr) (ctx : LinCtx) (Γ : TypEnv) (τ : Morph.Core.Typ) (cout : LinCtx),
        mE e < n → inferTypeC ctx Γ e = some (τ, cout) → HasType ctx Γ e τ cout) ∧
    (∀ (es : List Expr) (ctx : LinCtx) (Γ : TypEnv) (τs : List Morph.Core.Typ) (cout : LinCtx),
        mL es < n → inferTypesC ctx Γ es = some (τs, cout) →
        HasTypeAll ctx Γ es τs cout) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro e _ _ _ _ hn _
      exact absurd hn (Nat.not_lt_zero _)
    · intro es _ _ _ _ hn _
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    obtain ⟨ihE, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro e ctx Γ τ cout hn h
      cases e with
      | bvar k =>
        simp only [inferTypeC] at h
        cases hget : ctx[k]? with
        | none =>
          rw [hget] at h
          simp at h
        | some e =>
          obtain ⟨t0, u0⟩ := e
          rw [hget] at h
          cases u0 with
          | zero =>
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            have hlen : k < (LinCtx.types ctx).length := by
              rw [LinCtx.types_length]
              exact (List.getElem?_eq_some_iff.mp hget).1
            exact HasType.bvar_type ctx Γ k t0 _ hlen hget rfl
          | many =>
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            have hlen : k < (LinCtx.types ctx).length := by
              rw [LinCtx.types_length]
              exact (List.getElem?_eq_some_iff.mp hget).1
            exact HasType.bvar_type_many ctx Γ k t0 hlen hget
          | one => simp at h
      | fvar name =>
        simp only [inferTypeC] at h
        cases hl : lookupTyp Γ name with
        | none => rw [hl] at h; simp at h
        | some t =>
          rw [hl] at h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact HasType.fvar_type ctx Γ name t hl
      | lit v =>
        cases v with
        | int z =>
          simp only [inferTypeC] at h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact HasType.lit_int ctx Γ z
        | bool b =>
          simp only [inferTypeC] at h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact HasType.lit_bool ctx Γ b
        | string str =>
          simp only [inferTypeC] at h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact HasType.lit_string ctx Γ str
        | unit =>
          simp only [inferTypeC] at h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact HasType.lit_unit ctx Γ
        | pointer p =>
          simp only [inferTypeC] at h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact HasType.lit_pointer ctx Γ p
        | float f =>
          simp only [inferTypeC] at h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact HasType.lit_float ctx Γ .f64 f
        | some v' =>
          simp only [inferTypeC] at h
          split at h
          · rename_i t c hin
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            exact HasType.lit_some ctx Γ v' t
          · simp at h
        | none => simp only [inferTypeC] at h; simp at h
        | undef => simp only [inferTypeC] at h; simp at h
        | ok _ => simp only [inferTypeC] at h; simp at h
        | err _ => simp only [inferTypeC] at h; simp at h
        | loc _ => simp only [inferTypeC] at h; simp at h
        | tuple_ _ => simp only [inferTypeC] at h; simp at h
        | array_ _ => simp only [inferTypeC] at h; simp at h
      | unop op e =>
        cases op with
        | not =>
          simp only [inferTypeC] at h
          split at h
          · rename_i t c hin
            split at h
            · rename_i hc
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have hH := ihE e ctx Γ .boolType c
                (Nat.lt_of_lt_of_le (mE_unop .not e) (Nat.le_of_lt_succ hn)) hin
              rw [hc] at hH
              exact HasType.unop_not ctx Γ e hH
            · simp at h
          · simp at h
        | notb =>
          simp only [inferTypeC] at h
          split at h
          · rename_i t c hin
            split at h
            · rename_i hc
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have hH := ihE e ctx Γ .intType c
                (Nat.lt_of_lt_of_le (mE_unop .notb e) (Nat.le_of_lt_succ hn)) hin
              rw [hc] at hH
              exact HasType.unop_notb ctx Γ e hH
            · simp at h
          · simp at h
        | _ => simp only [inferTypeC] at h; simp at h
      | binop op e1 e2 =>
        simp only [inferTypeC] at h
        split at h
        · rename_i t1 cmid h1eq
          split at h
          · rename_i t2 c2 h2eq
            split at h
            · rename_i hc
              have hH1 := ihE e1 ctx Γ t1 cmid
                (Nat.lt_of_lt_of_le (mE_binop_l op e1 e2) (Nat.le_of_lt_succ hn)) h1eq
              have hH2 := ihE e2 cmid Γ t2 c2
                (Nat.lt_of_lt_of_le (mE_binop_r op e1 e2) (Nat.le_of_lt_succ hn)) h2eq
              rw [hc] at hH2
              exact binopResult_sound op t1 t2 cmid ctx Γ e1 e2 τ cout h hH1 hH2
            · simp at h
          · simp at h
        · simp at h
      | app fn args =>
        simp only [inferTypeC] at h
        split at h
        · rename_i ps rt cf hfn
          split at h
          · rename_i hcF
            split at h
            · rename_i ats ca hargs
              split at h
              · rename_i hcA
                split at h
                · rename_i hps
                  simp at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hHF := ihE fn ctx Γ (.functionType ps rt) cf
                    (Nat.lt_of_lt_of_le (mE_app_fn fn args) (Nat.le_of_lt_succ hn)) hfn
                  rw [hcF] at hHF
                  have hHA := ihL args ctx Γ ats ca
                    (Nat.lt_of_lt_of_le (mE_app_args fn args) (Nat.le_of_lt_succ hn)) hargs
                  rw [hps] at hHA
                  rw [hcA] at hHA
                  exact HasType.app_type ctx Γ fn args ps rt hHF hHA
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · rename_i ps rt cf hfn
          split at h
          · rename_i hcF
            split at h
            · rename_i ats ca hargs
              split at h
              · rename_i hcA
                split at h
                · rename_i hps
                  simp at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hHF := ihE fn ctx Γ (.linearFunctionType ps rt) cf
                    (Nat.lt_of_lt_of_le (mE_app_fn fn args) (Nat.le_of_lt_succ hn)) hfn
                  rw [hcF] at hHF
                  have hHA := ihL args ctx Γ ats ca
                    (Nat.lt_of_lt_of_le (mE_app_args fn args) (Nat.le_of_lt_succ hn)) hargs
                  rw [hps] at hHA
                  rw [hcA] at hHA
                  exact HasType.app_linear_type ctx Γ fn args ps rt hHF hHA
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | lam _ _ => simp only [inferTypeC] at h; simp at h
      | let_ e1 e2 =>
        simp only [inferTypeC] at h
        split at h
        · rename_i t1 c1 h1eq
          split at h
          · rename_i hc1
            split at h
            · rename_i t2 c2 h2eq
              split at h
              · rename_i hc2
                simp at h
                obtain ⟨rfl, rfl⟩ := h
                have hH1 := ihE e1 ctx Γ t1 c1
                  (Nat.lt_of_lt_of_le (mE_let_l e1 e2) (Nat.le_of_lt_succ hn)) h1eq
                rw [hc1] at hH1
                have hH2 := ihE e2 (linPushMany ctx [t1]) Γ t2 c2
                  (Nat.lt_of_lt_of_le (mE_let_r e1 e2) (Nat.le_of_lt_succ hn)) h2eq
                rw [hc2] at hH2
                exact HasType.let_type ctx Γ e1 e2 t1 t2 hH1 hH2
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | ifThenElse c t f =>
        simp only [inferTypeC] at h
        split at h
        · rename_i tc cc hc_eq
          split at h
          · rename_i hcc
            split at h
            · rename_i tt ct ht_eq
              split at h
              · rename_i hct
                split at h
                · rename_i tf cf hf_eq
                  split at h
                  · rename_i hcf
                    split at h
                    · rename_i htf
                      simp at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hHC := ihE c ctx Γ .boolType cc
                        (Nat.lt_of_lt_of_le (mE_if_c c t f) (Nat.le_of_lt_succ hn)) hc_eq
                      rw [hcc] at hHC
                      have hHT := ihE t ctx Γ tt ct
                        (Nat.lt_of_lt_of_le (mE_if_t c t f) (Nat.le_of_lt_succ hn)) ht_eq
                      rw [hct] at hHT
                      have hHF := ihE f ctx Γ tf cf
                        (Nat.lt_of_lt_of_le (mE_if_f c t f) (Nat.le_of_lt_succ hn)) hf_eq
                      rw [hcf] at hHF
                      rw [← htf] at hHF
                      exact HasType.if_type ctx Γ c t f tt hHC hHT hHF
                    · simp at h
                  · simp at h
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | forLoop s e body =>
        simp only [inferTypeC] at h
        split at h
        · rename_i ts cs hs_eq
          split at h
          · rename_i hcs
            split at h
            · rename_i te ce he_eq
              split at h
              · rename_i hce
                split at h
                · rename_i tunit cb hbody
                  split at h
                  · rename_i hcb
                    simp at h
                    obtain ⟨rfl, rfl⟩ := h
                    have hHS := ihE s ctx Γ .intType cs
                      (Nat.lt_of_lt_of_le (mE_for_s s e body) (Nat.le_of_lt_succ hn)) hs_eq
                    rw [hcs] at hHS
                    have hHE := ihE e ctx Γ .intType ce
                      (Nat.lt_of_lt_of_le (mE_for_e s e body) (Nat.le_of_lt_succ hn)) he_eq
                    rw [hce] at hHE
                    have hHB := ihL body
                      (linPushMany ctx [.intType]) Γ [.unitType] cb
                      (Nat.lt_of_lt_of_le (mE_for_body s e body) (Nat.le_of_lt_succ hn)) hbody
                    rw [hcb] at hHB
                    exact HasType.for_type ctx Γ s e body hHS hHE hHB
                  · simp at h
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | block exprs =>
        simp only [inferTypeC] at h
        split at h
        · rename_i tys coutB hlist
          split at h
          · rename_i hcB
            split at h
            · rename_i t rest hrev
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have hHA := ihL exprs ctx Γ tys coutB
                (Nat.lt_of_lt_of_le (mE_block exprs) (Nat.le_of_lt_succ hn)) hlist
              rw [hcB] at hHA
              have htys : tys = rest.reverse ++ [t] := by
                have h2 := congrArg List.reverse hrev
                rw [List.reverse_reverse, List.reverse_cons] at h2
                exact h2
              rw [htys] at hHA
              exact HasType.block_type ctx Γ exprs rest.reverse t hHA
            · simp at h
          · simp at h
        · simp at h
      | match_ _ _ => simp only [inferTypeC] at h; simp at h
      | field_ e name =>
        simp only [inferTypeC] at h
        split at h
        · rename_i sname fields ce he_eq
          split at h
          · rename_i hce
            split at h
            · rename_i t hfield
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have hHE := ihE e ctx Γ (.structType sname fields) ce
                (Nat.lt_of_lt_of_le (mE_field e name) (Nat.le_of_lt_succ hn)) he_eq
              rw [hce] at hHE
              exact HasType.field_access_type ctx Γ e name sname fields t hHE hfield
            · simp at h
          · simp at h
        · simp at h
      | pipe e f =>
        simp only [inferTypeC] at h
        split at h
        · rename_i te ce he_eq
          split at h
          · rename_i hce
            split at h
            · rename_i targ tret cf hf_eq
              split at h
              · rename_i hcf
                split at h
                · rename_i hta
                  simp at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hHE := ihE e ctx Γ te ce
                    (Nat.lt_of_lt_of_le (mE_pipe_l e f) (Nat.le_of_lt_succ hn)) he_eq
                  rw [hce] at hHE
                  have hHF := ihE f ctx Γ (.functionType [targ] tret) cf
                    (Nat.lt_of_lt_of_le (mE_pipe_r e f) (Nat.le_of_lt_succ hn)) hf_eq
                  rw [hcf] at hHF
                  rw [hta] at hHE
                  exact HasType.pipe_type ctx Γ e f targ tret hHE hHF
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | typeAsc e tAnn =>
        simp only [inferTypeC] at h
        split at h
        · rename_i t ce he_eq
          split at h
          · rename_i hce
            split at h
            · rename_i hta
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have hHE := ihE e ctx Γ t ce
                (Nat.lt_of_lt_of_le (mE_typeAsc e tAnn) (Nat.le_of_lt_succ hn)) he_eq
              rw [hce] at hHE
              rw [hta] at hHE
              exact HasType.typeAsc_type ctx Γ e tAnn hHE
            · simp at h
          · simp at h
        · simp at h
      | some_ e =>
        simp only [inferTypeC] at h
        split at h
        · rename_i t ce he_eq
          split at h
          · rename_i hce
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            have hHE := ihE e ctx Γ t ce
              (Nat.lt_of_lt_of_le (mE_some e) (Nat.le_of_lt_succ hn)) he_eq
            rw [hce] at hHE
            exact HasType.some_type ctx Γ e t hHE
          · simp at h
        · simp at h
      | none_ => simp only [inferTypeC] at h; simp at h
      | ok_ _ => simp only [inferTypeC] at h; simp at h
      | err_ _ => simp only [inferTypeC] at h; simp at h
      | nullCoalesce e1 e2 =>
        simp only [inferTypeC] at h
        split at h
        · rename_i t1 c1 h1eq
          split at h
          · rename_i hc1
            split at h
            · rename_i t2 c2 h2eq
              split at h
              · rename_i hc2
                split at h
                · rename_i hteq
                  simp at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hH1 := ihE e1 ctx Γ (.optionType t1) c1
                    (Nat.lt_of_lt_of_le (mE_null_l e1 e2) (Nat.le_of_lt_succ hn)) h1eq
                  rw [hc1] at hH1
                  have hH2 := ihE e2 ctx Γ (.optionType t2) c2
                    (Nat.lt_of_lt_of_le (mE_null_r e1 e2) (Nat.le_of_lt_succ hn)) h2eq
                  rw [hc2, ← hteq] at hH2
                  exact HasType.null_coalesce_type ctx Γ e1 e2 t1 hH1 hH2
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | tuple_ elems =>
        simp only [inferTypeC] at h
        split at h
        · rename_i tys coutB hlist
          split at h
          · rename_i hcB
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            have hHA := ihL elems ctx Γ tys coutB
              (Nat.lt_of_lt_of_le (mE_tuple elems) (Nat.le_of_lt_succ hn)) hlist
            rw [hcB] at hHA
            exact HasType.tuple_type ctx Γ elems tys hHA
          · simp at h
        · simp at h
      | arrayLit elems =>
        simp only [inferTypeC] at h
        split at h
        · rename_i tys coutB hlist
          split at h
          · rename_i hcB
            split at h
            · rename_i t headeq
              split at h
              · rename_i hcond
                simp at h
                obtain ⟨rfl, rfl⟩ := h
                rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
                obtain ⟨hall, hpos⟩ := hcond
                have htys := eq_all_replicate tys t hall
                have hlen := inferTypesC_length elems ctx Γ tys coutB hlist
                have hHA := ihL elems ctx Γ tys coutB
                  (Nat.lt_of_lt_of_le (mE_arrayLit elems) (Nat.le_of_lt_succ hn)) hlist
                rw [hcB] at hHA
                rw [htys, hlen] at hHA
                exact HasType.arrayLit_type ctx Γ elems t elems.length hHA rfl hpos
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | arrayIndex arr idx =>
        simp only [inferTypeC] at h
        split at h
        · rename_i t n ca heq
          split at h
          · rename_i hcA
            split at h
            · rename_i ti ci hieq
              split at h
              · rename_i hci
                simp at h
                obtain ⟨rfl, rfl⟩ := h
                have hHA := ihE arr ctx Γ (.arrayType t n) ca
                  (Nat.lt_of_lt_of_le (mE_index_l arr idx) (Nat.le_of_lt_succ hn)) heq
                rw [hcA] at hHA
                have hHI := ihE idx ctx Γ .intType ci
                  (Nat.lt_of_lt_of_le (mE_index_r arr idx) (Nat.le_of_lt_succ hn)) hieq
                rw [hci] at hHI
                exact HasType.arrayIndex_type ctx Γ arr idx t n hHA hHI
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | refCreate e cap tAnn =>
        simp only [inferTypeC] at h
        split at h
        · rename_i t ce heq
          split at h
          · rename_i hce
            split at h
            · rename_i hta
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have hHE := ihE e ctx Γ t ce
                (Nat.lt_of_lt_of_le (mE_refCreate e cap tAnn) (Nat.le_of_lt_succ hn)) heq
              rw [hce] at hHE
              rw [hta] at hHE
              exact HasType.refCreate_type ctx Γ e cap tAnn hHE
            · simp at h
          · simp at h
        · simp at h
      | refLoad e =>
        simp only [inferTypeC] at h
        split at h
        · rename_i cap t ce heq
          split at h
          · rename_i hce
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            have hHE := ihE e ctx Γ (.refType cap t) ce
              (Nat.lt_of_lt_of_le (mE_refLoad e) (Nat.le_of_lt_succ hn)) heq
            rw [hce] at hHE
            exact HasType.refLoad_type ctx Γ e cap t hHE
          · simp at h
        · simp at h
      | refStore e v tAnn =>
        simp only [inferTypeC] at h
        split at h
        · rename_i cap t ce heq
          split at h
          · rename_i hce
            split at h
            · rename_i hcap
              split at h
              · rename_i hte
                split at h
                · rename_i tv cv hveq
                  split at h
                  · rename_i hcv
                    split at h
                    · rename_i htv
                      simp at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hHE := ihE e ctx Γ (.refType cap t) ce
                        (Nat.lt_of_lt_of_le (mE_refStore_l e v tAnn) (Nat.le_of_lt_succ hn)) heq
                      rw [hce] at hHE
                      rw [hte] at hHE
                      have hHV := ihE v ctx Γ tv cv
                        (Nat.lt_of_lt_of_le (mE_refStore_r e v tAnn) (Nat.le_of_lt_succ hn)) hveq
                      rw [hcv] at hHV
                      rw [htv] at hHV
                      exact HasType.refStore_type ctx Γ e v cap tAnn hHE hHV hcap
                    · simp at h
                  · simp at h
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | refFree e =>
        simp only [inferTypeC] at h
        split at h
        · rename_i cap t ce heq
          split at h
          · rename_i hce
            split at h
            · rename_i hcap
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have hHE := ihE e ctx Γ (.refType cap t) ce
                (Nat.lt_of_lt_of_le (mE_refFree e) (Nat.le_of_lt_succ hn)) heq
              rw [hce] at hHE
              rw [hcap] at hHE
              exact HasType.refFree_type ctx Γ e t hHE
            · simp at h
          · simp at h
        · simp at h
      | refCast _ _ => simp only [inferTypeC] at h; simp at h
    · intro es ctx Γ τs cout hn h
      cases es with
      | nil =>
        simp only [inferTypesC] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact HasTypeAll.nil ctx Γ
      | cons e es' =>
        simp only [inferTypesC] at h
        split at h
        · rename_i t cmid hin
          split at h
          · rename_i tys cout' hrest
            split at h
            · rename_i hcout
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              rw [hcout] at hrest
              exact HasTypeAll.cons ctx Γ _ e es' t tys
                (ihE e ctx Γ t cmid (Nat.lt_of_lt_of_le (mL_cons_l e es') (Nat.le_of_lt_succ hn)) hin)
                (ihL es' cmid Γ tys cmid
                  (Nat.lt_of_lt_of_le (mL_cons_r e es') (Nat.le_of_lt_succ hn)) hrest)
            · simp at h
          · simp at h
        · simp at h

/-! ## Soundness corollaries -/

/-- **P13 main theorem.** The context-threading checker is sound: every
`some (τ, cout)` answer corresponds to a derivation of the declarative
judgment with exactly the returned output context. -/
theorem inferTypeC_sound (e : Expr) (ctx : LinCtx) (Γ : TypEnv) (τ : Morph.Core.Typ) (cout : LinCtx)
    (h : inferTypeC ctx Γ e = some (τ, cout)) : HasType ctx Γ e τ cout :=
  (sound_mutual (mE e + 1)).1 e ctx Γ τ cout (Nat.lt_succ_self _) h

/-- List-level analogue of `inferTypeC_sound`. -/
theorem inferTypesC_sound (es : List Expr) (ctx : LinCtx) (Γ : TypEnv) (τs : List Morph.Core.Typ)
    (cout : LinCtx) (h : inferTypesC ctx Γ es = some (τs, cout)) :
    HasTypeAll ctx Γ es τs cout :=
  (sound_mutual (mL es + 1)).2 es ctx Γ τs cout (Nat.lt_succ_self _) h

/-- **P13 theorem, type-only projection.** `inferType ctx Γ e = some τ`
implies the judgment derives `HasType ctx Γ e τ cout` for some output
context `cout`. -/
theorem inferType_sound (ctx : LinCtx) (Γ : TypEnv) (e : Expr) (τ : Morph.Core.Typ)
    (h : inferType ctx Γ e = some τ) : ∃ cout, HasType ctx Γ e τ cout := by
  unfold inferType at h
  cases hin : inferTypeC ctx Γ e with
  | none =>
    rw [hin] at h
    simp at h
  | some p =>
    obtain ⟨t, cout⟩ := p
    rw [hin] at h
    simp at h
    rw [h] at hin
    exact ⟨cout, inferTypeC_sound e ctx Γ τ cout hin⟩

/-- List-level projection of `inferType_sound`. -/
theorem inferTypes_sound (ctx : LinCtx) (Γ : TypEnv) (es : List Expr) (τs : List Morph.Core.Typ)
    (h : inferTypes ctx Γ es = some τs) : ∃ cout, HasTypeAll ctx Γ es τs cout := by
  unfold inferTypes at h
  cases hin : inferTypesC ctx Γ es with
  | none =>
    rw [hin] at h
    simp at h
  | some p =>
    obtain ⟨ts, cout⟩ := p
    rw [hin] at h
    simp at h
    rw [h] at hin
    exact ⟨cout, inferTypesC_sound es ctx Γ τs cout hin⟩

/-- `synthType` is definitionally `inferType`, so it is sound too. -/
theorem synthType_sound (ctx : LinCtx) (Γ : TypEnv) (e : Expr) (τ : Morph.Core.Typ)
    (h : Morph.TypeChecker.synthType ctx Γ e = some τ) :
    ∃ cout, HasType ctx Γ e τ cout :=
  inferType_sound ctx Γ e τ h

/-- `checkType` on a lambda checked against a `functionType`: the recursive
call on the body (with the `lam_type` push) succeeds. -/
theorem checkType_lam_fun (k : Nat) (body : Expr) (ctx : LinCtx) (Γ : TypEnv)
    (ps : List Morph.Core.Typ) (rt : Morph.Core.Typ)
    (h : Morph.TypeChecker.checkType ctx Γ (.lam k body) (.functionType ps rt) = true) :
    k = ps.length ∧
      Morph.TypeChecker.checkType (linPushMany ctx ps.reverse) Γ body rt = true := by
  simp only [Morph.TypeChecker.checkType] at h
  split at h
  · rename_i hdec
    exact ⟨hdec, h⟩
  · simp at h

/-- `checkType` on a lambda checked against a `linearFunctionType`: the
recursive call on the body (with the `lam_linear_type` push) succeeds and every
parameter occurs exactly once (`countUses`). -/
theorem checkType_lam_lin (k : Nat) (body : Expr) (ctx : LinCtx) (Γ : TypEnv)
    (ps : List Morph.Core.Typ) (rt : Morph.Core.Typ)
    (h : Morph.TypeChecker.checkType ctx Γ (.lam k body) (.linearFunctionType ps rt) = true) :
    k = ps.length ∧
      Morph.TypeChecker.checkType (linPushMany ctx ps.reverse) Γ body rt = true ∧
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

/-- The bidirectional checker is sound with an idempotence contract:
`checkType ctx Γ e expected = true` implies `HasType ctx Γ e expected ctx`
— in particular the checked expression leaves the linear context unchanged,
which is exactly what `lam_type`/`lam_linear_type` demand of lambda bodies. -/
theorem checkType_sound (n : Nat) :
    ∀ (e : Expr) (ctx : LinCtx) (Γ : TypEnv) (expected : Morph.Core.Typ),
      mE e < n → Morph.TypeChecker.checkType ctx Γ e expected = true →
      HasType ctx Γ e expected ctx := by
  induction n with
  | zero =>
    intro e _ _ _ hn _
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro e ctx Γ expected hn h
    cases heq : e with
    | lam k body =>
      rw [heq] at hn h
      cases heq2 : expected with
      | functionType ps rt =>
        rw [heq2] at h
        obtain ⟨hlen, hb⟩ := checkType_lam_fun k body ctx Γ ps rt h
        exact HasType.lam_type ctx Γ k body ps rt hlen
          (ih body _ Γ rt (by simp only [mE] at hn; omega) hb)
      | linearFunctionType ps rt =>
        rw [heq2] at h
        obtain ⟨hlen, hb, huses⟩ := checkType_lam_lin k body ctx Γ ps rt h
        exact HasType.lam_linear_type ctx Γ k body ps rt hlen
          (ih body _ Γ rt (by simp only [mE] at hn; omega) hb) huses
      | _ =>
        rw [heq2] at h
        simp [Morph.TypeChecker.checkType] at h
    | _ =>
      rw [heq] at h
      simp only [Morph.TypeChecker.checkType] at h
      split at h
      · rename_i t cout hin
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hte, hcc⟩ := h
        have hHas := inferTypeC_sound _ ctx Γ t cout hin
        rw [hte, hcc] at hHas
        exact hHas
      · simp at h

/-- Contract-level corollary of `checkType_sound` without the measure
bookkeeping. -/
theorem checkType_sound_true (ctx : LinCtx) (Γ : TypEnv) (e : Expr) (expected : Morph.Core.Typ)
    (h : Morph.TypeChecker.checkType ctx Γ e expected = true) :
    HasType ctx Γ e expected ctx :=
  checkType_sound (mE e + 1) e ctx Γ expected (Nat.lt_succ_self _) h

/-- `typeCheckBlock` is sound: every expression in the block is typable
(independently) by the judgment. -/
theorem typeCheckBlock_sound (ctx : LinCtx) (Γ : TypEnv) (exprs : List Expr)
    (h : Morph.TypeChecker.typeCheckBlock ctx Γ exprs = true) :
    ∀ e ∈ exprs, ∃ τ cout, HasType ctx Γ e τ cout := by
  intro e he
  have hall : (inferType ctx Γ e).isSome = true :=
    List.all_eq_true.mp h e he
  cases hs : inferType ctx Γ e with
  | none =>
    rw [hs] at hall
    simp at hall
  | some t =>
    obtain ⟨cout, hht⟩ := inferType_sound ctx Γ e t hs
    exact ⟨t, cout, hht⟩

end Morph.Specs.TypeSystem
