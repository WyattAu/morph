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

-- NOTE: bvar_type produces HasType bvs Γ (.bvar n) bvs[n], so any
-- HasType bvs Γ (.bvar n) τ must have τ = bvs[n] with n < bvs.length.
-- We split into two lemmas to avoid dependent indexing issues.
theorem HasType_bvar_has_length (bvs : List Typ) (Γ : TypEnv) (n : Nat) (τ : Typ) :
    HasType bvs Γ (.bvar n) τ → n < bvs.length := by
  intro h
  cases h with
  | bvar_type _ _ _ hLen => exact hLen

theorem HasType_fvar_inv (bvs : List Typ) (Γ : TypEnv) (name : String) (τ : Typ) :
    HasType bvs Γ (.fvar name) τ → lookupTyp Γ name = some τ := by
  intro h; cases h with | fvar_type => assumption

theorem HasType_lit_int_inv (bvs : List Typ) (Γ : TypEnv) (n : Int) (τ : Typ) :
    HasType bvs Γ (.lit (.int n)) τ → τ = .intType ∨ (∃ w, τ = .intWidthType w) := by
  intro h; cases h with
  | lit_int => left; rfl
  | lit_int_width _ _ w _ => right; exact ⟨w, rfl⟩

theorem HasType_lit_bool_inv (bvs : List Typ) (Γ : TypEnv) (b : Bool) (τ : Typ) :
    HasType bvs Γ (.lit (.bool b)) τ → τ = .boolType := by
  intro h; cases h with | lit_bool => rfl

theorem HasType_lit_string_inv (bvs : List Typ) (Γ : TypEnv) (s : String) (τ : Typ) :
    HasType bvs Γ (.lit (.string s)) τ → τ = .stringType := by
  intro h; cases h with | lit_string => rfl

theorem HasType_lit_unit_inv (bvs : List Typ) (Γ : TypEnv) (τ : Typ) :
    HasType bvs Γ (.lit .unit) τ → τ = .unitType := by
  intro h; cases h with | lit_unit => rfl

theorem HasType_lit_pointer_inv (bvs : List Typ) (Γ : TypEnv) (p : Pointer) (τ : Typ) :
    HasType bvs Γ (.lit (.pointer p)) τ → τ = .pointerType := by
  intro h; cases h with | lit_pointer => rfl

theorem HasType_lit_float_inv (bvs : List Typ) (Γ : TypEnv) (f : Float) (τ : Typ) :
    HasType bvs Γ (.lit (.float f)) τ → ∃ w, τ = .floatType w := by
  intro h; cases h with
  | lit_float _ _ w _ => exact ⟨w, rfl⟩

theorem HasType_unop_not_inv (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ) :
    HasType bvs Γ (.unop .not e) τ → τ = .boolType := by
  intro h; cases h with | unop_not => rfl

theorem HasType_unop_notb_inv (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ) :
    HasType bvs Γ (.unop .notb e) τ → τ = .intType := by
  intro h; cases h with | unop_notb => rfl

/-! ## Lift Simplification Lemmas

`liftUnder` is defined by well-founded recursion on a nested inductive type,
so Lean's kernel cannot unfold it definitionally. These lemmas provide
the necessary equalities for use in rewriting.
-/

@[simp] theorem lift_bvar (n k : Nat) : lift k (.bvar n) = .bvar (n + k) := by
  simp [lift, liftUnder]

@[simp] theorem lift_fvar (name : String) (k : Nat) : lift k (.fvar name) = .fvar name := by
  simp [lift, liftUnder]

@[simp] theorem lift_lit (v : Value) (k : Nat) : lift k (.lit v) = .lit v := by
  simp [lift, liftUnder]

@[simp] theorem lift_unop (op : Operator) (e : Expr) (k : Nat) :
    lift k (.unop op e) = .unop op (lift k e) := by
  simp [lift, liftUnder]

@[simp] theorem lift_binop (op : Operator) (e1 e2 : Expr) (k : Nat) :
    lift k (.binop op e1 e2) = .binop op (lift k e1) (lift k e2) := by
  simp [lift, liftUnder]

@[simp] theorem lift_lam (n : Nat) (body : Expr) (k : Nat) :
    lift k (.lam n body) = .lam n (liftUnder n k body) := by
  simp [lift, liftUnder]

@[simp] theorem lift_app (fn : Expr) (args : List Expr) (k : Nat) :
    lift k (.app fn args) = .app (lift k fn) (args.map (lift k)) := by
  simp [lift, liftUnder]

@[simp] theorem lift_let (e1 e2 : Expr) (k : Nat) :
    lift k (.let_ e1 e2) = .let_ (lift k e1) (liftUnder 1 k e2) := by
  simp [lift, liftUnder]

@[simp] theorem lift_if (c t f : Expr) (k : Nat) :
    lift k (.ifThenElse c t f) = .ifThenElse (lift k c) (lift k t) (lift k f) := by
  simp [lift, liftUnder]

@[simp] theorem lift_for (s e : Expr) (body : List Expr) (k : Nat) :
    lift k (.forLoop s e body) = .forLoop (lift k s) (lift k e) (body.map (liftUnder 1 k)) := by
  simp [lift, liftUnder]

@[simp] theorem lift_block (exprs : List Expr) (k : Nat) :
    lift k (.block exprs) = .block (exprs.map (lift k)) := by
  simp [lift, liftUnder]

@[simp] theorem lift_field (e : Expr) (name : String) (k : Nat) :
    lift k (.field_ e name) = .field_ (lift k e) name := by
  simp [lift, liftUnder]

@[simp] theorem lift_pipe (e f : Expr) (k : Nat) :
    lift k (.pipe e f) = .pipe (lift k e) (lift k f) := by
  simp [lift, liftUnder]

@[simp] theorem lift_typeAsc (e : Expr) (τ : Typ) (k : Nat) :
    lift k (.typeAsc e τ) = .typeAsc (lift k e) τ := by
  simp [lift, liftUnder]

@[simp] theorem lift_some (e : Expr) (k : Nat) :
    lift k (.some_ e) = .some_ (lift k e) := by
  simp [lift, liftUnder]

@[simp] theorem lift_none (k : Nat) :
    lift k .none_ = .none_ := by
  simp [lift, liftUnder]

@[simp] theorem lift_ok (e : Expr) (k : Nat) :
    lift k (.ok_ e) = .ok_ (lift k e) := by
  simp [lift, liftUnder]

@[simp] theorem lift_err (e : Expr) (k : Nat) :
  lift k (.err_ e) = .err_ (lift k e) := by
  simp [lift, liftUnder]

@[simp] theorem lift_nullCoalesce (e1 e2 : Expr) (k : Nat) :
  lift k (.nullCoalesce e1 e2) = .nullCoalesce (lift k e1) (lift k e2) := by
  simp [lift, liftUnder]

@[simp] theorem lift_tuple (elems : List Expr) (k : Nat) :
    lift k (.tuple_ elems) = .tuple_ (elems.map (lift k)) := by
  simp [lift, liftUnder]

@[simp] theorem lift_arrayLit (elems : List Expr) (k : Nat) :
    lift k (.arrayLit elems) = .arrayLit (elems.map (lift k)) := by
  simp [lift, liftUnder]

@[simp] theorem lift_arrayIndex (arr idx : Expr) (k : Nat) :
    lift k (.arrayIndex arr idx) = .arrayIndex (lift k arr) (lift k idx) := by
  simp [lift, liftUnder]

@[simp] theorem lift_refCreate (e : Expr) (cap : Capability) (τ : Typ) (k : Nat) :
    lift k (.refCreate e cap τ) = .refCreate (lift k e) cap τ := by
  simp [lift, liftUnder]

@[simp] theorem lift_refLoad (e : Expr) (k : Nat) :
    lift k (.refLoad e) = .refLoad (lift k e) := by
  simp [lift, liftUnder]

@[simp] theorem lift_refStore (e v : Expr) (τ : Typ) (k : Nat) :
    lift k (.refStore e v τ) = .refStore (lift k e) (lift k v) τ := by
  simp [lift, liftUnder]

@[simp] theorem lift_refFree (e : Expr) (k : Nat) :
    lift k (.refFree e) = .refFree (lift k e) := by
  simp [lift, liftUnder]

@[simp] theorem lift_refCast (e : Expr) (cap : Capability) (k : Nat) :
    lift k (.refCast e cap) = .refCast (lift k e) cap := by
  simp [lift, liftUnder]

/-! ## Lift-Zero Identity

`liftUnder bound 0 e = e` for all `bound` and `e`.
This is because lifting by 0 is a no-op: no variable index changes.
Proven by mutual structural recursion since `Expr` is nested inductive.
-/

mutual

theorem liftUnder_zero_eq_list : forall (bound : Nat) (es : List Expr),
    List.map (liftUnder bound 0) es = es
  | _, [] => rfl
  | bound, head :: tail => by
    simp [List.map, liftUnder_zero_eq bound head, liftUnder_zero_eq_list bound tail]

theorem liftUnder_zero_eq_arms : forall (bound : Nat) (arms : List (List String × Expr)),
    liftUnderArms bound 0 arms = arms
  | _, [] => by simp only [liftUnderArms]
  | bound, (vars, body) :: rest => by
    simp only [liftUnderArms, liftUnder_zero_eq (bound + vars.length) body,
               liftUnder_zero_eq_arms bound rest]

theorem liftUnder_zero_eq : forall (bound : Nat) (e : Expr), liftUnder bound 0 e = e
  | bound, .bvar n => by simp [liftUnder]
  | bound, .fvar name => by simp [liftUnder]
  | bound, .lit v => by simp [liftUnder]
  | bound, .unop op e' => by simp [liftUnder, liftUnder_zero_eq bound e']
  | bound, .binop op e1 e2 => by simp [liftUnder, liftUnder_zero_eq bound e1, liftUnder_zero_eq bound e2]
  | bound, .lam n body => by simp [liftUnder, liftUnder_zero_eq (bound + n) body]
  | bound, .app fn args => by
    simp only [liftUnder, liftUnder_zero_eq bound fn, liftUnder_zero_eq_list bound args]
  | bound, .let_ e1 e2 => by simp [liftUnder, liftUnder_zero_eq bound e1, liftUnder_zero_eq (bound + 1) e2]
  | bound, .ifThenElse c t f => by
    simp only [liftUnder, liftUnder_zero_eq bound c, liftUnder_zero_eq bound t, liftUnder_zero_eq bound f]
  | bound, .forLoop s e' body => by
    simp only [liftUnder, liftUnder_zero_eq bound s, liftUnder_zero_eq bound e',
               liftUnder_zero_eq_list (bound + 1) body]
  | bound, .block exprs => by
    simp only [liftUnder, liftUnder_zero_eq_list bound exprs]
  | bound, .field_ e name => by simp [liftUnder, liftUnder_zero_eq bound e]
  | bound, .pipe e f => by simp [liftUnder, liftUnder_zero_eq bound e, liftUnder_zero_eq bound f]
  | bound, .typeAsc e τ => by simp [liftUnder, liftUnder_zero_eq bound e]
  | bound, .some_ e => by simp [liftUnder, liftUnder_zero_eq bound e]
  | bound, .none_ => by simp [liftUnder]
  | bound, .ok_ e => by simp [liftUnder, liftUnder_zero_eq bound e]
  | bound, .err_ e => by simp [liftUnder, liftUnder_zero_eq bound e]
  | bound, .nullCoalesce e1 e2 => by
    simp only [liftUnder, liftUnder_zero_eq bound e1, liftUnder_zero_eq bound e2]
  | bound, .match_ scrut arms => by
    simp only [liftUnder, liftUnder_zero_eq bound scrut, liftUnder_zero_eq_arms bound arms]
   | bound, .tuple_ elems => by simp [liftUnder, liftUnder_zero_eq_list bound elems]
   | bound, .arrayLit elems => by simp [liftUnder, liftUnder_zero_eq_list bound elems]
   | bound, .arrayIndex arr idx => by simp [liftUnder, liftUnder_zero_eq bound arr, liftUnder_zero_eq bound idx]
   | bound, .refCreate e cap τ => by simp [liftUnder, liftUnder_zero_eq bound e]
   | bound, .refLoad e => by simp [liftUnder, liftUnder_zero_eq bound e]
   | bound, .refStore e v τ => by simp [liftUnder, liftUnder_zero_eq bound e, liftUnder_zero_eq bound v]
   | bound, .refFree e => by simp [liftUnder, liftUnder_zero_eq bound e]
   | bound, .refCast e _ => by simp [liftUnder, liftUnder_zero_eq bound e]

end

@[simp] theorem lift_zero_eq (e : Expr) : lift 0 e = e := liftUnder_zero_eq 0 e

/-! ## Lift-Under Composition

Composing two lifts with the same bound adds the lift amounts.
`liftUnder bound k1 (liftUnder bound k2 e) = liftUnder bound (k1 + k2) e`.
-/

mutual

theorem liftUnder_comp_list : forall (bound k1 k2 : Nat) (es : List Expr),
    List.map (liftUnder bound k1) (List.map (liftUnder bound k2) es) =
    List.map (liftUnder bound (k1 + k2)) es
  | _, _, _, [] => rfl
  | bound, k1, k2, head :: tail => by
    simp [List.map, liftUnder_comp bound k1 k2 head, liftUnder_comp_list bound k1 k2 tail]

theorem liftUnder_comp_arms : forall (bound k1 k2 : Nat) (arms : List (List String × Expr)),
    liftUnderArms bound k1 (liftUnderArms bound k2 arms) =
    liftUnderArms bound (k1 + k2) arms
  | _, _, _, [] => by simp only [liftUnderArms]
  | bound, k1, k2, (vars, body) :: rest => by
    simp only [liftUnderArms, liftUnder_comp (bound + vars.length) k1 k2 body,
               liftUnder_comp_arms bound k1 k2 rest]

theorem liftUnder_comp : forall (bound k1 k2 : Nat) (e : Expr),
    liftUnder bound k1 (liftUnder bound k2 e) = liftUnder bound (k1 + k2) e
  | bound, k1, k2, .bvar n => by
    rw [liftUnder.eq_1, liftUnder.eq_1]
    split
    · next h => rw [liftUnder.eq_1]; split <;> (try rfl) <;> omega
    · next h => rw [liftUnder.eq_1]; split <;> (try omega) <;> (next h2 => congr 1; omega)
  | _, _, _, .fvar name => by simp [liftUnder]
  | _, _, _, .lit v => by simp [liftUnder]
  | bound, k1, k2, .unop op e' => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e']
  | bound, k1, k2, .binop op e1 e2 => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e1, liftUnder_comp bound k1 k2 e2]
  | bound, k1, k2, .lam n body => by
    simp [liftUnder, liftUnder_comp (bound + n) k1 k2 body]
  | bound, k1, k2, .app fn args => by
    simp only [liftUnder, liftUnder_comp bound k1 k2 fn, liftUnder_comp_list bound k1 k2 args]
  | bound, k1, k2, .let_ e1 e2 => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e1, liftUnder_comp (bound + 1) k1 k2 e2]
  | bound, k1, k2, .ifThenElse c t f => by
    simp [liftUnder, liftUnder_comp bound k1 k2 c,
          liftUnder_comp bound k1 k2 t, liftUnder_comp bound k1 k2 f]
  | bound, k1, k2, .forLoop s e body => by
    simp only [liftUnder, liftUnder_comp bound k1 k2 s, liftUnder_comp bound k1 k2 e,
               liftUnder_comp_list (bound + 1) k1 k2 body]
  | bound, k1, k2, .block exprs => by
    simp only [liftUnder, liftUnder_comp_list bound k1 k2 exprs]
  | bound, k1, k2, .field_ e name => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e]
  | bound, k1, k2, .pipe e f => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e, liftUnder_comp bound k1 k2 f]
  | bound, k1, k2, .typeAsc e τ => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e]
  | bound, k1, k2, .some_ e => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e]
  | bound, k1, k2, .none_ => by simp [liftUnder]
  | bound, k1, k2, .ok_ e => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e]
  | bound, k1, k2, .err_ e => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e]
  | bound, k1, k2, .nullCoalesce e1 e2 => by
    simp [liftUnder, liftUnder_comp bound k1 k2 e1, liftUnder_comp bound k1 k2 e2]
  | bound, k1, k2, .match_ scrut arms => by
    simp only [liftUnder, liftUnder_comp bound k1 k2 scrut, liftUnder_comp_arms bound k1 k2 arms]
   | bound, k1, k2, .tuple_ elems => by simp [liftUnder, liftUnder_comp_list bound k1 k2 elems]
   | bound, k1, k2, .arrayLit elems => by simp [liftUnder, liftUnder_comp_list bound k1 k2 elems]
   | bound, k1, k2, .arrayIndex arr idx => by simp [liftUnder, liftUnder_comp bound k1 k2 arr, liftUnder_comp bound k1 k2 idx]
   | bound, k1, k2, .refCreate e cap τ => by simp [liftUnder, liftUnder_comp bound k1 k2 e]
   | bound, k1, k2, .refLoad e => by simp [liftUnder, liftUnder_comp bound k1 k2 e]
   | bound, k1, k2, .refStore e v τ => by simp [liftUnder, liftUnder_comp bound k1 k2 e, liftUnder_comp bound k1 k2 v]
   | bound, k1, k2, .refFree e => by simp [liftUnder, liftUnder_comp bound k1 k2 e]
   | bound, k1, k2, .refCast e _ => by simp [liftUnder, liftUnder_comp bound k1 k2 e]

end

theorem lift_comp (k1 k2 : Nat) (e : Expr) :
    lift k1 (lift k2 e) = lift (k1 + k2) e := liftUnder_comp 0 k1 k2 e

/-! ## Occurrence Counting (ADR-014)

`countUses` (defined in `Morph/Syntax.lean`) counts free occurrences of a de
Bruijn index. Lifting preserves counts strictly below the lifting bound and
annihilates counts inside the lifted window. These are the facts that let the
`lam_linear_type` single-use premise survive weakening. -/

mutual

theorem countUses_liftUnder_below : ∀ (bound k i : Nat) (e : Expr), i < bound →
    countUses (liftUnder bound k e) i = countUses e i
  | bound, k, i, .bvar m, h => by
    simp only [liftUnder]
    split
    · rfl
    · next hm =>
      have h1 : ¬ ((m + k) = i) := by omega
      have h2 : ¬ (m = i) := by omega
      simp only [countUses, if_neg h1, if_neg h2]
  | bound, k, i, .fvar _, _ => by simp [liftUnder, countUses]
  | bound, k, i, .lit _, _ => by simp [liftUnder, countUses]
  | bound, k, i, .unop _ e, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .binop _ e1 e2, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i e1 h, countUses_liftUnder_below bound k i e2 h]
  | bound, k, i, .app fn args, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i fn h, countUsesList_liftUnder_below bound k i args h]
  | bound, k, i, .lam m body, h => by
    simp only [liftUnder, countUses]
    exact countUses_liftUnder_below (bound + m) k (i + m) body (by omega)
  | bound, k, i, .let_ a b, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i a h,
        countUses_liftUnder_below (bound + 1) k (i + 1) b (by omega)]
  | bound, k, i, .ifThenElse c t f, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i c h, countUses_liftUnder_below bound k i t h,
        countUses_liftUnder_below bound k i f h]
  | bound, k, i, .forLoop s e body, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i s h, countUses_liftUnder_below bound k i e h,
        countUsesList_liftUnder_below (bound + 1) k (i + 1) body (by omega)]
  | bound, k, i, .block exprs, h => by
    simp only [liftUnder, countUses]
    exact countUsesList_liftUnder_below bound k i exprs h
  | bound, k, i, .match_ scrut arms, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i scrut h,
        countUsesArms_liftUnder_below bound k i arms h]
  | bound, k, i, .field_ e _, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .pipe e f, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i e h, countUses_liftUnder_below bound k i f h]
  | bound, k, i, .typeAsc e _, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .some_ e, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .none_, _ => by simp [liftUnder, countUses]
  | bound, k, i, .ok_ e, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .err_ e, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .nullCoalesce e1 e2, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i e1 h, countUses_liftUnder_below bound k i e2 h]
  | bound, k, i, .tuple_ elems, h => by
    simp only [liftUnder, countUses]
    exact countUsesList_liftUnder_below bound k i elems h
  | bound, k, i, .arrayLit elems, h => by
    simp only [liftUnder, countUses]
    exact countUsesList_liftUnder_below bound k i elems h
  | bound, k, i, .arrayIndex arr idx, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i arr h, countUses_liftUnder_below bound k i idx h]
  | bound, k, i, .refCreate e _ _, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .refLoad e, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .refStore e v _, h => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_below bound k i e h, countUses_liftUnder_below bound k i v h]
  | bound, k, i, .refFree e, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h
  | bound, k, i, .refCast e _, h => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_below bound k i e h

theorem countUsesList_liftUnder_below : ∀ (bound k i : Nat) (es : List Expr), i < bound →
    countUsesList (List.map (liftUnder bound k) es) i = countUsesList es i
  | bound, k, i, [], _ => by simp [countUsesList]
  | bound, k, i, e :: rest, h => by
    simp only [List.map_cons, countUsesList]
    rw [countUses_liftUnder_below bound k i e h, countUsesList_liftUnder_below bound k i rest h]

theorem countUsesArms_liftUnder_below : ∀ (bound k i : Nat) (arms : List (List String × Expr)),
    i < bound →
    countUsesArms i (liftUnderArms bound k arms) = countUsesArms i arms
  | bound, k, i, [], _ => by simp [liftUnderArms, countUsesArms]
  | bound, k, i, (vars, body) :: rest, h => by
    simp only [liftUnderArms, countUsesArms]
    rw [countUses_liftUnder_below (bound + vars.length) k (i + vars.length) body (by omega),
        countUsesArms_liftUnder_below bound k i rest h]

theorem countUses_liftUnder_above : ∀ (bound k i : Nat) (e : Expr), bound ≤ i → i < bound + k →
    countUses (liftUnder bound k e) i = 0
  | bound, k, i, .bvar m, h1, h2 => by
    simp only [liftUnder]
    split
    · next hm =>
      have : ¬ (m = i) := by omega
      simp [countUses, this]
    · next hm =>
      have : ¬ ((m + k) = i) := by omega
      simp [countUses, this]
  | bound, k, i, .fvar _, _, _ => by simp [liftUnder, countUses]
  | bound, k, i, .lit _, _, _ => by simp [liftUnder, countUses]
  | bound, k, i, .unop _ e, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .binop _ e1 e2, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i e1 h1 h2, countUses_liftUnder_above bound k i e2 h1 h2]
  | bound, k, i, .app fn args, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i fn h1 h2,
        countUsesList_liftUnder_above bound k i args h1 h2]
  | bound, k, i, .lam m body, h1, h2 => by
    simp only [liftUnder, countUses]
    exact countUses_liftUnder_above (bound + m) k (i + m) body (by omega) (by omega)
  | bound, k, i, .let_ a b, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i a h1 h2,
        countUses_liftUnder_above (bound + 1) k (i + 1) b (by omega) (by omega)]
  | bound, k, i, .ifThenElse c t f, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i c h1 h2, countUses_liftUnder_above bound k i t h1 h2,
        countUses_liftUnder_above bound k i f h1 h2]
  | bound, k, i, .forLoop s e body, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i s h1 h2, countUses_liftUnder_above bound k i e h1 h2,
        countUsesList_liftUnder_above (bound + 1) k (i + 1) body (by omega) (by omega)]
  | bound, k, i, .block exprs, h1, h2 => by
    simp only [liftUnder, countUses]
    exact countUsesList_liftUnder_above bound k i exprs h1 h2
  | bound, k, i, .match_ scrut arms, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i scrut h1 h2,
        countUsesArms_liftUnder_above bound k i arms h1 h2]
  | bound, k, i, .field_ e _, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .pipe e f, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i e h1 h2, countUses_liftUnder_above bound k i f h1 h2]
  | bound, k, i, .typeAsc e _, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .some_ e, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .none_, _, _ => by simp [liftUnder, countUses]
  | bound, k, i, .ok_ e, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .err_ e, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .nullCoalesce e1 e2, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i e1 h1 h2, countUses_liftUnder_above bound k i e2 h1 h2]
  | bound, k, i, .tuple_ elems, h1, h2 => by
    simp only [liftUnder, countUses]
    exact countUsesList_liftUnder_above bound k i elems h1 h2
  | bound, k, i, .arrayLit elems, h1, h2 => by
    simp only [liftUnder, countUses]
    exact countUsesList_liftUnder_above bound k i elems h1 h2
  | bound, k, i, .arrayIndex arr idx, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i arr h1 h2, countUses_liftUnder_above bound k i idx h1 h2]
  | bound, k, i, .refCreate e _ _, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .refLoad e, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .refStore e v _, h1, h2 => by
    simp only [liftUnder, countUses]
    rw [countUses_liftUnder_above bound k i e h1 h2, countUses_liftUnder_above bound k i v h1 h2]
  | bound, k, i, .refFree e, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2
  | bound, k, i, .refCast e _, h1, h2 => by
    simp only [liftUnder, countUses]; exact countUses_liftUnder_above bound k i e h1 h2

theorem countUsesList_liftUnder_above : ∀ (bound k i : Nat) (es : List Expr),
    bound ≤ i → i < bound + k →
    countUsesList (List.map (liftUnder bound k) es) i = 0
  | bound, k, i, [], _, _ => by simp [countUsesList]
  | bound, k, i, e :: rest, h1, h2 => by
    simp only [List.map_cons, countUsesList]
    rw [countUses_liftUnder_above bound k i e h1 h2,
        countUsesList_liftUnder_above bound k i rest h1 h2]

theorem countUsesArms_liftUnder_above : ∀ (bound k i : Nat) (arms : List (List String × Expr)),
    bound ≤ i → i < bound + k →
    countUsesArms i (liftUnderArms bound k arms) = 0
  | bound, k, i, [], _, _ => by simp [liftUnderArms, countUsesArms]
  | bound, k, i, (vars, body) :: rest, h1, h2 => by
    simp only [liftUnderArms, countUsesArms]
    rw [countUses_liftUnder_above (bound + vars.length) k (i + vars.length) body (by omega) (by omega),
        countUsesArms_liftUnder_above bound k i rest h1 h2]

end

/-! ## Occurrence Counts Under Simultaneous Substitution

`substAll' k vs e` only touches indices `≥ k`; occurrences strictly below `k`
are preserved verbatim, and the substituted values are lifted by `k`, so they
cannot mention indices below `k`. This is what lets the `lam_linear_type`
single-use premise survive substitution (ADR-014). -/

mutual

theorem countUses_substAll'_below : ∀ (k i : Nat) (vs : List Expr) (e : Expr), i < k →
    countUses (substAll' k vs e) i = countUses e i
  | k, i, vs, .bvar m, h => by
    simp only [substAll']
    split
    · rfl
    · next hm =>
      split
      · next hv =>
        have hne : ¬ (m = i) := by omega
        simp only [countUses, if_neg hne]
        exact countUses_liftUnder_above 0 k i _ (by omega) (by omega)
      · next hv =>
        have h1 : ¬ ((m - vs.length) = i) := by omega
        have h2 : ¬ (m = i) := by omega
        simp [countUses, h1, h2]
  | k, i, vs, .fvar _, _ => by simp [substAll', countUses]
  | k, i, vs, .lit _, _ => by simp [substAll', countUses]
  | k, i, vs, .unop _ e, h => by
    simp only [substAll', countUses]
    exact countUses_substAll'_below k i vs e h
  | k, i, vs, .binop _ e1 e2, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs e1 h, countUses_substAll'_below k i vs e2 h]
  | k, i, vs, .app fn args, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs fn h, countUsesList_substAll'_below k i vs args h]
  | k, i, vs, .lam m body, h => by
    simp only [substAll', countUses]
    exact countUses_substAll'_below (k + m) (i + m) vs body (by omega)
  | k, i, vs, .let_ a b, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs a h,
        countUses_substAll'_below (k + 1) (i + 1) vs b (by omega)]
  | k, i, vs, .ifThenElse c t f, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs c h, countUses_substAll'_below k i vs t h,
        countUses_substAll'_below k i vs f h]
  | k, i, vs, .forLoop s e body, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs s h, countUses_substAll'_below k i vs e h,
        countUsesList_substAll'_below (k + 1) (i + 1) vs body (by omega)]
  | k, i, vs, .block exprs, h => by
    simp only [substAll', countUses]
    exact countUsesList_substAll'_below k i vs exprs h
  | k, i, vs, .match_ scrut arms, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs scrut h,
        countUsesArms_substAll'_below k i vs arms h]
  | k, i, vs, .field_ e _, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h
  | k, i, vs, .pipe e f, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs e h, countUses_substAll'_below k i vs f h]
  | k, i, vs, .typeAsc e _, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h
  | k, i, vs, .some_ e, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h
  | k, i, vs, .none_, _ => by simp [substAll', countUses]
  | k, i, vs, .ok_ e, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h
  | k, i, vs, .err_ e, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h
  | k, i, vs, .nullCoalesce e1 e2, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs e1 h, countUses_substAll'_below k i vs e2 h]
  | k, i, vs, .tuple_ elems, h => by
    simp only [substAll', countUses]
    exact countUsesList_substAll'_below k i vs elems h
  | k, i, vs, .arrayLit elems, h => by
    simp only [substAll', countUses]
    exact countUsesList_substAll'_below k i vs elems h
  | k, i, vs, .arrayIndex arr idx, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs arr h, countUses_substAll'_below k i vs idx h]
  | k, i, vs, .refCreate e _ _, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h
  | k, i, vs, .refLoad e, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h
  | k, i, vs, .refStore e v _, h => by
    simp only [substAll', countUses]
    rw [countUses_substAll'_below k i vs e h, countUses_substAll'_below k i vs v h]
  | k, i, vs, .refFree e, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h
  | k, i, vs, .refCast e _, h => by
    simp only [substAll', countUses]; exact countUses_substAll'_below k i vs e h

theorem countUsesList_substAll'_below : ∀ (k i : Nat) (vs : List Expr) (es : List Expr), i < k →
    countUsesList (List.map (substAll' k vs) es) i = countUsesList es i
  | k, i, vs, [], _ => by simp [countUsesList]
  | k, i, vs, e :: rest, h => by
    simp only [List.map_cons, countUsesList]
    rw [countUses_substAll'_below k i vs e h, countUsesList_substAll'_below k i vs rest h]

theorem countUsesArms_substAll'_below : ∀ (k i : Nat) (vs : List Expr)
    (arms : List (List String × Expr)), i < k →
    countUsesArms i (substAllArms k vs arms) = countUsesArms i arms
  | k, i, vs, [], _ => by simp [substAllArms, countUsesArms]
  | k, i, vs, (vars, body) :: rest, h => by
    simp only [substAllArms, countUsesArms]
    rw [countUses_substAll'_below (k + vars.length) (i + vars.length) vs body (by omega),
        countUsesArms_substAll'_below k i vs rest h]

end

/-! ## Single-Substitution via Simultaneous Substitution

`substAll' k [v] e` and `subst' k e v` coincide. -/

mutual

theorem substAll'_singleton : ∀ (k : Nat) (v : Expr) (e : Expr),
    substAll' k [v] e = subst' k e v
  | k, v, .bvar n => by
    simp only [substAll', subst', List.length_cons, List.length_nil]
    split
    · rfl
    · next hm =>
      split
      · next hv =>
        have hnk : n = k := by omega
        subst hnk
        simp
      · next hv =>
        have hnk : ¬ (n = k) := by omega
        simp only [if_neg hnk]
  | k, v, .fvar _ => by simp [substAll', subst']
  | k, v, .lit _ => by simp [substAll', subst']
  | k, v, .unop op e => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .binop op e1 e2 => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v e1, substAll'_singleton k v e2]
  | k, v, .app fn args => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v fn, substAllList_singleton k v args]
  | k, v, .lam n body => by simp only [substAll', subst']; rw [substAll'_singleton (k + n) v body]
  | k, v, .let_ e1 e2 => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v e1, substAll'_singleton (k + 1) v e2]
  | k, v, .ifThenElse c t f => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v c, substAll'_singleton k v t, substAll'_singleton k v f]
  | k, v, .forLoop s e body => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v s, substAll'_singleton k v e, substAllList_singleton (k + 1) v body]
  | k, v, .block exprs => by
    simp only [substAll', subst']
    rw [substAllList_singleton k v exprs]
  | k, v, .match_ scrut arms => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v scrut, substAllArms_singleton k v arms]
  | k, v, .field_ e name => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .pipe e f => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v e, substAll'_singleton k v f]
  | k, v, .typeAsc e τ => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .some_ e => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .none_ => by simp [substAll', subst']
  | k, v, .ok_ e => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .err_ e => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .nullCoalesce e1 e2 => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v e1, substAll'_singleton k v e2]
  | k, v, .tuple_ elems => by simp only [substAll', subst']; rw [substAllList_singleton k v elems]
  | k, v, .arrayLit elems => by simp only [substAll', subst']; rw [substAllList_singleton k v elems]
  | k, v, .arrayIndex arr idx => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v arr, substAll'_singleton k v idx]
  | k, v, .refCreate e cap τ => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .refLoad e => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .refStore e v' τ => by
    simp only [substAll', subst']
    rw [substAll'_singleton k v e, substAll'_singleton k v v']
  | k, v, .refFree e => by simp only [substAll', subst']; rw [substAll'_singleton k v e]
  | k, v, .refCast e _ => by simp only [substAll', subst']; rw [substAll'_singleton k v e]

theorem substAllList_singleton : ∀ (k : Nat) (v : Expr) (es : List Expr),
    List.map (substAll' k [v]) es = List.map (subst' k · v) es
  | k, v, [] => rfl
  | k, v, e :: rest => by
    simp only [List.map_cons]
    rw [substAll'_singleton k v e, substAllList_singleton k v rest]

theorem substAllArms_singleton : ∀ (k : Nat) (v : Expr) (arms : List (List String × Expr)),
    substAllArms k [v] arms = substArms k v arms
  | k, v, [] => by simp [substAllArms, substArms]
  | k, v, (vars, body) :: rest => by
    simp only [substAllArms, substArms]
    rw [substAll'_singleton (k + vars.length) v body, substAllArms_singleton k v rest]

end

/-! ## Weakening (Trivial with de Bruijn)

With de Bruijn indices, weakening is simply prepending a type to `bvs`.
No freshness predicate is needed — bound variables are identified by index,
not by name, so there is no possibility of capture. Since ADR-014 there is no
context consumption at all, so weakening never interacts with obligations; the
`lam_linear_type` case survives because `countUses` is invariant under lifting
below the bound (`countUses_liftUnder_below`).
-/

private theorem nat_sub_lt_of_lt_add (a b c : Nat) (hGE : a ≥ c) (hLT : a < c + b) : a - c < b := by
  have h3 : (a - c) + c = a := Nat.sub_add_cancel hGE
  have h4 : (a - c) + c < b + c := by omega
  exact Nat.lt_of_add_lt_add_right h4

private theorem omega_list_len (as bs : List Typ) (n : Nat) (σ : Typ)
    (h : n < (as ++ bs).length) : n < (as ++ σ :: bs).length := by
  have h1 := @List.length_append Typ as bs
  have h2 := @List.length_append Typ as (σ :: bs)
  have h3 := @List.length_cons Typ σ bs
  have h4 := h2.trans (congrArg (as.length + ·) h3)
  omega

private theorem omega_list_len_succ (as bs : List Typ) (n : Nat) (σ : Typ)
    (h : n < (as ++ bs).length) : n + 1 < (as ++ σ :: bs).length := by
  have h1 := @List.length_append Typ as bs
  have h2 := @List.length_append Typ as (σ :: bs)
  have h3 := @List.length_cons Typ σ bs
  have h4 := h2.trans (congrArg (as.length + ·) h3)
  omega

set_option maxHeartbeats 500000 in
mutual

theorem weakening_at_depth (xs : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (e : Expr) (τ σ : Typ) :
    HasType (xs ++ bvs) Γ e τ → HasType (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) τ := by
  intro h
  cases h with
  | bvar_type _ _ n hLen =>
    simp only [liftUnder]
    split
    · rename_i hNlt
      have hLen2 := omega_list_len xs bvs n σ hLen
      have hBT := HasType.bvar_type (xs ++ σ :: bvs) Γ n hLen2
      have hEq := (@List.getElem_append_left Typ n xs (σ :: bvs) hNlt hLen2).trans
                 (@List.getElem_append_left Typ n xs bvs hNlt hLen).symm
      exact Eq.subst (motive := fun t => HasType (xs ++ σ :: bvs) Γ (.bvar n) t) hEq hBT
    · rename_i hNge
      have hLen2 := omega_list_len_succ xs bvs n σ hLen
      have hNge' : n ≥ xs.length := Nat.ge_of_not_lt hNge
      have hLIdx : n - xs.length < bvs.length := by
        have h1 := @List.length_append Typ xs bvs
        exact nat_sub_lt_of_lt_add n bvs.length xs.length hNge' (by omega)
      have hRIdx : (n - xs.length) + 1 < (σ :: bvs).length := by
        have h1 := @List.length_append Typ xs bvs
        have h2 := @List.length_cons Typ σ bvs
        omega
      have hBT := HasType.bvar_type (xs ++ σ :: bvs) Γ (n + 1) hLen2
      have h1 := @List.getElem_append_right Typ xs (σ :: bvs) (n + 1) (by omega) hLen2
      have h2 := @List.getElem_append_right Typ xs bvs n hNge' hLen
      have h3 := List.getElem_cons_succ σ bvs (n - xs.length) hRIdx
      have h4 : n + 1 - xs.length = (n - xs.length) + 1 := by omega
      have hBT1 := Eq.subst (motive := fun t => HasType (xs ++ σ :: bvs) Γ (.bvar (n + 1)) t) h1 hBT
      have h3' : (σ :: bvs)[n + 1 - xs.length] = bvs[n - xs.length] := by
        simp only [h4]; exact h3
      have hBT2 := Eq.subst (motive := fun t => HasType (xs ++ σ :: bvs) Γ (.bvar (n + 1)) t) h3' hBT1
      exact Eq.subst (motive := fun t => HasType (xs ++ σ :: bvs) Γ (.bvar (n + 1)) t) h2.symm hBT2
  | fvar_type _ _ name τ hLookup =>
    simp only [liftUnder]
    exact HasType.fvar_type (xs ++ σ :: bvs) Γ name τ hLookup
  | lit_int _ _ n => simp only [liftUnder]; exact HasType.lit_int (xs ++ σ :: bvs) Γ n
  | lit_bool _ _ b => simp only [liftUnder]; exact HasType.lit_bool (xs ++ σ :: bvs) Γ b
  | lit_string _ _ s => simp only [liftUnder]; exact HasType.lit_string (xs ++ σ :: bvs) Γ s
  | lit_unit _ _ => simp only [liftUnder]; exact HasType.lit_unit (xs ++ σ :: bvs) Γ
  | lit_pointer _ _ p => simp only [liftUnder]; exact HasType.lit_pointer (xs ++ σ :: bvs) Γ p
  | unop_not _ _ e' hE' =>
    simp only [liftUnder]
    exact HasType.unop_not (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e')
      (weakening_at_depth xs bvs Γ e' .boolType σ hE')
  | unop_notb _ _ e' hE' =>
    simp only [liftUnder]
    exact HasType.unop_notb (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e')
      (weakening_at_depth xs bvs Γ e' .intType σ hE')
  | binop_arith _ _ op e1 e2 hArith hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_arith (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hArith
      (weakening_at_depth xs bvs Γ e1 .intType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .intType σ hE2)
  | binop_comp _ _ op e1 e2 hComp hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_comp (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hComp
      (weakening_at_depth xs bvs Γ e1 .intType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .intType σ hE2)
  | binop_logic _ _ op e1 e2 hLogic hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_logic (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hLogic
      (weakening_at_depth xs bvs Γ e1 .boolType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .boolType σ hE2)
  | binop_bitwise _ _ op e1 e2 hBit hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_bitwise (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hBit
      (weakening_at_depth xs bvs Γ e1 .intType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .intType σ hE2)
  | binop_ptr_arith _ _ op e1 e2 hPtr hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_arith (xs ++ σ :: bvs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hPtr
      (weakening_at_depth xs bvs Γ e1 .pointerType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .intType σ hE2)
  | binop_ptr_load _ _ e1 e2 hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_load (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2)
      (weakening_at_depth xs bvs Γ e1 .pointerType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .unitType σ hE2)
  | binop_ptr_store _ _ e1 e2 hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_store (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2)
      (weakening_at_depth xs bvs Γ e1 .pointerType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .intType σ hE2)
  | binop_string_concat _ _ op e1 e2 hOp hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_string_concat (xs ++ σ :: bvs) Γ op
      (liftUnder xs.length 1 e1) (liftUnder xs.length 1 e2)
      hOp
      (weakening_at_depth xs bvs Γ e1 .stringType σ hE1)
      (weakening_at_depth xs bvs Γ e2 .stringType σ hE2)
  | lam_type _ _ n body paramTys retTy hLen hBody =>
    simp only [liftUnder, liftUnder]
    have hLenEq : (paramTys.reverse ++ xs).length = n + xs.length := by
      have h1 := @List.length_append Typ (paramTys.reverse) xs
      have h2 := @List.length_reverse Typ paramTys
      rw [h1, h2]; omega
    have hBody' := weakening_at_depth (paramTys.reverse ++ xs) bvs Γ body retTy σ
      (by rw [← List.append_assoc] at hBody; exact hBody)
    rw [hLenEq, Nat.add_comm] at hBody'
    exact HasType.lam_type (xs ++ σ :: bvs) Γ n (liftUnder (xs.length + n) 1 body) paramTys retTy hLen
      (Eq.subst (motive := fun ctx => HasType ctx Γ (liftUnder (xs.length + n) 1 body) retTy)
        (show paramTys.reverse ++ xs ++ σ :: bvs = paramTys.reverse ++ (xs ++ σ :: bvs) from
          by exact @List.append_assoc Typ (paramTys.reverse) xs (σ :: bvs)) hBody')
  | lam_linear_type _ _ n body paramTys retTy hLen hBody hCount =>
    subst hLen
    simp only [liftUnder]
    have hLenEq : (paramTys.reverse ++ xs).length = paramTys.length + xs.length := by
      have h1 := @List.length_append Typ (paramTys.reverse) xs
      have h2 := @List.length_reverse Typ paramTys
      rw [h1, h2]
    have hBody' := weakening_at_depth (paramTys.reverse ++ xs) bvs Γ body retTy σ
      (by rw [← List.append_assoc] at hBody; exact hBody)
    rw [hLenEq, Nat.add_comm] at hBody'
    have hCount' : ∀ i, i < paramTys.length →
        countUses (liftUnder (xs.length + paramTys.length) 1 body) i = 1 := by
      intro i hi
      rw [countUses_liftUnder_below _ 1 i body (by omega)]
      exact hCount i hi
    exact HasType.lam_linear_type (xs ++ σ :: bvs) Γ paramTys.length
      (liftUnder (xs.length + paramTys.length) 1 body) paramTys retTy rfl
      (Eq.subst (motive := fun ctx => HasType ctx Γ (liftUnder (xs.length + paramTys.length) 1 body) retTy)
        (show paramTys.reverse ++ xs ++ σ :: bvs = paramTys.reverse ++ (xs ++ σ :: bvs) from
          by exact @List.append_assoc Typ (paramTys.reverse) xs (σ :: bvs)) hBody')
      hCount'
  | app_type _ _ fn args τs τ hFn hArgs =>
    simp only [liftUnder]
    exact HasType.app_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 fn)
      (List.map (liftUnder xs.length 1) args) τs τ
      (weakening_at_depth xs bvs Γ fn (.functionType τs τ) σ hFn)
      (weakening_at_depth_all xs bvs Γ args τs σ hArgs)
  | app_linear_type _ _ fn args τs τ hFn hArgs =>
    simp only [liftUnder]
    exact HasType.app_linear_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 fn)
      (List.map (liftUnder xs.length 1) args) τs τ
      (weakening_at_depth xs bvs Γ fn (.linearFunctionType τs τ) σ hFn)
      (weakening_at_depth_all xs bvs Γ args τs σ hArgs)
  | let_type _ _ e1 e2 τ1 _ hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.let_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e1)
      (liftUnder (xs.length + 1) 1 e2) τ1 τ
      (weakening_at_depth xs bvs Γ e1 τ1 σ hE1)
      (weakening_at_depth (τ1 :: xs) bvs Γ e2 τ σ hE2)
  | if_type _ _ c t f τ hC hT hF =>
    simp only [liftUnder]
    exact HasType.if_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 c)
      (liftUnder xs.length 1 t) (liftUnder xs.length 1 f) τ
      (weakening_at_depth xs bvs Γ c .boolType σ hC)
      (weakening_at_depth xs bvs Γ t τ σ hT)
      (weakening_at_depth xs bvs Γ f τ σ hF)
  | for_type _ _ s e body hS hE hBody =>
    simp only [liftUnder, liftUnder]
    exact HasType.for_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 s)
      (liftUnder xs.length 1 e) (List.map (liftUnder (xs.length + 1) 1) body)
      (weakening_at_depth xs bvs Γ s .intType σ hS)
      (weakening_at_depth xs bvs Γ e .intType σ hE)
      (weakening_at_depth_all (.intType :: xs) bvs Γ body [.unitType] σ hBody)
  | block_type _ _ exprs τs τ hExprs =>
    simp only [liftUnder]
    exact HasType.block_type (xs ++ σ :: bvs) Γ (List.map (liftUnder xs.length 1) exprs) τs τ
      (weakening_at_depth_all xs bvs Γ exprs (τs ++ [τ]) σ hExprs)
  | lit_float _ _ w f => simp only [liftUnder]; exact HasType.lit_float (xs ++ σ :: bvs) Γ w f
  | lit_int_width _ _ w n => simp only [liftUnder]; exact HasType.lit_int_width (xs ++ σ :: bvs) Γ w n
  | lit_some _ _ v τ => simp only [liftUnder]; exact HasType.lit_some (xs ++ σ :: bvs) Γ v τ
  | lit_none _ _ τ => simp only [liftUnder]; exact HasType.lit_none (xs ++ σ :: bvs) Γ τ
  | lit_ok _ _ v τ_ok τ_err => simp only [liftUnder]; exact HasType.lit_ok (xs ++ σ :: bvs) Γ v τ_ok τ_err
  | lit_err _ _ v τ_err τ_ok => simp only [liftUnder]; exact HasType.lit_err (xs ++ σ :: bvs) Γ v τ_err τ_ok
  | pipe_type _ _ e f τ_arg τ hE hF =>
    simp only [liftUnder]
    exact HasType.pipe_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) (liftUnder xs.length 1 f) τ_arg τ
      (weakening_at_depth xs bvs Γ e τ_arg σ hE)
      (weakening_at_depth xs bvs Γ f (.functionType [τ_arg] τ) σ hF)
  | typeAsc_type _ _ e τ hE =>
    simp only [liftUnder]
    exact HasType.typeAsc_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) τ
      (weakening_at_depth xs bvs Γ e τ σ hE)
  | some_type _ _ e τ_inner hE =>
    simp only [liftUnder]
    exact HasType.some_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) τ_inner
      (weakening_at_depth xs bvs Γ e τ_inner σ hE)
  | none_type _ _ τ => simp only [liftUnder]; exact HasType.none_type (xs ++ σ :: bvs) Γ τ
  | ok_type _ _ e τ_ok τ_err hE =>
    simp only [liftUnder]
    exact HasType.ok_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) τ_ok τ_err
      (weakening_at_depth xs bvs Γ e τ_ok σ hE)
  | err_type _ _ e τ_err τ_ok hE =>
    simp only [liftUnder]
    exact HasType.err_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) τ_err τ_ok
      (weakening_at_depth xs bvs Γ e τ_err σ hE)
  | null_coalesce_type _ _ e1 e2 τ hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.null_coalesce_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) τ
      (weakening_at_depth xs bvs Γ e1 (.optionType τ) σ hE1)
      (weakening_at_depth xs bvs Γ e2 (.optionType τ) σ hE2)
   | tuple_type _ _ elems tys hTys =>
     simp only [liftUnder]
     exact HasType.tuple_type (xs ++ σ :: bvs) Γ (elems.map (liftUnder xs.length 1)) tys
       (weakening_at_depth_all xs bvs Γ elems tys σ hTys)
   | field_access_type _ _ e fname sname fields τ hE hField =>
     simp only [liftUnder]
     exact HasType.field_access_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) fname sname fields τ
       (weakening_at_depth xs bvs Γ e (.structType sname fields) σ hE)
       hField
   | match_type _ _ scrut arms _ _ hScrut hArms =>
      simp only [liftUnder]
      exact HasType.match_type _ _ (liftUnder xs.length 1 scrut) (liftUnderArms xs.length 1 arms) _ _
        (weakening_at_depth xs bvs Γ scrut _ σ hScrut)
        (ArmsTyped_weakening_at_depth xs σ hArms)
   | arrayLit_type _ _ elems τ n hElems hLen hn =>
     simp only [liftUnder]
     have hLen' : n = (List.map (liftUnder xs.length 1) elems).length := by
       rw [List.length_map]; exact hLen
     exact HasType.arrayLit_type (xs ++ σ :: bvs) Γ (elems.map (liftUnder xs.length 1)) τ n
       (weakening_at_depth_all xs bvs Γ elems (List.replicate n τ) σ hElems) hLen' hn
   | arrayIndex_type _ _ arr idx τ n hArr hIdx =>
     simp only [liftUnder]
     exact HasType.arrayIndex_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 arr)
       (liftUnder xs.length 1 idx) τ n
       (weakening_at_depth xs bvs Γ arr (.arrayType τ n) σ hArr)
       (weakening_at_depth xs bvs Γ idx .intType σ hIdx)
   | refCreate_type _ _ e cap τ hE =>
     simp only [liftUnder]
     exact HasType.refCreate_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) cap τ
       (weakening_at_depth xs bvs Γ e τ σ hE)
   | refLoad_type _ _ e cap τ hE =>
     simp only [liftUnder]
     exact HasType.refLoad_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) cap τ
       (weakening_at_depth xs bvs Γ e (.refType cap τ) σ hE)
   | refStore_type _ _ e v cap τ hE hV hCap =>
     simp only [liftUnder]
     exact HasType.refStore_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e)
       (liftUnder xs.length 1 v) cap τ
       (weakening_at_depth xs bvs Γ e (.refType cap τ) σ hE)
       (weakening_at_depth xs bvs Γ v τ σ hV)
       hCap
   | refFree_type _ _ e τ hE =>
     simp only [liftUnder]
     exact HasType.refFree_type (xs ++ σ :: bvs) Γ (liftUnder xs.length 1 e) τ
       (weakening_at_depth xs bvs Γ e (.refType .iso τ) σ hE)

theorem ArmsTyped_weakening_at_depth (xs : List Typ) (σ : Typ)
    {bvs : List Typ} {Γ : TypEnv} {τ_scrut : Typ}
    {arms : List (List String × Expr)} {τ_result : Typ}
    (h : ArmsTyped (xs ++ bvs) Γ τ_scrut arms τ_result) :
    ArmsTyped (xs ++ σ :: bvs) Γ τ_scrut (liftUnderArms xs.length 1 arms) τ_result := by
  cases h with
  | nil => simp only [liftUnderArms]; constructor
  | cons bvs Γ vars body rest τ_scrut τ_result hBody hRest =>
    simp only [liftUnderArms]
    constructor
    · have hBody' := weakening_at_depth (List.replicate vars.length τ_scrut ++ xs) bvs Γ body τ_result σ
        (by show HasType ((List.replicate vars.length τ_scrut ++ xs) ++ bvs) Γ body τ_result
            rw [List.append_assoc]; exact hBody)
      simp only [List.length_append, List.length_replicate] at hBody'
      rw [Nat.add_comm] at hBody'
      show HasType (List.replicate vars.length τ_scrut ++ (xs ++ σ :: bvs)) Γ
          (liftUnder (xs.length + vars.length) 1 body) τ_result
      rw [← List.append_assoc]; exact hBody'
    · exact ArmsTyped_weakening_at_depth xs σ hRest

 theorem weakening_at_depth_all (xs : List Typ) (bvs : List Typ) (Γ : TypEnv)
    (es : List Expr) (τs : List Typ) (σ : Typ)
    (h : HasTypeAll (xs ++ bvs) Γ es τs) :
    HasTypeAll (xs ++ σ :: bvs) Γ (es.map (liftUnder xs.length 1)) τs := by
  cases h with
  | nil _ _ => exact HasTypeAll.nil _ _
  | cons _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _
      (weakening_at_depth xs bvs Γ e τ σ hE)
      (weakening_at_depth_all xs bvs Γ es' τs' σ hRest)

end

/-! ## Multi-Type Weakening at Depth

Weaken by prepending multiple types (`xs`) after a prefix in the context.
`HasType (pfx ++ bvs) Γ e τ → HasType (pfx ++ xs ++ bvs) Γ (liftUnder pfx.length xs.length e) τ`
Uses `weakening_at_depth` iterated `xs.length` times, with `liftUnder_comp` to compose lifts.
-/

theorem weaken_many_at_depth (pfx xs bvs : List Typ) (Γ : TypEnv)
    (e : Expr) (τ : Typ)
    (hE : HasType (pfx ++ bvs) Γ e τ)
    : HasType (pfx ++ xs ++ bvs) Γ (liftUnder pfx.length xs.length e) τ := by
  induction xs generalizing bvs with
  | nil =>
    simp [List.length_nil]
    rw [liftUnder_zero_eq]
    exact hE
  | cons σ xs' ih =>
    have hInner := ih bvs hE
    simp only [List.length_cons]
    have hAssoc : (pfx ++ xs') ++ bvs = pfx ++ (xs' ++ bvs) := List.append_assoc pfx xs' bvs
    have hInner' := hAssoc ▸ hInner
    have hStep := weakening_at_depth pfx (xs' ++ bvs) Γ
      (liftUnder pfx.length xs'.length e) τ σ hInner'
    rw [liftUnder_comp] at hStep
    have hEq : (pfx ++ σ :: xs') ++ bvs = pfx ++ σ :: (xs' ++ bvs) := by
      simp [List.append_assoc, List.cons_append]
    have hResult := hEq.symm ▸ hStep
    rw [Nat.add_comm 1] at hResult
    exact hResult

/-! ## ArmsTyped Weakening (simple) -/

theorem ArmsTyped_weakening (σ : Typ)
    {bvs : List Typ} {Γ : TypEnv} {τ_scrut : Typ}
    {arms : List (List String × Expr)} {τ_result : Typ}
    (h : ArmsTyped bvs Γ τ_scrut arms τ_result) :
    ArmsTyped (σ :: bvs) Γ τ_scrut (liftUnderArms 0 1 arms) τ_result := by
  have h := ArmsTyped_weakening_at_depth [] σ h
  simp only [List.nil_append, List.length_nil] at h
  exact h

mutual

theorem weakening (bvs : List Typ) (Γ : TypEnv) (e : Expr) (τ : Typ) (σ : Typ) :
    HasType bvs Γ e τ → HasType (σ :: bvs) Γ (lift 1 e) τ := by
  intro h
  match h with
  | HasType.bvar_type bvs Γ n h =>
    have hLen' : n + 1 < (σ :: bvs).length := by simp; omega
    rw [lift_bvar]
    have : (σ :: bvs)[n + 1]'hLen' = bvs[n]'h := by
      exact List.getElem_cons_succ σ bvs n hLen'
    exact this ▸ HasType.bvar_type (σ :: bvs) Γ (n + 1) hLen'
  | HasType.fvar_type bvs Γ name τ hLookup =>
    rw [lift_fvar]
    exact HasType.fvar_type (σ :: bvs) Γ name τ hLookup
  | HasType.lit_int bvs Γ n =>
    rw [lift_lit]
    exact HasType.lit_int (σ :: bvs) Γ n
  | HasType.lit_bool bvs Γ b =>
    rw [lift_lit]
    exact HasType.lit_bool (σ :: bvs) Γ b
  | HasType.lit_string bvs Γ s =>
    rw [lift_lit]
    exact HasType.lit_string (σ :: bvs) Γ s
  | HasType.lit_unit bvs Γ =>
    rw [lift_lit]
    exact HasType.lit_unit (σ :: bvs) Γ
  | HasType.lit_pointer bvs Γ p =>
    rw [lift_lit]
    exact HasType.lit_pointer (σ :: bvs) Γ p
  | HasType.unop_not bvs Γ e hE =>
    rw [lift_unop]
    exact HasType.unop_not (σ :: bvs) Γ (lift 1 e) (weakening _ _ _ _ σ hE)
  | HasType.unop_notb bvs Γ e hE =>
    rw [lift_unop]
    exact HasType.unop_notb (σ :: bvs) Γ (lift 1 e) (weakening _ _ _ _ σ hE)
  | HasType.binop_arith bvs Γ op e1 e2 hArith hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_arith (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hArith
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_comp bvs Γ op e1 e2 hComp hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_comp (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hComp
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_logic bvs Γ op e1 e2 hLogic hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_logic (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hLogic
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_bitwise bvs Γ op e1 e2 hBit hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_bitwise (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hBit
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_ptr_arith bvs Γ op e1 e2 hPtr hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_ptr_arith (σ :: bvs) Γ op (lift 1 e1) (lift 1 e2) hPtr
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_ptr_load bvs Γ e1 e2 hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_ptr_load (σ :: bvs) Γ (lift 1 e1) (lift 1 e2)
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_ptr_store bvs Γ e1 e2 hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_ptr_store (σ :: bvs) Γ (lift 1 e1) (lift 1 e2)
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_string_concat bvs Γ op e1 e2 hOp hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_string_concat (σ :: bvs) Γ op
      (lift 1 e1) (lift 1 e2)
      hOp
      (weakening _ _ _ _ σ hE1)
      (weakening _ _ _ _ σ hE2)
  | HasType.lam_type bvs Γ n body paramTys retTy hLen hBody =>
    rw [lift_lam]
    have hLenEq1 := @List.length_reverse Typ paramTys
    have hLenEq2 : paramTys.reverse.length = n := hLenEq1.trans hLen.symm
    have hBody' := weakening_at_depth paramTys.reverse bvs Γ body retTy σ hBody
    exact HasType.lam_type (σ :: bvs) Γ n (liftUnder n 1 body) paramTys retTy hLen
      (Eq.subst (motive := fun i => HasType (paramTys.reverse ++ σ :: bvs) Γ (liftUnder i 1 body) retTy) hLenEq2 hBody')
  | HasType.lam_linear_type bvs Γ n body paramTys retTy hLen hBody hCount =>
    subst hLen
    rw [lift_lam]
    have hLenEq1 := @List.length_reverse Typ paramTys
    have hBody' := weakening_at_depth paramTys.reverse bvs Γ body retTy σ hBody
    have hCount' : ∀ i, i < paramTys.length → countUses (liftUnder paramTys.length 1 body) i = 1 := by
      intro i hi
      rw [countUses_liftUnder_below _ 1 i body (by omega)]
      exact hCount i hi
    exact HasType.lam_linear_type (σ :: bvs) Γ paramTys.length
      (liftUnder paramTys.length 1 body) paramTys retTy rfl
      (Eq.subst (motive := fun i => HasType (paramTys.reverse ++ σ :: bvs) Γ (liftUnder i 1 body) retTy)
        hLenEq1 hBody') hCount'
  | HasType.app_type bvs Γ fn args τs τ hFn hArgs =>
    rw [lift_app]
    exact HasType.app_type (σ :: bvs) Γ (lift 1 fn) (List.map (lift 1) args) τs τ
      (weakening _ _ _ _ σ hFn) (weakening_all _ _ _ _ σ hArgs)
  | HasType.app_linear_type bvs Γ fn args τs τ hFn hArgs =>
    rw [lift_app]
    exact HasType.app_linear_type (σ :: bvs) Γ (lift 1 fn) (List.map (lift 1) args) τs τ
      (weakening _ _ _ _ σ hFn) (weakening_all _ _ _ _ σ hArgs)
  | HasType.let_type bvs Γ e1 e2 τ1 τ2 hE1 hE2 =>
    rw [lift_let]
    exact HasType.let_type (σ :: bvs) Γ (lift 1 e1) (liftUnder 1 1 e2) τ1 τ2
      (weakening _ _ _ _ σ hE1) (weakening_at_depth [τ1] bvs Γ e2 τ2 σ hE2)
  | HasType.if_type bvs Γ c t f τ hC hT hF =>
    rw [lift_if]
    exact HasType.if_type (σ :: bvs) Γ (lift 1 c) (lift 1 t) (lift 1 f) τ
      (weakening _ _ _ _ σ hC) (weakening _ _ _ _ σ hT) (weakening _ _ _ _ σ hF)
  | HasType.for_type bvs Γ s e body hS hE hBody =>
    rw [lift_for]
    exact HasType.for_type (σ :: bvs) Γ (lift 1 s) (lift 1 e) (body.map (liftUnder 1 1))
      (weakening _ _ _ _ σ hS) (weakening _ _ _ _ σ hE)
      (weakening_at_depth_all [.intType] bvs Γ body [.unitType] σ hBody)
  | HasType.block_type bvs Γ exprs τs τ hExprs =>
    rw [lift_block]
    exact HasType.block_type (σ :: bvs) Γ (List.map (lift 1) exprs) τs τ
      (weakening_all _ _ _ _ σ hExprs)
  | HasType.lit_float bvs Γ w f =>
    rw [lift_lit]
    exact HasType.lit_float (σ :: bvs) Γ w f
  | HasType.lit_int_width bvs Γ w n =>
    rw [lift_lit]
    exact HasType.lit_int_width (σ :: bvs) Γ w n
  | HasType.lit_some bvs Γ v τ =>
    rw [lift_lit]
    exact HasType.lit_some (σ :: bvs) Γ v τ
  | HasType.lit_none bvs Γ τ =>
    rw [lift_lit]
    exact HasType.lit_none (σ :: bvs) Γ τ
  | HasType.lit_ok bvs Γ v τ_ok τ_err =>
    rw [lift_lit]
    exact HasType.lit_ok (σ :: bvs) Γ v τ_ok τ_err
   | HasType.lit_err bvs Γ v τ_err τ_ok =>
     rw [lift_lit]
     exact HasType.lit_err (σ :: bvs) Γ v τ_err τ_ok
   | HasType.pipe_type bvs Γ e f τ_arg τ hE hF =>
    rw [lift_pipe]
    exact HasType.pipe_type (σ :: bvs) Γ (lift 1 e) (lift 1 f) τ_arg τ
      (weakening _ _ _ _ σ hE) (weakening _ _ _ _ σ hF)
  | HasType.typeAsc_type bvs Γ e τ hE =>
    rw [lift_typeAsc]
    exact HasType.typeAsc_type (σ :: bvs) Γ (lift 1 e) τ (weakening _ _ _ _ σ hE)
  | HasType.some_type bvs Γ e τ_inner hE =>
    rw [lift_some]
    exact HasType.some_type (σ :: bvs) Γ (lift 1 e) τ_inner (weakening _ _ _ _ σ hE)
  | HasType.none_type bvs Γ τ =>
    rw [lift_none]
    exact HasType.none_type (σ :: bvs) Γ τ
  | HasType.ok_type bvs Γ e τ_ok τ_err hE =>
    rw [lift_ok]
    exact HasType.ok_type (σ :: bvs) Γ (lift 1 e) τ_ok τ_err (weakening _ _ _ _ σ hE)
  | HasType.err_type bvs Γ e τ_err τ_ok hE =>
    rw [lift_err]
    exact HasType.err_type (σ :: bvs) Γ (lift 1 e) τ_err τ_ok (weakening _ _ _ _ σ hE)
  | HasType.null_coalesce_type bvs Γ e1 e2 τ hE1 hE2 =>
    rw [lift_nullCoalesce]
    exact HasType.null_coalesce_type (σ :: bvs) Γ (lift 1 e1) (lift 1 e2) τ
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
   | HasType.tuple_type bvs Γ elems tys hTys =>
     rw [lift_tuple]
     exact HasType.tuple_type (σ :: bvs) Γ (elems.map (lift 1)) tys
       (weakening_all _ _ _ _ σ hTys)
   | HasType.field_access_type bvs Γ e fname sname fields τ hE hField =>
     rw [lift_field]
     exact HasType.field_access_type (σ :: bvs) Γ (lift 1 e) fname sname fields τ
       (weakening _ _ _ _ σ hE) hField
   | HasType.match_type bvs Γ scrut arms τ_scrut τ_result hScrut hArms =>
      simp only [liftUnder]
      exact HasType.match_type (σ :: bvs) Γ (lift 1 scrut) (liftUnderArms 0 1 arms) τ_scrut τ_result
        (weakening _ _ _ _ σ hScrut)
        (ArmsTyped_weakening σ hArms)
   | HasType.arrayLit_type bvs Γ elems τ n hElems hLen hn =>
     rw [lift_arrayLit]
     have hLen' : n = (List.map (lift 1) elems).length := by
       rw [List.length_map]; exact hLen
     exact HasType.arrayLit_type (σ :: bvs) Γ (elems.map (lift 1)) τ n
       (weakening_all _ _ _ _ σ hElems) hLen' hn
   | HasType.arrayIndex_type bvs Γ arr idx τ n hArr hIdx =>
     rw [lift_arrayIndex]
     exact HasType.arrayIndex_type (σ :: bvs) Γ (lift 1 arr) (lift 1 idx) τ n
       (weakening _ _ _ _ σ hArr) (weakening _ _ _ _ σ hIdx)
   | HasType.refCreate_type bvs Γ e cap τ hE =>
     rw [lift_refCreate]
     exact HasType.refCreate_type (σ :: bvs) Γ (lift 1 e) cap τ
       (weakening _ _ _ _ σ hE)
   | HasType.refLoad_type bvs Γ e cap τ hE =>
     rw [lift_refLoad]
     exact HasType.refLoad_type (σ :: bvs) Γ (lift 1 e) cap τ
       (weakening _ _ _ _ σ hE)
   | HasType.refStore_type bvs Γ e v cap τ hE hV hCap =>
     rw [lift_refStore]
     exact HasType.refStore_type (σ :: bvs) Γ (lift 1 e) (lift 1 v) cap τ
       (weakening _ _ _ _ σ hE) (weakening _ _ _ _ σ hV) hCap
   | HasType.refFree_type bvs Γ e τ hE =>
     rw [lift_refFree]
     exact HasType.refFree_type (σ :: bvs) Γ (lift 1 e) τ
       (weakening _ _ _ _ σ hE)

theorem weakening_all (bvs : List Typ) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (σ : Typ) (h : HasTypeAll bvs Γ es τs) : HasTypeAll (σ :: bvs) Γ (es.map (lift 1)) τs := by
  match h with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _
      (weakening _ _ _ _ σ hE)
      (weakening_all _ _ _ _ σ hRest)

end

/-!
## HasTypeAll Append

Append two HasTypeAll proofs.
-/

theorem HasTypeAll_append {bvs : List Typ} {Γ : TypEnv} {es₁ es₂ : List Expr} {τs₁ τs₂ : List Typ}
    (h₁ : HasTypeAll bvs Γ es₁ τs₁) (h₂ : HasTypeAll bvs Γ es₂ τs₂) :
    HasTypeAll bvs Γ (es₁ ++ es₂) (τs₁ ++ τs₂) := by
  match h₁ with
  | HasTypeAll.nil _ _ => exact h₂
  | HasTypeAll.cons _ _ e es τ τs hE hRest =>
    exact HasTypeAll.cons _ _ e (es ++ es₂) τ (τs ++ τs₂) hE (HasTypeAll_append hRest h₂)

/-!
## HasTypeAll Reverse

Reversing both the expression list and the type list preserves HasTypeAll.
-/

theorem HasTypeAll_reverse (bvs : List Typ) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (h : HasTypeAll bvs Γ es τs) : HasTypeAll bvs Γ es.reverse τs.reverse := by
  match h with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ e es' τ τs' hE hRest =>
    have ih := HasTypeAll_reverse bvs Γ es' τs' hRest
    show HasTypeAll bvs Γ (e :: es').reverse (τ :: τs').reverse
    rw [List.reverse_cons, List.reverse_cons]
    exact HasTypeAll_append ih (HasTypeAll.cons _ _ e [] τ [] hE (HasTypeAll.nil _ _))

/-!
## HasTypeAll Index Access

Extract the i-th element type from a HasTypeAll proof.
-/

theorem HasTypeAll_getElem (bvs : List Typ) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (i : Nat) (h : HasTypeAll bvs Γ es τs)
    (hi : i < es.length) (hiτ : i < τs.length) :
    HasType bvs Γ es[i] τs[i] := by
  cases i with
  | zero =>
    cases es with
    | nil => simp at hi
    | cons e es' =>
      cases τs with
      | nil => simp at hiτ
      | cons τ τs' =>
        simp only [List.getElem_cons_zero]
        match h with | HasTypeAll.cons _ _ _ _ _ _ hE _ => exact hE
  | succ n =>
    cases es with
    | nil => simp at hi
    | cons e es' =>
      cases τs with
      | nil => simp at hiτ
      | cons τ τs' =>
        simp only [List.getElem_cons_succ]
        match h with
        | HasTypeAll.cons _ _ _ _ _ _ _ hRest =>
          exact HasTypeAll_getElem bvs Γ es' τs' n hRest (by simp at hi; omega) (by simp at hiτ; omega)

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
