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

-- NOTE: bvar_type produces HasType ctx Γ (.bvar n) ctx[n], so any
-- HasType ctx Γ (.bvar n) τ must have τ = ctx.types[n] with n < (ctx.types).length.
-- We split into two lemmas to avoid dependent indexing issues.
theorem HasType_bvar_has_length (ctx : LinCtx) (Γ : TypEnv) (n : Nat) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.bvar n) τ ctx' → n < (ctx.types).length := by
  intro h
  cases h with
  | bvar_type _ _ _ hLen => exact hLen

theorem HasType_fvar_inv (ctx : LinCtx) (Γ : TypEnv) (name : String) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.fvar name) τ ctx' → lookupTyp Γ name = some τ := by
  intro h; cases h with | fvar_type => assumption

theorem HasType_lit_int_inv (ctx : LinCtx) (Γ : TypEnv) (n : Int) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.lit (.int n)) τ ctx' → τ = .intType ∨ (∃ w, τ = .intWidthType w) := by
  intro h; cases h with
  | lit_int => left; rfl
  | lit_int_width _ _ w _ => right; exact ⟨w, rfl⟩

theorem HasType_lit_bool_inv (ctx : LinCtx) (Γ : TypEnv) (b : Bool) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.lit (.bool b)) τ ctx' → τ = .boolType := by
  intro h; cases h with | lit_bool => rfl

theorem HasType_lit_string_inv (ctx : LinCtx) (Γ : TypEnv) (s : String) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.lit (.string s)) τ ctx' → τ = .stringType := by
  intro h; cases h with | lit_string => rfl

theorem HasType_lit_unit_inv (ctx : LinCtx) (Γ : TypEnv) (τ : Typ) {ctx' : LinCtx} :
    HasType ctx Γ (.lit .unit) τ ctx' → τ = .unitType := by
  intro h; cases h with | lit_unit => rfl

theorem HasType_lit_pointer_inv (ctx : LinCtx) (Γ : TypEnv) (p : Pointer) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.lit (.pointer p)) τ ctx' → τ = .pointerType := by
  intro h; cases h with | lit_pointer => rfl

theorem HasType_lit_float_inv (ctx : LinCtx) (Γ : TypEnv) (f : Float) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.lit (.float f)) τ ctx' → ∃ w, τ = .floatType w := by
  intro h; cases h with
  | lit_float _ _ w _ => exact ⟨w, rfl⟩

theorem HasType_unop_not_inv (ctx : LinCtx) (Γ : TypEnv) (e : Expr) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.unop .not e) τ ctx' → τ = .boolType := by
  intro h; cases h with | unop_not => rfl

theorem HasType_unop_notb_inv (ctx : LinCtx) (Γ : TypEnv) (e : Expr) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.unop .notb e) τ ctx' → τ = .intType := by
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

end

theorem lift_comp (k1 k2 : Nat) (e : Expr) :
    lift k1 (lift k2 e) = lift (k1 + k2) e := liftUnder_comp 0 k1 k2 e

/-! ## Weakening (Trivial with de Bruijn)

With de Bruijn indices, weakening is simply prepending a type to `ctx`.
No freshness predicate is needed — bound variables are identified by index,
not by name, so there is no possibility of capture.
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

theorem weakening_at_depth (xs : List Typ) (ctx : LinCtx) (Γ : TypEnv)
    (e : Expr) (τ σ : Typ) :
    HasType (LinCtx.pushMany ctx xs) Γ e τ (LinCtx.pushMany ctx xs) →
      HasType (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) τ
        (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) := by
  intro h
  cases h with
  | bvar_type _ _ n hLen =>
    simp only [liftUnder]
    split
    · rename_i hNlt
      have hLen2 := hLen
      rw [LinCtx.types_pushMany] at hLen2
      have hP1 : n < (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs).types.length := by
        rw [LinCtx.types_pushMany]
        show n < (xs ++ σ :: ctx.types).length
        have h1 : (xs ++ σ :: ctx.types).length = xs.length + (σ :: ctx.types).length :=
          List.length_append
        have h2 : (σ :: ctx.types).length = ctx.types.length + 1 := List.length_cons
        have h3 : (xs ++ ctx.types).length = xs.length + ctx.types.length :=
          List.length_append
        have h4 : n < (xs ++ ctx.types).length := hLen2
        omega
      have hBT := HasType.bvar_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ n hP1
      have eqTy := LinCtx.types_pushMany_push_index_low ctx xs σ n hNlt
      exact Eq.subst (motive := fun t => HasType _ Γ (.bvar n) t _) eqTy hBT
    · rename_i hNge
      have hNge' : n ≥ xs.length := Nat.ge_of_not_lt hNge
      have hLen2 := hLen
      rw [LinCtx.types_pushMany] at hLen2
      have hLIdx : n - xs.length < ctx.types.length :=
        nat_sub_lt_of_lt_add n ctx.types.length xs.length hNge' (by
          have h3 : (LinCtx.pushMany ctx xs).types.length = xs.length + ctx.types.length := by
            rw [LinCtx.types_pushMany]; rw [List.length_append]
          omega)
      have hlc := @List.length_cons Typ σ ctx.types
      have hCons : (n - xs.length) + 1 < (σ :: ctx.types).length := by omega
      have hP1 : n + 1 < (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs).types.length := by
        rw [LinCtx.types_pushMany]
        show n + 1 < (xs ++ σ :: ctx.types).length
        have h1 : (xs ++ σ :: ctx.types).length = xs.length + (σ :: ctx.types).length :=
          List.length_append
        have h2 : (σ :: ctx.types).length = ctx.types.length + 1 := List.length_cons
        have h3 : (xs ++ ctx.types).length = xs.length + ctx.types.length :=
          List.length_append
        have h4 : n < (xs ++ ctx.types).length := hLen2
        omega
      have hBT := HasType.bvar_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (n + 1) hP1
      have hOpt := LinCtx.types_pushMany_push_index_high ctx xs σ n hNge' hCons
      have s2 : (LinCtx.pushMany ctx xs).types[n]? =
          some ((LinCtx.pushMany ctx xs).types[n]'hLen) :=
        List.getElem?_eq_some_iff.mpr ⟨hLen, rfl⟩
      have hChain : (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs).types[n + 1]? =
          some ((LinCtx.pushMany ctx xs).types[n]'hLen) := by rw [hOpt]; exact s2
      obtain ⟨_, hEq⟩ := List.getElem?_eq_some_iff.mp hChain
      exact Eq.subst (motive := fun t => HasType _ Γ (.bvar (n + 1)) t _) hEq hBT
  | fvar_type _ _ name τ hLookup =>
    simp only [liftUnder]
    exact HasType.fvar_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ name τ hLookup
  | lit_int _ _ n => simp only [liftUnder]; exact HasType.lit_int (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ n
  | lit_bool _ _ b => simp only [liftUnder]; exact HasType.lit_bool (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ b
  | lit_string _ _ s => simp only [liftUnder]; exact HasType.lit_string (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ s
  | lit_unit _ _ => simp only [liftUnder]; exact HasType.lit_unit (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ
  | lit_pointer _ _ p => simp only [liftUnder]; exact HasType.lit_pointer (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ p
  | unop_not _ _ e' hE' =>
    simp only [liftUnder]
    exact HasType.unop_not (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e')
      (weakening_at_depth xs ctx Γ e' .boolType σ hE')
  | unop_notb _ _ e' hE' =>
    simp only [liftUnder]
    exact HasType.unop_notb (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e')
      (weakening_at_depth xs ctx Γ e' .intType σ hE')
  | binop_arith _ _ op e1 e2 hArith hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_arith (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hArith
      (weakening_at_depth xs ctx Γ e1 .intType σ hE1)
      (weakening_at_depth xs ctx Γ e2 .intType σ hE2)
  | binop_comp _ _ op e1 e2 hComp hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_comp (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hComp
      (weakening_at_depth xs ctx Γ e1 .intType σ hE1)
      (weakening_at_depth xs ctx Γ e2 .intType σ hE2)
  | binop_logic _ _ op e1 e2 hLogic hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_logic (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hLogic
      (weakening_at_depth xs ctx Γ e1 .boolType σ hE1)
      (weakening_at_depth xs ctx Γ e2 .boolType σ hE2)
  | binop_bitwise _ _ op e1 e2 hBit hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_bitwise (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hBit
      (weakening_at_depth xs ctx Γ e1 .intType σ hE1)
      (weakening_at_depth xs ctx Γ e2 .intType σ hE2)
  | binop_ptr_arith _ _ op e1 e2 hPtr hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_arith (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ op (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) hPtr
      (weakening_at_depth xs ctx Γ e1 .pointerType σ hE1)
      (weakening_at_depth xs ctx Γ e2 .intType σ hE2)
  | binop_ptr_load _ _ e1 e2 hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_load (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2)
      (weakening_at_depth xs ctx Γ e1 .pointerType σ hE1)
      (weakening_at_depth xs ctx Γ e2 .unitType σ hE2)
  | binop_ptr_store _ _ e1 e2 hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_store (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2)
      (weakening_at_depth xs ctx Γ e1 .pointerType σ hE1)
      (weakening_at_depth xs ctx Γ e2 .intType σ hE2)
  | binop_string_concat _ _ op e1 e2 hOp hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_string_concat (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ op
      (liftUnder xs.length 1 e1) (liftUnder xs.length 1 e2)
      hOp
      (weakening_at_depth xs ctx Γ e1 .stringType σ hE1)
      (weakening_at_depth xs ctx Γ e2 .stringType σ hE2)
  | lam_type _ _ n body paramTys retTy hLen hBody =>
    simp only [liftUnder, liftUnder]
    have hLenEq : (paramTys.reverse ++ xs).length = n + xs.length := by
      have h1 := @List.length_append Typ (paramTys.reverse) xs
      have h2 := @List.length_reverse Typ paramTys
      rw [h1, h2]; omega
    have hBody' := weakening_at_depth (paramTys.reverse ++ xs) ctx Γ body retTy σ
      (by rw [← LinCtx.pushMany_pushMany_append]; exact hBody)
    rw [hLenEq, Nat.add_comm] at hBody'
    exact HasType.lam_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ n
      (liftUnder (xs.length + n) 1 body) paramTys retTy hLen
      (by rw [LinCtx.pushMany_pushMany_append]; exact hBody')
  | app_type _ _ fn args τs τ hFn hArgs =>
    simp only [liftUnder]
    exact HasType.app_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 fn)
      (List.map (liftUnder xs.length 1) args) τs τ
      (weakening_at_depth xs ctx Γ fn (.functionType τs τ) σ hFn)
      (weakening_at_depth_all xs ctx Γ args τs σ hArgs)
  | let_type _ _ e1 e2 τ1 _ hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.let_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e1)
      (liftUnder (xs.length + 1) 1 e2) τ1 τ
      (weakening_at_depth xs ctx Γ e1 τ1 σ hE1)
      (weakening_at_depth (τ1 :: xs) ctx Γ e2 τ σ hE2)
  | if_type _ _ c t f τ hC hT hF =>
    simp only [liftUnder]
    exact HasType.if_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 c)
      (liftUnder xs.length 1 t) (liftUnder xs.length 1 f) τ
      (weakening_at_depth xs ctx Γ c .boolType σ hC)
      (weakening_at_depth xs ctx Γ t τ σ hT)
      (weakening_at_depth xs ctx Γ f τ σ hF)
  | for_type _ _ s e body hS hE hBody =>
    simp only [liftUnder, liftUnder]
    exact HasType.for_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 s)
      (liftUnder xs.length 1 e) (List.map (liftUnder (xs.length + 1) 1) body)
      (weakening_at_depth xs ctx Γ s .intType σ hS)
      (weakening_at_depth xs ctx Γ e .intType σ hE)
      (weakening_at_depth_all (.intType :: xs) ctx Γ body [.unitType] σ hBody)
  | block_type _ _ exprs τs τ hExprs =>
    simp only [liftUnder]
    exact HasType.block_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (List.map (liftUnder xs.length 1) exprs) τs τ
      (weakening_at_depth_all xs ctx Γ exprs (τs ++ [τ]) σ hExprs)
  | lit_float _ _ w f => simp only [liftUnder]; exact HasType.lit_float (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ w f
  | lit_int_width _ _ w n => simp only [liftUnder]; exact HasType.lit_int_width (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ w n
  | lit_some _ _ v τ => simp only [liftUnder]; exact HasType.lit_some (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ v τ
  | lit_none _ _ τ => simp only [liftUnder]; exact HasType.lit_none (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ τ
  | lit_ok _ _ v τ_ok τ_err => simp only [liftUnder]; exact HasType.lit_ok (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ v τ_ok τ_err
  | lit_err _ _ v τ_err τ_ok => simp only [liftUnder]; exact HasType.lit_err (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ v τ_err τ_ok
  | pipe_type _ _ e f τ_arg τ hE hF =>
    simp only [liftUnder]
    exact HasType.pipe_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) (liftUnder xs.length 1 f) τ_arg τ
      (weakening_at_depth xs ctx Γ e τ_arg σ hE)
      (weakening_at_depth xs ctx Γ f (.functionType [τ_arg] τ) σ hF)
  | typeAsc_type _ _ e τ hE =>
    simp only [liftUnder]
    exact HasType.typeAsc_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) τ
      (weakening_at_depth xs ctx Γ e τ σ hE)
  | some_type _ _ e τ_inner hE =>
    simp only [liftUnder]
    exact HasType.some_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) τ_inner
      (weakening_at_depth xs ctx Γ e τ_inner σ hE)
  | none_type _ _ τ => simp only [liftUnder]; exact HasType.none_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ τ
  | ok_type _ _ e τ_ok τ_err hE =>
    simp only [liftUnder]
    exact HasType.ok_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) τ_ok τ_err
      (weakening_at_depth xs ctx Γ e τ_ok σ hE)
  | err_type _ _ e τ_err τ_ok hE =>
    simp only [liftUnder]
    exact HasType.err_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) τ_err τ_ok
      (weakening_at_depth xs ctx Γ e τ_err σ hE)
  | null_coalesce_type _ _ e1 e2 τ hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.null_coalesce_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e1)
      (liftUnder xs.length 1 e2) τ
      (weakening_at_depth xs ctx Γ e1 (.optionType τ) σ hE1)
      (weakening_at_depth xs ctx Γ e2 (.optionType τ) σ hE2)
   | tuple_type _ _ elems tys hTys =>
     simp only [liftUnder]
     exact HasType.tuple_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (elems.map (liftUnder xs.length 1)) tys
       (weakening_at_depth_all xs ctx Γ elems tys σ hTys)
   | field_access_type _ _ e fname sname fields τ hE hField =>
     simp only [liftUnder]
     exact HasType.field_access_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) fname sname fields τ
       (weakening_at_depth xs ctx Γ e (.structType sname fields) σ hE)
       hField
   | match_type _ _ scrut arms _ _ hScrut hArms =>
      simp only [liftUnder]
      exact HasType.match_type _ _ (liftUnder xs.length 1 scrut) (liftUnderArms xs.length 1 arms) _ _
        (weakening_at_depth xs ctx Γ scrut _ σ hScrut)
        (ArmsTyped_weakening_at_depth xs σ hArms)
   | arrayLit_type _ _ elems τ n hElems hLen hn =>
     simp only [liftUnder]
     have hLen' : n = (List.map (liftUnder xs.length 1) elems).length := by
       rw [List.length_map]; exact hLen
     exact HasType.arrayLit_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (elems.map (liftUnder xs.length 1)) τ n
       (weakening_at_depth_all xs ctx Γ elems (List.replicate n τ) σ hElems) hLen' hn
   | arrayIndex_type _ _ arr idx τ n hArr hIdx =>
     simp only [liftUnder]
     exact HasType.arrayIndex_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 arr)
       (liftUnder xs.length 1 idx) τ n
       (weakening_at_depth xs ctx Γ arr (.arrayType τ n) σ hArr)
       (weakening_at_depth xs ctx Γ idx .intType σ hIdx)
   | refCreate_type _ _ e cap τ hE =>
     simp only [liftUnder]
     exact HasType.refCreate_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) cap τ
       (weakening_at_depth xs ctx Γ e τ σ hE)
   | refLoad_type _ _ e cap τ hE =>
     simp only [liftUnder]
     exact HasType.refLoad_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) cap τ
       (weakening_at_depth xs ctx Γ e (.refType cap τ) σ hE)
   | refStore_type _ _ e v cap τ hE hV hCap =>
     simp only [liftUnder]
     exact HasType.refStore_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e)
       (liftUnder xs.length 1 v) cap τ
       (weakening_at_depth xs ctx Γ e (.refType cap τ) σ hE)
       (weakening_at_depth xs ctx Γ v τ σ hV)
       hCap
   | refFree_type _ _ e τ hE =>
     simp only [liftUnder]
     exact HasType.refFree_type (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) τ
       (weakening_at_depth xs ctx Γ e (.refType .iso τ) σ hE)

theorem ArmsTyped_weakening_at_depth (xs : List Typ) (σ : Typ)
    {ctx : LinCtx} {Γ : TypEnv} {τ_scrut : Typ}
    {arms : List (List String × Expr)} {τ_result : Typ}
    (h : ArmsTyped (LinCtx.pushMany ctx xs) Γ τ_scrut arms τ_result (LinCtx.pushMany ctx xs)) :
    ArmsTyped (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ τ_scrut
      (liftUnderArms xs.length 1 arms) τ_result
      (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) := by
  cases h with
  | nil => simp only [liftUnderArms]; constructor
  | cons ctx Γ vars body rest τ_scrut τ_result hBody hRest =>
    simp only [liftUnderArms]
    constructor
    · have hBody' := weakening_at_depth (List.replicate vars.length τ_scrut ++ xs) ctx Γ body τ_result σ
        (by rw [← LinCtx.pushMany_pushMany_append]; exact hBody)
      simp only [List.length_append, List.length_replicate] at hBody'
      rw [Nat.add_comm] at hBody'
      show HasType (LinCtx.pushMany (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs)
          (List.replicate vars.length τ_scrut)) Γ
          (liftUnder (xs.length + vars.length) 1 body) τ_result
          (LinCtx.pushMany (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs)
            (List.replicate vars.length τ_scrut))
      rw [LinCtx.pushMany_pushMany_append]; exact hBody'
    · exact ArmsTyped_weakening_at_depth xs σ hRest

 theorem weakening_at_depth_all (xs : List Typ) (ctx : LinCtx) (Γ : TypEnv)
    (es : List Expr) (τs : List Typ) (σ : Typ)
    (h : HasTypeAll (LinCtx.pushMany ctx xs) Γ es τs (LinCtx.pushMany ctx xs)) :
    HasTypeAll (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (es.map (liftUnder xs.length 1)) τs
      (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) := by
  cases h with
  | nil _ _ => exact HasTypeAll.nil _ _
  | cons _ _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _ _
      (weakening_at_depth xs ctx Γ e τ σ hE)
      (weakening_at_depth_all xs ctx Γ es' τs' σ hRest)

end

/-! ## Multi-Type Weakening at Depth

Weaken by prepending multiple types (`xs`) after a prefix in the context.
`HasType (LinCtx.pushMany ctx pfx) Γ e τ → HasType (LinCtx.pushMany (LinCtx.pushMany ctx xs) pfx) Γ (liftUnder pfx.length xs.length e) τ`
Uses `weakening_at_depth` iterated `xs.length` times, with `liftUnder_comp` to compose lifts.
-/

theorem weaken_many_at_depth (pfx xs : List Typ) (ctx : LinCtx) (Γ : TypEnv)
    (e : Expr) (τ : Typ)
    (hE : HasType (LinCtx.pushMany ctx pfx) Γ e τ (LinCtx.pushMany ctx pfx))
    : HasType (LinCtx.pushMany (LinCtx.pushMany ctx xs) pfx) Γ (liftUnder pfx.length xs.length e) τ
        (LinCtx.pushMany (LinCtx.pushMany ctx xs) pfx) := by
  induction xs generalizing ctx e with
  | nil =>
    simp only [LinCtx.pushMany, List.map_nil, List.nil_append]
    simp only [List.length_nil]
    rw [liftUnder_zero_eq]
    exact hE
  | cons σ xs' ih =>
    have hStep1 := ih ctx e hE
    have hStep2 := weakening_at_depth pfx (LinCtx.pushMany ctx xs') Γ
      (liftUnder pfx.length xs'.length e) τ σ hStep1
    rw [liftUnder_comp, Nat.add_comm 1 xs'.length] at hStep2
    exact hStep2

/-! ## ArmsTyped Weakening (simple) -/

theorem ArmsTyped_weakening (σ : Typ)
    {ctx : LinCtx} {Γ : TypEnv} {τ_scrut : Typ}
    {arms : List (List String × Expr)} {τ_result : Typ}
    (h : ArmsTyped ctx Γ τ_scrut arms τ_result ctx) :
    ArmsTyped ((σ, LinCtx.initialUsage σ) :: ctx) Γ τ_scrut (liftUnderArms 0 1 arms) τ_result
      ((σ, LinCtx.initialUsage σ) :: ctx) := by
  have h := ArmsTyped_weakening_at_depth [] σ h
  simp only [LinCtx.pushMany, List.map_nil, List.nil_append, List.length_nil] at h
  exact h

mutual

theorem weakening (ctx : LinCtx) (Γ : TypEnv) (e : Expr) (τ : Typ) (σ : Typ) :
    HasType ctx Γ e τ ctx → HasType ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) τ
      ((σ, LinCtx.initialUsage σ) :: ctx) := by
  intro h
  match h with
  | HasType.bvar_type ctx Γ n h =>
    have hLen' : n + 1 < (LinCtx.types ((σ, LinCtx.initialUsage σ) :: ctx)).length := by
      have h' := h
      simp only [LinCtx.types, List.map_cons, List.length_cons] at h' ⊢
      omega
    rw [lift_bvar]
    have hEq : (LinCtx.types ((σ, LinCtx.initialUsage σ) :: ctx))[n + 1]'hLen'
        = (LinCtx.types ctx)[n]'h :=
      List.getElem_cons_succ σ (LinCtx.types ctx) n hLen'
    exact hEq ▸ HasType.bvar_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (n + 1) hLen'
  | HasType.fvar_type ctx Γ name τ hLookup =>
    rw [lift_fvar]
    exact HasType.fvar_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ name τ hLookup
  | HasType.lit_int ctx Γ n =>
    rw [lift_lit]
    exact HasType.lit_int ((σ, LinCtx.initialUsage σ) :: ctx) Γ n
  | HasType.lit_bool ctx Γ b =>
    rw [lift_lit]
    exact HasType.lit_bool ((σ, LinCtx.initialUsage σ) :: ctx) Γ b
  | HasType.lit_string ctx Γ s =>
    rw [lift_lit]
    exact HasType.lit_string ((σ, LinCtx.initialUsage σ) :: ctx) Γ s
  | HasType.lit_unit ctx Γ =>
    rw [lift_lit]
    exact HasType.lit_unit ((σ, LinCtx.initialUsage σ) :: ctx) Γ
  | HasType.lit_pointer ctx Γ p =>
    rw [lift_lit]
    exact HasType.lit_pointer ((σ, LinCtx.initialUsage σ) :: ctx) Γ p
  | HasType.unop_not ctx Γ e hE =>
    rw [lift_unop]
    exact HasType.unop_not ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) (weakening _ _ _ _ σ hE)
  | HasType.unop_notb ctx Γ e hE =>
    rw [lift_unop]
    exact HasType.unop_notb ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) (weakening _ _ _ _ σ hE)
  | HasType.binop_arith ctx Γ op e1 e2 hArith hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_arith ((σ, LinCtx.initialUsage σ) :: ctx) Γ op (lift 1 e1) (lift 1 e2) hArith
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_comp ctx Γ op e1 e2 hComp hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_comp ((σ, LinCtx.initialUsage σ) :: ctx) Γ op (lift 1 e1) (lift 1 e2) hComp
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_logic ctx Γ op e1 e2 hLogic hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_logic ((σ, LinCtx.initialUsage σ) :: ctx) Γ op (lift 1 e1) (lift 1 e2) hLogic
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_bitwise ctx Γ op e1 e2 hBit hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_bitwise ((σ, LinCtx.initialUsage σ) :: ctx) Γ op (lift 1 e1) (lift 1 e2) hBit
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_ptr_arith ctx Γ op e1 e2 hPtr hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_ptr_arith ((σ, LinCtx.initialUsage σ) :: ctx) Γ op (lift 1 e1) (lift 1 e2) hPtr
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_ptr_load ctx Γ e1 e2 hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_ptr_load ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e1) (lift 1 e2)
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_ptr_store ctx Γ e1 e2 hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_ptr_store ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e1) (lift 1 e2)
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
  | HasType.binop_string_concat ctx Γ op e1 e2 hOp hE1 hE2 =>
    rw [lift_binop]
    exact HasType.binop_string_concat ((σ, LinCtx.initialUsage σ) :: ctx) Γ op
      (lift 1 e1) (lift 1 e2)
      hOp
      (weakening _ _ _ _ σ hE1)
      (weakening _ _ _ _ σ hE2)
  | HasType.lam_type ctx Γ n body paramTys retTy hLen hBody =>
    rw [lift_lam]
    have hLenEq1 := @List.length_reverse Typ paramTys
    have hLenEq2 : paramTys.reverse.length = n := hLenEq1.trans hLen.symm
    have hBody' := weakening_at_depth paramTys.reverse ctx Γ body retTy σ hBody
    exact HasType.lam_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ n (liftUnder n 1 body) paramTys retTy hLen
      (Eq.subst (motive := fun i => HasType _ Γ (liftUnder i 1 body) retTy _) hLenEq2 hBody')
  | HasType.app_type ctx Γ fn args τs τ hFn hArgs =>
    rw [lift_app]
    exact HasType.app_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 fn) (List.map (lift 1) args) τs τ
      (weakening _ _ _ _ σ hFn) (weakening_all _ _ _ _ σ hArgs)
  | HasType.let_type ctx Γ e1 e2 τ1 τ2 hE1 hE2 =>
    rw [lift_let]
    exact HasType.let_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e1) (liftUnder 1 1 e2) τ1 τ2
      (weakening _ _ _ _ σ hE1) (weakening_at_depth [τ1] ctx Γ e2 τ2 σ hE2)
  | HasType.if_type ctx Γ c t f τ hC hT hF =>
    rw [lift_if]
    exact HasType.if_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 c) (lift 1 t) (lift 1 f) τ
      (weakening _ _ _ _ σ hC) (weakening _ _ _ _ σ hT) (weakening _ _ _ _ σ hF)
  | HasType.for_type ctx Γ s e body hS hE hBody =>
    rw [lift_for]
    exact HasType.for_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 s) (lift 1 e) (body.map (liftUnder 1 1))
      (weakening _ _ _ _ σ hS) (weakening _ _ _ _ σ hE)
      (weakening_at_depth_all [.intType] ctx Γ body [.unitType] σ hBody)
  | HasType.block_type ctx Γ exprs τs τ hExprs =>
    rw [lift_block]
    exact HasType.block_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (List.map (lift 1) exprs) τs τ
      (weakening_all _ _ _ _ σ hExprs)
  | HasType.lit_float ctx Γ w f =>
    rw [lift_lit]
    exact HasType.lit_float ((σ, LinCtx.initialUsage σ) :: ctx) Γ w f
  | HasType.lit_int_width ctx Γ w n =>
    rw [lift_lit]
    exact HasType.lit_int_width ((σ, LinCtx.initialUsage σ) :: ctx) Γ w n
  | HasType.lit_some ctx Γ v τ =>
    rw [lift_lit]
    exact HasType.lit_some ((σ, LinCtx.initialUsage σ) :: ctx) Γ v τ
  | HasType.lit_none ctx Γ τ =>
    rw [lift_lit]
    exact HasType.lit_none ((σ, LinCtx.initialUsage σ) :: ctx) Γ τ
  | HasType.lit_ok ctx Γ v τ_ok τ_err =>
    rw [lift_lit]
    exact HasType.lit_ok ((σ, LinCtx.initialUsage σ) :: ctx) Γ v τ_ok τ_err
   | HasType.lit_err ctx Γ v τ_err τ_ok =>
     rw [lift_lit]
     exact HasType.lit_err ((σ, LinCtx.initialUsage σ) :: ctx) Γ v τ_err τ_ok
   | HasType.pipe_type ctx Γ e f τ_arg τ hE hF =>
    rw [lift_pipe]
    exact HasType.pipe_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) (lift 1 f) τ_arg τ
      (weakening _ _ _ _ σ hE) (weakening _ _ _ _ σ hF)
  | HasType.typeAsc_type ctx Γ e τ hE =>
    rw [lift_typeAsc]
    exact HasType.typeAsc_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) τ (weakening _ _ _ _ σ hE)
  | HasType.some_type ctx Γ e τ_inner hE =>
    rw [lift_some]
    exact HasType.some_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) τ_inner (weakening _ _ _ _ σ hE)
  | HasType.none_type ctx Γ τ =>
    rw [lift_none]
    exact HasType.none_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ τ
  | HasType.ok_type ctx Γ e τ_ok τ_err hE =>
    rw [lift_ok]
    exact HasType.ok_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) τ_ok τ_err (weakening _ _ _ _ σ hE)
  | HasType.err_type ctx Γ e τ_err τ_ok hE =>
    rw [lift_err]
    exact HasType.err_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) τ_err τ_ok (weakening _ _ _ _ σ hE)
  | HasType.null_coalesce_type ctx Γ e1 e2 τ hE1 hE2 =>
    rw [lift_nullCoalesce]
    exact HasType.null_coalesce_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e1) (lift 1 e2) τ
      (weakening _ _ _ _ σ hE1) (weakening _ _ _ _ σ hE2)
   | HasType.tuple_type ctx Γ elems tys hTys =>
     rw [lift_tuple]
     exact HasType.tuple_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (elems.map (lift 1)) tys
       (weakening_all _ _ _ _ σ hTys)
   | HasType.field_access_type ctx Γ e fname sname fields τ hE hField =>
     rw [lift_field]
     exact HasType.field_access_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) fname sname fields τ
       (weakening _ _ _ _ σ hE) hField
   | HasType.match_type ctx Γ scrut arms τ_scrut τ_result hScrut hArms =>
      simp only [liftUnder]
      exact HasType.match_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 scrut) (liftUnderArms 0 1 arms) τ_scrut τ_result
        (weakening _ _ _ _ σ hScrut)
        (ArmsTyped_weakening σ hArms)
   | HasType.arrayLit_type ctx Γ elems τ n hElems hLen hn =>
     rw [lift_arrayLit]
     have hLen' : n = (List.map (lift 1) elems).length := by
       rw [List.length_map]; exact hLen
     exact HasType.arrayLit_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (elems.map (lift 1)) τ n
       (weakening_all _ _ _ _ σ hElems) hLen' hn
   | HasType.arrayIndex_type ctx Γ arr idx τ n hArr hIdx =>
     rw [lift_arrayIndex]
     exact HasType.arrayIndex_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 arr) (lift 1 idx) τ n
       (weakening _ _ _ _ σ hArr) (weakening _ _ _ _ σ hIdx)
   | HasType.refCreate_type ctx Γ e cap τ hE =>
     rw [lift_refCreate]
     exact HasType.refCreate_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) cap τ
       (weakening _ _ _ _ σ hE)
   | HasType.refLoad_type ctx Γ e cap τ hE =>
     rw [lift_refLoad]
     exact HasType.refLoad_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) cap τ
       (weakening _ _ _ _ σ hE)
   | HasType.refStore_type ctx Γ e v cap τ hE hV hCap =>
     rw [lift_refStore]
     exact HasType.refStore_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) (lift 1 v) cap τ
       (weakening _ _ _ _ σ hE) (weakening _ _ _ _ σ hV) hCap
   | HasType.refFree_type ctx Γ e τ hE =>
     rw [lift_refFree]
     exact HasType.refFree_type ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) τ
       (weakening _ _ _ _ σ hE)

theorem weakening_all (ctx : LinCtx) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (σ : Typ) (h : HasTypeAll ctx Γ es τs ctx) : HasTypeAll ((σ, LinCtx.initialUsage σ) :: ctx) Γ
      (es.map (lift 1)) τs ((σ, LinCtx.initialUsage σ) :: ctx) := by
  match h with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _ _
      (weakening _ _ _ _ σ hE)
      (weakening_all _ _ _ _ σ hRest)

end

/-!
## HasTypeAll Append

Append two HasTypeAll proofs.
-/

theorem HasTypeAll_append {ctx : LinCtx} {Γ : TypEnv} {es₁ es₂ : List Expr} {τs₁ τs₂ : List Typ}
    (h₁ : HasTypeAll ctx Γ es₁ τs₁ ctx) (h₂ : HasTypeAll ctx Γ es₂ τs₂ ctx) :
    HasTypeAll ctx Γ (es₁ ++ es₂) (τs₁ ++ τs₂) ctx := by
  match h₁ with
  | HasTypeAll.nil _ _ => exact h₂
  | HasTypeAll.cons _ _ _ e es τ τs hE hRest =>
    exact HasTypeAll.cons _ _ _ e (es ++ es₂) τ (τs ++ τs₂) hE (HasTypeAll_append hRest h₂)

/-!
## HasTypeAll Reverse

Reversing both the expression list and the type list preserves HasTypeAll.
-/

theorem HasTypeAll_reverse (ctx : LinCtx) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (h : HasTypeAll ctx Γ es τs ctx) : HasTypeAll ctx Γ es.reverse τs.reverse ctx := by
  match h with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ _ e es' τ τs' hE hRest =>
    have ih := HasTypeAll_reverse ctx Γ es' τs' hRest
    show HasTypeAll ctx Γ (e :: es').reverse (τ :: τs').reverse ctx
    rw [List.reverse_cons, List.reverse_cons]
    exact HasTypeAll_append ih (HasTypeAll.cons _ _ _ e [] τ [] hE (HasTypeAll.nil _ _))

/-!
## HasTypeAll Index Access

Extract the i-th element type from a HasTypeAll proof.
-/

theorem HasTypeAll_getElem (ctx : LinCtx) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (i : Nat) (h : HasTypeAll ctx Γ es τs ctx)
    (hi : i < es.length) (hiτ : i < τs.length) :
    HasType ctx Γ es[i] τs[i] ctx := by
  cases i with
  | zero =>
    cases es with
    | nil => simp at hi
    | cons e es' =>
      cases τs with
      | nil => simp at hiτ
      | cons τ τs' =>
        simp only [List.getElem_cons_zero]
        match h with | HasTypeAll.cons _ _ _ _ _ _ _ hE _ => exact hE
  | succ n =>
    cases es with
    | nil => simp at hi
    | cons e es' =>
      cases τs with
      | nil => simp at hiτ
      | cons τ τs' =>
        simp only [List.getElem_cons_succ]
        match h with
        | HasTypeAll.cons _ _ _ _ _ _ _ _ hRest =>
          exact HasTypeAll_getElem ctx Γ es' τs' n hRest (by simp at hi; omega) (by simp at hiτ; omega)

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
