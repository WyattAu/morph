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

/-! ## Values Do Not Consume

Typing a value never consumes the ambient context: literals, lambdas and
`none_` are typed by rules that thread the context through unchanged, and
`refCreate` threads it too (its allocation happens at run time, not in the
typing rule).

This is what makes the consumption-aware substitution lemma well-posed: when
`let_subst` replaces a bound variable by the value that was let-bound, the
substituted expression inherits exactly the context the value was typed in. -/

theorem value_does_not_consume : ∀ {e : Expr} {τ : Typ} {cin cout : LinCtx} {Γ : TypEnv},
    Morph.Semantics.IsValue e → HasType cin Γ e τ cout → cout = cin := by
  intro e τ cin cout Γ hv ht
  cases hv <;> cases ht <;> simp_all

/-! ## Inversion Lemmas -/

-- NOTE: both bvar rules bound n by the length of the context, so any
-- HasType ctx Γ (.bvar n) τ ctx' must have n < (ctx.types).length.
-- We split into two lemmas to avoid dependent indexing issues.
theorem HasType_bvar_has_length (ctx : LinCtx) (Γ : TypEnv) (n : Nat) (τ : Typ)
    {ctx' : LinCtx} :
    HasType ctx Γ (.bvar n) τ ctx' → n < (ctx.types).length := by
  intro h
  cases h with
  | bvar_type _ _ _ _ _ hLen _ _ => exact hLen
  | bvar_type_many _ _ _ _ hLen _ => exact hLen

/-! ## Consumption Facts -/

/-- Consuming index `n` rewrites the entry at `n` to `(τ, .one)`. -/
theorem LinCtx.consume_getElem?_self (ctx : LinCtx) (n : Nat) :
    (LinCtx.consume ctx n)[n]? = (ctx[n]?).map (fun e => (e.1, Morph.Usage.one)) := by
  induction ctx generalizing n with
  | nil => rfl
  | cons entry tail ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [LinCtx.consume, LinCtx.setUsage, Nat.add_sub_cancel, Nat.succ_ne_zero,
        if_false, List.getElem?_cons_succ, Option.map]
      rw [show LinCtx.setUsage tail n Morph.Usage.one = LinCtx.consume tail n from rfl, ih n]
      rfl

/-- Consuming a `.zero` slot really changes the context, so a `bvar_type`
derivation can never have the output context equal to its input context. This is
what makes `HasType ctx Γ e τ ctx` a genuinely *non-consuming* judgment. -/
theorem LinCtx.consume_ne {ctx : LinCtx} {n : Nat} {τ : Typ}
    (h : ctx[n]? = some (τ, Morph.Usage.zero)) : LinCtx.consume ctx n ≠ ctx := by
  intro hc
  have h1 : ctx[n]? = (LinCtx.consume ctx n)[n]? := by rw [hc]
  rw [LinCtx.consume_getElem?_self, h, Option.map] at h1
  exact Morph.Usage.noConfusion (congrArg Prod.snd (Option.some.inj h1))

/-- Entry-level index bridge for weakening: inserting `(σ, initialUsage σ)`
between the pushed prefix `xs` and the base context leaves the entry at
`n < xs.length` untouched (both sides land inside the prefix). -/
theorem LinCtx.entry_pushMany_push_index_low (ctx : LinCtx) (xs : List Typ) (σ : Typ)
    (n : Nat) (h : n < xs.length) :
    (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs)[n]?
      = (LinCtx.pushMany ctx xs)[n]? := by
  simp only [LinCtx.pushMany]
  rw [List.getElem?_append_left (by simpa using h), List.getElem?_append_left (by simpa using h)]

/-- Entry-level index bridge for weakening: index `n + 1` of the weakened context
reads index `n` of the original one (the inserted entry shifts everything above
the prefix by one). -/
theorem LinCtx.entry_pushMany_push_index_high (ctx : LinCtx) (xs : List Typ) (σ : Typ)
    (n : Nat) (hNge : n ≥ xs.length) :
    (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs)[n + 1]?
      = (LinCtx.pushMany ctx xs)[n]? := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + xs.length := ⟨n - xs.length, by omega⟩
  simp only [LinCtx.pushMany]
  rw [List.getElem?_append_right (l₂ := (σ, LinCtx.initialUsage σ) :: ctx) (by simp; omega)]
  simp only [List.length_map]
  rw [show i + xs.length + 1 - xs.length = i + 1 from by omega, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (l₂ := ctx) (by simp only [List.length_map]; omega)]
  simp only [List.length_map]
  rw [show i + xs.length - xs.length = i from by omega]

/-- Entry-level index bridge for substitution: below the pushed prefix `pfx`
both contexts read the same entry. -/
theorem LinCtx.entry_pushMany_index_low (pfx : List Typ) (base1 base2 : LinCtx) (n : Nat)
    (h : n < pfx.length) :
    (LinCtx.pushMany base1 pfx)[n]? = (LinCtx.pushMany base2 pfx)[n]? := by
  simp only [LinCtx.pushMany]
  rw [List.getElem?_append_left (by simpa using h), List.getElem?_append_left (by simpa using h)]

/-- Entry-level index bridge for substitution: at or above the pushed prefix,
the extended context reads index `n - pfx.length` of its base. -/
theorem LinCtx.entry_pushMany_index_high (pfx : List Typ) (base : LinCtx) (n : Nat)
    (h : pfx.length ≤ n) :
    (LinCtx.pushMany base pfx)[n]? = base[n - pfx.length]? := by
  simp only [LinCtx.pushMany]
  rw [List.getElem?_append_right (l₂ := base) (by simp only [List.length_map]; omega)]
  simp only [List.length_map]

theorem LinCtx.entry_pushMany_cons_index_high (pfx : List Typ) (base : LinCtx) (e : LinEntry)
    (n : Nat) (h : pfx.length ≤ n) :
    (LinCtx.pushMany (e :: base) pfx)[n]? = (e :: base)[n - pfx.length]? := by
  simp only [LinCtx.pushMany]
  rw [List.getElem?_append_right (l₂ := e :: base) (by simp only [List.length_map]; omega)]
  simp only [List.length_map]

theorem LinCtx.entry_cons_succ (e : LinEntry) (base : LinCtx) (k : Nat) :
    (e :: base)[k + 1]? = base[k]? := List.getElem?_cons_succ

/-- Entry-level bridge for `substAll'`: below the pushed prefix `pfx` both
contexts read the same entry. -/
theorem LinCtx.entry_pushMany_pushMany_index_low (ctx : LinCtx) (pfx σs : List Typ) (n : Nat)
    (h : n < pfx.length) :
    (LinCtx.pushMany (LinCtx.pushMany ctx σs) pfx)[n]? = (LinCtx.pushMany ctx pfx)[n]? := by
  simp only [LinCtx.pushMany]
  rw [List.getElem?_append_left (by simpa using h), List.getElem?_append_left (by simpa using h)]

/-- Entry-level bridge for `substAll'`: index `pfx.length + k` reads the entry
for `σs[k]`, carrying that entry's initial usage. -/
theorem LinCtx.entry_pushMany_pushMany_index_mid (ctx : LinCtx) (pfx σs : List Typ) (k : Nat)
    (h : k < σs.length) :
    (LinCtx.pushMany (LinCtx.pushMany ctx σs) pfx)[pfx.length + k]?
      = some (σs[k]'h, LinCtx.initialUsage (σs[k]'h)) := by
  rw [LinCtx.entry_pushMany_index_high pfx (LinCtx.pushMany ctx σs) (pfx.length + k) (by omega)]
  rw [show pfx.length + k - pfx.length = k from by omega]
  simp only [LinCtx.pushMany]
  rw [List.getElem?_append_left (by simpa using h)]
  rw [List.getElem?_map, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  rfl

/-- Entry-level bridge for `substAll'`: above both pushed blocks the entry shifts
down by `σs.length`. -/
theorem LinCtx.entry_pushMany_pushMany_index_high (ctx : LinCtx) (pfx σs : List Typ) (n : Nat)
    (h : n ≥ pfx.length + σs.length) :
    (LinCtx.pushMany (LinCtx.pushMany ctx σs) pfx)[n]? = (LinCtx.pushMany ctx pfx)[n - σs.length]? := by
  rw [LinCtx.entry_pushMany_index_high pfx (LinCtx.pushMany ctx σs) n (by omega)]
  rw [LinCtx.entry_pushMany_index_high pfx ctx (n - σs.length) (by omega)]
  rw [LinCtx.entry_pushMany_index_high σs ctx (n - pfx.length) (by omega)]
  rw [show n - pfx.length - σs.length = n - σs.length - pfx.length from by omega]

/-- Substitution bridge: removing the head entry shifts every index strictly
above the pushed prefix `pfx` down by one. -/
theorem LinCtx.entry_shift (pfx : List Typ) (base : LinCtx) (σ : Typ) (n : Nat)
    (h : pfx.length < n) :
    (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: base) pfx)[n]?
      = (LinCtx.pushMany base pfx)[n - 1]? := by
  rw [LinCtx.entry_pushMany_cons_index_high pfx base (σ, LinCtx.initialUsage σ) n (by omega)]
  rw [show n - pfx.length = (n - pfx.length - 1) + 1 from by omega, LinCtx.entry_cons_succ]
  rw [LinCtx.entry_pushMany_index_high pfx base (n - 1) (by omega)]
  rw [show n - 1 - pfx.length = n - pfx.length - 1 from by omega]

/-! ## Index Bridges for `linPushMany` (ADR-014 Loop 4)

Every binder rule pushes `Usage.many` entries via `linPushMany`, so the
substitution and weakening proofs need the same bridges as above, stated for
`linPushMany`. -/

theorem linPushMany_pushMany_append (ctx : LinCtx) (xs ys : List Typ) :
    linPushMany (linPushMany ctx ys) xs = linPushMany ctx (xs ++ ys) := by
  simp only [linPushMany, List.map_append, List.append_assoc]

theorem LinCtx.entry_linPushMany_index_low (pfx : List Typ) (base1 base2 : LinCtx) (n : Nat)
    (h : n < pfx.length) :
    (linPushMany base1 pfx)[n]? = (linPushMany base2 pfx)[n]? := by
  simp only [linPushMany]
  rw [List.getElem?_append_left (by simpa using h), List.getElem?_append_left (by simpa using h)]

theorem LinCtx.entry_linPushMany_index_high (pfx : List Typ) (base : LinCtx) (n : Nat)
    (h : pfx.length ≤ n) :
    (linPushMany base pfx)[n]? = base[n - pfx.length]? := by
  simp only [linPushMany]
  rw [List.getElem?_append_right (l₂ := base) (by simp only [List.length_map]; omega)]
  simp only [List.length_map]

theorem LinCtx.entry_linPushMany_cons_index_high (pfx : List Typ) (base : LinCtx) (e : LinEntry)
    (n : Nat) (h : pfx.length ≤ n) :
    (linPushMany (e :: base) pfx)[n]? = (e :: base)[n - pfx.length]? := by
  simp only [linPushMany]
  rw [List.getElem?_append_right (l₂ := e :: base) (by simp only [List.length_map]; omega)]
  simp only [List.length_map]

theorem LinCtx.entry_linPushMany_pushMany_index_low (ctx : LinCtx) (pfx σs : List Typ) (n : Nat)
    (h : n < pfx.length) :
    (linPushMany (linPushMany ctx σs) pfx)[n]? = (linPushMany ctx pfx)[n]? := by
  simp only [linPushMany]
  rw [List.getElem?_append_left (by simpa using h), List.getElem?_append_left (by simpa using h)]

/-- Index `pfx.length + k` of the double push reads the entry for `σs[k]`,
carrying `Usage.many`. -/
theorem LinCtx.entry_linPushMany_pushMany_index_mid (ctx : LinCtx) (pfx σs : List Typ) (k : Nat)
    (h : k < σs.length) :
    (linPushMany (linPushMany ctx σs) pfx)[pfx.length + k]?
      = some (σs[k]'h, Morph.Usage.many) := by
  rw [LinCtx.entry_linPushMany_index_high pfx (linPushMany ctx σs) (pfx.length + k) (by omega)]
  rw [show pfx.length + k - pfx.length = k from by omega]
  exact entry_linPushMany_mid ctx σs k h

theorem LinCtx.entry_linPushMany_pushMany_index_high (ctx : LinCtx) (pfx σs : List Typ) (n : Nat)
    (h : n ≥ pfx.length + σs.length) :
    (linPushMany (linPushMany ctx σs) pfx)[n]? = (linPushMany ctx pfx)[n - σs.length]? := by
  rw [LinCtx.entry_linPushMany_index_high pfx (linPushMany ctx σs) n (by omega)]
  rw [LinCtx.entry_linPushMany_index_high pfx ctx (n - σs.length) (by omega)]
  rw [LinCtx.entry_linPushMany_index_high σs ctx (n - pfx.length) (by omega)]
  rw [show n - pfx.length - σs.length = n - σs.length - pfx.length from by omega]

/-- Substitution bridge for `.many` pushes: removing the head entry shifts every
index strictly above the pushed prefix `pfx` down by one (any usage). -/
theorem LinCtx.entry_linShift (pfx : List Typ) (base : LinCtx) (σ : Typ) (u : Morph.Usage)
    (n : Nat) (h : pfx.length < n) :
    (linPushMany ((σ, u) :: base) pfx)[n]? = (linPushMany base pfx)[n - 1]? := by
  rw [LinCtx.entry_linPushMany_cons_index_high pfx base (σ, u) n (by omega)]
  rw [show n - pfx.length = (n - pfx.length - 1) + 1 from by omega, LinCtx.entry_cons_succ]
  rw [LinCtx.entry_linPushMany_index_high pfx base (n - 1) (by omega)]
  rw [show n - 1 - pfx.length = n - pfx.length - 1 from by omega]

/-- An entry `some (τ, u)` at index `n` witnesses the type at index `n`. -/
theorem LinCtx.types_of_entry_getElem? {ctx : LinCtx} {n : Nat} {τ : Typ} {u : Morph.Usage}
    (h : ctx[n]? = some (τ, u)) (hn : n < (ctx.types).length) :
    (ctx.types)[n]'hn = τ := by
  have hOpt : ctx.types[n]? = some τ := by
    rw [LinCtx.types, List.getElem?_map, h, Option.map]
  obtain ⟨hn', heq⟩ := List.getElem?_eq_some_iff.mp hOpt
  show (ctx.types)[n]'hn = _
  exact heq

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

/-! ## Closed Typing Keeps the Context Empty

With an empty input context there is nothing to consume (`bvar_type` needs
`n < 0`), and the `binop_*` rules pass through their first operand's output
context, so every derivation starting from `[]` ends at `[]`. This is what lets
`progress` apply its induction hypothesis to the *second* operand of a threaded
`binop` (ADR-010 Phase 1c-β-2). -/
/-- A derivation either leaves the context alone, or it is a `bvar_type` that
consumes exactly one linear slot. -/
theorem HasType_ctx_step {Γ : TypEnv} {e : Expr} {τ : Morph.Core.Typ} {ctx ctx' : Morph.LinCtx}
    (h : HasType ctx Γ e τ ctx') :
    ctx' = ctx ∨ ∃ (n : Nat) (σ : Morph.Core.Typ),
      ctx[n]? = some (σ, Morph.Usage.zero) ∧ ctx' = Morph.LinCtx.consume ctx n := by
  induction h using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | bvar_type _ _ _ _ _ _ hEnt hEq => exact Or.inr ⟨_, _, hEnt, hEq⟩
  | _ => first
    | exact Or.inl rfl
    | assumption
    | trivial
    | (intros; trivial)

/-- With an empty input context nothing can be consumed, and the `binop_*`
rules pass through their first operand's output context, so every derivation
that starts at `[]` also ends at `[]`. This is what lets `progress` apply its
induction hypothesis to the *second* operand of a threaded `binop`
(ADR-010 Phase 1c-β-2). -/
theorem HasType_empty_ctx_out {Γ : TypEnv} {e : Expr} {τ : Typ} {ctx' : LinCtx}
    (h : HasType [] Γ e τ ctx') : ctx' = [] := by
  rcases HasType_ctx_step h with hEq | ⟨n, σ, hEnt, _⟩
  · exact hEq
  · exact absurd hEnt (by simp)

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

/-! ## Weakening at Arbitrary Entry Frames

`weakening_entries_at` inserts one arbitrary context entry below the frame
`A`, lifting the expression by one at depth `A.length`. The classical
`weakening` and `weakening_at_depth` are the `A = []` and
`A = xs.map (·, initialUsage ·)` instantiations. The proof needs the
`lam_type`/`lam_linear_type` cases (ADR-014): both arrows push `.many`
entries via `linPushMany`, so the single-use premise of the linear arrow must
survive weakening — which is exactly `countUses_liftUnder_below`. -/

mutual

theorem weakening_entries_at (A : List LinEntry) (ent : LinEntry) (ctx : LinCtx) (Γ : TypEnv)
    (e : Expr) (τ : Typ)
    (hE : HasType (A ++ ctx) Γ e τ (A ++ ctx)) :
    HasType (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) τ (A ++ (ent :: ctx)) := by
  match hE with
  | .bvar_type _ _ _ _ _ _ hEnt hEq =>
    exact absurd hEq.symm (LinCtx.consume_ne hEnt)
  | .bvar_type_many _ _ n τ hLen hEnt =>
    simp only [liftUnder]
    split
    · rename_i hNlt
      have hP1 : n < (LinCtx.types (A ++ (ent :: ctx))).length := by
        have h1 : (LinCtx.types (A ++ ctx)).length = (A ++ ctx).length := by
          simp [LinCtx.types]
        have h2 : (LinCtx.types (A ++ (ent :: ctx))).length = (A ++ (ent :: ctx)).length := by
          simp [LinCtx.types]
        rw [h1] at hLen
        rw [h2]
        have h3 : (A ++ ctx).length = A.length + ctx.length := List.length_append
        rw [h3] at hLen
        have h4 := @List.length_append LinEntry A (ent :: ctx)
        have h5 := @List.length_cons LinEntry ent ctx
        rw [h5] at h4
        omega
      refine HasType.bvar_type_many (A ++ (ent :: ctx)) Γ n τ hP1 ?_
      rw [List.getElem?_append_left (l₁ := A) (l₂ := ent :: ctx) (by simpa using hNlt)]
      rw [List.getElem?_append_left (l₁ := A) (l₂ := ctx) (by simpa using hNlt)] at hEnt
      exact hEnt
    · rename_i hNge
      have hNge' : n ≥ A.length := Nat.ge_of_not_lt hNge
      have hP1 : n + 1 < (LinCtx.types (A ++ (ent :: ctx))).length := by
        have h1 : (LinCtx.types (A ++ ctx)).length = (A ++ ctx).length := by
          simp [LinCtx.types]
        have h2 : (LinCtx.types (A ++ (ent :: ctx))).length = (A ++ (ent :: ctx)).length := by
          simp [LinCtx.types]
        rw [h1] at hLen
        rw [h2]
        have h3 : (A ++ ctx).length = A.length + ctx.length := List.length_append
        rw [h3] at hLen
        have h4 := @List.length_append LinEntry A (ent :: ctx)
        have h5 := @List.length_cons LinEntry ent ctx
        rw [h5] at h4
        omega
      refine HasType.bvar_type_many (A ++ (ent :: ctx)) Γ (n + 1) τ hP1 ?_
      rw [List.getElem?_append_right (l₁ := A) (l₂ := ent :: ctx)
            (by have := hLen; omega),
          show n + 1 - A.length = (n - A.length) + 1 from by omega,
          List.getElem?_cons_succ]
      rw [List.getElem?_append_right (l₁ := A) (l₂ := ctx) (by omega)] at hEnt
      exact hEnt
  | .fvar_type _ _ name τ hLookup =>
    simp only [liftUnder]
    exact HasType.fvar_type (A ++ (ent :: ctx)) Γ name τ hLookup
  | .lit_int _ _ n => simp only [liftUnder]; exact HasType.lit_int (A ++ (ent :: ctx)) Γ n
  | .lit_bool _ _ b => simp only [liftUnder]; exact HasType.lit_bool (A ++ (ent :: ctx)) Γ b
  | .lit_string _ _ s => simp only [liftUnder]; exact HasType.lit_string (A ++ (ent :: ctx)) Γ s
  | .lit_unit _ _ => simp only [liftUnder]; exact HasType.lit_unit (A ++ (ent :: ctx)) Γ
  | .lit_pointer _ _ p => simp only [liftUnder]; exact HasType.lit_pointer (A ++ (ent :: ctx)) Γ p
  | .unop_not _ _ e' hE' =>
    simp only [liftUnder]
    exact HasType.unop_not (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e')
      (weakening_entries_at A ent ctx Γ e' .boolType hE')
  | .unop_notb _ _ e' hE' =>
    simp only [liftUnder]
    exact HasType.unop_notb (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e')
      (weakening_entries_at A ent ctx Γ e' .intType hE')
  | .binop_arith _ _ op e1 e2 _ hArith hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_arith (A ++ (ent :: ctx)) Γ op (liftUnder A.length 1 e1)
      (liftUnder A.length 1 e2) (A ++ (ent :: ctx)) hArith
      (weakening_entries_at A ent ctx Γ e1 .intType hE1)
      (weakening_entries_at A ent ctx Γ e2 .intType hE2)
  | .binop_comp _ _ op e1 e2 _ hComp hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_comp (A ++ (ent :: ctx)) Γ op (liftUnder A.length 1 e1)
      (liftUnder A.length 1 e2) (A ++ (ent :: ctx)) hComp
      (weakening_entries_at A ent ctx Γ e1 .intType hE1)
      (weakening_entries_at A ent ctx Γ e2 .intType hE2)
  | .binop_logic _ _ op e1 e2 _ hLogic hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_logic (A ++ (ent :: ctx)) Γ op (liftUnder A.length 1 e1)
      (liftUnder A.length 1 e2) (A ++ (ent :: ctx)) hLogic
      (weakening_entries_at A ent ctx Γ e1 .boolType hE1)
      (weakening_entries_at A ent ctx Γ e2 .boolType hE2)
  | .binop_bitwise _ _ op e1 e2 _ hBit hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_bitwise (A ++ (ent :: ctx)) Γ op (liftUnder A.length 1 e1)
      (liftUnder A.length 1 e2) (A ++ (ent :: ctx)) hBit
      (weakening_entries_at A ent ctx Γ e1 .intType hE1)
      (weakening_entries_at A ent ctx Γ e2 .intType hE2)
  | .binop_ptr_arith _ _ op e1 e2 _ hPtr hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_arith (A ++ (ent :: ctx)) Γ op (liftUnder A.length 1 e1)
      (liftUnder A.length 1 e2) (A ++ (ent :: ctx)) hPtr
      (weakening_entries_at A ent ctx Γ e1 .pointerType hE1)
      (weakening_entries_at A ent ctx Γ e2 .intType hE2)
  | .binop_ptr_load _ _ e1 e2 _ hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_load (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e1)
      (liftUnder A.length 1 e2) (A ++ (ent :: ctx))
      (weakening_entries_at A ent ctx Γ e1 .pointerType hE1)
      (weakening_entries_at A ent ctx Γ e2 .unitType hE2)
  | .binop_ptr_store _ _ e1 e2 _ hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_ptr_store (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e1)
      (liftUnder A.length 1 e2) (A ++ (ent :: ctx))
      (weakening_entries_at A ent ctx Γ e1 .pointerType hE1)
      (weakening_entries_at A ent ctx Γ e2 .intType hE2)
  | .binop_string_concat _ _ op e1 e2 _ hOp hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.binop_string_concat (A ++ (ent :: ctx)) Γ op
      (liftUnder A.length 1 e1) (liftUnder A.length 1 e2) (A ++ (ent :: ctx))
      hOp
      (weakening_entries_at A ent ctx Γ e1 .stringType hE1)
      (weakening_entries_at A ent ctx Γ e2 .stringType hE2)
  | .lam_type _ _ n body paramTys retTy hLen hBody =>
    simp only [liftUnder]
    have hFrame : linPushMany (A ++ ctx) paramTys.reverse
        = (paramTys.reverse.map (fun t => (t, Morph.Usage.many)) ++ A) ++ ctx := by
      simp only [linPushMany, List.append_assoc]
    rw [hFrame] at hBody
    have hLenEq : (paramTys.reverse.map (fun t => (t, Morph.Usage.many)) ++ A).length
        = n + A.length := by
      have h1 := @List.length_append LinEntry
        (paramTys.reverse.map (fun t => (t, Morph.Usage.many))) A
      have h2 := @List.length_reverse Typ paramTys
      simp only [List.length_map, List.length_append] at h1 ⊢
      omega
    have hResult := weakening_entries_at
      (paramTys.reverse.map (fun t => (t, Morph.Usage.many)) ++ A) ent ctx Γ body retTy hBody
    rw [hLenEq, Nat.add_comm] at hResult
    refine HasType.lam_type (A ++ (ent :: ctx)) Γ n (liftUnder (A.length + n) 1 body)
      paramTys retTy hLen ?_
    have hFrame2 : linPushMany (A ++ (ent :: ctx)) paramTys.reverse
        = (paramTys.reverse.map (fun t => (t, Morph.Usage.many)) ++ A) ++ (ent :: ctx) := by
      simp only [linPushMany, List.append_assoc]
    rw [hFrame2]
    exact hResult
  | .lam_linear_type _ _ n body paramTys retTy hLen hBody hCount =>
    subst hLen
    simp only [liftUnder]
    have hFrame : linPushMany (A ++ ctx) paramTys.reverse
        = ((paramTys.reverse.map (fun t => (t, Morph.Usage.many))) ++ A) ++ ctx := by
      simp only [linPushMany, List.append_assoc]
    rw [hFrame] at hBody
    have hFrameLen : ((paramTys.reverse.map (fun t => (t, Morph.Usage.many))) ++ A).length
        = paramTys.length + A.length := by simp
    have hResult := weakening_entries_at
      ((paramTys.reverse.map (fun t => (t, Morph.Usage.many))) ++ A) ent ctx Γ body retTy hBody
    have hCount' : ∀ i, i < paramTys.length →
        Morph.Syntax.countUses
          (liftUnder ((paramTys.reverse.map (fun t => (t, Morph.Usage.many))) ++ A).length 1 body) i
          = 1 := by
      intro i hi
      rw [countUses_liftUnder_below _ 1 i body (by rw [hFrameLen]; omega)]
      exact hCount i hi
    rw [hFrameLen, Nat.add_comm] at hResult hCount'
    refine HasType.lam_linear_type (A ++ (ent :: ctx)) Γ paramTys.length
      (liftUnder (A.length + paramTys.length) 1 body) paramTys retTy rfl ?_ hCount'
    have hFrame2 : linPushMany (A ++ (ent :: ctx)) paramTys.reverse
        = ((paramTys.reverse.map (fun t => (t, Morph.Usage.many))) ++ A) ++ (ent :: ctx) := by
      simp only [linPushMany, List.append_assoc]
    rw [hFrame2]
    exact hResult
  | .app_type _ _ fn args τs τ hFn hArgs =>
    simp only [liftUnder]
    exact HasType.app_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 fn)
      (List.map (liftUnder A.length 1) args) τs τ
      (weakening_entries_at A ent ctx Γ fn (.functionType τs τ) hFn)
      (weakening_at_entries_all A ent ctx Γ args τs hArgs)
  | .app_linear_type _ _ fn args τs τ hFn hArgs =>
    simp only [liftUnder]
    exact HasType.app_linear_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 fn)
      (List.map (liftUnder A.length 1) args) τs τ
      (weakening_entries_at A ent ctx Γ fn (.linearFunctionType τs τ) hFn)
      (weakening_at_entries_all A ent ctx Γ args τs hArgs)
  | .let_type _ _ e1 e2 τ1 _ hE1 hE2 =>
    simp only [liftUnder]
    have hE2' : HasType (((τ1, Morph.Usage.many) :: A) ++ ctx) Γ e2 τ
        (((τ1, Morph.Usage.many) :: A) ++ ctx) := hE2
    exact HasType.let_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e1)
      (liftUnder (A.length + 1) 1 e2) τ1 τ
      (weakening_entries_at A ent ctx Γ e1 τ1 hE1)
      (weakening_entries_at ((τ1, Morph.Usage.many) :: A) ent ctx Γ e2 τ hE2')
  | .if_type _ _ c t f τ hC hT hF =>
    simp only [liftUnder]
    exact HasType.if_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 c)
      (liftUnder A.length 1 t) (liftUnder A.length 1 f) τ
      (weakening_entries_at A ent ctx Γ c .boolType hC)
      (weakening_entries_at A ent ctx Γ t τ hT)
      (weakening_entries_at A ent ctx Γ f τ hF)
  | .for_type _ _ s e body hS hE hBody =>
    simp only [liftUnder]
    have hBody' : HasTypeAll (((.intType, Morph.Usage.many) :: A) ++ ctx) Γ body [.unitType]
        (((.intType, Morph.Usage.many) :: A) ++ ctx) := hBody
    exact HasType.for_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 s)
      (liftUnder A.length 1 e) (List.map (liftUnder (A.length + 1) 1) body)
      (weakening_entries_at A ent ctx Γ s .intType hS)
      (weakening_entries_at A ent ctx Γ e .intType hE)
      (weakening_at_entries_all ((.intType, Morph.Usage.many) :: A) ent ctx Γ body
        [.unitType] hBody')
  | .block_type _ _ exprs τs τ hExprs =>
    simp only [liftUnder]
    exact HasType.block_type (A ++ (ent :: ctx)) Γ (List.map (liftUnder A.length 1) exprs) τs τ
      (weakening_at_entries_all A ent ctx Γ exprs (τs ++ [τ]) hExprs)
  | .lit_float _ _ w f => simp only [liftUnder]; exact HasType.lit_float (A ++ (ent :: ctx)) Γ w f
  | .lit_int_width _ _ w n => simp only [liftUnder]; exact HasType.lit_int_width (A ++ (ent :: ctx)) Γ w n
  | .lit_some _ _ v τ => simp only [liftUnder]; exact HasType.lit_some (A ++ (ent :: ctx)) Γ v τ
  | .lit_none _ _ τ => simp only [liftUnder]; exact HasType.lit_none (A ++ (ent :: ctx)) Γ τ
  | .lit_ok _ _ v τ_ok τ_err => simp only [liftUnder]; exact HasType.lit_ok (A ++ (ent :: ctx)) Γ v τ_ok τ_err
  | .lit_err _ _ v τ_err τ_ok => simp only [liftUnder]; exact HasType.lit_err (A ++ (ent :: ctx)) Γ v τ_err τ_ok
  | .pipe_type _ _ e f τ_arg τ hE hF =>
    simp only [liftUnder]
    exact HasType.pipe_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) (liftUnder A.length 1 f) τ_arg τ
      (weakening_entries_at A ent ctx Γ e τ_arg hE)
      (weakening_entries_at A ent ctx Γ f (.functionType [τ_arg] τ) hF)
  | .typeAsc_type _ _ e τ hE =>
    simp only [liftUnder]
    exact HasType.typeAsc_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) τ
      (weakening_entries_at A ent ctx Γ e τ hE)
  | .some_type _ _ e τ_inner hE =>
    simp only [liftUnder]
    exact HasType.some_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) τ_inner
      (weakening_entries_at A ent ctx Γ e τ_inner hE)
  | .none_type _ _ τ => simp only [liftUnder]; exact HasType.none_type (A ++ (ent :: ctx)) Γ τ
  | .ok_type _ _ e τ_ok τ_err hE =>
    simp only [liftUnder]
    exact HasType.ok_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) τ_ok τ_err
      (weakening_entries_at A ent ctx Γ e τ_ok hE)
  | .err_type _ _ e τ_err τ_ok hE =>
    simp only [liftUnder]
    exact HasType.err_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) τ_err τ_ok
      (weakening_entries_at A ent ctx Γ e τ_err hE)
  | .null_coalesce_type _ _ e1 e2 τ hE1 hE2 =>
    simp only [liftUnder]
    exact HasType.null_coalesce_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e1)
      (liftUnder A.length 1 e2) τ
      (weakening_entries_at A ent ctx Γ e1 (.optionType τ) hE1)
      (weakening_entries_at A ent ctx Γ e2 (.optionType τ) hE2)
  | .tuple_type _ _ elems tys hTys =>
    simp only [liftUnder]
    exact HasType.tuple_type (A ++ (ent :: ctx)) Γ (elems.map (liftUnder A.length 1)) tys
      (weakening_at_entries_all A ent ctx Γ elems tys hTys)
  | .field_access_type _ _ e fname sname fields τ hE hField =>
    simp only [liftUnder]
    exact HasType.field_access_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) fname sname fields τ
      (weakening_entries_at A ent ctx Γ e (.structType sname fields) hE)
      hField
  | .match_type _ _ scrut arms _ _ hScrut hArms =>
    simp only [liftUnder]
    exact HasType.match_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 scrut)
      (liftUnderArms A.length 1 arms) _ _
      (weakening_entries_at A ent ctx Γ scrut _ hScrut)
      (ArmsTyped_weakening_entries_at A ent hArms)
  | .arrayLit_type _ _ elems τ n hElems hLen hn =>
    simp only [liftUnder]
    have hLen' : n = (List.map (liftUnder A.length 1) elems).length := by
      rw [List.length_map]; exact hLen
    exact HasType.arrayLit_type (A ++ (ent :: ctx)) Γ (elems.map (liftUnder A.length 1)) τ n
      (weakening_at_entries_all A ent ctx Γ elems (List.replicate n τ) hElems) hLen' hn
  | .arrayIndex_type _ _ arr idx τ n hArr hIdx =>
    simp only [liftUnder]
    exact HasType.arrayIndex_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 arr)
      (liftUnder A.length 1 idx) τ n
      (weakening_entries_at A ent ctx Γ arr (.arrayType τ n) hArr)
      (weakening_entries_at A ent ctx Γ idx .intType hIdx)
  | .refCreate_type _ _ e cap τ hE =>
    simp only [liftUnder]
    exact HasType.refCreate_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) cap τ
      (weakening_entries_at A ent ctx Γ e τ hE)
  | .refLoad_type _ _ e cap τ hE =>
    simp only [liftUnder]
    exact HasType.refLoad_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) cap τ
      (weakening_entries_at A ent ctx Γ e (.refType cap τ) hE)
  | .refStore_type _ _ e v cap τ hE hV hCap =>
    simp only [liftUnder]
    exact HasType.refStore_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e)
      (liftUnder A.length 1 v) cap τ
      (weakening_entries_at A ent ctx Γ e (.refType cap τ) hE)
      (weakening_entries_at A ent ctx Γ v τ hV)
      hCap
  | .refFree_type _ _ e τ hE =>
    simp only [liftUnder]
    exact HasType.refFree_type (A ++ (ent :: ctx)) Γ (liftUnder A.length 1 e) τ
      (weakening_entries_at A ent ctx Γ e (.refType .iso τ) hE)

theorem weakening_at_entries_all (A : List LinEntry) (ent : LinEntry) (ctx : LinCtx) (Γ : TypEnv)
    (es : List Expr) (τs : List Typ)
    (h : HasTypeAll (A ++ ctx) Γ es τs (A ++ ctx)) :
    HasTypeAll (A ++ (ent :: ctx)) Γ (es.map (liftUnder A.length 1)) τs (A ++ (ent :: ctx)) := by
  match h with
  | .nil _ _ => exact HasTypeAll.nil _ _
  | .cons _ _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _ _
      (weakening_entries_at A ent ctx Γ e τ hE)
      (weakening_at_entries_all A ent ctx Γ es' τs' hRest)

theorem ArmsTyped_weakening_entries_at (A : List LinEntry) (ent : LinEntry)
    {ctx : LinCtx} {Γ : TypEnv} {τ_scrut : Typ}
    {arms : List (List String × Expr)} {τ_result : Typ}
    (h : ArmsTyped (A ++ ctx) Γ τ_scrut arms τ_result (A ++ ctx)) :
    ArmsTyped (A ++ (ent :: ctx)) Γ τ_scrut
      (liftUnderArms A.length 1 arms) τ_result
      (A ++ (ent :: ctx)) := by
  match h with
  | .nil _ _ _ => simp only [liftUnderArms]; constructor
  | .cons _ _ vars body rest _ _ hBody hRest =>
    simp only [liftUnderArms]
    constructor
    · have hFrame : linPushMany (A ++ ctx) (List.replicate vars.length τ_scrut)
        = (List.replicate vars.length τ_scrut).map (fun t => (t, Morph.Usage.many))
            ++ A ++ ctx := by
        simp only [linPushMany, List.append_assoc]
      rw [hFrame] at hBody
      have hResult := weakening_entries_at
        ((List.replicate vars.length τ_scrut).map (fun t => (t, Morph.Usage.many)) ++ A)
        ent ctx Γ body τ_result hBody
      simp only [List.length_map, List.length_append, List.length_replicate] at hResult
      rw [Nat.add_comm] at hResult
      show HasType
          (linPushMany (A ++ (ent :: ctx)) (List.replicate vars.length τ_scrut)) Γ
          (liftUnder (A.length + vars.length) 1 body) τ_result
          (linPushMany (A ++ (ent :: ctx)) (List.replicate vars.length τ_scrut))
      have hFrame2 : linPushMany (A ++ (ent :: ctx)) (List.replicate vars.length τ_scrut)
        = (List.replicate vars.length τ_scrut).map (fun t => (t, Morph.Usage.many))
            ++ A ++ (ent :: ctx) := by
        simp only [linPushMany, List.append_assoc]
      rw [hFrame2]
      exact hResult
    · exact ArmsTyped_weakening_entries_at A ent hRest

end

theorem weakening_at_depth (xs : List Typ) (ctx : LinCtx) (Γ : TypEnv)
    (e : Expr) (τ σ : Typ) :
    HasType (LinCtx.pushMany ctx xs) Γ e τ (LinCtx.pushMany ctx xs) →
      HasType (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (liftUnder xs.length 1 e) τ
        (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) := by
  intro h
  have hFrame : LinCtx.pushMany ctx xs
      = (xs.map (fun t => (t, LinCtx.initialUsage t))) ++ ctx := rfl
  rw [hFrame] at h
  have h'' := weakening_entries_at (xs.map (fun t => (t, LinCtx.initialUsage t)))
    (σ, LinCtx.initialUsage σ) ctx Γ e τ h
  rw [List.length_map] at h''
  exact h''

/-- `.many`-push version of `weakening_at_depth` (ADR-014 Loop 4): every push
installs `Usage.many` entries via `linPushMany`. -/
theorem weakening_at_depth_many (xs : List Typ) (ctx : LinCtx) (Γ : TypEnv)
    (e : Expr) (τ σ : Typ) :
    HasType (linPushMany ctx xs) Γ e τ (linPushMany ctx xs) →
      HasType (linPushMany ((σ, Morph.Usage.many) :: ctx) xs) Γ (liftUnder xs.length 1 e) τ
        (linPushMany ((σ, Morph.Usage.many) :: ctx) xs) := by
  intro h
  have hFrame : linPushMany ctx xs
      = (xs.map (fun t => (t, Morph.Usage.many))) ++ ctx := rfl
  rw [hFrame] at h
  have h'' := weakening_entries_at (xs.map (fun t => (t, Morph.Usage.many)))
    (σ, Morph.Usage.many) ctx Γ e τ h
  rw [List.length_map] at h''
  exact h''

theorem ArmsTyped_weakening_at_depth (xs : List Typ) (σ : Typ)
    {ctx : LinCtx} {Γ : TypEnv} {τ_scrut : Typ}
    {arms : List (List String × Expr)} {τ_result : Typ}
    (h : ArmsTyped (linPushMany ctx xs) Γ τ_scrut arms τ_result (linPushMany ctx xs)) :
    ArmsTyped (linPushMany ((σ, Morph.Usage.many) :: ctx) xs) Γ τ_scrut
      (liftUnderArms xs.length 1 arms) τ_result
      (linPushMany ((σ, Morph.Usage.many) :: ctx) xs) := by
  match h with
  | .nil _ _ _ => simp only [liftUnderArms]; constructor
  | .cons _ _ vars body rest _ _ hBody hRest =>
    simp only [liftUnderArms]
    constructor
    · have hBody' := weakening_at_depth_many (List.replicate vars.length τ_scrut ++ xs) ctx Γ
        body τ_result σ
        (by rw [← linPushMany_pushMany_append]; exact hBody)
      simp only [List.length_append, List.length_replicate] at hBody'
      rw [Nat.add_comm] at hBody'
      show HasType (linPushMany (linPushMany ((σ, Morph.Usage.many) :: ctx) xs)
          (List.replicate vars.length τ_scrut)) Γ
          (liftUnder (xs.length + vars.length) 1 body) τ_result
          (linPushMany (linPushMany ((σ, Morph.Usage.many) :: ctx) xs)
            (List.replicate vars.length τ_scrut))
      rw [linPushMany_pushMany_append]
      exact hBody'
    · exact ArmsTyped_weakening_at_depth xs σ hRest

theorem weakening_at_depth_all (xs : List Typ) (ctx : LinCtx) (Γ : TypEnv)
    (es : List Expr) (τs : List Typ) (σ : Typ)
    (h : HasTypeAll (LinCtx.pushMany ctx xs) Γ es τs (LinCtx.pushMany ctx xs)) :
    HasTypeAll (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) Γ (es.map (liftUnder xs.length 1)) τs
      (LinCtx.pushMany ((σ, LinCtx.initialUsage σ) :: ctx) xs) := by
  match h with
  | .nil _ _ => exact HasTypeAll.nil _ _
  | .cons _ _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _ _
      (weakening_at_depth xs ctx Γ e τ σ hE)
      (weakening_at_depth_all xs ctx Γ es' τs' σ hRest)


/-! ## Multi-Type Weakening at Depth

Weaken by prepending multiple types (`xs`) after a prefix in the context.
`HasType (linPushMany ctx pfx) Γ e τ → HasType (linPushMany (linPushMany ctx xs) pfx) Γ (liftUnder pfx.length xs.length e) τ`
Uses the `.many`-entry `weakening_at_depth_many` iterated `xs.length` times,
with `liftUnder_comp` to compose lifts. All pushes here are `linPushMany`
(ADR-014 Loop 4: every push installs `Usage.many`). -/

theorem weaken_many_at_depth (pfx xs : List Typ) (ctx : LinCtx) (Γ : TypEnv)
    (e : Expr) (τ : Typ)
    (hE : HasType (linPushMany ctx pfx) Γ e τ (linPushMany ctx pfx))
    : HasType (linPushMany (linPushMany ctx xs) pfx) Γ (liftUnder pfx.length xs.length e) τ
        (linPushMany (linPushMany ctx xs) pfx) := by
  induction xs generalizing ctx e with
  | nil =>
    simp only [linPushMany, List.map_nil, List.nil_append]
    simp only [List.length_nil]
    rw [liftUnder_zero_eq]
    exact hE
  | cons σ xs' ih =>
    have hStep1 := ih ctx e hE
    have hStep2 := weakening_at_depth_many pfx (linPushMany ctx xs') Γ
      (liftUnder pfx.length xs'.length e) τ σ hStep1
    rw [liftUnder_comp, Nat.add_comm 1 xs'.length] at hStep2
    exact hStep2

/-! ## ArmsTyped Weakening (simple) -/

theorem ArmsTyped_weakening (σ : Typ)
    {ctx : LinCtx} {Γ : TypEnv} {τ_scrut : Typ}
    {arms : List (List String × Expr)} {τ_result : Typ}
    (h : ArmsTyped ctx Γ τ_scrut arms τ_result ctx) :
    ArmsTyped ((σ, Morph.Usage.many) :: ctx) Γ τ_scrut (liftUnderArms 0 1 arms) τ_result
      ((σ, Morph.Usage.many) :: ctx) := by
  have h := ArmsTyped_weakening_at_depth [] σ h
  simp only [linPushMany, List.map_nil, List.nil_append, List.length_nil] at h
  exact h

theorem weakening (ctx : LinCtx) (Γ : TypEnv) (e : Expr) (τ : Typ) (σ : Typ) :
    HasType ctx Γ e τ ctx → HasType ((σ, LinCtx.initialUsage σ) :: ctx) Γ (lift 1 e) τ
      ((σ, LinCtx.initialUsage σ) :: ctx) := by
  intro h
  exact weakening_entries_at [] (σ, LinCtx.initialUsage σ) ctx Γ e τ h

theorem weakening_all (ctx : LinCtx) (Γ : TypEnv) (es : List Expr) (τs : List Typ)
    (σ : Typ) (h : HasTypeAll ctx Γ es τs ctx) : HasTypeAll ((σ, LinCtx.initialUsage σ) :: ctx) Γ
      (es.map (lift 1)) τs ((σ, LinCtx.initialUsage σ) :: ctx) := by
  match h with
  | HasTypeAll.nil _ _ => exact HasTypeAll.nil _ _
  | HasTypeAll.cons _ _ _ e es' τ τs' hE hRest =>
    exact HasTypeAll.cons _ _ _ _ _ _ _
      (weakening _ _ _ _ σ hE)
      (weakening_all _ _ _ _ σ hRest)


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
