/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.LinearContext

namespace Morph.Specs.TypeSystem

/-!
# Type System Specification (de Bruijn)

This module formalizes the type system for the Morph language specification
using de Bruijn indices for bound variables.

## Key Design Decisions

- `HasType ctx Γ e τ ctx'`: The first parameter `ctx : LinCtx` tracks the types
  and usages of currently-bound de Bruijn indices. `ctx.types[0]` is the
  type of bvar 0, etc. The last parameter `ctx'` is the context *after*
  typing `e`. In ADR-010 Phase 1c-β-2 only `bvar_type` (consuming a linear slot)
  and the `binop_*` rules (threading a mid context) change it; the rest still
  return `ctx` unchanged.
- `TypEnv` maps free variable names to types (unchanged from named-variable system).
- `inferType ctx env e`: Executable type inference with bound-variable context.
- Weakening is trivial: just prepend entries via `LinCtx.pushMany`.
- Substitution lemma is straightforward induction (no capture-avoidance needed).

## Overview

The TypeSystem module formalizes:
- **Type Environments:** Mapping variable names to types (for free variables)
- **Bound-variable context:** Stack of types for de Bruijn indices
- **Type Inference:** Computing types from expressions
- **Type Checking:** Verifying expressions against expected types
- **Type Well-Formedness:** Ensuring types are valid
- **Subtyping:** Type compatibility relationships
- **Type Safety:** Preservation of types under evaluation

-/

abbrev TypEnv := List (String × Morph.Core.Typ)

/-! ## Struct Field Type Lookup

Look up the type of a named field in a struct's field list.
Returns `none` if the field name is not found.
-/
def structFieldType (fields : List (String × Morph.Core.Typ)) (name : String) : Option Morph.Core.Typ :=
  (fields.find? (fun (n, _) => n == name)).map Prod.snd

def lookupTyp (env : TypEnv) (name : String) : Option Morph.Core.Typ :=
  env.find? (fun (n, _) => n == name) |>.map Prod.snd

def extendTypEnv (env : TypEnv) (name : String) (typ : Morph.Core.Typ) : TypEnv :=
  (name, typ) :: env

/-!
## Linear Arrows (ADR-014 stage 1)

`linPushMany ctx τs` pushes the parameter types `τs` as *unrestricted* entries
(`Usage.many`). A `linearFunctionType` binder never consumes: the exactly-once
obligation for each parameter is discharged syntactically by `countUses` in the
`lam_linear_type` rule, mirroring Linear Haskell's design where the context is
never mutated during typing. -/
def linPushMany (ctx : LinCtx) (τs : List Morph.Core.Typ) : LinCtx :=
  (τs.map (fun τ => (τ, Usage.many))) ++ ctx

theorem types_linPushMany (ctx : LinCtx) (τs : List Morph.Core.Typ) :
    LinCtx.types (linPushMany ctx τs) = τs ++ LinCtx.types ctx := by
  have hmap : Prod.fst ∘ (fun (τ : Morph.Core.Typ) => (τ, Usage.many)) = id := by
    funext x; rfl
  simp [linPushMany, LinCtx.types, hmap]

/-- The entry at index `k < τs.length` of `linPushMany ctx τs` is `(τs[k], .many)`. -/
theorem entry_linPushMany_mid (ctx : LinCtx) (τs : List Morph.Core.Typ) (k : Nat)
    (h : k < τs.length) :
    (linPushMany ctx τs)[k]? = some (τs[k]'h, Usage.many) := by
  simp only [linPushMany]
  rw [List.getElem?_append_left (by simpa using h)]
  simp

/-!
## Decidable Equality for `Typ`

`Typ` is a *nested* inductive (its `List Typ` fields make the `induction`
tactic and the `DecidableEq` deriving handler inapplicable), so decidable
equality is built by hand: `eqTyp` is a plain structural comparison function
(recursive definitions over nested inductives compile fine — cf. `countUses`),
proven lawful against propositional `=` by induction on the size measure
`tS`/`tSl`/`tSlF`, and the `DecidableEq` instance is derived from it. This
instance is what lets the executable checker test context-idempotence
(`cout = ctx`) and annotation agreement (`τ' = τ`) computably while keeping
those tests provable.
-/

mutual
def eqTyp : Morph.Core.Typ → Morph.Core.Typ → Bool
  | .intType, .intType => true
  | .boolType, .boolType => true
  | .stringType, .stringType => true
  | .pointerType, .pointerType => true
  | .unitType, .unitType => true
  | .neverType, .neverType => true
  | .arrayType t n, .arrayType t' n' => eqTyp t t' && n == n'
  | .functionType ts r, .functionType ts' r' => eqTyps ts ts' && eqTyp r r'
  | .linearFunctionType ts r, .linearFunctionType ts' r' => eqTyps ts ts' && eqTyp r r'
  | .intWidthType w, .intWidthType w' => decide (w = w')
  | .floatType w, .floatType w' => decide (w = w')
  | .refType c t, .refType c' t' => decide (c = c') && eqTyp t t'
  | .effectFunctionType ts r es, .effectFunctionType ts' r' es' =>
      eqTyps ts ts' && eqTyp r r' && decide (es = es')
  | .typeVar n, .typeVar n' => n == n'
  | .optionType t, .optionType t' => eqTyp t t'
  | .resultType t u, .resultType t' u' => eqTyp t t' && eqTyp u u'
  | .tupleType ts, .tupleType ts' => eqTyps ts ts'
  | .structType nm fs, .structType nm' fs' => nm == nm' && eqTypFields fs fs'
  | _, _ => false

def eqTyps : List Morph.Core.Typ → List Morph.Core.Typ → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => eqTyp t t' && eqTyps ts ts'
  | _, _ => false

def eqTypFields : List (String × Morph.Core.Typ) → List (String × Morph.Core.Typ) → Bool
  | [], [] => true
  | (n, t) :: fs, (n', t') :: fs' => n == n' && eqTyp t t' && eqTypFields fs fs'
  | _, _ => false
end

mutual
def tS : Morph.Core.Typ → Nat
  | .arrayType t _ => tS t + 1
  | .functionType ts r => tSl ts + tS r + 1
  | .linearFunctionType ts r => tSl ts + tS r + 1
  | .refType _ t => tS t + 1
  | .effectFunctionType ts r _ => tSl ts + tS r + 1
  | .optionType t => tS t + 1
  | .resultType t u => tS t + tS u + 1
  | .tupleType ts => tSl ts + 1
  | .structType _ fs => tSlF fs + 1
  | _ => 1
termination_by t => sizeOf t

def tSl : List Morph.Core.Typ → Nat
  | [] => 0
  | t :: ts => tS t + tSl ts + 1
termination_by ts => sizeOf ts

def tSlF : List (String × Morph.Core.Typ) → Nat
  | [] => 0
  | (_, t) :: fs => tS t + tSlF fs + 1
termination_by fs => sizeOf fs
end

set_option linter.unusedSimpArgs false in
/-- `eqTyp` is complete: it compares `true` exactly on equal types. -/
theorem eqTyp_complete : ∀ (n : Nat),
    (∀ a b : Morph.Core.Typ, tS a + tS b ≤ n → (eqTyp a b = true ↔ a = b)) ∧
    (∀ as bs : List Morph.Core.Typ, tSl as + tSl bs ≤ n → (eqTyps as bs = true ↔ as = bs)) ∧
    (∀ as bs : List (String × Morph.Core.Typ),
      tSlF as + tSlF bs ≤ n → (eqTypFields as bs = true ↔ as = bs)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro a b hn
      exfalso
      cases a <;> cases b <;> simp only [tS, tSl, tSlF] at hn <;> omega
    · intro as bs hn
      cases as with
      | nil =>
        cases bs with
        | nil => simp [eqTyps]
        | cons _ _ => simp [eqTyps]
      | cons _ _ =>
        cases bs with
        | nil => simp [eqTyps]
        | cons _ _ =>
          exfalso
          simp only [tS, tSl] at hn
          omega
    · intro as bs hn
      cases as with
      | nil =>
        cases bs with
        | nil => simp [eqTypFields]
        | cons _ _ => simp [eqTypFields]
      | cons p ps =>
        obtain ⟨_, t⟩ := p
        cases bs with
        | nil => simp [eqTypFields]
        | cons q qs =>
          obtain ⟨_, t'⟩ := q
          exfalso
          simp only [tS, tSlF] at hn
          omega
  | succ n ih =>
    obtain ⟨ihT, ihL, ihF⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro a b hn
      cases a with
      | intType =>
        cases b with
        | intType => simp [eqTyp]
        | _ => simp [eqTyp]
      | boolType =>
        cases b with
        | boolType => simp [eqTyp]
        | _ => simp [eqTyp]
      | stringType =>
        cases b with
        | stringType => simp [eqTyp]
        | _ => simp [eqTyp]
      | pointerType =>
        cases b with
        | pointerType => simp [eqTyp]
        | _ => simp [eqTyp]
      | unitType =>
        cases b with
        | unitType => simp [eqTyp]
        | _ => simp [eqTyp]
      | neverType =>
        cases b with
        | neverType => simp [eqTyp]
        | _ => simp [eqTyp]
      | arrayType a n0 =>
        cases b with
        | arrayType b n1 =>
          constructor
          · intro h
            simp only [eqTyp, Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨h1, h2⟩ := h
            rw [(ihT a b (by simp only [tS] at hn; omega)).mp h1, h2]
          · intro h
            injection h with h1 h2
            simp only [eqTyp, Bool.and_eq_true, beq_iff_eq]
            exact ⟨(ihT a b (by simp only [tS] at hn; omega)).mpr h1, h2⟩
        | _ => simp [eqTyp]
      | functionType as r =>
        cases b with
        | functionType bs s =>
          constructor
          · intro h
            simp only [eqTyp, Bool.and_eq_true] at h
            obtain ⟨h1, h2⟩ := h
            rw [(ihL as bs (by simp only [tS, tSl] at hn; omega)).mp h1,
                (ihT r s (by simp only [tS, tSl] at hn; omega)).mp h2]
          · intro h
            injection h with h1 h2
            simp only [eqTyp, Bool.and_eq_true]
            exact ⟨(ihL as bs (by simp only [tS, tSl] at hn; omega)).mpr h1,
                   (ihT r s (by simp only [tS, tSl] at hn; omega)).mpr h2⟩
        | _ => simp [eqTyp]
      | linearFunctionType as r =>
        cases b with
        | linearFunctionType bs s =>
          constructor
          · intro h
            simp only [eqTyp, Bool.and_eq_true] at h
            obtain ⟨h1, h2⟩ := h
            rw [(ihL as bs (by simp only [tS, tSl] at hn; omega)).mp h1,
                (ihT r s (by simp only [tS, tSl] at hn; omega)).mp h2]
          · intro h
            injection h with h1 h2
            simp only [eqTyp, Bool.and_eq_true]
            exact ⟨(ihL as bs (by simp only [tS, tSl] at hn; omega)).mpr h1,
                   (ihT r s (by simp only [tS, tSl] at hn; omega)).mpr h2⟩
        | _ => simp [eqTyp]
      | intWidthType w =>
        cases b with
        | intWidthType w' =>
          constructor
          · intro h
            simp only [eqTyp, decide_eq_true_eq] at h
            rw [h]
          · intro h
            injection h with h1
            simp only [eqTyp, decide_eq_true_eq]
            exact h1
        | _ => simp [eqTyp]
      | floatType w =>
        cases b with
        | floatType w' =>
          constructor
          · intro h
            simp only [eqTyp, decide_eq_true_eq] at h
            rw [h]
          · intro h
            injection h with h1
            simp only [eqTyp, decide_eq_true_eq]
            exact h1
        | _ => simp [eqTyp]
      | refType c a =>
        cases b with
        | refType c' b =>
          constructor
          · intro h
            simp only [eqTyp, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨h1, h2⟩ := h
            rw [h1, (ihT a b (by simp only [tS] at hn; omega)).mp h2]
          · intro h
            injection h with h1 h2
            simp only [eqTyp, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨h1, (ihT a b (by simp only [tS] at hn; omega)).mpr h2⟩
        | _ => simp [eqTyp]
      | effectFunctionType as r es =>
        cases b with
        | effectFunctionType bs s es' =>
          constructor
          · intro h
            simp only [eqTyp, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨h1, h2⟩, h3⟩ := h
            rw [(ihL as bs (by simp only [tS, tSl] at hn; omega)).mp h1,
                (ihT r s (by simp only [tS, tSl] at hn; omega)).mp h2, h3]
          · intro h
            injection h with h1 h2 h3
            simp only [eqTyp, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨(ihL as bs (by simp only [tS, tSl] at hn; omega)).mpr h1,
                   (ihT r s (by simp only [tS, tSl] at hn; omega)).mpr h2⟩, h3⟩
        | _ => simp [eqTyp]
      | typeVar n0 =>
        cases b with
        | typeVar n1 =>
          constructor
          · intro h
            simp only [eqTyp, beq_iff_eq] at h
            rw [h]
          · intro h
            injection h with h1
            simp only [eqTyp, beq_iff_eq]
            exact h1
        | _ => simp [eqTyp]
      | optionType a =>
        cases b with
        | optionType b =>
          constructor
          · intro h
            simp only [eqTyp] at h
            rw [(ihT a b (by simp only [tS] at hn; omega)).mp h]
          · intro h
            injection h with h1
            simp only [eqTyp]
            exact (ihT a b (by simp only [tS] at hn; omega)).mpr h1
        | _ => simp [eqTyp]
      | resultType a u =>
        cases b with
        | resultType b v =>
          constructor
          · intro h
            simp only [eqTyp, Bool.and_eq_true] at h
            obtain ⟨h1, h2⟩ := h
            rw [(ihT a b (by simp only [tS] at hn; omega)).mp h1,
                (ihT u v (by simp only [tS] at hn; omega)).mp h2]
          · intro h
            injection h with h1 h2
            simp only [eqTyp, Bool.and_eq_true]
            exact ⟨(ihT a b (by simp only [tS] at hn; omega)).mpr h1,
                   (ihT u v (by simp only [tS] at hn; omega)).mpr h2⟩
        | _ => simp [eqTyp]
      | tupleType as =>
        cases b with
        | tupleType bs =>
          constructor
          · intro h
            simp only [eqTyp] at h
            rw [(ihL as bs (by simp only [tS, tSl] at hn; omega)).mp h]
          · intro h
            injection h with h1
            simp only [eqTyp]
            exact (ihL as bs (by simp only [tS, tSl] at hn; omega)).mpr h1
        | _ => simp [eqTyp]
      | structType nm fs =>
        cases b with
        | structType nm' fs' =>
          constructor
          · intro h
            simp only [eqTyp, Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨h1, h2⟩ := h
            rw [h1, (ihF fs fs' (by simp only [tS, tSlF] at hn; omega)).mp h2]
          · intro h
            injection h with h1 h2
            simp only [eqTyp, Bool.and_eq_true, beq_iff_eq]
            exact ⟨h1, (ihF fs fs' (by simp only [tS, tSlF] at hn; omega)).mpr h2⟩
        | _ => simp [eqTyp]
    · intro as bs hn
      cases as with
      | nil =>
        cases bs with
        | nil => simp [eqTyps]
        | cons _ _ => simp [eqTyps]
      | cons a as' =>
        cases bs with
        | nil => simp [eqTyps]
        | cons b bs' =>
          constructor
          · intro h
            simp only [eqTyps, Bool.and_eq_true] at h
            obtain ⟨h1, h2⟩ := h
            rw [(ihT a b (by simp only [tS, tSl] at hn; omega)).mp h1,
                (ihL as' bs' (by simp only [tS, tSl] at hn; omega)).mp h2]
          · intro h
            injection h with h1 h2
            simp only [eqTyps, Bool.and_eq_true]
            exact ⟨(ihT a b (by simp only [tS, tSl] at hn; omega)).mpr h1,
                   (ihL as' bs' (by simp only [tS, tSl] at hn; omega)).mpr h2⟩
    · intro as bs hn
      cases as with
      | nil =>
        cases bs with
        | nil => simp [eqTypFields]
        | cons _ _ => simp [eqTypFields]
      | cons a as' =>
        obtain ⟨n0, t⟩ := a
        cases bs with
        | nil => simp [eqTypFields]
        | cons b bs' =>
          obtain ⟨n1, t'⟩ := b
          constructor
          · intro h
            simp only [eqTypFields, Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨⟨h1, h2⟩, h3⟩ := h
            rw [h1, (ihT t t' (by simp only [tS, tSlF] at hn; omega)).mp h2,
                (ihF as' bs' (by simp only [tS, tSlF] at hn; omega)).mp h3]
          · intro h
            injection h with h1 h2
            injection h1 with he1 he2
            simp only [eqTypFields, Bool.and_eq_true, beq_iff_eq]
            exact ⟨⟨he1, (ihT t t' (by simp only [tS, tSlF] at hn; omega)).mpr he2⟩,
                   (ihF as' bs' (by simp only [tS, tSlF] at hn; omega)).mpr h2⟩

theorem eqTyp_iff (a b : Morph.Core.Typ) : eqTyp a b = true ↔ a = b :=
  (eqTyp_complete (tS a + tS b)).1 a b (Nat.le_refl _)

theorem eqTyps_iff (as bs : List Morph.Core.Typ) : eqTyps as bs = true ↔ as = bs :=
  (eqTyp_complete (tSl as + tSl bs)).2.1 as bs (Nat.le_refl _)

theorem eqTypFields_iff (as bs : List (String × Morph.Core.Typ)) :
    eqTypFields as bs = true ↔ as = bs :=
  (eqTyp_complete (tSlF as + tSlF bs)).2.2 as bs (Nat.le_refl _)

/-- Decidable equality on `Typ`, derived from the lawful `eqTyp` comparison
(see the section docstring for why the deriving handler cannot do this). -/
instance : DecidableEq Morph.Core.Typ := fun a b =>
  if h : eqTyp a b = true then
    isTrue ((eqTyp_iff a b).mp h)
  else
    isFalse (fun he => h ((eqTyp_iff a b).mpr he))

/-!
## Type Well-Formedness
-/
inductive WellTyped : TypEnv -> Morph.Core.Typ -> Prop where
  | intType_wf : forall env, WellTyped env .intType
  | boolType_wf : forall env, WellTyped env .boolType
  | stringType_wf : forall env, WellTyped env .stringType
  | pointerType_wf : forall env, WellTyped env .pointerType
  | unitType_wf : forall env, WellTyped env .unitType
  | floatType_wf : forall env w, WellTyped env (.floatType w)
  | intWidthType_wf : forall env w, WellTyped env (.intWidthType w)
  | neverType_wf : forall env, WellTyped env .neverType
  | arrayType_wf : forall env elemTy sz,
      WellTyped env elemTy ->
      WellTyped env (.arrayType elemTy sz)
  | functionType_wf : forall env paramTys retTy,
      (forall paramTy, paramTy ∈ paramTys -> WellTyped env paramTy) ->
      WellTyped env retTy ->
      WellTyped env (.functionType paramTys retTy)
  | linearFunctionType_wf : forall env paramTys retTy,
      (forall paramTy, paramTy ∈ paramTys -> WellTyped env paramTy) ->
      WellTyped env retTy ->
      WellTyped env (.linearFunctionType paramTys retTy)
  | refType_wf : forall env cap innerTy,
      WellTyped env innerTy -> WellTyped env (.refType cap innerTy)
  | effectFunctionType_wf : forall env paramTys retTy effects,
      (forall paramTy, paramTy ∈ paramTys -> WellTyped env paramTy) ->
      WellTyped env retTy ->
      WellTyped env (.effectFunctionType paramTys retTy effects)
  | typeVar_wf : forall env n, WellTyped env (.typeVar n)
  | optionType_wf : forall env innerTy,
      WellTyped env innerTy → WellTyped env (.optionType innerTy)
  | resultType_wf : forall env okTy errTy,
      WellTyped env okTy → WellTyped env errTy → WellTyped env (.resultType okTy errTy)
  | tupleType_wf : forall env elemTys,
      (forall elemTy, elemTy ∈ elemTys → WellTyped env elemTy) →
      WellTyped env (.tupleType elemTys)
  | structType_wf : forall env name fields,
      (forall p, p ∈ fields → WellTyped env p.snd) →
      WellTyped env (.structType name fields)

/-!
## Type Inference (Executable)

`inferTypeC ctx env e` infers the type of expression `e` **and** returns the
linear context *after* typing `e`, mirroring the context-transformer judgment
`HasType ctx Γ e τ ctx'` rule by rule (research program P13, CakeML frontend-2
discipline; soundness is proven in `Morph.Specs.TypeSystem.InferenceSound`):

- `.bvar n` reads `ctx[n]?`: a `Usage.zero` slot is consumed
  (`HasType.bvar_type`), a `Usage.many` slot is left unchanged
  (`HasType.bvar_type_many`), a `Usage.one` slot is rejected (neither rule
  applies).
- Sub-expressions typed in sequence see the previous one's output context,
  exactly as the judgment threads it; rules whose premise demands
  input = output context (`binop_*` for the second operand, `let_type`,
  `if_type`, `app_type`, `block_type`, `tuple_type`, `arrayLit_type`,
  `HasTypeAll` lists, …) check that idempotence explicitly.
- Context extensions use the same pushes as the judgment: `let_type`'s
  `(τ, initialUsage τ)` push here, and — in `checkType` (`Morph.TypeChecker`)
  — `lam_type`'s `LinCtx.pushMany` and `lam_linear_type`'s `linPushMany`.

`inferType` is the type-only projection used by the rest of the code base;
`inferTypes`/`inferTypesC` are the list-level analogues.
-/

/-- Result-type dispatch for `binop`: `e1 : t1` was typed in the input context,
`e2 : t2` in `cmid` (= `e1`'s output context), and a well-typed `binop` leaves
the context at `cmid` (the `binop_*` rules). -/
def binopResult (op : Morph.Core.Operator) (t1 t2 : Morph.Core.Typ) (cmid : LinCtx) :
    Option (Morph.Core.Typ × LinCtx) :=
  match t1, t2 with
  | .intType, .intType =>
    match op with
    | .add | .sub | .mul | .div | .mod => some (.intType, cmid)
    | .eq | .neq | .lt | .leq | .gt | .geq => some (.boolType, cmid)
    | .andb | .orb | .xorb | .shl | .shr => some (.intType, cmid)
    | _ => none
  | .boolType, .boolType =>
    match op with
    | .and | .or => some (.boolType, cmid)
    | _ => none
  | .pointerType, .intType =>
    match op with
    | .ptrAdd | .ptrSub => some (.pointerType, cmid)
    | .ptrStore => some (.unitType, cmid)
    | _ => none
  | .pointerType, .unitType =>
    match op with
    | .ptrLoad => some (.unitType, cmid)
    | _ => none
  | .stringType, .stringType =>
    match op with
    | .add => some (.stringType, cmid)
    | _ => none
  | _, _ => none

mutual
def inferTypesC (ctx : LinCtx) (env : TypEnv) :
    List Morph.Syntax.Expr -> Option (List Morph.Core.Typ × LinCtx)
  | [] => some ([], ctx)
  | e :: es =>
    match inferTypeC ctx env e with
    | some (τ, cout) =>
      match inferTypesC cout env es with
      | some (tys, cout') => if cout' = cout then some (τ :: tys, cout) else none
      | none => none
    | none => none
  termination_by es => sizeOf es

def inferTypeC (ctx : LinCtx) (env : TypEnv) :
    Morph.Syntax.Expr -> Option (Morph.Core.Typ × LinCtx)
  | .bvar n =>
    match ctx[n]? with
    | some (τ, Usage.zero) => some (τ, LinCtx.consume ctx n)
    | some (τ, Usage.many) => some (τ, ctx)
    | _ => none
  | .fvar name => (lookupTyp env name).map (fun τ => (τ, ctx))
  | .lit (.int _) => some (.intType, ctx)
  | .lit (.bool _) => some (.boolType, ctx)
  | .lit (.string _) => some (.stringType, ctx)
  | .lit .unit => some (.unitType, ctx)
  | .lit (.pointer _) => some (.pointerType, ctx)
  | .lit (.float _) => some (.floatType .f64, ctx)
  | .lit .undef => none
  | .lit (.some v) =>
    match inferTypeC ctx env (.lit v) with
    | some (τ, _) => some (.optionType τ, ctx)
    | none => none
  | .lit .none => none
  | .lit (.ok _) => none
  | .lit (.err _) => none
  | .lit (.tuple_ _) => none  -- no HasType rule for tuple value literals
  | .lit (.array_ _) => none  -- no HasType rule for array value literals
  | .lit (.loc _) => none     -- no HasType rule for location literals
  | .unop op e =>
    match op with
    | .not =>
      match inferTypeC ctx env e with
      | some (.boolType, cout) => if cout = ctx then some (.boolType, ctx) else none
      | _ => none
    | .notb =>
      match inferTypeC ctx env e with
      | some (.intType, cout) => if cout = ctx then some (.intType, ctx) else none
      | _ => none
    | _ => none
  | .binop op e1 e2 =>
    match inferTypeC ctx env e1 with
    | some (t1, cmid) =>
      match inferTypeC cmid env e2 with
      | some (t2, c2) =>
        if c2 = cmid then binopResult op t1 t2 cmid else none
      | none => none
    | none => none
  | .app fn args =>
    match inferTypeC ctx env fn with
    | some (.functionType paramTys retTy, coutF) =>
      if coutF = ctx then
        match inferTypesC ctx env args with
        | some (argTys, coutA) =>
          if coutA = ctx then
            if argTys = paramTys then some (retTy, ctx) else none
          else none
        | none => none
      else none
    | some (.linearFunctionType paramTys retTy, coutF) =>
      if coutF = ctx then
        match inferTypesC ctx env args with
        | some (argTys, coutA) =>
          if coutA = ctx then
            if argTys = paramTys then some (retTy, ctx) else none
          else none
        | none => none
      else none
    | _ => none
  | .lam _ _ => none  -- Lambdas need annotations for synthesis
  | .let_ e1 e2 =>
    match inferTypeC ctx env e1 with
    | some (τ1, cout1) =>
      if cout1 = ctx then
        match inferTypeC ((τ1, LinCtx.initialUsage τ1) :: ctx) env e2 with
        | some (τ2, cout2) =>
          if cout2 = (τ1, LinCtx.initialUsage τ1) :: ctx then some (τ2, ctx) else none
        | none => none
      else none
    | none => none
  | .ifThenElse c t f =>
    match inferTypeC ctx env c with
    | some (.boolType, coutC) =>
      if coutC = ctx then
        match inferTypeC ctx env t with
        | some (typT, coutT) =>
          if coutT = ctx then
            match inferTypeC ctx env f with
            | some (typF, coutF) =>
              if coutF = ctx then
                if typT = typF then some (typT, ctx) else none
              else none
            | none => none
          else none
        | none => none
      else none
    | _ => none
  | .forLoop s e body =>
    match inferTypeC ctx env s with
    | some (.intType, coutS) =>
      if coutS = ctx then
        match inferTypeC ctx env e with
        | some (.intType, coutE) =>
          if coutE = ctx then
            match inferTypesC ((.intType, LinCtx.initialUsage .intType) :: ctx) env body with
            | some ([.unitType], coutB) =>
              if coutB = (.intType, LinCtx.initialUsage .intType) :: ctx then
                some (.unitType, ctx)
              else none
            | _ => none
          else none
        | _ => none
      else none
    | _ => none
  | .block exprs =>
    match inferTypesC ctx env exprs with
    | some (tys, cout) =>
      if cout = ctx then
        match tys.reverse with
        | τ :: _ => some (τ, ctx)
        | [] => none
      else none
    | none => none
  | .match_ _ _ => none  -- match_ type inference is complex; typing via HasType.match_type
  | .field_ e name =>
    match inferTypeC ctx env e with
    | some (.structType _ fields, cout) =>
      if cout = ctx then
        match structFieldType fields name with
        | some τ => some (τ, ctx)
        | none => none
      else none
    | _ => none
  | .pipe e f =>
    match inferTypeC ctx env e with
    | some (τ_e, coutE) =>
      if coutE = ctx then
        match inferTypeC ctx env f with
        | some (.functionType [τ_arg] τ_ret, coutF) =>
          if coutF = ctx then
            if τ_e = τ_arg then some (τ_ret, ctx) else none
          else none
        | _ => none
      else none
    | none => none
  | .some_ e =>
    match inferTypeC ctx env e with
    | some (τ, cout) => if cout = ctx then some (.optionType τ, ctx) else none
    | none => none
  | .none_ => none
  | .ok_ _ => none
  | .err_ _ => none
  | .nullCoalesce e1 e2 =>
    match inferTypeC ctx env e1 with
    | some (.optionType τ1, cout1) =>
      if cout1 = ctx then
        match inferTypeC ctx env e2 with
        | some (.optionType τ2, cout2) =>
          if cout2 = ctx then
            if τ1 = τ2 then some (.optionType τ1, ctx) else none
          else none
        | _ => none
      else none
    | _ => none
  | .typeAsc e τ =>
    match inferTypeC ctx env e with
    | some (τ', cout) =>
      if cout = ctx then
        if τ' = τ then some (τ, ctx) else none
      else none
    | none => none
  | .tuple_ elems =>
    match inferTypesC ctx env elems with
    | some (tys, cout) =>
      if cout = ctx then some (.tupleType tys, ctx) else none
    | none => none
  | .arrayLit elems =>
    match inferTypesC ctx env elems with
    | some (tys, cout) =>
      if cout = ctx then
        match tys.head? with
        | some τ =>
          if tys.all (fun t => decide (t = τ)) && elems.length > 0 then
            some (.arrayType τ elems.length, ctx)
          else none
        | none => none
      else none
    | none => none
  | .arrayIndex arr idx =>
    match inferTypeC ctx env arr with
    | some (.arrayType τ _, coutA) =>
      if coutA = ctx then
        match inferTypeC ctx env idx with
        | some (.intType, coutI) =>
          if coutI = ctx then some (τ, ctx) else none
        | _ => none
      else none
    | _ => none
  | .refCreate e cap τ =>
    match inferTypeC ctx env e with
    | some (τ', cout) =>
      if cout = ctx then
        if τ' = τ then some (.refType cap τ, ctx) else none
      else none
    | none => none
  | .refLoad e =>
    match inferTypeC ctx env e with
    | some (.refType _ τ, cout) =>
      if cout = ctx then some (τ, ctx) else none
    | _ => none
  | .refStore e v τ =>
    match inferTypeC ctx env e with
    | some (.refType cap τ', cout) =>
      if cout = ctx then
        if cap ≠ .val then
          if τ' = τ then
            match inferTypeC ctx env v with
            | some (τv, coutV) =>
              if coutV = ctx then
                if τv = τ then some (.unitType, ctx) else none
              else none
            | none => none
          else none
        else none
      else none
    | _ => none
  | .refFree e =>
    match inferTypeC ctx env e with
    | some (.refType cap _, cout) =>
      if cout = ctx then
        if cap = .iso then some (.unitType, ctx) else none
      else none
    | _ => none
  | .refCast _ _ => none  -- capability casts are store-typed only (ADR-010 amendment)
  termination_by e => sizeOf e
end

/-- Type-only projection of `inferTypeC` (the output context is dropped). -/
def inferType (ctx : LinCtx) (env : TypEnv) : Morph.Syntax.Expr -> Option Morph.Core.Typ :=
  fun e => (inferTypeC ctx env e).map Prod.fst

/-- Type-only projection of `inferTypesC`. -/
def inferTypes (ctx : LinCtx) (env : TypEnv) :
    List Morph.Syntax.Expr -> Option (List Morph.Core.Typ) :=
  fun es => (inferTypesC ctx env es).map Prod.fst

def typeCheck (ctx : LinCtx) (env : TypEnv) (e : Morph.Syntax.Expr) (expected : Morph.Core.Typ) : Prop :=
  inferType ctx env e = some expected

/-!
## Subtyping
-/
inductive Subtype : Morph.Core.Typ -> Morph.Core.Typ -> Prop where
  | refl : forall typ, Subtype typ typ
  | trans : forall typ1 typ2 typ3,
      Subtype typ1 typ2 ->
      Subtype typ2 typ3 ->
      Subtype typ1 typ3

/-! ## Operator Classifications -/

def isArithOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .add | .sub | .mul | .div | .mod => True
  | _ => False

def isCompOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .eq | .neq | .lt | .leq | .gt | .geq => True
  | _ => False

def isLogicOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .and | .or => True
  | _ => False

def isBitwiseOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .andb | .orb | .xorb | .shl | .shr => True
  | _ => False

def isPtrArithOp (op : Morph.Core.Operator) : Prop :=
  match op with
  | .ptrAdd | .ptrSub => True
  | _ => False

/-! ## Typing Judgments

`HasType ctx Γ e τ ctx'`:
- `ctx : LinCtx` — linear context of bound de Bruijn indices
  (ctx.types[0] = type of bvar 0, the most recent binder)
- `Γ : TypEnv` — types of free variables by name
- `e : Expr` — the expression
- `τ : Typ` — the inferred type
- `ctx' : LinCtx` — the linear context *after* typing `e` (ADR-010)

The judgment is a *state transformer on contexts*: it consumes the input
context `ctx` and produces the output context `ctx'`. Phase 1c-β-1 only installed
the plumbing (every rule returned the context it was given unchanged).

Phase 1c-β-2 (this increment) makes `Usage` matter in exactly two places, and
is deliberately partial elsewhere:
- `bvar_type` reads a linear slot (`ctx[n] = some (τ, .zero)`) and *consumes* it:
  its output context is `LinCtx.consume ctx n` (slot `n` advances to `.one`).
  `bvar_type_many` reads an unrestricted slot (`ctx[n] = some (τ, .many)`) and
  leaves the context unchanged.
- the `binop_*` rules *thread* the context: the second operand is typed in the
  first operand's **output** context, and the rule's own output context is that
  same mid context. This matches `HasTypeAll.cons`.

Every other rule still passes its input context through unchanged. That is
inconsistent with the consuming `bvar_type` but sound, and it is temporary: later
phases thread the remaining rules and merge contexts at branching points.
-/

mutual

inductive HasType : LinCtx → TypEnv → Morph.Syntax.Expr → Morph.Core.Typ → LinCtx → Prop where
  -- linear binding: consuming it advances the slot to .one
  | bvar_type : ∀ ctx Γ n τ (ctx' : LinCtx),
      (h : n < (ctx.types).length) →
      ctx[n]? = some (τ, Usage.zero) →
      ctx' = LinCtx.consume ctx n →
      HasType ctx Γ (.bvar n) τ ctx'
  -- unrestricted binding: available any number of times
  | bvar_type_many : ∀ ctx Γ n τ,
      (h : n < (ctx.types).length) →
      ctx[n]? = some (τ, Usage.many) →
      HasType ctx Γ (.bvar n) τ ctx
  | fvar_type : ∀ ctx Γ name τ,
      lookupTyp Γ name = some τ →
      HasType ctx Γ (.fvar name) τ ctx
  | lit_int : ∀ ctx Γ n, HasType ctx Γ (.lit (.int n)) .intType ctx
  | lit_bool : ∀ ctx Γ b, HasType ctx Γ (.lit (.bool b)) .boolType ctx
  | lit_string : ∀ ctx Γ s, HasType ctx Γ (.lit (.string s)) .stringType ctx
  | lit_unit : ∀ ctx Γ, HasType ctx Γ (.lit .unit) .unitType ctx
  | lit_pointer : ∀ ctx Γ p, HasType ctx Γ (.lit (.pointer p)) .pointerType ctx
  | lit_float : ∀ ctx Γ w f, HasType ctx Γ (.lit (.float f)) (.floatType w) ctx
  | lit_int_width : ∀ ctx Γ w n, HasType ctx Γ (.lit (.int n)) (.intWidthType w) ctx
  | lit_some : ∀ ctx Γ v τ, HasType ctx Γ (.lit (.some v)) (.optionType τ) ctx
  | lit_none : ∀ ctx Γ τ, HasType ctx Γ (.lit .none) (.optionType τ) ctx
  | lit_ok : ∀ ctx Γ v τ_ok τ_err, HasType ctx Γ (.lit (.ok v)) (.resultType τ_ok τ_err) ctx
  | lit_err : ∀ ctx Γ v τ_err τ_ok, HasType ctx Γ (.lit (.err v)) (.resultType τ_ok τ_err) ctx
  | unop_not : ∀ ctx Γ e,
      HasType ctx Γ e .boolType ctx →
      HasType ctx Γ (.unop .not e) .boolType ctx
  | unop_notb : ∀ ctx Γ e,
      HasType ctx Γ e .intType ctx →
      HasType ctx Γ (.unop .notb e) .intType ctx
  | binop_arith : ∀ ctx Γ op e1 e2 cmid,
      isArithOp op →
      HasType ctx Γ e1 .intType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop op e1 e2) .intType cmid
  | binop_comp : ∀ ctx Γ op e1 e2 cmid,
      isCompOp op →
      HasType ctx Γ e1 .intType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop op e1 e2) .boolType cmid
  | binop_logic : ∀ ctx Γ op e1 e2 cmid,
      isLogicOp op →
      HasType ctx Γ e1 .boolType cmid →
      HasType cmid Γ e2 .boolType cmid →
      HasType ctx Γ (.binop op e1 e2) .boolType cmid
  | binop_bitwise : ∀ ctx Γ op e1 e2 cmid,
      isBitwiseOp op →
      HasType ctx Γ e1 .intType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop op e1 e2) .intType cmid
  | binop_ptr_arith : ∀ ctx Γ op e1 e2 cmid,
      isPtrArithOp op →
      HasType ctx Γ e1 .pointerType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop op e1 e2) .pointerType cmid
  | binop_ptr_load : ∀ ctx Γ e1 e2 cmid,
      HasType ctx Γ e1 .pointerType cmid →
      HasType cmid Γ e2 .unitType cmid →
      HasType ctx Γ (.binop .ptrLoad e1 e2) .unitType cmid
  | binop_ptr_store : ∀ ctx Γ e1 e2 cmid,
      HasType ctx Γ e1 .pointerType cmid →
      HasType cmid Γ e2 .intType cmid →
      HasType ctx Γ (.binop .ptrStore e1 e2) .unitType cmid
  | binop_string_concat : ∀ ctx Γ op e1 e2 cmid,
      op = .add →
      HasType ctx Γ e1 .stringType cmid →
      HasType cmid Γ e2 .stringType cmid →
      HasType ctx Γ (.binop op e1 e2) .stringType cmid
  | lam_type : ∀ ctx Γ n body paramTys retTy,
      n = paramTys.length →
      HasType (LinCtx.pushMany ctx paramTys.reverse) Γ body retTy
          (LinCtx.pushMany ctx paramTys.reverse) →
      HasType ctx Γ (.lam n body) (.functionType paramTys retTy) ctx
  | app_type : ∀ ctx Γ fn args τs τ,
      HasType ctx Γ fn (.functionType τs τ) ctx →
      HasTypeAll ctx Γ args τs ctx →
      HasType ctx Γ (.app fn args) τ ctx
  -- linear arrow (ADR-014 stage 1): parameters are pushed as unrestricted
  -- entries (no consumption); the exactly-once obligation is discharged
  -- syntactically by `countUses`.
  | lam_linear_type : ∀ ctx Γ n body paramTys retTy,
      n = paramTys.length →
      HasType (linPushMany ctx paramTys.reverse) Γ body retTy
          (linPushMany ctx paramTys.reverse) →
      (∀ i, i < paramTys.length → Morph.Syntax.countUses body i = 1) →
      HasType ctx Γ (.lam n body) (.linearFunctionType paramTys retTy) ctx
  | app_linear_type : ∀ ctx Γ fn args τs τ,
      HasType ctx Γ fn (.linearFunctionType τs τ) ctx →
      HasTypeAll ctx Γ args τs ctx →
      HasType ctx Γ (.app fn args) τ ctx
  | let_type : ∀ ctx Γ e1 e2 τ1 τ2,
      HasType ctx Γ e1 τ1 ctx →
      HasType ((τ1, LinCtx.initialUsage τ1) :: ctx) Γ e2 τ2
          ((τ1, LinCtx.initialUsage τ1) :: ctx) →
      HasType ctx Γ (.let_ e1 e2) τ2 ctx
  | if_type : ∀ ctx Γ c t f τ,
      HasType ctx Γ c .boolType ctx →
      HasType ctx Γ t τ ctx → HasType ctx Γ f τ ctx →
      HasType ctx Γ (.ifThenElse c t f) τ ctx
  | for_type : ∀ ctx Γ s e body,
      HasType ctx Γ s .intType ctx → HasType ctx Γ e .intType ctx →
      HasTypeAll ((.intType, LinCtx.initialUsage .intType) :: ctx) Γ body [.unitType]
          ((.intType, LinCtx.initialUsage .intType) :: ctx) →
      HasType ctx Γ (.forLoop s e body) .unitType ctx
  | block_type : ∀ ctx Γ exprs τs τ,
      HasTypeAll ctx Γ exprs (τs ++ [τ]) ctx →
      HasType ctx Γ (.block exprs) τ ctx
  | pipe_type : ∀ ctx Γ e f τ_arg τ_ret,
      HasType ctx Γ e τ_arg ctx →
      HasType ctx Γ f (.functionType [τ_arg] τ_ret) ctx →
      HasType ctx Γ (.pipe e f) τ_ret ctx
  | typeAsc_type : ∀ ctx Γ e τ,
      HasType ctx Γ e τ ctx →
      HasType ctx Γ (.typeAsc e τ) τ ctx
  | some_type : ∀ ctx Γ e τ_inner,
      HasType ctx Γ e τ_inner ctx →
      HasType ctx Γ (.some_ e) (.optionType τ_inner) ctx
  | none_type : ∀ ctx Γ τ,
      HasType ctx Γ .none_ (.optionType τ) ctx
  | ok_type : ∀ ctx Γ e τ_ok τ_err,
      HasType ctx Γ e τ_ok ctx →
      HasType ctx Γ (.ok_ e) (.resultType τ_ok τ_err) ctx
  | err_type : ∀ ctx Γ e τ_err τ_ok,
      HasType ctx Γ e τ_err ctx →
      HasType ctx Γ (.err_ e) (.resultType τ_ok τ_err) ctx
  | null_coalesce_type : ∀ ctx Γ e1 e2 τ,
      HasType ctx Γ e1 (.optionType τ) ctx →
      HasType ctx Γ e2 (.optionType τ) ctx →
      HasType ctx Γ (.nullCoalesce e1 e2) (.optionType τ) ctx
  | tuple_type : ∀ ctx Γ elems tys,
      HasTypeAll ctx Γ elems tys ctx →
      HasType ctx Γ (.tuple_ elems) (.tupleType tys) ctx
  | arrayLit_type : ∀ ctx Γ elems τ n,
      HasTypeAll ctx Γ elems (List.replicate n τ) ctx →
      n = elems.length →
      n > 0 →
      HasType ctx Γ (.arrayLit elems) (.arrayType τ n) ctx
  | arrayIndex_type : ∀ ctx Γ arr idx τ n,
      HasType ctx Γ arr (.arrayType τ n) ctx →
      HasType ctx Γ idx .intType ctx →
      HasType ctx Γ (.arrayIndex arr idx) τ ctx
  -- Reference operations (storeless placeholders, ADR-010)
  | refCreate_type : ∀ ctx Γ e cap τ,
      HasType ctx Γ e τ ctx →
      HasType ctx Γ (.refCreate e cap τ) (.refType cap τ) ctx
  | refLoad_type : ∀ ctx Γ e cap τ,
      HasType ctx Γ e (.refType cap τ) ctx →
      HasType ctx Γ (.refLoad e) τ ctx
  | refStore_type : ∀ ctx Γ e v cap τ,
      HasType ctx Γ e (.refType cap τ) ctx →
      HasType ctx Γ v τ ctx →
      cap ≠ .val →  -- cannot store through immutable reference
      HasType ctx Γ (.refStore e v τ) .unitType ctx
  | refFree_type : ∀ ctx Γ e τ,
      HasType ctx Γ e (.refType .iso τ) ctx →
      HasType ctx Γ (.refFree e) .unitType ctx
  | field_access_type : ∀ ctx Γ e fname sname fields τ,
      HasType ctx Γ e (.structType sname fields) ctx →
      structFieldType fields fname = some τ →
      HasType ctx Γ (.field_ e fname) τ ctx
  | match_type : ∀ ctx Γ scrut arms τ_scrut τ_result,
      HasType ctx Γ scrut τ_scrut ctx →
      ArmsTyped ctx Γ τ_scrut arms τ_result ctx →
      HasType ctx Γ (.match_ scrut arms) τ_result ctx

/-- `HasTypeAll ctx Γ es τs ctx'`: a list is typable element by element, threading
    the context: each element consumes what it needs and hands the resulting
    context to the next one, with a single output context for the whole list. -/
inductive HasTypeAll : LinCtx → TypEnv → List Morph.Syntax.Expr → List Morph.Core.Typ → LinCtx → Prop where
  | nil : ∀ ctx Γ,
      HasTypeAll ctx Γ [] [] ctx
  | cons : ∀ ctx Γ cout e es τ τs,
      HasType ctx Γ e τ cout → HasTypeAll cout Γ es τs cout →
      HasTypeAll ctx Γ (e :: es) (τ :: τs) cout

/-- `ArmsTyped ctx Γ τ_scrut arms τ_result ctx'`: every arm body is typable in the
    scrutinee context extended with its pattern variables.

    Phase 1c-β-1: arms do not consume anything, so all arms keep the same
    context and the arms are *not* merged — a later phase (1c-β-2) will thread
    each arm's output context and merge them pointwise. -/
inductive ArmsTyped : LinCtx → TypEnv → Morph.Core.Typ → List (List String × Morph.Syntax.Expr) → Morph.Core.Typ → LinCtx → Prop where
  | nil : ∀ ctx Γ τ_scrut,
      ArmsTyped ctx Γ τ_scrut [] .unitType ctx
  | cons : ∀ ctx Γ vars body rest τ_scrut τ_result,
      HasType (LinCtx.pushMany ctx (List.replicate vars.length τ_scrut)) Γ body τ_result
          (LinCtx.pushMany ctx (List.replicate vars.length τ_scrut)) →
      ArmsTyped ctx Γ τ_scrut rest τ_result ctx →
      ArmsTyped ctx Γ τ_scrut ((vars, body) :: rest) τ_result ctx

end

end Morph.Specs.TypeSystem
