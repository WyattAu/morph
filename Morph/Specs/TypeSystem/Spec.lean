/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax

namespace Morph.Specs.TypeSystem

/-!
# Type System Specification (de Bruijn)

This module formalizes the type system for the Morph language specification
using de Bruijn indices for bound variables.

## Key Design Decisions

- `HasType bvs Γ e τ`: The first parameter `bvs : List Typ` tracks the types
  of currently-bound de Bruijn indices. `bvs[0]` is the type of bvar 0, etc.
  ADR-014: the context is plain types — no `Usage`, no output context, and
  the context is never mutated during typing. Multiplicity lives on arrows
  (`linearFunctionType`): a linear parameter's exactly-once obligation is
  discharged at the binder by the executable `countUses` check
  (`lam_linear_type`), mirroring Linear Haskell.
- `TypEnv` maps free variable names to types (unchanged from named-variable system).
- `inferType bvs env e`: Executable type inference with bound-variable context.
- Weakening is trivial: just prepend a type to `bvs`.
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
## Linear Arrows (ADR-014)

`linearFunctionType ts ret` is a function type whose parameters are each used
exactly once. The typing context stays a plain `List Typ`: a binder (either
arrow kind) pushes its parameter types as ordinary types
(`paramTys.reverse ++ bvs`), and the exactly-once obligation for a linear
arrow is discharged *syntactically* by `countUses` (defined in
`Morph/Syntax.lean`) in the `lam_linear_type` rule — the same single-use check
Koka/Granule-style systems perform on the binder's body. There is no context
consumption anywhere in the judgment (ADR-014).
-/

/-!
## Decidable Equality for `Typ`

`Typ` is a *nested* inductive (its `List Typ` fields make the `induction`
tactic and the `DecidableEq` deriving handler inapplicable), so decidable
equality is built by hand: `eqTyp` is a plain structural comparison function
(recursive definitions over nested inductives compile fine — cf. `countUses`),
proven lawful against propositional `=` by induction on the size measure
`tS`/`tSl`/`tSlF`, and the `DecidableEq` instance is derived from it. This
instance is what lets the executable checker test annotation agreement
(`τ' = τ`) computably while keeping those tests provable.
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
                (ihT u v (by simp only [tS, tSl] at hn; omega)).mp h2]
          · intro h
            injection h with h1 h2
            simp only [eqTyp, Bool.and_eq_true]
            exact ⟨(ihT a b (by simp only [tS] at hn; omega)).mpr h1,
                   (ihT u v (by simp only [tS, tSl] at hn; omega)).mpr h2⟩
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

`inferType bvs env e` infers the type of expression `e` in:
- `bvs : List Typ` — types of bound de Bruijn indices (bvs[0] = type of bvar 0)
- `env : TypEnv` — types of free variables by name

Soundness against the declarative judgment is proven in
`Morph.Specs.TypeSystem.InferenceSound` (research program P13). The checker
is deliberately conservative where the judgment has no rule: `.loc` literals,
`.undef`, `ok`/`err` literals, `match_` and `refCast` all return `none`, and
the annotation-style rules (`typeAsc`, `refCreate`, `refStore`) check that the
annotation agrees with the inferred types.
-/

/-- Result-type dispatch for `binop`. -/
def binopResult (op : Morph.Core.Operator) (t1 t2 : Morph.Core.Typ) :
    Option Morph.Core.Typ :=
  match t1, t2 with
  | .intType, .intType =>
    match op with
    | .add | .sub | .mul | .div | .mod => some .intType
    | .eq | .neq | .lt | .leq | .gt | .geq => some .boolType
    | .andb | .orb | .xorb | .shl | .shr => some .intType
    | _ => none
  | .boolType, .boolType =>
    match op with
    | .and | .or => some .boolType
    | _ => none
  | .pointerType, .intType =>
    match op with
    | .ptrAdd | .ptrSub => some .pointerType
    | .ptrStore => some .unitType
    | _ => none
  | .pointerType, .unitType =>
    match op with
    | .ptrLoad => some .unitType
    | _ => none
  | .stringType, .stringType =>
    match op with
    | .add => some .stringType
    | _ => none
  | _, _ => none

mutual
def inferTypes (bvs : List Morph.Core.Typ) (env : TypEnv) : List Morph.Syntax.Expr -> Option (List Morph.Core.Typ)
  | [] => some []
  | e :: es =>
    match inferType bvs env e, inferTypes bvs env es with
    | some τ, some tys => some (τ :: tys)
    | _, _ => none
  termination_by es => sizeOf es

def inferType (bvs : List Morph.Core.Typ) (env : TypEnv) : Morph.Syntax.Expr -> Option Morph.Core.Typ
  | .bvar n => if h : n < bvs.length then some bvs[n] else none
  | .fvar name => lookupTyp env name
  | .lit (.int _) => some .intType
  | .lit (.bool _) => some .boolType
  | .lit (.string _) => some .stringType
  | .lit .unit => some .unitType
  | .lit (.pointer _) => some .pointerType
  | .lit (.float _) => some (.floatType .f64)
  | .lit .undef => none
  | .lit (.some v) =>
    match inferType bvs env (.lit v) with
    | some τ => some (.optionType τ)
    | none => none
  | .lit .none => none
  | .lit (.ok _) => none  -- no HasType rule for result value literals
  | .lit (.err _) => none
  | .lit (.tuple_ _) => none  -- no HasType rule for tuple value literals
  | .lit (.array_ _) => none  -- no HasType rule for array value literals
  | .lit (.loc _) => none     -- no HasType rule for location literals
  | .lit (.closure _ _) => none -- closures are MIR-only (ADR-012); no surface type yet
  | .unop op e =>
    match op with
    | .not =>
      match inferType bvs env e with
      | some .boolType => some .boolType
      | _ => none
    | .notb =>
      match inferType bvs env e with
      | some .intType => some .intType
      | _ => none
    | _ => none
  | .binop op e1 e2 =>
    match inferType bvs env e1 with
    | some t1 =>
      match inferType bvs env e2 with
      | some t2 => binopResult op t1 t2
      | none => none
    | none => none
  | .app fn args =>
    match inferType bvs env fn with
    | some (.functionType paramTys retTy) =>
      match inferTypes bvs env args with
      | some argTys => if argTys = paramTys then some retTy else none
      | none => none
    | some (.linearFunctionType paramTys retTy) =>
      match inferTypes bvs env args with
      | some argTys => if argTys = paramTys then some retTy else none
      | none => none
    | _ => none
  | .lam _ _ => none  -- Lambdas need annotations for synthesis
  | .let_ e1 e2 =>
    match inferType bvs env e1 with
    | some τ1 => inferType (τ1 :: bvs) env e2
    | none => none
  | .ifThenElse c t f =>
    match inferType bvs env c with
    | some .boolType =>
      match inferType bvs env t with
      | some typT =>
        match inferType bvs env f with
        | some typF => if typT = typF then some typT else none
        | none => none
      | none => none
    | _ => none
  | .forLoop s e body =>
    match inferType bvs env s with
    | some .intType =>
      match inferType bvs env e with
      | some .intType =>
        match inferTypes (.intType :: bvs) env body with
        | some [.unitType] => some .unitType
        | _ => none
      | _ => none
    | _ => none
  | .block exprs =>
    match inferTypes bvs env exprs with
    | some tys =>
      match tys.reverse with
      | τ :: _ => some τ
      | [] => none  -- `block_type` cannot derive an empty block
    | none => none
  | .match_ _ _ => none  -- match_ type inference is complex; typing via HasType.match_type
  | .field_ e name =>
    match inferType bvs env e with
    | some (.structType _ fields) =>
      match structFieldType fields name with
      | some τ => some τ
      | none => none
    | _ => none
  | .pipe e f =>
    match inferType bvs env e with
    | some τ_e =>
      match inferType bvs env f with
      | some (.functionType [τ_arg] τ_ret) =>
        if τ_e = τ_arg then some τ_ret else none
      | _ => none
    | none => none
  | .some_ e =>
    match inferType bvs env e with
    | some τ => some (.optionType τ)
    | none => none
  | .none_ => none
  | .ok_ _ => none
  | .err_ _ => none
  | .nullCoalesce e1 e2 =>
    match inferType bvs env e1 with
    | some (.optionType τ1) =>
      match inferType bvs env e2 with
      | some (.optionType τ2) =>
        if τ1 = τ2 then some (.optionType τ1) else none
      | _ => none
    | _ => none
  | .typeAsc e τ =>
    match inferType bvs env e with
    | some τ' => if τ' = τ then some τ else none
    | none => none
  | .tuple_ elems =>
    match inferTypes bvs env elems with
    | some tys => some (.tupleType tys)
    | none => none
  | .arrayLit elems =>
    match inferTypes bvs env elems with
    | some tys =>
      match tys.head? with
      | some τ =>
        if tys.all (fun t => decide (t = τ)) && elems.length > 0 then
          some (.arrayType τ elems.length)
        else none
      | none => none
    | none => none
  | .arrayIndex arr idx =>
    match inferType bvs env arr with
    | some (.arrayType τ _) =>
      match inferType bvs env idx with
      | some .intType => some τ
      | _ => none
    | _ => none
  | .refCreate e cap τ =>
    match inferType bvs env e with
    | some τ' => if τ' = τ then some (.refType cap τ) else none
    | none => none
  | .refLoad e =>
    match inferType bvs env e with
    | some (.refType _ τ) => some τ
    | _ => none
  | .refStore e v τ =>
    match inferType bvs env e with
    | some (.refType cap τ') =>
      if cap ≠ .val then
        if τ' = τ then
          match inferType bvs env v with
          | some τv => if τv = τ then some .unitType else none
          | none => none
        else none
      else none
    | _ => none
  | .refFree e =>
    match inferType bvs env e with
    | some (.refType cap _) => if cap = .iso then some .unitType else none
    | _ => none
  | .refCast _ _ => none  -- capability casts are store-typed only (ADR-010 amendment)
  termination_by e => sizeOf e
end

def typeCheck (bvs : List Morph.Core.Typ) (env : TypEnv) (e : Morph.Syntax.Expr) (expected : Morph.Core.Typ) : Prop :=
  inferType bvs env e = some expected

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

`HasType bvs Γ e τ`:
- `bvs : List Typ` — types of bound de Bruijn indices
  (bvs[0] = type of bvar 0, the most recent binder)
- `Γ : TypEnv` — types of free variables by name
- `e : Expr` — the expression
- `τ : Typ` — the inferred type

ADR-014: the context is plain types and is never mutated. Every binder rule
pushes its binder's types (`paramTys.reverse ++ bvs`, pattern variables
prepended, `let`/`for` single types); no rule consumes anything. Multiplicity
lives on arrows: `lam_linear_type` discharges the exactly-once obligation of a
`linearFunctionType` binder syntactically via `countUses` (Linear Haskell's
arrangement), while a plain `functionType` binder carries no obligation.
-/

mutual

inductive HasType : List Morph.Core.Typ → TypEnv → Morph.Syntax.Expr → Morph.Core.Typ → Prop where
  | bvar_type : ∀ bvs Γ n,
      (h : n < bvs.length) →
      HasType bvs Γ (.bvar n) bvs[n]
  | fvar_type : ∀ bvs Γ name τ,
      lookupTyp Γ name = some τ →
      HasType bvs Γ (.fvar name) τ
  | lit_int : ∀ bvs Γ n, HasType bvs Γ (.lit (.int n)) .intType
  | lit_bool : ∀ bvs Γ b, HasType bvs Γ (.lit (.bool b)) .boolType
  | lit_string : ∀ bvs Γ s, HasType bvs Γ (.lit (.string s)) .stringType
  | lit_unit : ∀ bvs Γ, HasType bvs Γ (.lit .unit) .unitType
  | lit_pointer : ∀ bvs Γ p, HasType bvs Γ (.lit (.pointer p)) .pointerType
  | lit_float : ∀ bvs Γ w f, HasType bvs Γ (.lit (.float f)) (.floatType w)
  | lit_int_width : ∀ bvs Γ w n, HasType bvs Γ (.lit (.int n)) (.intWidthType w)
  | lit_some : ∀ bvs Γ v τ, HasType bvs Γ (.lit (.some v)) (.optionType τ)
  | lit_none : ∀ bvs Γ τ, HasType bvs Γ (.lit .none) (.optionType τ)
  | lit_ok : ∀ bvs Γ v τ_ok τ_err, HasType bvs Γ (.lit (.ok v)) (.resultType τ_ok τ_err)
  | lit_err : ∀ bvs Γ v τ_err τ_ok, HasType bvs Γ (.lit (.err v)) (.resultType τ_ok τ_err)
  | unop_not : ∀ bvs Γ e,
      HasType bvs Γ e .boolType →
      HasType bvs Γ (.unop .not e) .boolType
  | unop_notb : ∀ bvs Γ e,
      HasType bvs Γ e .intType →
      HasType bvs Γ (.unop .notb e) .intType
  | binop_arith : ∀ bvs Γ op e1 e2,
      isArithOp op →
      HasType bvs Γ e1 .intType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop op e1 e2) .intType
  | binop_comp : ∀ bvs Γ op e1 e2,
      isCompOp op →
      HasType bvs Γ e1 .intType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop op e1 e2) .boolType
  | binop_logic : ∀ bvs Γ op e1 e2,
      isLogicOp op →
      HasType bvs Γ e1 .boolType → HasType bvs Γ e2 .boolType →
      HasType bvs Γ (.binop op e1 e2) .boolType
  | binop_bitwise : ∀ bvs Γ op e1 e2,
      isBitwiseOp op →
      HasType bvs Γ e1 .intType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop op e1 e2) .intType
  | binop_ptr_arith : ∀ bvs Γ op e1 e2,
      isPtrArithOp op →
      HasType bvs Γ e1 .pointerType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop op e1 e2) .pointerType
  | binop_ptr_load : ∀ bvs Γ e1 e2,
      HasType bvs Γ e1 .pointerType → HasType bvs Γ e2 .unitType →
      HasType bvs Γ (.binop .ptrLoad e1 e2) .unitType
  | binop_ptr_store : ∀ bvs Γ e1 e2,
      HasType bvs Γ e1 .pointerType → HasType bvs Γ e2 .intType →
      HasType bvs Γ (.binop .ptrStore e1 e2) .unitType
  | binop_string_concat : ∀ bvs Γ op e1 e2,
      op = .add →
      HasType bvs Γ e1 .stringType → HasType bvs Γ e2 .stringType →
      HasType bvs Γ (.binop op e1 e2) .stringType
  -- unrestricted arrow: parameters pushed as plain types, no obligations
  | lam_type : ∀ bvs Γ n body paramTys retTy,
      n = paramTys.length →
      HasType (paramTys.reverse ++ bvs) Γ body retTy →
      HasType bvs Γ (.lam n body) (.functionType paramTys retTy)
  | app_type : ∀ bvs Γ fn args τs τ,
      HasType bvs Γ fn (.functionType τs τ) →
      HasTypeAll bvs Γ args τs →
      HasType bvs Γ (.app fn args) τ
  -- linear arrow (ADR-014 stage 1): parameters pushed as plain types; the
  -- exactly-once obligation is discharged syntactically by `countUses`.
  | lam_linear_type : ∀ bvs Γ n body paramTys retTy,
      n = paramTys.length →
      HasType (paramTys.reverse ++ bvs) Γ body retTy →
      (∀ i, i < paramTys.length → Morph.Syntax.countUses body i = 1) →
      HasType bvs Γ (.lam n body) (.linearFunctionType paramTys retTy)
  | app_linear_type : ∀ bvs Γ fn args τs τ,
      HasType bvs Γ fn (.linearFunctionType τs τ) →
      HasTypeAll bvs Γ args τs →
      HasType bvs Γ (.app fn args) τ
  | let_type : ∀ bvs Γ e1 e2 τ1 τ2,
      HasType bvs Γ e1 τ1 →
      HasType (τ1 :: bvs) Γ e2 τ2 →
      HasType bvs Γ (.let_ e1 e2) τ2
  | if_type : ∀ bvs Γ c t f τ,
      HasType bvs Γ c .boolType →
      HasType bvs Γ t τ → HasType bvs Γ f τ →
      HasType bvs Γ (.ifThenElse c t f) τ
  | for_type : ∀ bvs Γ s e body,
      HasType bvs Γ s .intType → HasType bvs Γ e .intType →
      HasTypeAll (.intType :: bvs) Γ body [.unitType] →
      HasType bvs Γ (.forLoop s e body) .unitType
  | block_type : ∀ bvs Γ exprs τs τ,
      HasTypeAll bvs Γ exprs (τs ++ [τ]) →
      HasType bvs Γ (.block exprs) τ
  | pipe_type : ∀ bvs Γ e f τ_arg τ_ret,
      HasType bvs Γ e τ_arg →
      HasType bvs Γ f (.functionType [τ_arg] τ_ret) →
      HasType bvs Γ (.pipe e f) τ_ret
  | typeAsc_type : ∀ bvs Γ e τ,
      HasType bvs Γ e τ →
      HasType bvs Γ (.typeAsc e τ) τ
  | some_type : ∀ bvs Γ e τ_inner,
      HasType bvs Γ e τ_inner →
      HasType bvs Γ (.some_ e) (.optionType τ_inner)
  | none_type : ∀ bvs Γ τ,
      HasType bvs Γ .none_ (.optionType τ)
  | ok_type : ∀ bvs Γ e τ_ok τ_err,
      HasType bvs Γ e τ_ok →
      HasType bvs Γ (.ok_ e) (.resultType τ_ok τ_err)
  | err_type : ∀ bvs Γ e τ_err τ_ok,
      HasType bvs Γ e τ_err →
      HasType bvs Γ (.err_ e) (.resultType τ_ok τ_err)
  | null_coalesce_type : ∀ bvs Γ e1 e2 τ,
      HasType bvs Γ e1 (.optionType τ) →
      HasType bvs Γ e2 (.optionType τ) →
      HasType bvs Γ (.nullCoalesce e1 e2) (.optionType τ)
  | tuple_type : ∀ bvs Γ elems tys,
      HasTypeAll bvs Γ elems tys →
      HasType bvs Γ (.tuple_ elems) (.tupleType tys)
  | arrayLit_type : ∀ bvs Γ elems τ n,
      HasTypeAll bvs Γ elems (List.replicate n τ) →
      n = elems.length →
      n > 0 →
      HasType bvs Γ (.arrayLit elems) (.arrayType τ n)
  | arrayIndex_type : ∀ bvs Γ arr idx τ n,
      HasType bvs Γ arr (.arrayType τ n) →
      HasType bvs Γ idx .intType →
      HasType bvs Γ (.arrayIndex arr idx) τ
  -- Reference operations (storeless placeholders, ADR-010)
  | refCreate_type : ∀ bvs Γ e cap τ,
      HasType bvs Γ e τ →
      HasType bvs Γ (.refCreate e cap τ) (.refType cap τ)
  | refLoad_type : ∀ bvs Γ e cap τ,
      HasType bvs Γ e (.refType cap τ) →
      HasType bvs Γ (.refLoad e) τ
  | refStore_type : ∀ bvs Γ e v cap τ,
      HasType bvs Γ e (.refType cap τ) →
      HasType bvs Γ v τ →
      cap ≠ .val →  -- cannot store through immutable reference
      HasType bvs Γ (.refStore e v τ) .unitType
  | refFree_type : ∀ bvs Γ e τ,
      HasType bvs Γ e (.refType .iso τ) →
      HasType bvs Γ (.refFree e) .unitType
  | field_access_type : ∀ bvs Γ e fname sname fields τ,
      HasType bvs Γ e (.structType sname fields) →
      structFieldType fields fname = some τ →
      HasType bvs Γ (.field_ e fname) τ
  | match_type : ∀ bvs Γ scrut arms τ_scrut τ_result,
      HasType bvs Γ scrut τ_scrut →
      ArmsTyped bvs Γ τ_scrut arms τ_result →
      HasType bvs Γ (.match_ scrut arms) τ_result


inductive HasTypeAll : List Morph.Core.Typ → TypEnv → List Morph.Syntax.Expr → List Morph.Core.Typ → Prop where
  | nil : ∀ bvs Γ,
      HasTypeAll bvs Γ [] []
  | cons : ∀ bvs Γ e es τ τs,
      HasType bvs Γ e τ → HasTypeAll bvs Γ es τs →
      HasTypeAll bvs Γ (e :: es) (τ :: τs)

/-- `ArmsTyped bvs Γ τ_scrut arms τ_result`: every arm body is typable in the
    scrutinee context extended with its pattern variables. Arms share the same
    context — there is no merge operator (ADR-014). -/
inductive ArmsTyped : List Morph.Core.Typ → TypEnv → Morph.Core.Typ → List (List String × Morph.Syntax.Expr) → Morph.Core.Typ → Prop where
  | nil : ∀ bvs Γ τ_scrut,
      ArmsTyped bvs Γ τ_scrut [] .unitType
  | cons : ∀ bvs Γ vars body rest τ_scrut τ_result,
      HasType (List.replicate vars.length τ_scrut ++ bvs) Γ body τ_result →
      ArmsTyped bvs Γ τ_scrut rest τ_result →
      ArmsTyped bvs Γ τ_scrut ((vars, body) :: rest) τ_result

end

end Morph.Specs.TypeSystem
