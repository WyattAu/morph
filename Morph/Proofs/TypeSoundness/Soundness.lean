/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Store
import Morph.Specs.TypeSystem.Spec
import Morph.Proofs.TypeSoundness.Progress
import Morph.Proofs.TypeSoundness.Preservation

namespace Morph.Proofs.TypeSoundness

open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Morph.Specs.TypeSystem

/-! # Type Safety (Soundness)

Type Safety is the combination of progress and preservation:

1. **Progress:** Every well-typed closed term is either a value or can take a step.
2. **Preservation:** If a well-typed term takes a step, the result has the same type.

Together, they guarantee that well-typed closed terms never get stuck
(i.e., reach a non-value state with no possible step).

## Well-Typed Values

A value is well-typed if it inhabits its declared type under the empty context.
- Integer literals are well-typed at intType
- Boolean literals are well-typed at boolType
- String literals are well-typed at stringType
- Unit literal is well-typed at unitType
- Pointer literals are well-typed at pointerType
- Lambdas are well-typed at their function type
- `Value.undef` has no type (intentionally excluded from well-typed programs)
-/

inductive WellTypedValue : Expr → Typ → Prop where
  | lit_int : forall n, WellTypedValue (.lit (.int n)) .intType
  | lit_bool : forall b, WellTypedValue (.lit (.bool b)) .boolType
  | lit_string : forall s, WellTypedValue (.lit (.string s)) .stringType
  | lit_unit : WellTypedValue (.lit .unit) .unitType
  | lit_pointer : forall p, WellTypedValue (.lit (.pointer p)) .pointerType
  | lit_float : forall w f, WellTypedValue (.lit (.float f)) (.floatType w)
  | lit_int_width : forall w n, WellTypedValue (.lit (.int n)) (.intWidthType w)
  | lam : forall n body paramTys retTy,
      WellTypedValue (.lam n body) (.functionType paramTys retTy)
  | lit_none : forall τ,
      WellTypedValue (.lit Value.none) (.optionType τ)
  | lit_some : forall v τ,
      WellTypedValue (.lit (.some v)) (.optionType τ)
  | lit_ok : forall v τ_ok τ_err,
      WellTypedValue (.lit (.ok v)) (.resultType τ_ok τ_err)
   | lit_err : forall v τ_ok τ_err,
       WellTypedValue (.lit (.err v)) (.resultType τ_ok τ_err)
   | none_val : forall τ,
      WellTypedValue .none_ (.optionType τ)
  | err_val : forall e τ_ok τ_err,
      IsValue e -> WellTypedValue (.err_ e) (.resultType τ_ok τ_err)
  | ok_val : forall e τ_ok τ_err,
      IsValue e -> WellTypedValue (.ok_ e) (.resultType τ_ok τ_err)
   | some_val : forall e τ,
       IsValue e -> WellTypedValue (.some_ e) (.optionType τ)
   | tuple_val : forall elems tys,
       HasTypeAll [] [] elems tys [] -> WellTypedValue (.tuple_ elems) (.tupleType tys)
   | array_val : forall elems τ n,
       HasTypeAll [] [] elems (List.replicate n τ) [] -> n = elems.length -> n > 0 ->
       WellTypedValue (.arrayLit elems) (.arrayType τ n)
   | refCreate_val : forall e cap τ, IsValue e → WellTypedValue (.refCreate e cap τ) (.refType cap τ)
   | refLoad_val : forall e τ, IsValue e → WellTypedValue (.refLoad e) τ
   | refStore_val : forall e v τ, IsValue e → IsValue v → WellTypedValue (.refStore e v τ) .unitType
   | refFree_val : forall e _τ, IsValue e → WellTypedValue (.refFree e) .unitType

/-! ## Progress-Preservation Combination

The combined type safety theorem: for any well-typed closed term, either it is a
value, or it takes a step to another well-typed term.

This is strictly stronger than progress alone because it also guarantees type
preservation for the step.
-/

theorem type_safety : forall {σ : Store} {e : Expr} {τ : Typ} {cout : LinCtx},
    HasType [] [] e τ cout ->
    IsValue e \/ exists e', Step σ e σ e' /\ HasType [] [] e' τ cout := by
  intro σ e τ cout hType
  have hProgress := @progress σ _ _ _ hType
  cases hProgress with
  | inl hv => left; exact hv
  | inr hStep =>
    obtain ⟨e', hStep'⟩ := hStep
    right; exact ⟨e', hStep', preservation hType hStep'⟩

/-! ## Stuck-Freedom

A term is "stuck" if it is not a value and cannot take a step.
Type safety guarantees that no well-typed closed term is stuck.
-/

theorem not_stuck : forall {σ : Store} {e : Expr} {τ : Typ} {cout : LinCtx},
    HasType [] [] e τ cout -> ¬(¬IsValue e /\ forall e', ¬Step σ e σ e') := by
  intro σ e τ cout hType hStuck
  obtain ⟨hNotVal, hNoStep⟩ := hStuck
  have hProgress := @progress σ _ _ _ hType
  cases hProgress with
  | inl hv => exact hNotVal hv
  | inr hStep =>
    obtain ⟨e', hStep'⟩ := hStep
    exact hNoStep e' hStep'

/-! ## Multi-Step Type Preservation

If a well-typed closed term reduces to another term in zero or more steps,
the result has the same type.
-/

inductive MultiStep : Store → Expr → Store → Expr → Prop where
  | refl : forall σ e, MultiStep σ e σ e
  | step : forall σ1 e1 σ2 e2 σ3 e3, Step σ1 e1 σ2 e2 → MultiStep σ2 e2 σ3 e3 → MultiStep σ1 e1 σ3 e3

theorem multi_step_preservation : forall {σ σ' : Store} {e e' : Expr} {τ : Typ} {cout : LinCtx},
    HasType [] [] e τ cout -> MultiStep σ e σ' e' -> HasType [] [] e' τ cout
  | _, _, _, _, _, _, hType, .refl _ _ => hType
  | _, _, _, _, _, _, hType, .step _ _ _ _ _ _ hStep hRest =>
    multi_step_preservation (preservation hType hStep) hRest

/-! ## Values Are Well-Typed

Every value that has a type under the empty context is a well-typed value.
This connects the syntactic `IsValue` predicate with the semantic `WellTypedValue` predicate.
-/

theorem value_is_well_typed : forall {e : Expr} {τ : Typ} {cout : LinCtx},
    IsValue e -> HasType [] [] e τ cout -> WellTypedValue e τ := by
  intro e τ cout hv ht
  cases hv with
  | lit v =>
    cases v with
    | int n => cases ht with
      | lit_int => exact WellTypedValue.lit_int n
      | lit_int_width => exact WellTypedValue.lit_int_width _ _
    | bool b => cases ht with
      | lit_bool => exact WellTypedValue.lit_bool b
    | string s => cases ht with
      | lit_string => exact WellTypedValue.lit_string s
    | unit => cases ht with
      | lit_unit => exact WellTypedValue.lit_unit
    | pointer p => cases ht with
      | lit_pointer => exact WellTypedValue.lit_pointer p
      | _ => contradiction
    | loc _ => cases ht with
      | _ => contradiction
    | float f => cases ht with
      | lit_float => exact WellTypedValue.lit_float _ _
      | _ => contradiction
    | undef => cases ht with
      | _ => contradiction
    | some v' => cases ht with
      | lit_some _ _ _ τ_inner => exact WellTypedValue.lit_some v' τ_inner
      | _ => contradiction
    | none => cases ht with
      | lit_none _ _ τ_inner => exact WellTypedValue.lit_none τ_inner
      | _ => contradiction
    | ok v' => cases ht with
      | lit_ok _ _ _ τ_ok τ_err => exact WellTypedValue.lit_ok v' τ_ok τ_err
      | _ => contradiction
     | err v' => cases ht with
       | lit_err _ _ _ τ_err τ_ok => exact WellTypedValue.lit_err v' τ_ok τ_err
       | _ => contradiction
     | tuple_ vs => contradiction
    | array_ vs => contradiction
  | lam n body =>
    cases ht with
    | lam_type => exact WellTypedValue.lam n body _ _
    | _ => contradiction
  | none_ => cases ht with
    | none_type _ _ τ_inner => exact WellTypedValue.none_val τ_inner
    | _ => contradiction
  | err_ e hv' => cases ht with
    | err_type _ _ _ τ_err τ_ok _ => exact WellTypedValue.err_val e τ_ok τ_err hv'
    | _ => contradiction
  | ok_ e hv' => cases ht with
    | ok_type _ _ _ τ_ok τ_err _ => exact WellTypedValue.ok_val e τ_ok τ_err hv'
    | _ => contradiction
  | some_ e hv' => cases ht with
    | some_type _ _ _ τ_inner _ => exact WellTypedValue.some_val e τ_inner hv'
    | _ => contradiction
  | tuple_ elems hvs => cases ht with
    | tuple_type _ _ _ tys hAll => exact WellTypedValue.tuple_val elems tys hAll
    | _ => contradiction
  | array_ elems hvs => cases ht with
    | arrayLit_type _ _ _ τ n hAll hLen hn => exact WellTypedValue.array_val elems τ n hAll hLen hn
    | _ => contradiction
  | refCreate e cap τ hv => cases ht with
    | refCreate_type _ _ _ _ _ hE => exact WellTypedValue.refCreate_val e cap τ hv
    | _ => contradiction

/-! ## Closed Term Typing Inversion

If a closed term has type under the empty environment, it has no free variables.
More precisely: bvar accesses are impossible in a closed term.
-/

theorem closed_no_bvar : forall {e : Expr} {τ : Typ} {cout : LinCtx},
    HasType [] [] e τ cout -> forall n, ¬HasType [] [] (.bvar n) τ [] := by
  intro e τ cout hType n hBvar
  cases hBvar with
  | bvar_type _ _ _ _ _ _ hEnt _ => exact absurd hEnt (by simp)
  | bvar_type_many _ _ _ _ hLen _ => exact absurd hLen (Nat.not_lt_zero _)

end Morph.Proofs.TypeSoundness
