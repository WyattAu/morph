/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem.Spec
import Morph.Proofs.TypeSoundness.Progress
import Morph.Proofs.TypeSoundness.Preservation

namespace Morph.Proofs.TypeSoundness

open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Morph.Specs.TypeSystem

/-! # Type Safety (Soundness)

Type safety is the combination of progress and preservation:

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
  | lam : forall n body paramTys retTy,
      WellTypedValue (.lam n body) (.functionType paramTys retTy)

/-! ## Progress-Preservation Combination

The combined type safety theorem: for any well-typed closed term, either it is a
value, or it takes a step to another well-typed term.

This is strictly stronger than progress alone because it also guarantees type
preservation for the step.
-/

theorem type_safety : forall {e : Expr} {τ : Typ},
    HasType [] [] e τ ->
    IsValue e \/ exists e', Step e e' /\ HasType [] [] e' τ := by
  intro e τ hType
  have hProgress := progress hType
  cases hProgress with
  | inl hv => left; exact hv
  | inr hStep =>
    obtain ⟨e', hStep'⟩ := hStep
    right; exact ⟨e', hStep', preservation hType hStep'⟩

/-! ## Stuck-Freedom

A term is "stuck" if it is not a value and cannot take a step.
Type safety guarantees that no well-typed closed term is stuck.
-/

theorem not_stuck : forall {e : Expr} {τ : Typ},
    HasType [] [] e τ -> ¬(¬IsValue e /\ forall e', ¬Step e e') := by
  intro e τ hType hStuck
  obtain ⟨hNotVal, hNoStep⟩ := hStuck
  have hProgress := progress hType
  cases hProgress with
  | inl hv => exact hNotVal hv
  | inr hStep =>
    obtain ⟨e', hStep'⟩ := hStep
    exact hNoStep e' hStep'

/-! ## Multi-Step Type Preservation

If a well-typed closed term reduces to another term in zero or more steps,
the result has the same type.
-/

inductive MultiStep : Expr → Expr → Prop where
  | refl : forall e, MultiStep e e
  | step : forall e e' e'', Step e e' → MultiStep e' e'' → MultiStep e e''

theorem multi_step_preservation : forall {e e' : Expr} {τ : Typ},
    HasType [] [] e τ -> MultiStep e e' -> HasType [] [] e' τ
  | _, _, _, hType, .refl _ => hType
  | _, _, _, hType, .step _ _ _ hStep hRest =>
    multi_step_preservation (preservation hType hStep) hRest

/-! ## Values Are Well-Typed

Every value that has a type under the empty context is a well-typed value.
This connects the syntactic `IsValue` predicate with the semantic `WellTypedValue` predicate.
-/

theorem value_is_well_typed : forall {e : Expr} {τ : Typ},
    IsValue e -> HasType [] [] e τ -> WellTypedValue e τ := by
  intro e τ hv ht
  cases hv with
  | lit v =>
    cases v with
    | int n => cases ht with
      | lit_int => exact WellTypedValue.lit_int n
    | bool b => cases ht with
      | lit_bool => exact WellTypedValue.lit_bool b
    | string s => cases ht with
      | lit_string => exact WellTypedValue.lit_string s
    | unit => cases ht with
      | lit_unit => exact WellTypedValue.lit_unit
    | pointer p => cases ht with
      | lit_pointer => exact WellTypedValue.lit_pointer p
    | float _ => cases ht
    | undef => cases ht
  | lam n body =>
    cases ht with
    | lam_type => exact WellTypedValue.lam n body _ _

/-! ## Closed Term Typing Inversion

If a closed term has type under the empty environment, it has no free variables.
More precisely: bvar accesses are impossible in a closed term.
-/

theorem closed_no_bvar : forall {e : Expr} {τ : Typ},
    HasType [] [] e τ -> forall n, ¬HasType [] [] (.bvar n) τ := by
  intro e τ hType n hBvar
  cases hBvar with
  | bvar_type _ _ _ hLen => exact absurd hLen (Nat.not_lt_zero _)

end Morph.Proofs.TypeSoundness
