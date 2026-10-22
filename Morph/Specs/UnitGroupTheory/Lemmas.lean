/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.UnitGroupTheory.Spec

/-!
# UnitGroupTheory: the dimension algebra, proved

Research loop 24. Target: `Morph/Specs/UnitGroupTheory/`.

**What was there.** A genuine dimensional-analysis model — four base units, unit
*vectors* over the integers, multiplication/division/pow as vector arithmetic —
and fifteen real theorems about the base evaluations. Two properties were `True`:

- `spec_exchange_rate_invariant` — which should say: dividing a unit by itself
  gives the identity vector, i.e. a ratio of like units is *dimensionless*;
- `spec_unit_names_unique` — which should say: the four base units have pairwise
  distinct unit vectors, so no two base units can be confused.

**What is here.** Both, proved, plus the algebra of `addUnitVectors`:
commutativity (for equal-length vectors), associativity, and the identity vector
as the unit of addition.

**A finding.** `addUnitVectors` is commutative **only for equal-length
vectors**: `List.zipWith` truncates to the shorter list, so adding a
length-1 vector to a length-2 vector keeps the length-2 vector's tail. Units of
different vector lengths are not compatible in the first place (`areCompatible`
requires equal lengths), so the operation is never called that way — but the
commutativity law needs the hypothesis stated, and it is.
-/

namespace Morph.Specs.UnitGroupTheory

/-! ### The algebra, on raw exponent lists

`addUnitVectors` is `zipWith` over the exponent lists, so the algebra is proved
on the lists and lifted to the structures. Working on raw lists avoids the
structure destructuring that made the direct induction unprovable. -/

private theorem zipWith_add_comm : ∀ (xs ys : List Int), xs.length = ys.length →
    List.zipWith (· + ·) xs ys = List.zipWith (· + ·) ys xs := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys => simp [List.zipWith]
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp [List.zipWith]
      | cons y ys =>
          simp only [List.length_cons] at h
          simp only [List.zipWith_cons_cons]
          rw [Int.add_comm]
          congr 1
          exact ih ys (by omega)

private theorem zipWith_add_assoc : ∀ (xs ys zs : List Int),
    List.zipWith (· + ·) (List.zipWith (· + ·) xs ys) zs =
      List.zipWith (· + ·) xs (List.zipWith (· + ·) ys zs) := by
  intro xs
  induction xs with
  | nil => intro ys zs; simp [List.zipWith]
  | cons x xs ih =>
      intro ys zs
      cases ys with
      | nil => simp [List.zipWith]
      | cons y ys =>
          cases zs with
          | nil => simp [List.zipWith]
          | cons z zs =>
              simp only [List.zipWith_cons_cons]
              rw [Int.add_assoc]
              congr 1
              exact ih ys zs

private theorem zipWith_add_replicate_self : ∀ (xs : List Int),
    List.zipWith (· + ·) xs (List.replicate xs.length 0) = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.zipWith_cons_cons, List.replicate_succ, List.length_cons]
      rw [Int.add_zero]
      congr 1

/-- **Adding unit vectors is commutative**, for equal-length vectors. (`zipWith`
truncates to the shorter list, so the law needs the lengths to agree — and units
of different vector lengths are not compatible anyway.) -/
theorem addUnitVectors_comm (v1 v2 : UnitVector)
    (h : v1.exponents.length = v2.exponents.length) :
    addUnitVectors v1 v2 = addUnitVectors v2 v1 := by
  cases v1 with
  | mk xs =>
      cases v2 with
      | mk ys =>
          simp only [addUnitVectors]
          congr 1
          exact zipWith_add_comm xs ys h

/-- **Adding unit vectors is associative.** -/
theorem addUnitVectors_assoc (v1 v2 v3 : UnitVector) :
    addUnitVectors (addUnitVectors v1 v2) v3 = addUnitVectors v1 (addUnitVectors v2 v3) := by
  cases v1 with
  | mk xs =>
      cases v2 with
      | mk ys =>
          cases v3 with
          | mk zs =>
              simp only [addUnitVectors]
              congr 1
              exact zipWith_add_assoc xs ys zs

/-- **The identity vector is the unit of addition.** -/
theorem addUnitVectors_ident (v : UnitVector) :
    addUnitVectors v (identityVector v.exponents.length) = v := by
  cases v with
  | mk xs =>
      simp only [addUnitVectors, identityVector]
      congr 1
      exact zipWith_add_replicate_self xs

/-- **The exchange-rate invariant: dividing a unit by itself is dimensionless.**
A ratio of like units has the identity unit vector — this is what makes an
exchange rate a pure number rather than a quantity with a unit. -/
theorem div_self_dimensionless (u : BaseUnit) :
    evaluateUnitExpression (.div (.base u) (.base u)) = identityVector 4 := by
  cases u <;> rfl

/-- **The four base units have pairwise distinct unit vectors** — so no two base
units can be confused, and a quantity in one base unit cannot be silently used
as another. -/
theorem base_unit_vectors_distinct :
    ∀ (v1 v2 : BaseUnit), v1 ≠ v2 →
      (evaluateUnitExpression (.base v1)).exponents
        ≠ (evaluateUnitExpression (.base v2)).exponents := by
  intro v1 v2 hne
  cases v1 <;> cases v2 <;> simp [evaluateUnitExpression] <;> first
    | exact absurd rfl hne
    | decide

end Morph.Specs.UnitGroupTheory
