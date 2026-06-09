/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Std
import Plausible
import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem.Spec
import Morph.Specs.TypeSystem.Lemmas

namespace Tests.Property

open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Morph.Specs.TypeSystem
open Plausible

/-! # Arbitrary Instances for Property-Based Testing

We provide `Arbitrary` and `Shrinkable` instances for Morph core types
so that `plausible` can generate random test values.
-/

-- Phase: simple enumeration
instance : Arbitrary Phase where
  arbitrary := Gen.oneOf #[pure .Surface, pure .Resolved, pure .Core]

instance : Shrinkable Phase where
  shrink := fun _ => []

-- BlockId
instance : Arbitrary BlockId where
  arbitrary := return ⟨← Arbitrary.arbitrary⟩

instance : Shrinkable BlockId where
  shrink := fun b => (Shrinkable.shrink b.id).map BlockId.mk

-- ProvenanceId
instance : Arbitrary ProvenanceId where
  arbitrary := return ⟨← Arbitrary.arbitrary⟩

instance : Shrinkable ProvenanceId where
  shrink := fun p => (Shrinkable.shrink p.id).map ProvenanceId.mk

-- Pointer
instance : Arbitrary Pointer where
  arbitrary := return ⟨← Arbitrary.arbitrary, ← Arbitrary.arbitrary, ← Arbitrary.arbitrary⟩

instance : Shrinkable Pointer where
  shrink := fun p =>
    (Shrinkable.shrink (p.block, p.offset, p.provenance)).map
      fun (b, o, pr) => ⟨b, o, pr⟩

-- Value: simple recursive inductive
instance : Arbitrary Value where
  arbitrary := Gen.oneOf #[
    Value.int <$> Arbitrary.arbitrary,
    Value.bool <$> Arbitrary.arbitrary,
    Value.string <$> Arbitrary.arbitrary,
    Value.pointer <$> Arbitrary.arbitrary,
    pure .unit,
    pure .undef
  ]

instance : Shrinkable Value where
  shrink := fun v => match v with
    | .int n => (Shrinkable.shrink n).map .int
    | .bool _ => []
    | .string s => (Shrinkable.shrink s).map .string
    | .pointer p => (Shrinkable.shrink p).map .pointer
    | .float _ => []
    | .unit => []
    | .undef => []
    | .some v => [v]
    | .none => []
    | .ok v => [v]
    | .err v => [v]
    | .tuple_ vs => vs

-- Typ: non-recursive for property testing (only base types needed)
instance : Arbitrary Typ where
  arbitrary := Gen.oneOf #[
    pure .intType,
    pure .boolType,
    pure .stringType,
    pure .pointerType,
    pure .unitType
  ]

instance : Shrinkable Typ where
  shrink := fun _ => []

-- Operator: simple enumeration (20 constructors)
instance : Arbitrary Operator where
  arbitrary := Gen.oneOf #[
    pure (Operator.add), pure .sub, pure .mul, pure .div, pure .mod,
    pure .eq, pure .neq, pure .lt, pure .leq, pure .gt, pure .geq,
    pure .and, pure .or, pure .not,
    pure .andb, pure .orb, pure .xorb, pure .notb, pure .shl, pure .shr,
    pure .ptrAdd, pure .ptrSub, pure .ptrLoad, pure .ptrStore
  ]

instance : Shrinkable Operator where
  shrink := fun _ => []

/-! # Property Tests: Core Types -/

section CoreProperties

-- BlockId round-trip
#test ∀ (n : Nat), (BlockId.mk n).id = n

-- ProvenanceId round-trip
#test ∀ (n : Nat), (ProvenanceId.mk n).id = n

-- Pointer component access (proven; struct equality needs DecidableEq for #test)
example : ∀ (b : BlockId) (o : Int) (p : Option ProvenanceId),
    let ptr := Pointer.mk b o p
    ptr.block = b ∧ ptr.offset = o ∧ ptr.provenance = p := by
  intro b o p; exact ⟨rfl, rfl, rfl⟩

-- Value discriminators
-- Value constructors are disjoint (proven; Value lacks DecidableEq for #test)
example : ∀ (n : Int), Value.int n ≠ Value.unit := by intro n; intro h; injection h
example : ∀ (b : Bool), Value.bool b ≠ Value.unit := by intro b; intro h; injection h
example : ∀ (s : String), Value.string s ≠ Value.unit := by intro s; intro h; injection h
example : ∀ (p : Pointer), Value.pointer p ≠ Value.unit := by intro p; intro h; injection h
example : Value.undef ≠ Value.unit := by intro h; injection h

-- Typ is never equal to a different constructor (proven, Typ lacks BEq for #test)
example : Typ.intType ≠ Typ.boolType := by intro h; nomatch h
example : Typ.intType ≠ Typ.unitType := by intro h; nomatch h
example : Typ.boolType ≠ Typ.stringType := by intro h; nomatch h
example : Typ.unitType ≠ Typ.pointerType := by intro h; nomatch h

-- Phase BEq reflexivity (proven)
example : ∀ (p : Phase), (p == p) = true := by intro p; cases p <;> rfl

end CoreProperties

/-! # Property Tests: Operator Classifications -/

section OperatorProperties

-- Arithmetic operators are disjoint from comparison operators (proven)
example : Morph.Specs.TypeSystem.isArithOp .add → ¬Morph.Specs.TypeSystem.isCompOp .add := by
  intro h₁ h₂; simp [Morph.Specs.TypeSystem.isArithOp, Morph.Specs.TypeSystem.isCompOp] at h₁ h₂
example : Morph.Specs.TypeSystem.isCompOp .lt → ¬Morph.Specs.TypeSystem.isArithOp .lt := by
  intro h₁ h₂; simp [Morph.Specs.TypeSystem.isCompOp, Morph.Specs.TypeSystem.isArithOp] at h₁ h₂

-- Bitwise operators are disjoint from comparison operators (proven)
example : Morph.Specs.TypeSystem.isBitwiseOp .andb → ¬Morph.Specs.TypeSystem.isCompOp .andb := by
  intro h₁ h₂; simp [Morph.Specs.TypeSystem.isBitwiseOp, Morph.Specs.TypeSystem.isCompOp] at h₁ h₂
example : Morph.Specs.TypeSystem.isCompOp .lt → ¬Morph.Specs.TypeSystem.isBitwiseOp .lt := by
  intro h₁ h₂; simp [Morph.Specs.TypeSystem.isCompOp, Morph.Specs.TypeSystem.isBitwiseOp] at h₁ h₂

-- Logic operators are disjoint from bitwise operators (proven)
example : Morph.Specs.TypeSystem.isLogicOp .and → ¬Morph.Specs.TypeSystem.isBitwiseOp .and := by
  intro h₁ h₂; simp [Morph.Specs.TypeSystem.isLogicOp, Morph.Specs.TypeSystem.isBitwiseOp] at h₁ h₂
example : Morph.Specs.TypeSystem.isBitwiseOp .andb → ¬Morph.Specs.TypeSystem.isLogicOp .andb := by
  intro h₁ h₂; simp [Morph.Specs.TypeSystem.isBitwiseOp, Morph.Specs.TypeSystem.isLogicOp] at h₁ h₂

-- Arithmetic and logic are disjoint (proven)
example : Morph.Specs.TypeSystem.isArithOp .add → ¬Morph.Specs.TypeSystem.isLogicOp .add := by
  intro h₁ h₂; simp [Morph.Specs.TypeSystem.isArithOp, Morph.Specs.TypeSystem.isLogicOp] at h₁ h₂
example : Morph.Specs.TypeSystem.isLogicOp .and → ¬Morph.Specs.TypeSystem.isArithOp .and := by
  intro h₁ h₂; simp [Morph.Specs.TypeSystem.isLogicOp, Morph.Specs.TypeSystem.isArithOp] at h₁ h₂

-- Semantic operator classifications match spec classifications (proven examples)
-- These are Prop-based, not Decidable, so can't use #test
example : Morph.Semantics.isArithOp .add ↔ Morph.Specs.TypeSystem.isArithOp .add := by
  simp [Morph.Semantics.isArithOp, Morph.Specs.TypeSystem.isArithOp]
example : Morph.Semantics.isCompOp .lt ↔ Morph.Specs.TypeSystem.isCompOp .lt := by
  simp [Morph.Semantics.isCompOp, Morph.Specs.TypeSystem.isCompOp]
example : Morph.Semantics.isLogicOp .and ↔ Morph.Specs.TypeSystem.isLogicOp .and := by
  simp [Morph.Semantics.isLogicOp, Morph.Specs.TypeSystem.isLogicOp]
example : Morph.Semantics.isBitwiseOp .andb ↔ Morph.Specs.TypeSystem.isBitwiseOp .andb := by
  simp [Morph.Semantics.isBitwiseOp, Morph.Specs.TypeSystem.isBitwiseOp]

end OperatorProperties

/-! # Property Tests: Type System Inversion Lemmas

Expr lacks Arbitrary, so these use concrete examples.
Full inversion coverage is in Morph/Tests/Typing.lean.
-/

section TypeInversionProperties

-- Lit int inversion: concrete test (now returns disjunction since lit_int_width also matches)
example : ∀ (bvs : List Typ) (n : Int) (τ : Typ),
    HasType bvs [] (.lit (.int n)) τ → τ = Typ.intType ∨ (exists w, τ = .intWidthType w) := by
  intro bvs n τ h; exact HasType_lit_int_inv bvs [] n τ h

-- Lit bool inversion: concrete test
example : ∀ (bvs : List Typ) (b : Bool) (τ : Typ),
    HasType bvs [] (.lit (.bool b)) τ → τ = Typ.boolType := by
  intro bvs b τ h; exact HasType_lit_bool_inv bvs [] b τ h

-- Lit unit inversion
example : ∀ (bvs : List Typ) (τ : Typ),
    HasType bvs [] (.lit .unit) τ → τ = Typ.unitType := by
  intro bvs τ h; exact HasType_lit_unit_inv bvs [] τ h

-- Unop not result is always boolType
example : ∀ (bvs : List Typ) (e : Expr) (τ : Typ),
    HasType bvs [] (.unop .not e) τ → τ = Typ.boolType := by
  intro bvs e τ h; exact HasType_unop_not_inv bvs [] e τ h

-- Unop notb result is always intType
example : ∀ (bvs : List Typ) (e : Expr) (τ : Typ),
    HasType bvs [] (.unop .notb e) τ → τ = Typ.intType := by
  intro bvs e τ h; exact HasType_unop_notb_inv bvs [] e τ h

end TypeInversionProperties

/-! # Property Tests: Evaluation Determinism -/

section EvalProperties

-- Arithmetic eval is total for non-zero divisors (proven, not #test with ∃)
-- See evalLogicOp_some_of_isLogicOp and evalBitwiseOp_some_of_isBitwiseOp in Lemmas.lean

-- Division by zero produces none
#test ∀ (n1 : Int), Morph.Semantics.evalArithOp .div n1 0 = none
#test ∀ (n1 : Int), Morph.Semantics.evalArithOp .mod n1 0 = none

end EvalProperties

/-! # Property Tests: Lift and Substitution

Expr lacks BEq/Arbitrary, so property tests use concrete values.
See Morph/Tests/Typing.lean for comprehensive HasType tests.
-/

section LiftSubstProperties

-- substAll' with empty value list is identity
-- This follows from the definition: substAll' k [] e never matches
-- the substitution branch (vs.length = 0), so every bvar either
-- stays (n < k) or shifts by 0 (n - vs.length = n).
-- Proven in Lemmas.lean via liftUnder_zero_eq as a special case.

-- Concrete verification (substAll' uses wf recursion, can't use rfl):
example : substAll' 0 [] (.lit (.int 42)) = .lit (.int 42) := by simp [substAll']
example : substAll' 0 [] (.fvar "x") = .fvar "x" := by simp [substAll']
example : substAll' 0 [] (.bvar 0) = .bvar 0 := by simp [substAll']
example : substAll' 5 [] (.bvar 3) = .bvar 3 := by simp [substAll']

end LiftSubstProperties

end Tests.Property
