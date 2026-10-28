/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.Subtyping.Spec

/-!
# Worked examples: subtyping, decided
-/

namespace Morph.Specs.Subtyping

open Morph.Core

/-- `neverType` is the bottom: it is a subtype of everything. -/
example (τ : Typ) : Sub .neverType τ := Sub.never τ

/-- `unitType` is the top: everything is a subtype of it. -/
example (τ : Typ) : Sub τ .unitType := Sub.unit τ

/-- `optionType` is covariant. -/
example : Sub (.optionType .neverType) (.optionType .intType) :=
  Sub.option (Sub.never _)

/-- `tupleType` is covariant, pointwise, with exact length. -/
example : Sub (.tupleType [.neverType, .intType]) (.tupleType [.intType, .intType]) :=
  Sub.tuple (SubList.cons (Sub.never _) (SubList.cons (Sub.refl _) SubList.nil))

/-- `structType` is covariant in field types, with exact names. -/
example : Sub (.structType "Point" [("x", .neverType)])
    (.structType "Point" [("x", .intType)]) :=
  Sub.struct (SubFields.cons (Sub.never _) SubFields.nil)

/-- The decision procedure accepts tuple covariance. -/
example : isSubtype (.tupleType [.neverType]) (.tupleType [.intType]) = true :=
  isSubtype_complete (Sub.tuple (SubList.cons (Sub.never _) SubList.nil))

/-- And struct covariance, including nested inside `optionType`. -/
example : isSubtype
    (.optionType (.structType "Point" [("x", .neverType)]))
    (.optionType (.structType "Point" [("x", .intType)])) = true :=
  isSubtype_complete (Sub.option (Sub.struct (SubFields.cons (Sub.never _) SubFields.nil)))

/-- The decision procedure agrees with the relation, in both directions. -/
example (τ σ : Typ) (h : Sub τ σ) : isSubtype τ σ = true :=
  isSubtype_complete h

example (τ σ : Typ) (h : isSubtype τ σ = true) : Sub τ σ :=
  isSubtype_sound τ σ h

/-- And so subtyping is decidable. -/
example (τ σ : Typ) : Decidable (Sub τ σ) := inferInstance

/-- **The old relation was equality.** This is why loop 1 found nothing to
prove about it: `refl` and `trans` over reflexivity derive equality and
nothing else. -/
example (τ σ : Typ) : Morph.Specs.TypeSystem.Subtype τ σ ↔ τ = σ :=
  subtype_iff_eq

end Morph.Specs.Subtyping
