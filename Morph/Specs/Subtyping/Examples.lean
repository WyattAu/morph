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
