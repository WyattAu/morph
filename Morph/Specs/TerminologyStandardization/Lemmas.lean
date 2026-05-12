/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TerminologyStandardization.Spec

namespace Morph.Specs.TerminologyStandardization

/-!
## Lemmas

Lemmas and auxiliary results for the TerminologyStandardization specification.
-/

/-! ### Canonical Mapping -/

theorem canonicalMapping_id (t : Term) : canonicalMapping t = t := rfl

theorem isDeprecated_canonical (t : Term) : canonicalMapping t = t → ¬isDeprecated t := by
  unfold isDeprecated; simp

/-! ### Naming Conventions -/

theorem isPascalCase_empty : ¬isPascalCase "" := by
  unfold isPascalCase; simp

theorem isCamelCase_empty : ¬isCamelCase "" := by
  unfold isCamelCase; simp

theorem isSnakeCase_empty : isSnakeCase "" = true := by
  unfold isSnakeCase; simp

/-! ### Referential Transparency -/

theorem referentialTransparency_id {A B : Type} (f : PureFunction A B) (x : A) :
  f.apply x = f.apply x := rfl

theorem referentialTransparency_eq {A B : Type} (f : PureFunction A B) (x y : A)
    (h : x = y) : f.apply x = f.apply y := by
  subst h; rfl

/-! ### Consistency Invariant -/

theorem consistencyInvariant_empty :
    consistencyInvariant ([] : List Term) := by
  unfold consistencyInvariant; simp

end Morph.Specs.TerminologyStandardization
