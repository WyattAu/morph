/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TerminologyStandardization.Spec

namespace Morph.Specs.TerminologyStandardization

/-!
## Lemmas

Lemmas and auxiliary results for the TerminologyStandardization specification.
-/

theorem canonicalMapping_id (t : Term) : canonicalMapping t = t := rfl

theorem isDeprecated_canonical (t : Term) : canonicalMapping t = t → ¬isDeprecated t := by
  unfold isDeprecated; simp

theorem isPascalCase_empty : ¬isPascalCase "" := by
  unfold isPascalCase; simp

theorem isCamelCase_empty : ¬isCamelCase "" := by
  unfold isCamelCase; simp

theorem referentialTransparency_id {A B : Type} (f : PureFunction A B) (x : A) :
  f.apply x = f.apply x := rfl

end Morph.Specs.TerminologyStandardization
