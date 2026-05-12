/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SyntaxTranslation.Spec

namespace Morph.Specs.SyntaxTranslation

/-!
## Lemmas

Lemmas and auxiliary results for the SyntaxTranslation specification.
-/

theorem translationRules_length : translationRules.length = 5 := rfl

theorem roundTripProperty_empty : roundTripProperty "" = true := by
  unfold roundTripProperty minToHum humToMin; simp

theorem semanticEquivalence_trivial (code : String) :
  semanticEquivalence code code = true := rfl

theorem minToHum_empty : minToHum "" = "" := rfl

theorem humToMin_empty : humToMin "" = "" := rfl

end Morph.Specs.SyntaxTranslation
