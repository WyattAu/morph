/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SyntaxTranslation.Spec

namespace Morph.Specs.SyntaxTranslation

/-!
## Lemmas

Lemmas and auxiliary results for the SyntaxTranslation specification.
-/

/-! ### Translation Rules -/

theorem translationRules_length : translationRules.length = 5 := rfl

theorem translationRules_nonempty : translationRules.length > 0 := by
  unfold translationRules; decide

/-! ### Round-Trip Property -/

theorem roundTripProperty_empty : roundTripProperty "" = true := by
  unfold roundTripProperty minToHum humToMin; simp

/-! ### Semantic Equivalence -/

theorem semanticEquivalence_trivial (code : String) :
  semanticEquivalence code code = true := rfl

/-! ### Translation Functions -/

theorem minToHum_empty : minToHum "" = "" := rfl

theorem humToMin_empty : humToMin "" = "" := rfl

theorem minToHum_any (code : String) : minToHum code = "" := rfl

theorem humToMin_any (code : String) : humToMin code = "" := by unfold humToMin; rfl

/-! ### Translation Rule Access -/

theorem translationRules_head :
  translationRules.head? = some { minPattern := "fn", humPattern := "function", description := "Function keyword" } := rfl

theorem translationRules_getLast :
  translationRules.getLast? = some { minPattern := "fix", humPattern := "match", description := "Match keyword" } := rfl

end Morph.Specs.SyntaxTranslation
