/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SyntaxTranslation.Spec

namespace Morph.Specs.SyntaxTranslation

/-!
## Examples

Concrete examples demonstrating the SyntaxTranslation specification.
-/

example : translationRules.length = 5 := rfl

def fnRule : TranslationRule := {
  minPattern := "fn",
  humPattern := "function",
  description := "Function keyword"
}

example : fnRule.minPattern = "fn" := rfl

example : fnRule.humPattern = "function" := rfl

example : roundTripProperty "" = true := by
  unfold roundTripProperty minToHum humToMin; simp

example : semanticEquivalence "fn" "function" = true := rfl

end Morph.Specs.SyntaxTranslation
