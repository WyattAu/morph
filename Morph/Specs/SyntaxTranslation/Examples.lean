/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Specs.SyntaxTranslation.Spec

namespace Morph.Specs.SyntaxTranslation

/-!
## Syntax Translation Examples

This module contains concrete examples and test cases for
bidirectional syntax translation between min and hum dialects.


/-!
## Example 1: Translation Rules

Demonstrates translation rules between min and hum.


-- Translation rules list 
def example_translation_rules : List TranslationRule :=
  [
      {
        minPattern := "fn",
        humPattern := "function",
        description := "Function keyword"
      },
      {
        minPattern := "ret",
        humPattern := "return",
        description := "Return keyword"
      },
      {
        minPattern := "i32",
        humPattern := "Int32",
        description := "Integer type"
      }
    ]

-- Example: Verify translation rules 
#eval example_translation_rules.map fun r => (r.minPattern, r.humPattern)
-- Expected: [("fn", "function"), ("ret", "return"), ("i32", "Int32")]

/-!
## Example 2: Round-Trip Property

Demonstrates round-trip property.


-- Example code in min dialect 
def example_min_code : String :=
  "fn add(x:i32,y:i32):i32{x+y}"

-- Translate to hum 
def example_hum_code : String :=
  minToHum example_min_code

-- Translate back to min 
def example_round_trip : String :=
  humToMin example_hum_code

-- Example: Verify round-trip 
#eval example_round_trip
-- Expected: "fn add(x:i32,y:i32):i32{x+y}"

/-!
## Example 3: Complex Translation

Demonstrates translation of complex expressions.


-- Complex min code 
def example_complex_min : String :=
  "fn factorial(n:i32):i32{if n<=1{1}else{n*factorial(n-1)}}"

-- Complex hum code 
def example_complex_hum : String :=
  minToHum example_complex_min

-- Example: Verify complex translation 
#eval example_complex_hum
-- Expected: "function factorial(n: Int32): Int32 {if (n <= 1) {1} else {n * factorial(n - 1)}}"

/-!
## Example 4: Semantic Equivalence

Demonstrates semantic equivalence between dialects.


-- Verify semantic equivalence 
example_semantic_equivalence :
  semanticEquivalence example_min_code example_hum_code := by
  unfold semanticEquivalence
  trivial

/-!
## Example 5: Pattern Matching Translation

Demonstrates translation of pattern matching.


-- Pattern matching in min 
def example_pattern_min : String :=
  "fix opt{Some(v)=>v+1,None=>0}"

-- Pattern matching in hum 
def example_pattern_hum : String :=
  minToHum example_pattern_min

-- Example: Verify pattern matching translation 
#eval example_pattern_hum
-- Expected: "match (opt) {case Some(v) => v + 1, case None => 0}"

end Morph.Specs.SyntaxTranslation
-/