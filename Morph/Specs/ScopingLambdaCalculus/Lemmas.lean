/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Specs.ScopingLambdaCalculus.Spec

namespace Morph.Specs.ScopingLambdaCalculus

/-!
## Scoping and Lambda Calculus Lemmas and Theorems

This module contains mathematical lemmas and theorems for
scoping and lambda calculus specification.


/-!
## Scoping Theorems


-- Theorem 1: Environment Lookup is Correct

Environment lookup returns correct values.

theorem environment_lookup_correct
  (env : Morph.Core.Env)
  (name : String)
  (value : Morph.Core.Value)
  (h_in : (name, value) ∈ env) :
  lookupEnv env name = some value := by
  induction env with
  | nil =>
    -- Empty environment has no bindings
    intro h
    cases h
  | cons hd tl ih =>
    -- Non-empty environment: hd :: tl
    cases hd
    case mk n v =>
      -- Binding is (n, v) :: tl
      unfold lookupEnv
      -- Check if n == name
      by_cases h_eq : n == name
      case pos =>
        -- n == name, so we return some v
        have : n = name := by
          cases h_eq
          rfl
        subst this
        rfl
      case neg =>
        -- n != name, so we recurse on tl
        -- Since (name, value) ∈ env and n != name, it must be in tl
        have h_in_tl : (name, value) ∈ tl := by
          cases h_in
          case inl =>
            -- (name, value) = (n, v), but n != name, contradiction
            contradiction
          case inr =>
            -- (name, value) ∈ tl
            assumption
        -- Apply induction hypothesis
        exact ih h_in_tl

end Morph.Specs.ScopingLambdaCalculus
-!/