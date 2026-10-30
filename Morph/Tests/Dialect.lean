/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.Dialect

/-!
# Dialect projection tests (loop 79)

The executable counterpart of the translation table
(`Morph.Specs.SyntaxTranslation`): min `fix` projects to hum `match` at the
token level, so identifiers (`prefix`), strings (`"fix"`), and everything
else pass through untouched.
-/

namespace Morph.Tests.Dialect

open Morph.Frontend Morph.Frontend.Dialect

/-- `fix` projects to `match`, keeping lexeme and position. -/
example : projectToken { kind := .keyword "fix", lexeme := "fix", line := 1, col := 1 } =
    { kind := .keyword "match", lexeme := "fix", line := 1, col := 1 } := by
  rfl

/-- Anything else is untouched — including identifiers containing `fix`. -/
example : projectToken { kind := .identifier, lexeme := "prefix", line := 1, col := 1 } =
    { kind := .identifier, lexeme := "prefix", line := 1, col := 1 } := by
  rfl

example : projectToken { kind := .stringLiteral, lexeme := "fix", line := 1, col := 1 } =
    { kind := .stringLiteral, lexeme := "fix", line := 1, col := 1 } := by
  rfl

/-- Whole-stream projection maps only the `fix` keyword. -/
example : projectMinToHum
    [{ kind := .keyword "fix", lexeme := "fix", line := 1, col := 1 },
     { kind := .identifier, lexeme := "prefix", line := 1, col := 5 }] =
    [{ kind := .keyword "match", lexeme := "fix", line := 1, col := 1 },
     { kind := .identifier, lexeme := "prefix", line := 1, col := 5 }] := by
  rfl

/-- The proven properties, instantiated: idempotence and hum-identity. -/
example (toks : List Token) :
    projectMinToHum (projectMinToHum toks) = projectMinToHum toks :=
  projectMinToHum_idem toks

end Morph.Tests.Dialect
