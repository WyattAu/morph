/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TotalLexer.Lemmas

/-!
# Worked examples: the lexer, computed

`nextToken` returns a pair, so every example below has an answer — including on
input no rule matches, which is the case `Option Token` could not express.
-/

namespace Morph.Specs.TotalLexer

open Std

example : nextToken ['1','2'] = (.num 12, []) := rfl
example : nextToken ['x','y','_','1'] = (.ident "xy_1", []) := rfl
example : nextToken ['+'] = (.op "+", []) := rfl
example : nextToken [' ','\t','4','2'] = (.num 42, []) := rfl
example : nextToken [' ','\t'] = (.eof, []) := rfl

/-- **An unknown character is still a token.** `#` matches no rule, and the lexer
does not go silent: it reports it as an operator. A lexer that returned `none`
here would force every caller to distinguish "error" from "end of input" by
guesswork — which is exactly what `Option Token` asks of them. -/
example : nextToken ['#'] = (.op "#", []) := by decide

/-- Exhausted input is `.eof`, and `.eof` is a token rather than an absence. -/
example : (nextToken [' ','#']).1 ≠ .eof := by decide

example : (nextToken [' ','\n']).1 = .eof := by decide

/-- Maximal munch takes the whole run, not a prefix. -/
example : takeWhile isIdentRest ['a','b','1','+'] = ['a', 'b', '1'] := rfl

example : dropWhile isIdentRest ['a','b','1','+'] = ['+'] := rfl

/-- Every character of a maximal-munch run satisfies the rule. -/
example : ∀ c ∈ takeWhile isIdentRest ['a','b','1','+'], isIdentRest c = true :=
  takeWhile_all isIdentRest ['a','b','1','+']

/-- **The scan terminates.** This is the theorem that replaces the shipped
`partial def nextToken`: the lexer reaches end of input within `|cs| + 1` steps.
Computed on a concrete input — `42` is two characters, so the scan ends within
three steps. -/
example : ∃ j, j ≤ ['4', '2'].length + 1 ∧
    (nextToken (residual j ['4', '2'])).1 = .eof :=
  reaches_eof ['4', '2']

/-- And here is the witness, by construction: the first step consumes both
characters, so the second step reports `.eof`. -/
example : nextToken (residual 1 ['4', '2']) = (.eof, []) := by decide

/-- Progress, discharged: every step either reports `.eof` or shortens the input. -/
example : (nextToken ['1', '2']).1 = .eof ∨
    (nextToken ['1', '2']).2.length < (['1', '2']).length := nextToken_progress ['1', '2']

end Morph.Specs.TotalLexer
