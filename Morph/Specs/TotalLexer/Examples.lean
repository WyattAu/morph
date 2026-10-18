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

end Morph.Specs.TotalLexer
