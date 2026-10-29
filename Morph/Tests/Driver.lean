/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Driver

/-!
# Driver tests

End-to-end checks of the pipeline the `morph` executable runs: source text in,
`Outcome` out. Both pipeline stages are proved-total components (the parser,
loops 9/39; the evaluator, loop 38), so these tests only have to pin down the
*values*, which they do on the compiled evaluator (`native_decide`, the same
style as `Morph.Tests.Executable`).

The surface below is what `parseExpr` covers today: numeric/string/bool/option
literals, arrays, tuples, postfix indexing and field access, the binary
operators, and `if`/`let`/`fn`. Unparsed or unevaluated, named in
`docs/RESEARCH-LOOPS-70-79.md`: `match`/`for` expressions, the `??` and `|>`
operators (the lexer has no two-character token for them), and unary minus
(the reference semantics has no `unop .sub` rule, so `-e` parses but is stuck).
-/

namespace Morph.Tests.Driver

open Morph.Driver

/-! ## Arithmetic and precedence -/

example : runSource "1 + 2 * 3" == .value "7" := by native_decide

example : runSource "(1 + 2) * 3" == .value "9" := by native_decide

example : runSource "10 / 3" == .value "3" := by native_decide

example : runSource "10 % 3" == .value "1" := by native_decide

example : runSource "2 - 5" == .value "-3" := by native_decide

/-! ## Comparisons and logic -/

example : runSource "2 < 3" == .value "true" := by native_decide

example : runSource "3 == 3" == .value "true" := by native_decide

example : runSource "true && false" == .value "false" := by native_decide

example : runSource "true || false" == .value "true" := by native_decide

example : runSource "if true then 1 else 2" == .value "1" := by native_decide

example : runSource "if 1 == 2 then 10 else 20" == .value "20" := by
  native_decide

/-! ## Strings -/

example : runSource "\"abc\" + \"def\"" == .value "abcdef" := by native_decide

example : runSource "\"hi\"" == .value "hi" := by native_decide

/-! ## Bindings: `let` and `fn` (loop 72)

The parser now resolves identifiers against the enclosing binders and emits de
Bruijn indices, so parsed bindings are visible to the bvar-binding evaluator. -/

example : runSource "let x = 5 in x + 1" == .value "6" := by native_decide

-- Shadowing: the innermost binder wins.
example : runSource "let x = 1 in let x = 2 in x" == .value "2" := by
  native_decide

example : runSource "let x = 1 in let y = 2 in x + y" == .value "3" := by
  native_decide

-- The initialiser is in the outer scope.
example : runSource "let x = 1 in let x = x + 1 in x" == .value "2" := by
  native_decide

-- Lambdas parse and apply, with parameters in source order.
example : runSource "(fn x -> x) 5" == .value "5" := by native_decide

example : runSource "(fn x y -> x) 1 2" == .value "1" := by native_decide

example : runSource "(fn x y -> y - x) 3 10" == .value "7" := by native_decide

-- A lambda over an outer binding.
example : runSource "let y = 10 in (fn x -> x + y) 5" == .value "15" := by
  native_decide

/-! ## Tuples, arrays, indexing, options (loop 73) -/

example : runSource "()" == .value "()" := by native_decide

example : runSource "(1, 2)" == .value "(1, 2)" := by native_decide

example : runSource "[1, 2, 3]" == .value "[1, 2, 3]" := by native_decide

example : runSource "[]" == .value "[]" := by native_decide

example : runSource "[[1], [2]][1]" == .value "[2]" := by native_decide

-- Indexing binds tighter than grouping and works on bound names.
example : runSource "[1, 2, 3][1]" == .value "2" := by native_decide

example : runSource "let a = [10, 20] in a[1]" == .value "20" := by
  native_decide

-- Option and result literals, with a prefix wrapper over an atom.
example : runSource "none" == .value "none" := by native_decide

example : runSource "some 5" == .value "some (5)" := by native_decide

example : runSource "if true then ok 1 else err 2" == .value "ok (1)" := by
  native_decide

/-! ## Statement programs (loop 74)

`runProgram` parses a statement sequence and runs it: declarations, updates,
assignment, `while`/`do`-`while`, `return`. The sequence's value is its last
expression statement. -/

example : runProgram "let x = 5; x * x" == .value "25" := by native_decide

-- Assignment updates the innermost binding and does not introduce.
example : runProgram "let x = 1; x = x + 10; x" == .value "11" := by
  native_decide

-- A `while` loop whose body declares; the environment threads per iteration.
example :
    runProgram "let a = 0; let i = 0; while (i < 5) { let a = a + i; let i = i + 1; }; a"
      == .value "10" := by
  native_decide

example :
    runProgram "let x = 2; while (x < 100) { let x = x * x; }; x"
      == .value "256" := by
  native_decide

-- `do .. while` runs the body at least once.
example :
    runProgram "let i = 0; do { let i = i + 1; } while (i < 3); i"
      == .value "3" := by
  native_decide

-- `return` short-circuits, even from inside a loop body.
example : runProgram "return 42;" == .value "42" := by native_decide

example : runProgram "while (true) { return 7; }" == .value "7" := by
  native_decide

-- A program that is one expression still works under `runProgram`.
example : runProgram "1 + 2 * 3" == .value "7" := by native_decide

/-! ## Failure is a value, not a crash -/

-- A truncated expression fails to parse.
example : isParseFailed (runSource "1 +") := by
  native_decide

-- So does garbage.
example : isParseFailed (runSource "!!") := by
  native_decide

-- The empty program has no expression to parse.
example : isParseFailed (runSource "") := by
  native_decide

-- A type error at evaluation time is `stuck`, not a crash.
example : isStuck (runSource "1 && true") := by
  native_decide

-- An unbound name is `stuck` too.
example : isStuck (runSource "noSuchVariable + 1") := by
  native_decide

-- And `morph parse` reports the AST without evaluating.
example : isValue (parseSource "1 + 2") := by native_decide

end Morph.Tests.Driver
