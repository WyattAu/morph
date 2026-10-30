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
operators, `??`/`|>` (loop 78a), `if`/`let`/`fn`/`match` (loop 77), `for`
expressions (loop 78b), unary minus (loop 78c: prefix `-` elaborates to
`.unop .sub`, now stepped by `Step.unop_neg`), `match` statements (loop 78d),
and min-dialect `fix` wherever `match` goes (loop 79: `matchHead`
normalization plus the token-level `Dialect.projectMinToHum` map).
-/

namespace Morph.Tests.Driver

open Morph.Driver

/-! ## Arithmetic and precedence -/

example : runSource "1 + 2 * 3" == .value "7" := by native_decide

example : runSource "(1 + 2) * 3" == .value "9" := by native_decide

example : runSource "10 / 3" == .value "3" := by native_decide

example : runSource "10 % 3" == .value "1" := by native_decide

example : runSource "2 - 5" == .value "-3" := by native_decide

/-! ## Unary minus (loop 78c: prefix `-` elaborates to `.unop .sub`) -/

example : runSource "-5" == .value "-5" := by native_decide

example : runSource "--5" == .value "5" := by native_decide

example : runSource "-2 * 3" == .value "-6" := by native_decide

example : runSource "-(2 + 3)" == .value "-5" := by native_decide

example : runSource "-true" == .stuck := by native_decide

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

/-! ## `??` and `|>` (loop 78a) -/

-- `??` yields the left side when present, the right side when null.
example : runSource "none ?? some 1" == .value "some (1)" := by
  native_decide

example : runSource "some 5 ?? some 6" == .value "some (5)" := by
  native_decide

example : runSource "none ?? none" == .value "none" := by native_decide

-- `|>` applies the left value to the right function.
example : runSource "5 |> fn x -> x + 10" == .value "15" := by
  native_decide

-- `|>` folds left.
example : runSource "1 |> fn x -> x + 1 |> fn y -> y * 10" == .value "20" := by
  native_decide

-- `|>` binds tighter than `??`: the pipe is the fallback's operand.
example : runSource "none ?? some 1 |> fn x -> x" == .value "some (1)" := by
  native_decide

/-! ## `for` expressions (loop 78b) -/

-- The body runs start..stop times; the value is unit (the AST binds the
-- iterator anonymously, so surface names cannot reach it yet).
example : runSource "for 0 in 3 { 42 }" == .value "()" := by
  native_decide

example : runSource "for 0 in 0 { 42 }" == .value "()" := by
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

-- The statement conditional: `(` commits to `if (c) { .. } [else ..]`.
example : runProgram "if (true) { 1; } else { 2; }" == .value "1" := by
  native_decide

example : runProgram "if (false) { 1; } else { 2; }" == .value "2" := by
  native_decide

-- `else if` chains and a bare `if` that falls through to later statements.
example :
    runProgram "if (false) { 1; } else if (true) { 3; } else { 2; }"
      == .value "3" := by
  native_decide

example :
    runProgram "let x = 0; if (false) { let x = 99; }; x" == .value "0" := by
  native_decide

-- An expression-`if` with a parenthesised condition still parses in
-- statement position: the dispatch scans past the group and sees `then`.
example : runProgram "if (1 == 1) then 10 else 20" == .value "10" := by
  native_decide

-- Nested parens balance correctly on both sides of the dispatch.
example : runProgram "if ((1 == 1)) then 10 else 20" == .value "10" := by
  native_decide

example : runProgram "if ((true)) { 1; } else { 2; }" == .value "1" := by
  native_decide

-- A paren inside a string literal is one token, not a group: the scan sees
-- past `"("` to `then` and takes the expression branch (parse-level: the
-- condition is a string, so it would be stuck at runtime).
example : (match Morph.Frontend.parseProgram "if (\"(\") then 1 else 2" with
  | .ok _ => true | .error _ => false) = true := by
  native_decide

-- Guarded loop control: `if` gives `break`/`continue` a condition.
example :
    runProgram "let i = 0; while (true) { let i = i + 1; if (i == 3) { break; }; }; i"
      == .value "3" := by
  native_decide

example :
    runProgram "let i = 0; let s = 0; while (i < 5) { let i = i + 1; if (i == 3) { continue; }; let s = s + i; }; s"
      == .value "12" := by
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

/-! ## `match` expressions (loop 77) -/

-- Through the expression pipeline (`runSource` = `parse` + `Executable.run`),
-- plus one statement-pipeline check (`runProgram` evaluates expression
-- statements through the same evaluator).

-- Payload binding through a wrapper pattern.
example : runSource "match (some 1) { case some(x) => x, case none => 0 }"
    == .value "1" := by
  native_decide

-- A miss falls through to the next arm.
example : runSource "match (none) { case some(x) => x, case none => 0 }"
    == .value "0" := by
  native_decide

-- First match wins.
example :
    runSource "match (ok 5) { case ok(x) => x + 1, case ok(y) => y + 100 }"
      == .value "6" := by
  native_decide

-- Literal patterns match by equality.
example : runSource "match (2) { case 1 => 10, case 2 => 20, case _ => 30 }"
    == .value "20" := by
  native_decide

-- `_` catches what earlier arms miss.
example : runSource "match (none) { case some(x) => x, case _ => 99 }"
    == .value "99" := by
  native_decide

-- Nested wrapper patterns.
example :
    runSource "match (some(ok 3)) { case some(ok(y)) => y * 2, case _ => 0 }"
      == .value "6" := by
  native_decide

-- Statement position works too: the arm body sees the payload binder.
example : runProgram "match (some 1) { case some(x) => x + 10, case none => 0 }"
    == .value "11" := by
  native_decide

/-! ## `match` statements (loop 78d)

The statement form drops the scrutinee parens (`match s { ... }`); arm
bodies are brace-wrapped statement sequences, so arms can assign, break,
and bind pattern variables. -/

-- First-match-wins over statement arms, with assignment in the body.
example : runProgram "let y = 0; match some 1 { case some(x) => { y = x + 10; } case none => { y = 99; } } y"
    == .value "11" := by
  native_decide

-- A miss falls to the next arm.
example : runProgram "let y = 0; match none { case some(x) => { y = 1; } case none => { y = 2; } } y"
    == .value "2" := by
  native_decide

-- Literal patterns match by equality; `_` catches the rest.
example : runProgram "let y = 0; match 2 { case 1 => { y = 10; } case 2 => { y = 20; } case _ => { y = 30; } } y"
    == .value "20" := by
  native_decide

-- No arm matches: unit, and the program falls through.
example : runProgram "match 5 { case 1 => { 10; } } 42"
    == .value "42" := by
  native_decide

-- `break` inside an arm exits the enclosing loop.
example : runProgram "let i = 0; while (true) { let i = i + 1; match i { case 3 => { break; } case _ => { i; } } }; i"
    == .value "3" := by
  native_decide

/-! ## `fix`: the min-dialect `match` (loop 79)

`fix` is accepted everywhere `match` is — expression and statement forms —
via `matchHead` normalization, so these evaluate exactly like their `match`
counterparts above. -/

example : runSource "fix (some 1) { case some(x) => x + 10, case none => 0 }"
    == .value "11" := by
  native_decide

example : runSource "fix (2) { case 1 => 10, case 2 => 20, case _ => 30 }"
    == .value "20" := by
  native_decide

example : runProgram "let y = 0; fix some 1 { case some(x) => { y = x + 10; } case none => { y = 99; } } y"
    == .value "11" := by
  native_decide

end Morph.Tests.Driver
