/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Driver
import Morph.Version

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

/-! ## Error-message goldens (Sprint 5) -/

-- Golden: the exact bytes on stderr for a truncated expression.
example : runSource "1 +" == .parseFailed "line 1, col 1: failed to parse" := by
  native_decide

-- Golden: garbage fails with the same single-line report.
example : runSource "!!" == .parseFailed "line 1, col 1: failed to parse" := by
  native_decide

-- Golden: a bad first character reports at 1:1 too.
example : runSource "@" == .parseFailed "line 1, col 1: failed to parse" := by
  native_decide

-- Golden: empty input has its own zero-position report.
example : runSource "" == .parseFailed "line 0, col 0: empty input" := by
  native_decide

-- Golden: stuck carries no message -- these equalities pin that.
example : runSource "1 && true" == .stuck := by native_decide

example : runSource "noSuchVariable + 1" == .stuck := by native_decide

-- Golden: the CLI help text (`morph` with missing/bad args prints this).
example : usage =
    "usage: morph <command> [argument]\n" ++
    "  eval <expr>   parse and evaluate an expression\n" ++
    "  parse <expr>  print the parsed AST\n" ++
    "  check <expr>  print the inferred type or the type error\n" ++
    "  run <file>    run the statement program in a file\n" ++
    "  run --hir <file>  run the file through the HIR lowering\n" ++
    "  build --codegen=cranelift <file>  emit a CLIF artifact for the file\n" ++
    "  fmt <file>    format the statement program in a file\n" ++
    "  doc <file>    render the file's /// docs as Markdown\n" ++
    "  test <file|dir>  run .hum test files through the HIR interpreter\n" ++
    "  version       print the Morph version\n" := by
  native_decide

-- Golden: the release version `morph version` prints.
example : Morph.versionString == "0.1.0" := by native_decide

-- Golden: what the CLI prints for a stuck outcome.
example : report .stuck = "stuck: evaluation got stuck or exhausted its fuel" := by
  rfl

-- Golden: `check` surfaces the type error verbatim (the top-level
-- expectation is `unitType` -- see `checkSource`).
example : checkSource "1 + true" == .typeError
    "Cannot infer type for expression: Morph.Syntax.Expr.binop\n  (Morph.Core.Operator.add)\n  (Morph.Syntax.Expr.lit (Morph.Core.Value.int 1))\n  (Morph.Syntax.Expr.lit (Morph.Core.Value.bool true))" := by
  native_decide

-- Golden: an unbound name is a type error under `check` (stuck under `eval`).
example : checkSource "noSuchVariable + 1" == .typeError
    "Cannot infer type for expression: Morph.Syntax.Expr.binop\n  (Morph.Core.Operator.add)\n  (Morph.Syntax.Expr.fvar \"noSuchVariable\")\n  (Morph.Syntax.Expr.lit (Morph.Core.Value.int 1))" := by
  native_decide

-- Golden: `--hir` on a program outside the fragment reports exactly this.
example : runProgramHIR "let y = 0; match none { case none => { y = 1; } }" ==
    .unsupported
      "program leaves the HIR fragment (--hir runs first-order let/match/while programs only)" := by
  native_decide

-- Golden: `--hir` on a first-order program evaluates it.
example : runProgramHIR "let y = 5; y" == .value "5" := by native_decide

/-! ## `fmt` and `doc` goldens (Sprint 6 / loop 90) -/

-- Golden: `fmt` prints the canonical `hum` rendering of a program.
example : formatProgram "let y = 5; y" == .value "let y = 5;\ny" := by
  native_decide

-- Golden: formatting is a fixpoint — canonical output reformats cleanly.
example : formatProgram "let y = 5;\ny" == .value "let y = 5;\ny" := by
  native_decide

-- Golden: `while` programs format structurally.
example : formatProgram "while (true) { y = 1; }" ==
    .value "while true { y = 1 }" := by
  native_decide

-- Golden: `fmt` fails exactly like `run` on unparseable input.
example : formatProgram "1 +" == .parseFailed "line 1, col 1: failed to parse" := by
  native_decide

-- Golden: `///` lines are skipped by the parser, so documented files run.
example : runProgram "/// Add one.\nlet y = 5;\ny" == .value "5" := by
  native_decide

-- Golden: `doc` renders doc entries as Markdown.
example : docSource "/// Add one.\n/// Uses `y`.\nlet y = 5;\ny" ==
    .value "# Documentation\n\n## `let y = 5;`\nAdd one.\nUses `y`.\n" := by
  native_decide

-- Golden: plain `//` comments between the docs and the code are tolerated.
example : docSource "let y = 5;\n// plain comment\n/// Documented.\ny = 6;" ==
    .value "# Documentation\n\n## `y = 6;`\nDocumented.\n" := by
  native_decide

-- Golden: files without docs get the empty note, not an error.
example : docSource "let y = 5;\ny" ==
    .value "# Documentation\n\nNo documentation comments found.\n" := by
  native_decide

-- Golden: trailing docs with no following statement are dropped.
example : docSource "/// Trailing docs with no statement." ==
    .value "# Documentation\n\nNo documentation comments found.\n" := by
  native_decide

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

/-! ## `check`: synthesized types and the checker's message (loop 82)

`checkSource` parses, then synthesizes. Success prints the inferred
type; failure prints `formatTypeError`'s cannot-infer message (exit 1
at the CLI). -/

example : checkSource "1 + 2" == .value "Morph.Core.Typ.intType" := by
  native_decide

example : isTypeError (checkSource "1 + true") = true := by
  native_decide

example : isValue (checkSource "let x = 5 in x + 1") = true := by
  native_decide

/-! ## `build --codegen=cranelift` goldens (stage B / item B6)

`buildClif` is the pipeline the CLI command runs; `Main.lean` writes the
`.value` text next to the input and exits 0, and prints any other outcome to
stderr and exits 1. So pinning the `Outcome` pins both the artifact text and the
exit code. The artifact below is the whole stage-B story in four lines: the unit
prologue is gone (it cannot be encoded), register 1 holds the literal, and the
return names it. -/

-- Golden: an in-subset program emits this artifact, exactly.
example : buildClif "let y = 5; y" ==
    .value "function %main() -> i64 {\nblock0:\n  v1 = iconst.i64 5\n  return v1\n}\n" := by
  native_decide

-- Golden: arithmetic encodes to one instruction per operator.
example : buildClif "let x = 2; let y = 3; x * y + 1" ==
    .value "function %main() -> i64 {\nblock0:\n  v1 = iconst.i64 2\n  v2 = iconst.i64 3\n  v3 = imul v1, v2\n  v4 = iconst.i64 1\n  v5 = iadd v3, v4\n  return v5\n}\n" := by
  native_decide

-- Golden: `div` is outside the D-4 subset (loop 146: section 1.2's truncation
-- and trap semantics have no agreement lemma yet), so it is rejected, not
-- mistranslated.
example : buildClif "let x = 7 / 2; x" ==
    .unsupported
      "codegen: the CLIF subset cannot encode this program (boolean- or unit-valued programs, div/mod, bitwise andb/orb/xorb, bool constants, copy, memory, calls)" := by
  native_decide

-- Golden: a program whose value is unit is refused (loop 151). `return v0`
-- would name the prologue's register, which no instruction defines, so the text
-- would not be CLIF. The model can express it; the printer does not pretend to.
example : buildClif "let y = 5;" ==
    .unsupported
      "codegen: the CLIF subset cannot encode this program (boolean- or unit-valued programs, div/mod, bitwise andb/orb/xorb, bool constants, copy, memory, calls)" := by
  native_decide

example : buildClif "" ==
    .unsupported
      "codegen: the CLIF subset cannot encode this program (boolean- or unit-valued programs, div/mod, bitwise andb/orb/xorb, bool constants, copy, memory, calls)" := by
  native_decide

-- Golden: a boolean-valued program is refused (loop 152). `run` prints `true`,
-- but `icmp` produces an i8 truth value and the printed signature is `-> i64`,
-- with no widening instruction in the modelled subset.
example : buildClif "let a = 3; let b = 5; a < b" ==
    .unsupported
      "codegen: the CLIF subset cannot encode this program (boolean- or unit-valued programs, div/mod, bitwise andb/orb/xorb, bool constants, copy, memory, calls)" := by
  native_decide

-- Golden: a program outside the HIR fragment is rejected before MIR.
example : buildClif "let y = 5; match none { case none => { y = 1; } }" ==
    .unsupported
      "codegen: program leaves the HIR fragment (stage B compiles first-order let/assign/return programs only)" := by
  native_decide

-- Golden: codegen fails exactly like `run` on unparseable input.
example : buildClif "1 +" == .parseFailed "line 1, col 1: failed to parse" := by
  native_decide

/-! ### The artifact path

The extension is replaced, not appended, so `morph build` on `main.hum` leaves a
`main.clif` and the input's dots survive (`Compiler.v2.hum` → `Compiler.v2.clif`). -/

example : clifArtifactPath "main.hum" = "main.clif" := by native_decide

example : clifArtifactPath "src/Main.hum" = "src/Main.clif" := by native_decide

example : clifArtifactPath "src/Compiler.v2.hum" = "src/Compiler.v2.clif" := by
  native_decide

example : clifArtifactPath "Makefile" = "Makefile.clif" := by native_decide

/-! ### Stage C: branching programs

The straight-line path above is unchanged; a program with control flow falls
through to `lowerProgramCFG` and the block model. The golden pins the text
shape — blocks, parameters, one argument list per edge — and the refusals pin
what is still outside the fragment. -/

-- Golden: an `if` with a computed condition emits four blocks, a `brif` with one
-- argument list per target, and a join whose parameter is returned.
example : buildClif "if (1 < 2) { 10 } else { 20 }" ==
    .value "function %main() -> i64 {\nblock0:\n  v1 = iconst.i64 1\n  v2 = iconst.i64 2\n  v3 = icmp slt v1, v2\n  brif v3, block1, block2\nblock3(v6: i64):\n  return v6\nblock2:\n  v5 = iconst.i64 20\n  jump block3(v5)\nblock1:\n  v4 = iconst.i64 10\n  jump block3(v4)\n}\n" := by
  native_decide

-- Golden: a fresh `varDecl` inside an arm takes the old join verbatim (C2c
-- merge path): `x` is not in the pre-branch env, so no merge phi is needed
-- and the arm's value is unit (the prologue register `v0`), merged against
-- the else-arm's `2`. The lowered CFG executes this to unit, matching the
-- interpreter, so the program now encodes instead of being refused.
example : buildClif "if (1 < 2) { let x = 1; } else { 2 }" ==
    .value "function %main() -> i64 {\nblock0:\n  v1 = iconst.i64 1\n  v2 = iconst.i64 2\n  v3 = icmp slt v1, v2\n  brif v3, block1, block2\nblock3(v6: i64):\n  return v6\nblock2:\n  v5 = iconst.i64 2\n  jump block3(v5)\nblock1:\n  v4 = iconst.i64 1\n  jump block3(v0)\n}\n" := by
  native_decide

-- Golden: a loop lowers (C7a) but the cyclic CFG is outside the CLIF block
-- subset the emitter encodes (back-edges carry no edge arguments there).
example : buildClif "while (1 < 2) { 1 }" ==
    .unsupported
      "codegen: the CLIF block subset cannot encode this program (switch, non-leading phi, missing edge argument, bool constants)" := by
  native_decide

-- Golden: a literal boolean condition lowers fine and *encodes* not at all —
-- the CLIF subset has no boolean constant (the `bconst` widening is named in
-- docs/STAGEC-SCOPE.md §3).
example : buildClif "if (true) { 10 } else { 20 }" ==
    .unsupported
      "codegen: the CLIF block subset cannot encode this program (switch, non-leading phi, missing edge argument, bool constants)" := by
  native_decide

/-! ### Stage C: `morph test` goldens (C9)

`runTestCase` is the per-case pipeline the `test` command runs: parse, lower
to the HIR fragment, run `runHIRStmts` to completion. A terminating value
(including `return`) passes; stuck, top-level `break`/`continue`, fragment
refusals and parse failures fail with a one-line reason. `formatTestReport`
pins the CLI text: one line per case plus the `passed/total` summary. -/

example : runTestCase "let y = 5; y" == (true, "ok") := by native_decide

example : runTestCase "while (true) { return 7; }" == (true, "ok") := by
  native_decide

example : runTestCase "1 + true" ==
    (false, "stuck: evaluation got stuck or exhausted its fuel") := by
  native_decide

example : runTestCase "let y = 0; match none { case none => { y = 1; } }" ==
    (false, "program leaves the HIR fragment") := by
  native_decide

example : runTestCase "1 +" ==
    (false, "parse error: line 1, col 1: failed to parse") := by
  native_decide

example : formatTestReport [("a.hum", true, "ok"),
    ("b.hum", false, "stuck: evaluation got stuck or exhausted its fuel")] ==
    "ok a.hum\nFAIL b.hum: stuck: evaluation got stuck or exhausted its fuel\n1/2 tests passed" := by
  native_decide

end Morph.Tests.Driver
