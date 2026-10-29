# Research Loops 70–79 — Implementation Track

Loop 70 closes the last `Morph/Specs` TODOs. From here the track turns toward
*implementation*: the specifications are now dense enough that the most
valuable next iterations land their guarantees in the shipped compiler, not
only in `Morph/Specs`.

## Loop 74 — statement execution: `morph run` runs real programs (DONE, Lean)

**Target.** The driver was expression-only; `Program`/`Stmt` existed in
`Syntax.lean` with no parser and no interpreter.

**Delivered.**
- `parseStmt`/`parseExprStmt`/`parseStmts`/`parseProgram`
  (`Morph/Frontend/Parser.lean`): declarations (`let x = e;` — the
  `let .. in` expression form is still recognised and re-routed), assignment
  (`x = e;`, a single `=`, not `==`), `return e;`, `break;`, `continue;`,
  `while (c) { .. }`, `do { .. } while (c);`, and expression statements. Same
  fuel discipline, plus `parseStmt_mono`/`parseExprStmt_mono`/
  `parseStmts_mono` in the monotonicity block, and `peek2` for the
  `=`-vs-`==` lookahead.
- `Morph/Interp.lean`: `runProgram`/`runStmts`/`runWhile`/`runDoWhile` —
  statement variables bound by name in `Context.fvs` (the representation
  `parseStmt` targets), expression evaluation delegated to the proved-total
  `eval`. The **environment threads through everything**: a loop body's final
  environment is the next iteration's starting environment (the first draft
  discarded it, so every loop was infinite; the tests caught it immediately).
  One fuel unit per statement and per iteration; exhaustion is `Flow.stuck`.
  Assignment updates the innermost binding and never introduces.
- `morph run file` now runs statement programs; `morph eval` stays
  expression-mode.

**Result.** `morph run fact.morph` computes 720:
```
let n = 6; let acc = 1;
while (n > 1) { let acc = acc * n; let n = n - 1; };
acc
```
Also pinned by tests: the summation loop → 10, `x * x` squaring to 256,
`do .. while` running once, `return` short-circuiting from a loop body, and a
bare expression program under `runProgram`.

**Still named.** No `if` *statement* in the `Stmt` AST (conditionals are the
expression form; `break`/`continue` therefore have no guarded form except
loop conditions), no `match`/`for` statements, no `??`/`|>` operators, and
unary minus still parses-but-sticks (the reference semantics has no
`unop .sub` rule).

## Loop 73 — tuples, arrays, indexing, and option literals (DONE, Lean)

**Target.** The evaluator already handled `tuple_`, `arrayLit`,
`arrayIndex`, `none_`, `some_`, `ok_` and `err_`; the parser could produce
none of them. This loop closes the syntax gap.

**Delivered** (`Morph/Frontend/Parser.lean`, `Morph/Frontend/Lexer.lean`):
- `()` is the unit literal; `(e)` stays grouping; `(a, b, ...)` is a tuple.
- `[a, b, ...]` is an array literal (`parseArrayLit`/`parseArrayElems`).
- `parsePostfix` adds the tightest-binding postfix loop: indexing `a[i]`
  (each `[`/`]` consumed) and field access `a.f`.
- `none` is a keyword literal; `some`/`ok`/`err` are prefix wrappers over one
  atom — all four registered as keywords (they used to lex as identifiers).
- The fuel-monotonicity section gained `parseAtomPrimary_mono`,
  `parsePostfix_mono`, `parseSomeLike_mono`, `parseTupleRest_mono`,
  `parseArrayLit_mono`, `parseArrayElems_mono` — every new recursion makes
  token progress and passes the fuel predecessor, and the lemmas hold.

**Result.** `[1, 2, 3][1]` → `2`; `[[1], [2]][1]` → `[2]`;
`let a = [10, 20] in a[1]` → `20`; `some (1 + 1)` → `some (2)`;
`if true then ok 1 else err 2` → `ok (1)`. Driver tests pin each.

**One more bug found while wiring it up**: `parseArrayElems` never consumed
the separating comma, so `[1, 2]` failed to parse while `[1]` succeeded —
the same class of cursor bug as loop 71's `fn` keyword.

**Named here, addressed in loop 74**: statement-level execution
(`Program` parsing and running). **Still named**: `match`/`for` expressions
(the evaluator's `match_` takes the first arm, so honest parser support needs
the pattern language the AST lacks), the `??` and `|>` operators (no
two-character lexer tokens), and unary minus (the reference semantics has no
`unop .sub` rule, so `-e` parses but is stuck).

## Verification

- `lake build morph` ✔, `lake build Morph` ✔, `lake build Morph.Tests` ✔;
  zero `sorry`; the full mono section holds.

## Loop 72 — parse-to-de-Bruijn lowering: parsed bindings finally run (DONE, Lean)

**Target.** Loop 71 named the gap: the parser emitted `.fvar` for *every*
identifier while the evaluator binds `bvar` (`Context.pushBv`), so a parsed
`let x = 5 in x + 1` evaluated to `stuck`, not `6`; `fn` could not parse at
all (the cursor was never advanced past the keyword); and `parseFnParams`
dropped its parameters.

**Delivered** (`Morph/Frontend/Parser.lean`):
- `resolveIdent (scope) (name)` — the innermost binder for `name` becomes its
  de Bruijn index; unbound names stay `.fvar` (and so stay `stuck`, which is
  the correct semantics for a free name).
- Every parser function threads a `scope : List String` (innermost first).
  `let` parses its initialiser in the outer scope and its body in
  `name :: scope`; `fn` parses its body in `params ++ scope` — the
  accumulated parameter list is already innermost-first, and the outer
  bindings shift by `params.length`, which is exactly what `.lam`'s
  substitution performs.
- `parseAtom` now consumes the `fn` keyword before collecting parameters.
- The fuel-monotonicity section was restated over the threaded scope: every
  `parseX_mono` keeps its statement (more fuel never hurts) with `scope`
  fixed, and `parseExpr_seed_robust` seeds the empty scope.

**Result.** `let x = 5 in x + 1` → `6`; shadowing picks the innermost binder;
`(fn x y -> y - x) 3 10` → `7`; `let y = 10 in (fn x -> x + y) 5` → `15`
(closures over outer bindings); `morph run sq.morph` on
`let x = 5 in x * x` → `25`. Driver tests pin each of these.

**Named here, fixed in loop 73**: unit/array literals, postfix indexing and
the option/result prefixes. **Still named**: `match`/`for` expressions,
`??`/`|>`, unary minus, and statement-level (`Program`) execution.

## Verification

- `lake build morph` ✔ (the executable), `lake build Morph` ✔,
  `lake build Morph.Tests` ✔; zero `sorry`; the fuel-monotonicity lemmas hold
  unchanged in statement.

## Loop 71 — the `morph` executable, and the lexer bugs it exposed (DONE, Lean)

**Target.** The repository had no executable: parser, type checker and
evaluator were libraries with no way in. The driver loop adds `morph` —
`lake exe morph eval/parse/run` — and fixes what it surfaced.

**Delivered.**
- `Morph/Driver.lean`: the pipeline as a pure function
  (`runSource : String → Outcome`), with `Outcome` making every failure a
  *value* (`parseFailed`, `stuck`) — the driver cannot crash, because both
  stages it composes are proved-total components (parser, loops 9/39;
  evaluator, loop 38). `Main.lean` is an IO shell; `lakefile.lean` gains
  `lean_exe morph`.
- `Morph/Tests/Driver.lean`: end-to-end checks — precedence, comparisons,
  boolean operators, string concatenation, `if`, and the
  failure-is-a-value cases.
- **Lexer fix 1 — string literals.** `scanStringFuel` examined the character
  *after* the cursor and recursed past it, so it looked at one character in
  every two: `"hi"` lexed as `h`, `"abc"` produced *no token at all*, and two
  literals in a row produced nothing (the quirk `Morph/Tests/Lexer.lean` had
  pinned "so the bug is visible to whoever fixes it"). The scanner now
  examines the character under the cursor; the pinned tests are replaced with
  the correct behaviour, including escapes.
- **Lexer fix 2 — booleans.** `true`/`false` were missing from
  `keywordList`, so they lexed as identifiers and `parseLiteral`'s
  `.keyword "true"` cases were unreachable. `if true then 1 else 2` now
  evaluates.

**Named here, fixed in loop 72**: the parser emitted `fvar` for bound names
while the evaluator binds `bvar`, `fn` did not parse at all, and
`parseFnParams` dropped its parameters. **Still named**: unit/array literal
parsing and statement-level (`Program`) execution.

## Verification

- `lake build morph` ✔ (the executable), `lake build Morph` ✔ (389 jobs),
  `lake build Morph.Tests` ✔ (223 jobs); zero `sorry`.
- Smoke test: `morph eval "1 + 2 * 3"` → `7`; `morph run bad.morph` exits 1
  with the parse error; `morph` with no arguments prints usage and exits 1.

## Loop 70 — ModuleSystem: link tables, workspaces, mangling (DONE, Lean)

**Target.** `Morph/Specs/ModuleSystem/Spec.lean`'s four TODOs: module ID
uniqueness in well-formed link tables, link-table consistency, workspace root
validity, and symbol mangling injectivity (the last marked "Blocked on: String
reasoning in Lean 4").

**Model.** Three predicates on a `LinkTable`, composed into
`WellFormed t := keysMatch t ∧ keyNodup t ∧ depsResolved t`; a workspace
predicate `workspaceWellFormed w := w.root ≠ "" ∧ 0 < w.config.maxDepth ∧
WellFormed w.modules ∧ namesNodup w.modules`; and a structured
`MangledName (hash, version, symbol)` whose `renderMangled` is the shipped
textual form.

**Proved.**
- `wellFormed_key_unique` — two entries in a well-formed table with the same
  id *are* the same module. The proof indexes both occurrences and cancels
  them with `List.getElem?_inj` on the nodup key list.
- `wellFormed_deps_resolve` — every dependency of every stored module resolves
  to `some` module; `wellFormed_add` shows `addToLinkTable` preserves
  well-formedness when the added module's own dependencies resolve in the
  extended table (so the §5.2 diamond — `Log v1` and `Log v2` side by side —
  is fine: each version lists its own dependencies).
- `workspace_root_nonempty`, `resolveModuleByName_eq_some_of_mem_of_namesNodup`
  (name resolution finds exactly the stored module),
  `resolveModuleByName_deps_resolve` (workspace resolution composes with link
  consistency).
- `mangleName_injective` — the structured name is a faithful encoding.

**Refuted.** The textual mangling claim as the TODO stated it:
`mangleSymbol_not_injective`. Hash `"a"` at version 1 with symbol `"b_v2_c"`
collides with hash `"a_v1_b"` at version 2 with symbol `"c"` — both render to
`"a_v1_b_v2_c"` — because the rendering erases the separator boundary the
format was supposed to carry. The fix is the structured name; the textual form
is proved to be its rendering (`mangleSymbol_eq_render`), so every collision of
the string form is visible as a merge of two distinct structured names.

## Verification

- `lake build Morph.Specs.ModuleSystem.Spec / .Lemmas / .Examples` ✔.
- Full `lake build Morph` and `lake build Morph.Tests` ✔; zero `sorry`.
