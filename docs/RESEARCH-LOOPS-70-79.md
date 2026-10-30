# Research Loops 70–79 — Implementation Track

Loop 70 closes the last `Morph/Specs` TODOs. From here the track turns toward
*implementation*: the specifications are now dense enough that the most
valuable next iterations land their guarantees in the shipped compiler, not
only in `Morph/Specs`.

## Loop 79 — min-dialect `fix` (DONE, Lean)

**Target.** The last still-named item: the `min`-dialect `match` shape
(`fix`, per the `SyntaxTranslation` table). The `minToHum`/`humToMin`
string functions are still abstract stubs, and the parser note said one
dialect per construct — so this loop did both halves and resolved the
tension explicitly.

**Delivered.**
- `Lexer.lean`: `fix` joins `keywordList` (no identifier collisions
  anywhere in `Morph/`; the `TotalLexer` specs pin no keyword list).
- `Parser.lean`: `fix` is accepted everywhere `match` is (expression atom
  + `isAtomStart` + statement dispatch with the same `(` statement/expression
  split). Dispatch goes through `matchHead`, a fuel-free token-local
  rewrite of a leading `fix` to `match` — the hum parsers below run
  unchanged, and every monotonicity proof quantifies over the rewritten
  parser transparently (all mono theorems build untouched).
- `Frontend/Dialect.lean` (new): the executable token-level projection —
  `projectToken`/`projectMinToHum` map exactly the table entry the parser
  can observe (`fix`→`match`; the module-level entries never reach an
  expression, and the surface is already mixed). Keywords are classified
  pre-map, so identifiers (`prefix`), strings (`"fix"`), and comments
  cannot be confused. Proved: single-token and whole-stream idempotence,
  hum-streams project to themselves. (The condition is propositional
  `DecidableEq`, not `BEq`: `TokenKind` has no `LawfulBEq`, so the `==`
  bridge is unprovable — the same gap `Core.lean` documents.)
- Tests: `Dialect.lean` pins the map (`rfl` on explicit tokens) plus the
  idempotence theorem; `Driver.lean` pins `fix` end to end (expression and
  `match`-statement forms, same values as the `match` counterparts).

**Still named.** `minToHum`/`humToMin` stay string-level stubs (a full
string-to-string translation needs formatting-preserving re-emission, which
is tooling, not parsing); statement-`match` with a parenthesised scrutinee
is still rejected by design (parens mean the expression form).

## Verification

- `lake build Morph Morph.Tests morph` ✔ (all targets); zero `sorry`;
  no new warnings (the `Lexer.lean` unused-`l` is pre-existing).
- Smoke tests: `morph eval 'fix (some 1) { case some(x) => x + 10, case
  none => 0 }'` → `11`, and the `fix` statement-program twin → `11`.

## Loop 78 — `for`, unary minus, `match` statements (DONE, Lean)

**Target.** Loop 77's still-named list: `for` expressions, the `??`/`|>`
operators (done: surface only, semantics already existed), unary minus, and
`Stmt.matchStmt`.

**Delivered.**
- 78a `??`/`|>`: lexer tokens plus left-fold `Rest` parsers at their
  precedence levels (`|>` above `??`), with monotonicity proofs in the
  existing mould and driver tests (`none ?? some 1 |> fn x -> x`).
- 78b `for start in stop { body }`: inverts the pretty-printer
  (`exprStr` renders `forLoop` exactly so). The AST binds the iterator
  anonymously, so the body parses in the same scope. The stop position
  needed one grammar-level fix: `{` left `isAtomStart`, so `for 0 in 3
  { 42 }` swallowed the body as `app 3 [block]`. `while`/`match` dodge this
  by parenthesizing; `for` keeps the spec's bare shape (`for param in
  node.parameters { ...}`) instead — a `{` after an expression now always
  opens a structural block, never a trailing block argument (the language
  has no trailing-closure call syntax).
- 78c unary minus: prefix `-` already elaborated to `.unop .sub`, which had
  no step rule, no evaluator case, and no typing — it parsed but was stuck.
  Added `Step.unop_neg`, the `evalUnop` case, `HasType.unop_neg`, the
  `inferType` arm, and the Preservation/Progress/weakening/soundness cases
  (all mirroring `notb`). `-2 * 3` is `-(2*3)`; `-true` is stuck.
- 78d `Stmt.matchStmt`: `match scrut { case pat => { stmts } ... }`.
  The statement form drops the scrutinee parens — `parseStmt` routes
  `match (` to the expression form on that fuel-free `(` discriminant
  (same discipline as `parseIfAlt`), so there is no try-then-fallback and
  monotonicity holds. Arm bodies are brace-wrapped statement sequences
  (reusing `parseStmts`); the interpreter runs first-match-wins with
  pattern names (`patVars`) bound positionally from `matchPat`, propagating
  `break`/`continue`/`return` like an `if` branch and leaking the arm
  environment like one too. No-match is unit (`match_empty`).
- Collateral: the loop-76/77 `Pattern`-arm migration had left four modules
  red (`Soundness`'s `WellTypedValue` arities, and the old
  `List String × Expr` arm shape in `SubstTheory`/`MachineRelation`/`
  SimultaneousSubst` lemmas + examples). Migrated all to
  `patBindCount`-based binders. Also notable: bare `lake build` does not
  rebuild all targets (stale oleans observed) — verify with explicit
  `lake build Morph Morph.Tests morph`.

**Still named.** `min`-dialect `fix` (unchanged); statement-`match` with a
parenthesised scrutinee is rejected (parens mean the expression form);
`match` arm bodies that are bare `{ 42; }`-style blocks parse as statement
arms, not expression blocks (disjoint positions, so no ambiguity).

## Verification

- `lake build Morph Morph.Tests morph` ✔ (all targets); zero `sorry`;
  no new warnings in touched files (two pre-existing unused-simp warnings
  in `SubstTheory` left alone).
- Smoke tests: `morph eval "-5"` → `-5`, `--5` → `5`,
  `morph eval "for 0 in 3 { 42 }"` → `()`,
  `morph run` of a `match`-statement program binding `some(x)` → `11`.

## Loop 77 — surface syntax for `match` (DONE, Lean)

**Target.** Loop 76's still-named list opened with it: `match ...` failed to
parse in either dialect, so the newly typed-and-sound `match_` was
unreachable from source text.

**Delivered.**
- `Lexer.lean`: one new keyword, `case` (`match` was already one).
- `Parser.lean`: `match (scrut) { case pat => body, ... }` — the hum arm
  shape — as an expression. `parsePattern`/`parseWrapperPat` form a small
  standalone mutual pair (patterns contain no expressions): `_` (lexed as an
  identifier) is the wildcard, any other identifier binds, `none`/int/string
  /bool literals match by equality, and lowercase `some`/`ok`/`err` wrap one
  parenthesised sub-pattern, mirroring the expression constructors. Arm
  bodies parse with `patVars` in scope, matching `matchPat`'s left-to-right
  collection for today's at-most-one-binder patterns. `=>` lexes as `=` `>`;
  each arm takes an optional trailing comma. `parseMatchExpr`/
  `parseMatchArms` join the big fuel-mutual block with dispatch from
  `parseAtomPrimary` (plus `isAtomStart`, so matches compose as call
  arguments). The `min`-dialect `fix` shape stays named: one dialect per
  construct is the executable parser's established pattern.
- Monotonicity: `parsePattern_mono`/`parseWrapperPat_mono` (own mutual
  block) plus `parseMatchExpr_mono`/`parseMatchArms_mono` in the existing
  mono block, wired into `parseAtomPrimary_mono` — the exact
  `match n / rw [Nat.succ_add] / repeat' split / first ... exact ...` mould.
- Tests (`Morph/Tests/Driver.lean`): payload binding, miss fall-through,
  first-match-wins, literal patterns, wildcard catch-all, nested wrappers,
  and one statement-position check (an expression statement — there is still
  no `Stmt.matchStmt` node).

**Result.** `match` is reachable from source: parse, typecheck (loop 76's
rules), and evaluate agree end to end through both `runSource` and
`runProgram`, with zero `sorry` and no new warnings.

**Still named.** `for` expressions/statements, the `??`/`|>` operators,
and unary minus (unchanged); the `min` `fix` match shape; `Stmt.matchStmt`.

## Verification (loop 77)

- `lake build` ✔ (all targets, plus `Morph.Tests.Driver/Typing/Executable/
  Lexer` explicitly); zero `sorry`; the only warning in touched files is the
  pre-existing `Lexer.lean:249` unused-`l` (confirmed via `git stash`).
- Smoke tests: `morph eval 'match (some 1) { case some(x) => x + 10, case
  none => 0 }'` → `11`,
  `morph eval 'match (none) { case some(x) => x, case _ => 99 }'` → `99`.

## Loop 76 — `match` expressions, end to end (DONE, Lean)

**Target.** Loops 73–75 all named it: `match_` evaluated (first arm wins)
but had no typing and no soundness story — no `Pattern` language, no rule
for when a successful match binds well-typed values, and no preservation
case for stepping into an arm body.

**Delivered.**
- `Syntax.lean`: the `Pattern` language
  (`wild`/`var_`/`lit_`/`none_`/`some_`/`ok_`/`err_`) and `matchPat`, which
  matches over *both* evaluated `.lit` values and raw constructor forms (a
  small-step scrutinee can be `IsValue` without being normalised, e.g.
  `.some_ e`), plus `matchPat_length` (a successful match binds exactly the
  pattern's binder count).
- `Specs/TypeSystem/Spec.lean`: `PatTyped`/`ArmsTyped`; the option/result
  *literal* rules carry payload premises (`lit_some`/`lit_ok`/`lit_err`
  require the payload typed at the inner type), and the constructor forms
  get `some_type`/`none_type`/`ok_type`/`err_type`.
- Preservation: `matchPat_sound` — a successful match yields `HasTypeAll`
  at exactly the pattern's bound types (`lit_`/`none_` bind nothing and need
  no inversion). `match_hit` substitutes the bound values into the arm body
  via `HasType_iterSubst`, with the length side-condition discharged by
  `matchPat_length`/`patTyped_length`; `match_miss`/`match_empty` retype
  directly. The `*_none_done` steps invert the inner `none_` typing to pin
  the payload type. The `subst`-of-literal cases recurse on the payload
  premise and reduce definitionally.
- Progress: the scrutinee-step/hit/miss/empty cases, plus the
  null-coalesce literal cases.
- Tests pin it at both levels: evaluation (`first-match-wins`, empty match
  yields none) and synthesis (arm-shape mismatch rejected).

**Result.** `match` is now typed and sound, not just executable: the
preservation/progress proofs cover every new rule, and the full build holds
with zero `sorry`.

**Still named.** Surface syntax for `match` (the parser has no `match` arm
— `match ...` currently fails to parse, in either dialect), `Stmt.matchStmt`,
`for` statements, the `??`/`|>` operators, and unary minus (unchanged from
loop 75).

## Verification

- `lake build` ✔ (all targets, including `morph` and `Morph.Tests`); zero
  `sorry`; no new warnings in touched files.
- Smoke tests: `morph eval "1 + 2 * 3"` → `7`,
  `morph eval "let x = 5 in x * x"` → `25`,
  `morph eval "some (1 + 1)"` → `some (2)`,
  `morph run fact.morph` → `720`.

## Loop 75 — the `if` statement (DONE, Lean)

**Target.** Loop 74's still-named list opened with it: no `if` statement in
the `Stmt` AST, so `break`/`continue` had no guarded form except loop
conditions.

**Delivered.**
- `Syntax.lean`: `Stmt.ifStmt : Expr → List Stmt → List Stmt → Stmt`
  (condition, then-branch, else-branch; bare `if` carries `[]`).
- `Parser.lean`: `parseIfStmt` (`if (c) { .. } [else { .. } | else if ..]`,
  with `else if` chains nested as a singleton else-branch) and `parseIfAlt`,
  wired into `parseStmt`'s `if` arm.
- The dispatch is a **fuel-free syntactic split** (`parseIfAlt`): `(` after
  `if` tentatively opens the statement shape, then `skipParen` scans past
  the balanced group token-by-token and `{` after the matching `)` commits
  to `if (c) { .. }` — anything else falls back to the expression statement
  `if c then a else b;`, including a parenthesised-condition expression-`if`
  (`if (c) then ..`). A try-statement-then-fallback would not be
  fuel-monotone — more fuel can flip the first branch `none` → `some`,
  changing the result — so `parseIfAlt_mono`/`parseIfStmt_mono` sit in the
  monotonicity block in dependency order, with every split discriminant
  fuel-free. The scan is token-level, so parens inside string literals never
  confuse it — pinned by a parse-level test (`if ("(") then ..` takes the
expression branch) plus nested-paren tests on both dispatch sides.
- `Interp.lean`: the `runStmts` case evaluates the condition, runs the taken
  branch from a unit accumulator, and propagates `break`/`continue`/`return`
  (only a completed branch falls through via `acc.replace`).

**Result.** Driver tests pin `if (true/false)` both directions, an
`else if` chain, fall-through leaving the environment intact, and guarded
`break`/`continue` inside `while` (the loop-74 gap that motivated this).

**Still named.** `match`/`for` statements, `??`/`|>` operators, unary minus
(unchanged from loop 74).

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

**Still named.** No `if` *statement* in the `Stmt` AST — closed in loop
75 — (conditionals are the expression form; `break`/`continue` therefore
have no guarded form except loop conditions), no `match`/`for` statements,
no `??`/`|>` operators, and unary minus still parses-but-sticks (the
reference semantics has no `unop .sub` rule).

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
