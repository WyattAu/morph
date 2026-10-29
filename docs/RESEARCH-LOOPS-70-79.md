# Research Loops 70–79 — Implementation Track

Loop 70 closes the last `Morph/Specs` TODOs. From here the track turns toward
*implementation*: the specifications are now dense enough that the most
valuable next iterations land their guarantees in the shipped compiler, not
only in `Morph/Specs`.

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

**Still named.** Unit/array literals and `match`/`for` expressions are not
parsed; statement-level (`Program`) parsing and execution do not exist yet.

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
