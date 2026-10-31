# Changelog

All notable changes to Morph are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/); versioning follows
`STABILITY.md` (SemVer, 0.x: minor bumps may break experimental surface).

## [0.1.0] — 2026-10-31

First versioned release: the `morph` CLI over the verified pipeline.

### Added

- `morph eval <expr>`: parse and evaluate an expression (exit 0 with the
  value; exit 1 with the parse report or the stuck report).
- `morph parse <expr>`: print the parsed AST without evaluating.
- `morph check <expr>`: print the inferred type or the exact type error.
- `morph run <file>`: run a statement program; the last expression
  statement is the value, `return` short-circuits.
- `morph run --hir <file>`: run through HIR lowering. First-order
  let/match/while programs evaluate identically to the direct interpreter
  (loop 88 agreement); anything outside the fragment reports
  `program leaves the HIR fragment ...` with exit 1.
- `morph fmt <file>`: print the canonical (`hum`) rendering of a program.
  Formatting is a fixpoint; declarations print in surface syntax so formatted
  output always reparses (loop 90).
- `morph doc <file>`: render the file's `///` documentation comments as
  Markdown. A run of `///` lines documents the next statement; the lexer
  skips them like ordinary comments, so documented files run unchanged.
- `morph version`: print the release version (`0.1.0`).
- Error-message goldens: every user-visible error byte is pinned by tests —
  parse reports (`line 1, col 1: failed to parse`, `line 0, col 0: empty
  input`), the stuck report, `check` type errors, and the `--hir`
  unsupported message.

### Verified

- The parser and both evaluators (direct and HIR statement interpreters)
  are proved-total components; failure is an `Outcome` value, never a crash.
- HIR lowering agrees with direct evaluation on the first-order fragment
  (outcome-level agreement theorem plus the expression/statement inversions).
- 1508 machine-checked theorems, 0 `sorry`, 0 axioms, 0 build
  warnings/errors; spec lint and cross-reference checks green.

### Known limitations

- `morph check` checks against elaboration only (checking against an
  expected type needs type-syntax parsing — still named future work).
- Two `AbiDataRefinement` spec Props overstate their claims (see
  `SPEC_CONTRADICTIONS.md` #11); the validated conditional forms are
  pinned in `Morph/Specs/AbiDataRefinement/Lemmas.lean`.
- Statement `let` takes no type annotation; the pretty-printer drops the
  elaborator's placeholder type so output stays in surface syntax.
