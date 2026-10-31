# Research Loops 80–89 — Property Testing Track

Loop 79 closed the last named surface item (`fix`). From here the track turns
toward *properties of the shipped implementation*: universal statements over
the evaluator and the parse/pretty-print round trip, checked by Plausible
sampling (`#test`), `native_decide`, and proof — instead of single-example
driver pins.

## Loop 80 — property tests over the evaluator and the round trip (DONE, Lean)

**Target.** The `Morph/Tests/Property.lean` module sampled four `#test`
properties but proved nothing about the shipped pipeline: no universal
statement over `evalWithFuel`, and no check that `exprStr` output reparses
to the same tree. This loop closes both, in the style the file already uses
(sampling where types lack decidability, proof/examples where they do).

**Delivered.**
- `Arbitrary`/`Shrinkable` instances for `Phase`, `BlockId`,
  `ProvenanceId`, `Pointer`, `Value` (constructor-discriminated shrink),
  `Typ` (base types), and `Operator` (full 24-constructor enumeration), so
  `plausible` can generate random test values. No `lakefile.lean` change
  was needed: `Plausible` resolves through the existing
  mathlib/batteries/aesop dependency closure (pinned in
  `lake-manifest.json`).
- `EvalLawProperties` (new): five *universal* theorems over the shipped
  evaluator, all with explicit `k + n` fuel so the equation lemmas fire
  (`fuel 0` evaluates nothing, so the statements need positive fuel):
  literals evaluate at any positive fuel; negation is involutive
  (`- -n = n` via `omega`); addition commutes on evaluated literals;
  a `for` loop whose bounds already meet runs zero iterations without
  touching the body (even a stuck one); `none ?? e` is `e` up to one fuel
  unit for the dispatch.
- `RoundTripProperties` (new): six `native_decide` pins that `exprStr`
  output reparses to the same tree — nested mixed-precedence operators,
  unary minus through its parentheses, `if`, `for` through its bare
  surface (loop 78b), single-level `??`, single-level `|>`. Same style as
  `Morph.Tests.Driver` (seeded `parse`, `==` on the tree).
- Pre-existing sections untouched: `CoreProperties`, `OperatorProperties`
  (disjointness + `Semantics`/`TypeSystem` classification agreement),
  `TypeInversionProperties` (now noting the `lit_int_width` disjunction),
  `EvalProperties` (div/mod-by-zero `none`), `LiftSubstProperties`
  (concrete `substAll' ... []` identity cases; the general law lives in
  `Lemmas.lean` as `liftUnder_zero_eq` because `substAll'` uses
  well-founded recursion and resists `rfl`).

**Still named.** `Expr` has neither `BEq`-lawful equality bridges nor
`Arbitrary`, so inversion/lift properties stay concrete examples rather
than sampled `#test`s (same `DecidableEq`-vs-`BEq` gap `Core.lean` and
loop 79 document). Value comparison in `tests/differential` stays future
work: the Lean/Rust top-level intersect is still empty and Rust `run`
still does not execute, so verdicts — not values — compare.

## Verification

- `lake build Morph Morph.Tests morph` ✔ (408 + 229 jobs); zero `sorry`,
  zero `axiom`, zero `example : True` stubs repo-wide.
- `Morph.Tests.Property` reports 4× `Unable to find a counter-example`
  (the `#test` sample pins); the 5 eval laws + 6 round-trip pins typecheck
  as theorems/examples.
- `tests/differential/diff.sh` ✔ 8/8 cases match the manifest (4 Lean-ok /
  Rust-reject, 4 Rust-ok / Lean-reject — the documented divergence map).
- `spec-tools` pytest ✔ 803 passed, 96.04% coverage.
- Counts at commit: 209 `.lean` files / ~42.3k lines, 1130
  `theorem`/`lemma` declarations.

## Loop 81 — zero-warning gate (DONE, Lean + CI)

**Target.** PATH_FORWARD §2.1 / ROADMAP §2.1: the sorry gate was already
blocking, but the warning gate was advisory (`::warning::`), and 89
linter warnings stood between the repo and a hard zero-warning CI.
This loop clears them and flips the gate.

**Delivered.**
- Fixed all 89 `warning: Morph/` linter hits, mechanically and without
  changing any statement: 20 unused-variable binders prefixed with `_`
  (`Serve._q`, `progress_invariant._hp`, `progress_not_deadlock._rank`,
  `NonInterference._high`, `gcd._h` with its `decreasing_by` updated,
  `tokenizeLoop._l`, `Interp._fuel`/`_acc`, `LoweringLemmas._v`/`_s`, plus
  seven more in `MemoryBounds`/`TaintFlow`/`DialectSemantics`/
  `ExecutionMachine`/`SimultaneousSubst`); 69 unused `simp` arguments
  omitted exactly as the linter hinted (`Nat.add_assoc` × 17 in
  `SimultaneousSubst/Spec`, `hnum`/`hid`/`hop` in `TotalLexer`,
  `hA`/`Option.some.injEq` in `LoweringLemmas`, and the rest across
  `LexicalStructureSyntax`, `MorphLanguage`, `TaintFlow`, `SubstTheory`,
  `DialectSemantics`, `EffectAlgebra`, `MachineRelation`,
  `ActorDeadlock`, `MemoryBounds`, `StealingFairness`, and
  `Frontend/Parser`). Residual `simp []` normalized to `simp`.
- Hardened `.github/workflows/lean-build.yml`: the warning step now
  fails the build (`::error::` + `exit 1`); the stub step now fails on
  any `example : True := trivial` (count is 0, so any regression
  blocks). `.githooks/pre-commit` stub check flipped from warn to
  block, matching its sorry check.

**Still named.** `Morph/Tests` build info lines (`Unable to find a
counter-example` — Plausible success reports, not linter warnings)
are untouched; the gate greps `warning: Morph/` only. Nightly/billing
and the 26 broken-link / numbering items are separate tracks.

## Verification

- `lake build Morph` ✔ 394 jobs, **0 warnings, 0 errors** (forced
  recompile of all touched files, full log captured).
- `lake build Morph.Tests` ✔ 229 jobs; 0 `sorry`, 0 stubs repo-wide.
- `tests/differential/diff.sh` ✔ 8/8 cases match the manifest.
- Gate behavior reviewed by reading the workflow/pre-commit text (CI
  itself is blocked on billing, so the `exit 1` paths are verified by
  inspection, not by a live run).

## Loop 82 — name resolution, HIR lowering, `morph check`, spec-status CI (DONE, Lean)

**Target.** The roadmap's open implementation spine (§6.1 remainders,
§6.2 error reporting, §5.2 status automation) plus the doc staleness
called out in discussion: both roadmaps still prescribed SlimCheck and
an advisory warning gate, and carried May tables with October patches
bolted on.

**Delivered.**
- `Frontend/NameResolution.lean` (new): the occurrence decision moved
  out of the parser unchanged, plus the structural `resolveExpr` pass
  whose scope extensions mirror the parser exactly (`match_` arms see
  `patVars`; anonymous `lam`/`let_`/`forLoop` slots pass the scope
  through). Proved: `resolveIdent` fires exactly on membership
  (`resolveIdent_self/of_mem/of_not_mem` over `findIdx?`), the pass is
  a projection (`resolveExpr_idem`), name-free trees are fixed points
  (`resolveExpr_closed` via `hasFVar`). `Expr` is nested inductive, so
  definitions and proofs use the codebase's `mutual` pattern (à la
  `liftUnder`), not the `induction` tactic. `Parser.parseIdentifier`
  now calls it; behavior identical (all driver tests untouched and
  green). Tests: `Morph/Tests/NameResolution.lean` (occurrence pins,
  arm-extension pin, projection/fixed-point instantiations, parse-then-
  resolve end-to-end).
- `Frontend/HIRLower.lean` (new): `toHIR : Expr → Option HIR.Expr`
  in the `lowerIn` partial-lowering discipline. De Bruijn slots map to
  `Id ⟨n, "bv"⟩` (binders agree by index); free names map to
  `⟨0, "free:" ++ x⟩`. Supported: variables, literals, unop/binop,
  variable-applied `app`, `lam`/`let_`/`ifThenElse`/`block`, `match_`
  over `wild`/`lit_`/`var_` patterns. Rejected (`none`): `field_`/`pipe`/
  `typeAsc`, all option/result constructors, tuples/arrays/indexing, all
  `ref*`, `forLoop`, non-variable application, complex patterns. Pinned
  as equation theorems per constructor plus `Morph/Tests/HIRLower.lean`
  (structural pins + parse-to-HIR end-to-end both ways). Semantic
  preservation is named future work: HIR has no evaluator yet.
- `morph check` (new CLI command): `Driver.checkSource` parses then
  synthesizes (`synthType [] []`); success prints the inferred type, failure
  prints `formatTypeError`'s message via a new `Outcome.typeError`
  (exit 1). The `formatTypeError` dummy expectation never surfaces —
  without an annotation only the cannot-infer branch is reachable.
  `eval`/`parse`/`run` behavior unchanged. Tests in `Tests/Driver.lean`;
  smoke-tested (`check "1 + 2"` → `intType`, `check "1 + true"` →
  cannot-infer, exit 1).
- Spec-status CI: `lean-build.yml` runs `gen-spec-status.sh` and fails
  on drift vs the committed `.reports/spec-status.md` (date line
  excluded); the committed report was genuinely stale (ModuleSystem /
  TypeSystem / MorphLanguage growth) and is refreshed here.
- Docs: SlimCheck → Plausible corrected in both roadmaps (loop 80
  used Plausible via the mathlib closure, no lakefile change); warning/
  stub gates marked done (loop 81); §6.1/§6.2 rows marked delivered;
  cross-pointers added (`PATH_FORWARD` = execution view, `ROADMAP` =
  status view, live progress in `RESEARCH-LOOPS`, counts in
  `.reports/spec-status.md`).

**Still named.** Statement-level resolution (statements thread the scope
but never extend it — one observation, no pass needed yet); HIR
`Stmt`/`Program` lowering; `check` against an expected type (needs type
syntax parsing); the 26 broken links / numbering lint (noise, not risk);
Rust/C++ runtime (separate track).

## Verification

- `lake build Morph Morph.Tests morph` ✔ 416 jobs, **0 warnings,
  0 errors**; 0 `sorry`, 0 stubs repo-wide.
- `tests/differential/diff.sh` ✔ 8/8 cases match the manifest.
- `spec-tools` pytest ✔ 803 passed, 96.04% coverage.
- Counts at commit: 213 `.lean` files / ~43k lines, 1160
  `theorem`/`lemma` declarations, 16 `Morph/Tests/` files.

## Loop 83 — HIR statement/program lowering (DONE, Lean)

**Target.** Loop 82 lowered expressions but left the §6.1 row half-open:
`HIR.Stmt`/`HIR.Program` had no map into them. This loop closes the row
(the remaining §6.1 item is now only runtime-adjacent work, out of scope
for the Lean track).

**Delivered.**
- `toHIRStmt`/`toHIRStmtList`/`toHIRProgram` in
  `Morph/Frontend/HIRLower.lean`, same `Option` discipline as the
  expression pass. Surface statements are name-based (`Syntax.Id` is
  just a name; they never entered the de Bruijn system), so lowering is
  scope-free: embedded expressions go through `toHIR`, identifiers map
  to `Id ⟨0, name⟩`. `whileLoop` lowers; `doWhile` (at-least-once
  semantics has no HIR counterpart, and desugaring would change
  meaning), `ifStmt`, and `matchStmt` (HIR statements have no
  conditional or match) are `none`. The scope-extending `matchStmt`
  arms need no scope threading precisely because the statement rejects.
- Contract theorems per statement class (`break`/`nop` identity,
  `doWhile`/`ifStmt`/`matchStmt` rejection, `varDecl` name mapping,
  empty-program identity) plus test pins in `Morph/Tests/HIRLower.lean`,
  including parse end-to-end both ways (`let y = 5; y` lowers, a `match`
  statement program does not).

**Still named.** HIR evaluation semantics (preservation proofs await
it); `check` against an expected type (needs type-syntax parsing); the
26 broken links / numbering lint; the Rust/C++ runtime track.

## Verification

- `lake build Morph Morph.Tests morph` ✔ 416 jobs, **0 warnings,
  0 errors**; 0 `sorry`, 0 stubs repo-wide.
- `tests/differential/diff.sh` ✔ 8/8 cases match the manifest.
- `spec-tools` pytest ✔ 803 passed, 96.04% coverage.
- Counts at commit: 213 `.lean` files / ~43k lines, 1167
  `theorem`/`lemma` declarations, 16 `Morph/Tests/` files.

## Loop 87 — HIR statement interpreter + `morph run --hir` (DONE, Lean)

**Target.** Loops 82/83 lowered expressions, statements, and programs to
HIR but never executed them: HIR had no statement semantics, and the
`run` pipeline was surface-only. This loop closes the §6.1 execution
row: run lowered programs and ship the flag.

**Delivered.**
- `Frontend/HIRInterp.lean` (new): `runHIRStmts`/`runHIRWhile`/
  `runHIRProgram`, mirroring `Morph.Interp` stage by stage over `HEnv`
  (`HFlow`/`HRan`, `updateHEnv` with propositional equality like
  `lookupHEnv`, loop-value-is-unit convention, `break`/`continue`/
  `return` propagation). Expression positions evaluate with `evalHIR`
  seeded at 256 — the same seed as surface `Executable.eval` — and the
  statement fuel matches `Interp.runProgram` (1024). `doWhile`/`ifStmt`/
  `matchStmt` need no mirror: they never lower.
- `morph run --hir <file>` (new CLI arm): `Driver.runProgramHIR`
  parses, lowers via `toHIRProgram`, and runs the HIR interpreter. A
  program that leaves the fragment reports the new
  `Outcome.unsupported` (exit 1) instead of running — `Main.finish`
  and `Driver.report`/`usage` extended; `isUnsupported` added beside
  the other outcome predicates.
- Namespace fix (found by executing, not by reading): loop 83 mapped
  statement identifiers to `Id ⟨0, name⟩` while the expression pass maps
  free names to `⟨0, "free:" ++ name⟩`, so no lowered program with a
  variable could evaluate — and a statement variable named `"bv"`
  would have captured binder slot 0. Statement `varDecl`/`assign` ids
  now join the `free:` namespace (surface identifiers never contain
  `':'`, so the prefix is injective, and `hirId_free_ne_bv/ctx` keeps
  them disjoint from binder/slot ids). The `toHIRStmt_varDecl`
  contract theorem and both pins updated; the rationale is recorded in
  the `toHIRStmt` doc block.
- Tests in `Morph/Tests/HIRLower.lean`: declaration/read, assignment,
  a counting loop, `return`-from-`while`, and the `unsupported` path
  for an `if` program — all `native_decide` through `runProgramHIR`.
  Three unused-`simp`-arg warnings in the loop-86 `match_` proofs
  removed along the way (gate stays at zero warnings).
- Smoke-tested the built binary: `run` and `run --hir` agree (`10`)
  on a counting-loop file; `run --hir` on an `if` program prints the
  fragment message with exit 1.

**Still named.** Statement-level preservation (the 4e half of this
sprint: relating `runHIRStmts` to `runStmts` across `toHIRProgram`);
`check` against an expected type; the 26 broken links / numbering lint;
the Rust/C++ runtime track.

## Verification

- `lake build Morph` ✔ 400 jobs, **0 warnings, 0 errors** (forced
  recompile of all touched files).
- `lake build morph` ✔ exe relinked; CLI smoke test above ✔.
- `Morph.Tests.HIRLower` ✔ 5 new `runProgramHIR` examples green.

## Loop 88 — statement-level preservation (DONE, Lean)

**Target.** Loop 87 ran lowered programs but proved nothing about them:
`evalHIR_preservation` agreed on one expression while `runHIRProgram`
ran whole statement sequences on faith. This loop closes the 4e half:
relate `runHIRStmts` to `runStmts` across `toHIRProgram`.

**Delivered.**
- `stmtFirstOrder` in `HIRLower.lean`: the proved statement fragment
  (every embedded expression `FirstOrder`; lowering success alone does
  not imply it — `toHIR` also maps `lam`/variable-applied `app`).
- `agreeBoth`/`runHIRProgram_preservation` in `HIRInterp.lean`: when
  `toHIRStmtList ss = some ss'` and every statement is `stmtFirstOrder`,
  related environments stay related and surface success is HIR success
  — for statements and `while` loops, mutually, by induction on fuel.
  The relation is lookup-based (`relStmtEnv`: every surface `getFv?`
  hit is a literal the HIR side sees under the `free:` id), the
  conclusion is one-directional like `evalHIR_preservation` (a stuck
  surface run imposes nothing, so failure coincidence is never owed).
  Supporting lemmas: `free:`-injectivity, `getFv?`/`lookupHEnv`
  cons/update characterizations, declaration/assignment preservation
  (`relStmtEnv_push/update`), lowering inversions, outcome inversions.
- Visibility change: `Interp.runStmts`/`runWhile` (and the HIR
  runners) are no longer `private` — the cross-stage theorem must name
  both sides. The statement is about `ranStmts`-level agreement with
  the program corollary at the `runProgram` fuel (1024).
- Snapshot: `scripts/regression-snapshot.sh` ✔ no regressions;
  total theorems 1395 → 1424, modules 214 → 215, warnings still 0.

**Still named.** `check` against an expected type (needs type-syntax
parsing); the 26 broken links / numbering lint; the Rust/C++ runtime
track.

## Verification

- `lake build Morph` ✔ 400 jobs, **0 warnings, 0 errors**.
- `lake build morph` ✔ exe relinked; `run`/`run --hir` agree (`10`)
  on the counting-loop file; `run --hir` on an `if` program still
  reports the fragment message with exit 1.
- Regression snapshot ✔ recorded, no regressions, +29 theorems.

## Loop 89 — error-message golden tests (DONE, Sprint 5)

- Pinned the exact user-visible error bytes nobody had pinned: the
  old tests only checked *variants* (`isParseFailed`, `isStuck`).
- `Morph/Tests/Driver.lean`: `runSource` parse-failure goldens
  (`"1 +"`/`"!!"`/`"@"` → `line 1, col 1: failed to parse`;
  `""` → `line 0, col 0: empty input`), stuck equalities (no message),
  `usage` help text (caught a transcription slip — the real text ends
  with `\n`), `report .stuck`, `checkSource` type-error goldens, and
  the `--hir` unsupported message plus a `--hir` success golden.
  `Outcome` has no `DecidableEq`, so goldens use the file's `==` style.
- `Morph/Tests/Typing.lean`: new `ErrorMessageTests` section pinning
  `formatTypeError` strings both ways (mismatch + cannot-infer,
  including the two-space `repr` continuation indent).
- `Morph/Tests/HIRLower.lean`: rejection goldens for every previously
  unpinned `none` arm (`nullCoalesce`, `some_`, `ok_`, non-variable
  `app`, `arrayLit`, `some_` patterns, `matchStmt`, an `ifStmt`
  program) plus a `whileLoop` lowers-positive.
- CLI verified end-to-end: `eval '1 +'` prints the golden bytes on
  stderr with exit 1; `check '1 + true'` likewise.
- Snapshot: `scripts/regression-snapshot.sh` ✔ no regressions;
  total theorems 1424 (unchanged — `example`s aren't theorems),
  LOC 45698 → 45817, warnings still 0.

## Loop 90 — `morph fmt` + `morph doc` (DONE, Sprint 6)

- `morph fmt <file>` = `Driver.formatProgram` (parse + canonical `hum`
  `renderCode`); `morph doc <file>` = `Driver.docSource` (Markdown from
  `///` entries). Both wired in `Main.lean`, both pinned by goldens.
- Blocker found by probing: `stmtStr` printed `let y: unit = 5`, which the
  parser rejects (statement `let` takes no annotation — the type is a
  placeholder). A formatter must round-trip, so `stmtStr` now prints
  surface syntax (`let y = 5`); the two spec pins
  (`Lemmas`/`Examples`) updated from `let x: int = 5`. Type-syntax
  parsing stays deferred (still named). Fixpoint golden:
  `formatProgram "let y = 5;\ny"` is stable.
- New `Morph.Frontend.DocComment`: `///` blocks (one space stripped)
  attach to the next code line across blanks/plain-`//` lines; trailing
  blocks drop; `renderMarkdown` emits `# Documentation` + `## \`code\``
  sections, or the empty note. No lexer/parser change — `///` already
  lexes as a `//` comment, pinned by a documented-file-still-runs test.
- Spec: `lexical_structure_syntax_spec.md` §1.3 `///` behavior += `morph
  doc` tooling note; file lint ✔ clean.
- CLI verified on a demo file (`fmt`/`doc`/`run` all exit 0; `run` → `3`).
- Snapshot ✔ no regressions; modules 215 → 216, LOC 45817 → 45951,
  warnings still 0.

## Loop 91 — depth re-audit across the 58 Specs modules (DONE, Sprint 7)

- Audit: 58 topic dirs, all with a `Lemmas.lean`; no axioms, no sorries.
  Total 1424 → goal ≥1500 real theorems (+76 needed, `example`s excluded
  from the count). Thinnest-first, every addition a property of the
  module's own defs (no padding: the audit kept the loop-17 convention of
  recording findings as theorems).
- `DialectProjection` 1→14: capability facts, validity-table positives +
  the self-projection negative, `equiv` refl/symm/trans, `lower_into_target`
  (nested induction mirroring `lower_identity`). Quirk: multi-line `{ s with
  ... }` updates fail to parse — single-line form used.
- `MonadicEffect` 2→16: `effectName`/`canHandle`/`effectNames`/`contains`/
  `findHandler` facts (hit/miss/skip-top). Dotted-ctor fix: `EffectOp.read`.
- `ExecutionModel` 3→15: `subst` hit/miss/shadow, env lookup/shadow,
  `isTerminal` all three, trace counting. (Pre-existing Nat fillers kept.)
- `Financial` 3→19: codes, decimal places, major-unit round-trip, add/sub
  same/cross-currency, non-negativity, `isBalanced` triviality.
- `LexicalStructureSyntax` 3→16: keyword/char/delimiter facts.
- `AbiDataRefinement` 4→10: validation outcomes, compatibility pins, and
  two spec refutations (`spec_layout_compatibility_false`,
  `spec_data_validation_false`) — the mapping summary's ✓ overstates.
  Logged as SPEC_CONTRADICTIONS.md #11 (revision proposed, not applied).
- `DocComment` +7 contract pins (`native_decide`: String internals are
  kernel-opaque, `rfl`/`decide` fail — same class as the `usage` fixpoint).
- Snapshot ✔ no regressions (2 improvements); total theorems **1508**,
  build 401 jobs, 0 warnings/errors, sorry count 0.

## Loop 92 — Morph 0.1 release artifacts (DONE, Sprint 8)

- `CHANGELOG.md` (Keep a Changelog, 0.1.0 entry: seven CLI commands,
  error goldens, fixpoint `fmt`, HIR agreement, 1508 theorems) and
  `STABILITY.md` (SemVer tiers: CLI + error text + core syntax + `fmt`
  form + proof invariants stable; `--hir` membership, `doc` layout,
  spec Props experimental; deprecation + snapshot mechanics).
- Version constant: new `Morph/Version.lean` (`versionString = "0.1.0"`),
  `morph version` in `Main.lean` (exit 0), usage line, golden test.
  No `git tag` cut — left as the release step.
- Snapshot ✔ no regressions (1 improvement); build 402 jobs, 0 warnings.

## Loop 93 — external audit packet prep (DONE, Sprint 9 prep; gate open)

- `docs/AUDIT-PACKET-0.1.md`: scope, proved-vs-trusted inventory (totality,
  HIR agreement, soundness, substitution theory, 1508 theorems / 0 sorry /
  0 axioms), trust base (toolchain, spec text — auditor warned that ✓
  marks are claims, citing #11), known issues (3 handed over), repro
  steps, reviewer entry points.
- **Hard gate NOT cleared: review invitations are unsent.** Packet
  authorship ≠ Sprint 9 completion; invites need the maintainer.
