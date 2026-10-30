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
