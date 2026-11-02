# Research Loops 103–112 — HIR Statement Coverage

> Loops 103–110 shipped batch specs (BatchBCD/BatchFGH/BatchHIJ/P1–P5) with
> briefs + ADR records but no heartbeat entries. Loop 111 closed
> Contradiction #11 (AbiDataRefinement). Loop 112 closes the HIR statement gap.

## Loop 111 — AbiDataRefinement resolution

- `Spec.lean` weakened to validated conditionals (`refinesLayout`
  characterization; validity needs offsets + size match; compatibility
  implies field agreement).
- Proved as `spec_type_refinement_holds`, `spec_data_validation_holds`,
  `spec_layout_compatibility_holds`.
- `SPEC_CONTRADICTIONS.md` #11 marked resolved; refutations retained in git history.

## Loop 112 — HIR `ifStmt`/`matchStmt` (this pass)

**Problem.** HIR had expressions `ifThenElse`/`match` but statements only
`whileLoop`. Surface `ifStmt`/`matchStmt` lowered to `none` with pinned
theorems. Era-1 exit asks for full-fragment lowering.

**Work.**
- `Morph/HIR.lean`: added `Stmt.ifStmt : Expr → List Stmt → List Stmt → Stmt`
  and `Stmt.matchStmt : Expr → List (Pattern × List Stmt) → Stmt`.
- `Morph/Frontend/HIRLower.lean`: `toHIRStmtPat` (var binds `free:`-id,
  matching `runMatchArms` `patVars`-zip discipline), `toHIRStmtArms`,
  `toHIRStmt` cases for `ifStmt`/`matchStmt`; `stmtFirstOrder` extended via
  mutual `stmtArmsFirstOrder`; inversion theorems `toHIRStmt_if`,
  `toHIRStmt_match`, `toHIRStmtArms_cons`; `doWhile` stays `none` with
  pinned reason (at-least-once vs `whileLoop`).
- `Morph/Interp.lean`: `runDoWhile`/`runMatchArms` made public for the
  preservation proof (no semantics change).
- `Morph/Frontend/HIRInterp.lean`: `runHIRStmts` cases for `ifStmt`/
  `matchStmt`, `hirPatVars` + `runHIRMatchArms` (first-match-wins, mirroring
  surface); bridge lemmas (`toHIRStmtPat_shape`, `matchStmtPat_nobind`,
  `relStmtEnv_match_var`, `stmtArmsFirstOrder_mem`, `toHIRStmtArms_mem`);
  `agreeBoth` extended to triple (statements, while, match-arms);
  statement `ifStmt`/`matchStmt` cases proved; match-arms agreement at
  succ proved by cases (hit via `ihS`, miss via `ihM`).
- `Morph/HIRToMIR.lean`: new constructors rejected (`none`, single-block
  MIR has no control flow); proof cases added.
- `Morph/Tests/HIRLower.lean`: updated pins (if/match lower, programs stay
  in fragment); new goldens (`if (true)… → 1`, var-pattern match → 1).

**Exit.** `lake build Morph Morph.Tests` 454 jobs, 0 errors, 0 warnings,
0 sorry. `runProgramHIR` runs every statement except `doWhile`/`forLoop`
(which stay `none` with pinned reasons).

## Explicitly not done (gates)

- `doWhile` lowering: needs desugar-faithfulness proof (at-least-once vs
  `whileLoop`); stays `none` — see `HARD-GATES.md` G-6.
- `forLoop` lowering: anonymous unreachable iterator; stays `none` — G-6.
- Billing-blocked CI/Pages/nightly, external audit, Rust runtime, stdlib —
  see `HARD-GATES.md` G-1–G-5, G-7–G-8.

## Verification (loop 112)

- `lake build Morph Morph.Tests`: 454 jobs, 0 errors, 0 warnings.
- `grep -rn sorry Morph/`: empty.
- `pytest`: 836 passed (1 waiver-test failure under `TMPDIR=$PWD/.tmp` is
  a harness artifact; clean `TMPDIR` gives 836 passed).
- Thin-module audit: `MachineRelation` (single deep β-agreement theorem),
  `Maths` (Nat/Int/Rational/gcd data + ops), `DualOptimization`
  (O0–O3 + pass/result data) — all complete as specified, no padding added.

## Loop 113 — `spec/build/` restoration (this pass)

**Problem.** The working tree had deleted the six tracked
`spec/build/*.md` files, breaking 72 spec-lint cross-reference errors and
68 cross-ref-validate failures (all `../build/*` links from
`execution_model`, `morph_language`, `memory_model`,
`optimization_manifold` specs).

**Work.** `git checkout -- spec/build/` to restore the tracked files;
no content changes. Re-ran the full battery.

**Verification (loop 113).** `lake build Morph Morph.Tests` 454 jobs,
0 errors, 0 warnings; `sorry` 0; stubs 0; pytest 836 passed;
spec lint 0 errors / 106 warnings (matches documented baseline);
cross-refs 1704 pass / 0 fail; theorems 2075 repo-wide (1633 in specs).
Regression snapshot: lint errors 72→0, cross-ref broken 68→0;
lint warnings 101→106 is the restored files' own warnings, matching the
`CORE-ROADMAP.md` baseline, not a regression.
