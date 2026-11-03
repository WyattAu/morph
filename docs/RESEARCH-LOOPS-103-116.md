# Research Loops 103–116 — HIR Statement Coverage, Status Regen, G-6 Analysis, Closeout

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

## Loop 114 — `SPEC_STATUS.md` regeneration

**Problem.** `SPEC_STATUS.md` was stale at 55 modules: the 12 batch /
earliest / UI / identity modules plus `TypeUnification` were missing, and
several rows predated recent lemma growth (e.g. `DialectProjection`
1→15, `EffectAlgebra` 26→39, `AbiDataRefinement` 4→11 after loop 111).
Sprint 6's exit criterion (status counts match the tree) was violated.

**Work.** Regenerated the full table under the file's own documented
methodology (same grep rules, byte-sort order): 68 modules, 1408 real
lemmas, 934 real examples, 0 stubs, 0 sorries, 67 tier-1 + README tier-2.
`.reports/spec-status.md` refreshed with the generator script and
committed alongside (counts agree). Noted accounting gap: the repo
"specs theorems" metric (1633) also sweeps 105 theorems stated in
`Spec.lean` files, 20 in `Examples.lean` files, and doc-comment lines
beginning with the word "theorem" — the table counts `Lemmas.lean` only.

## Loop 115 — G-6 desugar-faithfulness analysis (this pass)

**Problem.** G-6 (HIR `forLoop`/`doWhile` lowering) unblocks on "a
desugar-faithfulness proof vs surface semantics". Loop 112 decided the
rejection; the analysis itself was never written.

**Work.**
- `Morph/Interp.lean`: six `runDoWhile_*` characterization pins
  (`zero`, `body_stuck/broke/continued/done_false/done_true`) making the
  at-least-once discipline machine-checked — the body runs before `cond`
  is ever consulted.
- Checked three desugar candidates: naive `body; while` (break/continue
  in the leading copy escape instead of completing/checking — contradicts
  the `broke`/`continued` pins); `while (flag || cond)` (surface `or` is
  strict per `Executable.evalWithFuel`, so a stuck `cond` aborts before
  the first body run — contradicts the `stuck` pin); flag + lazy
  `ifThenElse` guard (entry-faithful, but needs stmt free-vars +
  freshness, fuel-inequality agreement vs same-fuel `agreeBoth`, and
  env-extension reasoning — a compilation pass, not a sprint tail).
- `forLoop`: second rejection leg recorded — iteration needs statement
  context (`whileLoop` is `Stmt`-only, `HIR.Expr` has no iteration form),
  so no counter-desugar can target HIR without a phase split; stands with
  loop 78b (anonymous unreachable iterator).
- Fixed stale `HIRInterp.lean` header (claimed `ifStmt`/`matchStmt` never
  lower — true before loop 112, false since); `HIRLower.lean` doc now
  points at the G-6 analysis.

**Disposition.** Rejection retained conservatively; analysis recorded in
`HARD-GATES.md` G-6. Unblocks if (a)+(b)+(c) above are built, or new
evidence for a 1:1 map appears.

## Loop 116 — Roadmap closeout + final verification (this pass)

**Problem.** `CORE-ROADMAP.md` still showed its loop-111 opening baseline
(2 warnings, 9 sorry false positives, 2066 theorems) with all sprints
written as future work, though every sprint had since completed.

**Work.** Marked all seven sprints DONE with their completing loops and
replaced the baseline with the closing state (454 jobs, 0/0;
0 sorries/stubs; 2081 theorems). Ran the full battery: build, pytest
(836), lint (0/106), cross-refs (1704/0), regression snapshot — no
regressions vs the loop-113 baseline, one improvement (total theorems
2075→2081 from the loop-115 pins). Full disposition of remaining work
is `HARD-GATES.md` G-1–G-8, all maintainer- or Era-2-blocked.

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
