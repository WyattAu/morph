# Research Loops 103–124 — HIR Statement Coverage, Status Regen, G-6 Analysis, Closeout, CI Repair, Roadmap Reconciliation, Runtime CI, Sprint Sweep, Site Metrics, 5-Year Design, Y1 Readiness

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

## Loop 117 — Audit packet refresh + G-7 checklist

**Problem.** `docs/AUDIT-PACKET-0.1.md` was stale five ways (1508
theorems/58 modules, #11 shown unresolved, pre-112 theorem names,
402-job repro, no HIR coverage); invites quoted the old numbers;
G-7 had no concrete tag procedure.

**Work.** Packet rewritten to loop-116 truth (2081 theorems, 1633 in
Specs, 68 modules; #11 resolved-with-history; `agreeBoth` triple +
`runHIRProgram_preservation`; 454-job repro + `TMPDIR` caveat). Invites
updated (2,081 theorems, #11 resolved). `HARD-GATES.md` G-7 gained a
five-step maintainer checklist with preconditions and do-NOT rules.

## Loop 118 — CI red-on-arrival repair (this pass)

**Problem.** `PATH_FORWARD.md` §3.4's ghost references are already gone
(no `specification_tests.yml`, no ghost paths) — but three CI jobs were
red against the *current* tree: `spec-validation.yml` ran
`format --check` (exits 1, ~16k deviations) and full `validate` (exits
1, 624 missing-section errors) as hard steps; `Jenkinsfile` ran
`format --check`, `lint --strict` (fails on the 106 accepted-baseline
warnings), and `validate` under `set -e`. All three configs would fail
on the first billed run.

**Work.** Per the ROADMAP's own precedent (lint → non-blocking with
reporting): format and validate are advisory with uploaded reports in
both configs; the blocking gate is plain `lint` (verified: exits 1 on
errors — probed with a broken-link file — 0 on warnings-only).
`validate`'s 624 errors are all `*-001` "section missing" demands for
Traceability/Verification/Risk/Security/Performance/Maintainability
sections the corpus was never written to — same category as the
section-numbering warnings. `PATH_FORWARD.md` §3.4 marked DONE, §4.1
updated (`lean-build.yml` already builds Tests, gates all four checks,
enforces status freshness, caches elan + Lake; only the snapshot-in-CI
step still needs runners).

## Loop 119 — `ROADMAP.md` reconciliation (this pass)

**Problem.** `ROADMAP.md`, the canonical status view, contradicted the
verified state in five places: §1.2–§1.5 tier tables listed nonzero stub
counts for modules that have shipped real lemmas (stubs are 0
repo-wide, CI-gated); §1.1's per-row "Needs proof" statuses contradicted
its own DONE header; §3.1 still assigned work for the 26 broken links
(0 broken since loops 112–113); the §4.1 table predated the loop-118 CI
fix; and the success-criteria table said pre-commit "warns only" on
sorry (it exits 1 — verified by reading `.githooks/pre-commit`).

**Work.** Dated DONE banners on §1.2–§1.5 pointing at `SPEC_STATUS.md`
as the live inventory (history tables retained, not rewritten); §1.1
rows annotated as the pre-fix plan; §3.1 marked done with the
1704/0 evidence; §4.1 rows updated for the loop-118 gate semantics;
success-criteria rows corrected (stubs CI-gated, cross-refs 1704/0,
pre-commit blocks). No plan changes — the phases were already complete;
only the status view caught up.

## Loop 120 — Runtime CI green + lint baseline measured (this pass)

**Problem.** With Lean-side sprints closed, the remaining red-on-arrival
risk was the Rust workspace CI (`rust-ci.yml` runs `cargo fmt --check`,
`clippy --all-targets -- -D warnings`, full build + tests — all verified
by running them locally): clippy emitted 2 warnings
(`manual_is_ascii_check` at `compiler/src/lexer/mod.rs:130`,
`unnecessary_map_or` at :638), which `-D warnings` promotes to failure.
Separately, `nightly.yml`'s error gate grepped `^error:` — an anchor
Lean diagnostics (`file:line:col: error: ...`) never match, so a broken
nightly would report green.

**Work.** Fixed both clippy lints at the source
(`is_ascii_hexdigit()`, `is_some_and()` — semantics unchanged);
`clippy -D warnings`, `fmt --check`, and `cargo test --workspace`
(218 passed) all green locally. Unanchored the nightly error grep to
match `lean-build.yml`. Measured the lint baseline through the linter
API instead of stale prose: 74 `header-validation` + 31 `change-log` +
1 `section-structure` (false positive on the intentional §2.2.8 series
return — waived, 19 waived total, 105 warnings). The 105
missing-boilerplate warnings stay accepted baseline; `PATH_FORWARD`
§3.2 dispositioned with the measured breakdown, §4.2 verified done
(cache keys include the manifest, elan cached); `ROADMAP.md` §3.2/§4.2
updated to match. All baselines (roadmap, packet, changelog) moved
106 → 105.

## Loop 121 — Sprint sweep: scratch cleanup, coverage gate, states recorded (this pass)

**Problem.** Three leftover items from the sprint tables: (1) Sprint 1's
scratch cleanup missed eleven tracked root files (`probe5/6/10–18.lean`,
`TestVars.lean` — `#check`/experiment fragments, unreferenced, outside
the build glob); (2) the coverage gate was hollow — `scripts/tests/
pytest.ini` (which overrides `pyproject.toml` by rootdir proximity)
pinned `--cov-fail-under=48` while the stated target is 95%; (3)
`ROADMAP.md` §5.2/§6.3/§6.4 had no measured state.

**Work.** `git rm` the twelve scratch files. Measured coverage properly
(`coverage run` from root collects nothing — no source there; from
`scripts/` with pytest-cov: **96.08%**) and hardened the effective gate
48 → 95 in `pytest.ini` (plus `pyproject.toml` for consistency) — passes
with margin. Cross-ref total 1704 → 1700 is expected: the script checks
imports in the deleted `TestVars.lean` (4 imports), 0 fail either way.

## Loop 122 — Site metrics refresh (this pass)

**Problem.** The undeployable-but-visible site carried stale numbers:
`site/index.html` showed 402 Lean jobs / 1,508 theorems (now 454 /
2,081); `site/docs/tools.html` claimed 636 tests at 88% coverage (now
836 at 96.08%). Audited and deliberately left alone: the "60+ spec
modules" taglines (68 Lean modules / 104 md files — still true), the
curated ADR page (11 key-decision entries; the 22 frontier-register
files are research logs, out of scope for that page), and the
`SPECIFICATION_INDEX.md` + `specs.html` 0.1.0 stamp (unreproducible
"170 modules / 1,094 theorems" — re-stamp is G-7 release work, already
checklisted). The site can't deploy until billing (G-2) regardless; this
keeps the source of truth correct for when it can.

## Loop 123 — Five-year roadmap design (this pass)

**Problem.** The repo had a 10-year horizon (`LONGTERM_ROADMAP.md`,
eras/outcomes) and a task-level execution view (`PATH_FORWARD.md`), but
nothing scheduling outcomes by year for the fundable, plannable middle
distance — and the existing implementation plan (`impl/roadmap.md`:
12-month v1.0, C++ runtime, LLVM) contradicts the measured tree (no C++
exists, backend language undecided, audit gate freezes Era-2 work).

**Work.** Wrote `docs/FIVE-YEAR-ROADMAP.md`: entry state fully measured
at loop 122, Years 1–5 with per-year exit criteria and miss-rules, six
dated decisions with conservative defaults (D-1…D-6), an annual
scoreboard seeded with today's numbers, plan-specific risks, and an
explicit out-of-scope list (Eras 4–5). Adopts `ERA2-BACKEND-SCOPE.md`
Stages A–D as the Year 2–3 spine; declares governance over
`impl/roadmap.md` on timeline/backend-language conflicts pending a Y1
review ADR. No code, no gates moved — a planning artifact for
maintainers and (post-tag) auditors.

## Loop 124 — Year-1 release-readiness probe (this pass)

**Problem.** Year 1's remaining unblocked work is proving the 0.1.0
release candidate actually behaves as `CHANGELOG.md` + `STABILITY.md`
promise — not re-verifying proofs (green), but exercising the shipped
artifact end to end.

**Work.** Built `morph` (`lake build morph`, 46 jobs) and ran the full
CLI matrix against it: `version` → 0.1.0; `eval` arithmetic → 7 and
empty-input / parse-failure goldens (exit 1, byte-exact messages);
`parse`/`check` success + type-error paths; `run` vs `run --hir`
agreement on let-programs (6 = 6), `ifStmt` through `--hir` (1),
var-pattern `match` through `--hir` (1 = 1, loop-112 golden live);
`fmt` fixpoint rendering; `doc` Markdown output; `doWhile` direct run
(3) vs `--hir` rejection (exit 1, exact leaves-fragment message — the
G-6 path behaving as documented). Toolchain pins verified:
`leanprover/lean4:v4.27.0`, Lake 5.0.0, build offline-clean.

**Not done (gates, noted):** billing → live CI (G-1), audit invites +
findings (G-3), tag + announce (G-7). The artifact is proven ready;
the actions are maintainers'. Recorded: §5.2 open (no `doc-gen4` dep; new dependency
needs maintainer approval); §6.3 measured (workspace builds, 218 Rust
tests green); §6.4 seed noted (`Morph/Stdlib.lean`, 187 lines, unwired
— wiring is a maintainer call); G-7 checklist gained the index/specs
re-stamp step (`SPECIFICATION_INDEX.md` + `site/docs/specs.html` stamp
predates the tree: "170 modules" vs 104 md files).

## Loop 125 — Year-1 maintenance + Stage-A design prep (this pass)

**Work.** Baseline re-verify: `lake build Morph Morph.Tests` 454 jobs,
0 errors, 0 warnings; `sorry`/`example : True` scans empty; theorem grep
2096 repo-wide / 1642 in `Specs/` (loop-122 scoreboard seeded 2081 /
1633 — delta is same-grep drift on an unchanged Lean tree, recorded not
reconciled; `SPEC_STATUS.md` real-lemma methodology unchanged);
`pytest` 836 passed, 96.14% (gate 95%); Rust workspace 218 passed
(30 + 133 + 55). Wrote `docs/STAGEA-PREP-125.md` (design-only, no code):
strict-subset `morph build` contract position (D-4 default; `IsStraight`
IN, `whileLoop`/match/calls + G-6 `doWhile`/`forLoop` OUT, `Option`-`none`
+ goldens as the rejection shape), verified-lowering default (D-2) with
the per-backend TCB the ADR must state, and the MIR small-step semantics
gap Stage A must close post-audit.

**Not done (gates, noted):** G-1 (billing → live CI), G-3 (audit invites
+ findings — this prep is what auditors react to), G-7 (tag + announce).
No Era-2 implementation landed (Year-1 freeze honored).

## Loop 126 — Audit-packet freshness (this pass)

**Problem.** `docs/AUDIT-PACKET-0.1.md` was pinned "current as of loop
116" while the tree moved on: cross-refs 1704 → 1700 (loop 121
scratch-file removal), coverage 96% → 96.14% (loop-125 measure), and the
new `docs/STAGEA-PREP-125.md` design positions existed nowhere in the
auditor-facing materials.

**Work.** Four-line patch, all measured: provenance loop 116 → 125;
coverage 96.14%; cross-refs 1700/0 (re-ran both checks this loop);
new §6 pointing auditors at `ERA2-BACKEND-SCOPE.md` + `STAGEA-PREP-125.md`
as the Era-2 scope they react to. Theorem counts left on the loop-114
`SPEC_STATUS.md` methodology (packet §2) — the loop-125 grep drift
(2096/1642 vs 2081/1633) is recorded in the loop-125 entry, not
reconciled by churning the packet.

**Not done (gates, noted):** G-1/G-3/G-7 unchanged — the packet is
prepped, sending + tag + findings remain maintainers'.

## Loop 127 — Regression-snapshot verdict, G-7 step 1 (this pass)

**Work.** Ran `bash scripts/regression-snapshot.sh` (clean `TMPDIR`):
RESULT: No regressions. All clear — sorry 0, stubs 0, pytest 836/0,
lint 0/105, cross-refs 0 broken, coverage 96%, Lean modules 268 / spec
modules 208 unchanged. The snapshot's canonical counters read
specs-theorems 1633 / total-theorems 2081, matching the loop-122
scoreboard and packet §2 — this reconciles the loop-125 grep drift
(2096/1642): the rough `^\s*(theorem|lemma)` grep overcounts vs the
snapshot methodology, so the packet correctly stayed on 2081/1633.
The new snapshot JSON is left untracked per convention (tag-time record
ships with release materials per `AUDIT-INVITES-0.1.md` item 3).

**Not done (gates, noted):** G-7 steps 2–6 (tag, CI-on-tag, invites,
re-stamp, announce) are maintainer actions; G-1/G-3 unchanged.

## Loop 128 — Roadmap governance banner (this pass)

**Problem.** `impl/roadmap.md` promises a 12-month v1.0 with a C++
runtime and LLVM backend, and cites stale formal counts ("40+ modules",
"6 sorries") — contradicting the measured tree (no C++ exists, audit
gate freezes Era-2 work, 0 sorries, 68 spec modules) and risking
stakeholder confusion per the five-year risk register.

**Work.** Docs-only banner at the top of `impl/roadmap.md`: names the
file as the Rust-implementation viewpoint, states the five-year file
governs on timeline/backend-language pending the Y1 review ADR,
requires any C++ introduction to justify itself in the Year-2 backend
ADR, and redirects formal counts to `SPEC_STATUS.md`. No timeline,
code, or gate changed — the conflict was already adjudicated in the
five-year doc; this makes it visible where a reader lands.

**Not done (gates, noted):** the Y1 review ADR itself is maintainer
work; G-1/G-3/G-7 unchanged.

## Loop 129 — Overview governance banner (this pass)

**Problem.** Same conflict as loop 128, second file: `impl/overview.md`
recommends the Hybrid "Rust + C++" architecture (C++23 runtime, LLVM
backends/JIT/libFuzzer) and "40+ specification modules" — inputs to
the Year-2 backend ADR (D-3), not decisions, and stale counts.

**Work.** Docs-only banner at the top of `impl/overview.md`: the C++23
/ LLVM architecture is an input to the backend ADR, the tree holds a
Rust workspace with zero C++, and the five-year file governs conflicts
pending the Y1 review ADR. No code, no gates moved.

**Year-1 unilateral closeout (loops 124–129).** Everything actionable
without a maintainer now stands done: release artifact probed end to
end (124), baseline re-verified (125), Stage-A design prep for auditors
(125), packet current (126), snapshot verdict clean (127), both `impl/`
strategy files bannered (128–129). What remains is maintainer-gated:
billing → live CI (G-1), audit invites + findings (G-3), tag + announce
(G-7), Y1 review ADR. Next unilateral work is maintenance duty (keep
`lake build` green against toolchain churn) until a gate clears.

## Loop 130 — CHANGELOG drift repair (this pass)

**Problem.** `CHANGELOG.md` had two dead heartbeat links — two
`[Unreleased]` sections still cited `docs/RESEARCH-LOOPS-103-124.md`,
renamed to `-103-129.md` by the heartbeat-rename convention — and no
entry at all for loops 121–129 (site metrics, five-year roadmap,
release-readiness probe, Stage-A prep, packet refresh, snapshot
verdict, governance banners). The file is the release-notes source
(G-7 step 6), so drift there is an auditor-visible defect.

**Work.** Repointed both stale refs to `docs/RESEARCH-LOOPS-103-129.md`;
added one `[Unreleased] — loops 121–129` section grouped Added / Changed
/ Verified, each claim traceable to its loop entry and to a measured
number (2,081 theorems, 836 pytest, 0/0 Lean, cross-refs 1700/0). The
loop-127 grep-drift reconciliation is not restated here — the snapshot
counters are the canonical figures.

**Second defect, same commit.** The rename-per-loop convention was
being committed with a pathspec that named only the *new* path, so each
`git mv` deletion stayed out of the commit: HEAD accumulated six stale
heartbeat files (`103-124`…`103-129`) that are growing prefixes of the
current one (304 → 398 lines vs 421). Verified byte-identical prefixes
before deleting; `docs/RESEARCH-LOOPS-103-130.md` is now the single
heartbeat file. Convention going forward: stage the rename with `git add
-A <dir>`, never a pathspec naming only the destination.

**Verification.** Cross-refs 1700 pass / 0 fail (dead links gone); spec
lint 0 errors / 105 warnings (baseline unchanged). No code touched.

## Loop 131 — Pre-commit step 7 jurisdiction (this pass)

**Problem.** Step 7 of `.githooks/pre-commit` ran `spec-tools lint` on
every staged `*.md` — including CHANGELOG, heartbeat notes, and `impl/`
strategy docs. Those are not specs and must not carry spec sections
(the waivers module states the doctrine: fabricating missing sections
would be worse), so every docs commit printed advisory failures that
taught reviewers to ignore the step. CI (`spec-validation.yml`) already
lints only `spec/`; the hook disagreed with CI on jurisdiction.

**Work.** One-line scope change plus a comment recording the reason:
the hook now collects staged files under `spec/*.md` + `spec/**/*.md`
only. Verified both directions: a staged non-spec md yields an empty
set (skip branch), and the same pathspec matches all 97 tracked spec
files (`git ls-files`). Real spec edits still get the per-file check;
non-spec docs edits stop generating noise.

**Not done (gates, noted):** G-1/G-3/G-7 unchanged.

**Not done (gates, noted):** G-1/G-3/G-7 unchanged — CHANGELOG is
release *input*, not the release.

## Loop 132 — Year-2 entry-gated kickoff, design-only (this pass)

**Request:** start Year 2. **Constraint:** Era-1 exit is not met, so
Year-2 implementation remains frozen: no audit (G-3), no 0.1 tag (G-7),
no live CI (G-1). The freeze rule is explicit in Year 1 of the five-year
roadmap and the Era-2 scope header.

**Work.** Added `docs/YEAR2-KICKOFF.md`: entry-gate verdict, allowed
vs blocked work, the five-item blocked queue (MIR semantics,
`compile_correct`, backend ADR, flagged `morph build`, Rust pipeline
plus advisory differential testing), and the audit dependencies that
must be answered before implementation. No Lean/Rust code, no gates
moved, no timeline proposed.

**Not done (gates, noted):** G-1/G-3/G-7 unchanged; implementation
starts only after the audit publishes.

## Loop 133 — Era-1 exit: close the in-repo prep (this pass)

**Request:** finish Era-1 exit. **Constraint:** three exit items are
maintainer/external-only and cannot be produced from inside the repo —
G-1 billing (CI per push + Pages), G-3 audit invites + published
findings, G-7 tag + announce. What *can* close here is every in-repo
precondition so the exit is maintainer-action-only.

**Work.**
- G-7 item 5 (re-stamp): `SPECIFICATION_INDEX.md` header and
  `site/docs/specs.html` banner marked the 0.1.0 numbers historical
  ("170 modules / 1,094 theorems" frozen at tag time) and pointed at
  the live counters — 104 `spec/*.md` files, 68 Lean spec modules
  (`SPEC_STATUS.md`), 1633 Specs theorems / 2081 repo-wide, 0 sorry /
  0 stubs, all re-measured this loop. `CHANGELOG.md` 0.1.0 section
  deliberately untouched (frozen release notes, not the live count).
- Re-verified cheap gates: `sorry` 0, `example : True := trivial` 0,
  `theorem`/`lemma` lines 2081 repo-wide / 1633 in `Specs/`.
- Exit verdict: in-repo prep COMPLETE; remaining exit actions are
  maintainer-only in dependency order — (1) resolve billing G-1 so
  runners + Pages go live, (2) cut + push tag 0.1.0 per the G-7
  checklist (snapshot JSON ships with the tag), (3) send audit invites
  G-3 with packet + snapshot, (4) publish findings and triage. No
  Era-2 implementation starts before (3) publishes (Year-1 freeze).

**Not done (gates, noted):** G-1/G-3/G-7 — maintainer/external only;
no code or proof work remains for Era-1 exit.

## Loop 134 — Era-2 unfreeze + Stage A1 execution groundwork (this pass)

**Request:** finish Era 1; if not closable in-round, unfreeze Era 2.
**Verdict:** Era-1 exit cannot close in-round (G-1 billing, G-3 audit,
G-7 tag/announce are all maintainer/external-only). Per maintainer
directive the Year-1 freeze is lifted: `docs/ERA2-UNFREEZE.md` records
the decision, `docs/YEAR2-KICKOFF.md` + `docs/ERA2-BACKEND-SCOPE.md`
headers updated from blocked-queue to build-order (defaults D-2/D-4
unchanged, one-directional preservation unchanged).

**Work (Stage A1).** New `Morph/MIRExecLemmas.lean` (imports
`Morph.MIR` + `Morph.Store`, `open Morph.Core` so `Value`/`Typ`
resolve): `execInstrsFull_nil`/`cons`/`append` composition,
`evalInstrFull_*_agrees` (const/copy/unop/binop env-projection
agreement with the pure oracle) + `*_store` (pure success never touches
the store), `execBlockFuel_return` + `findBlock_singleton` +
`execFunc_single_block` (two-fuel single-block `return_` reduction —
the exact shape Stage-A2 `compile_correct` concludes with).

**Not done (gates, noted):** G-1/G-3/G-7 unchanged (maintainer-only).
Build + commit blocked this pass: `/tmp` full, so `lake env lean` and
the pre-commit hook (mktemp) cannot run — re-run `lake build Morph`
and commit when space is freed; no code beyond the new lemma file and
the three docs updates in this loop.

## Loop 135 — Stage A1 proof-hardening + build wiring (this pass)

**Request:** proceed all (all sprints, max rigor; skip hard gates by
noting). **Verdict:** G-1/G-3/G-7 remain maintainer-only — noted, not
attempted. In-repo track proceeds.

**Work.**
- Hardened `Morph/MIRExecLemmas.lean` proof shapes: `*_store` lemmas
  now `simp only [evalInstrFull] at h` before case-splitting (equation-
  lemma reduction instead of raw `unfold`, which left an unreduced
  `match Instr.copy …` scrutinee shadowing `dst`/`src` and broke `rw`).
  `copy`/`unop`/`binop` agreement lemmas now case-split first, then
  `simp [evalInstrFull, evalInstr, h]` — no pre-unfold.
- Wired into the build: `Morph.lean` now imports
  `Morph.MIRExecLemmas` so `lake build` checks it.
- Roadmap two-track amendments landed (loop 134): `YEAR2-KICKOFF` §1/§3,
  `ERA2-BACKEND-SCOPE` staging label, `STAGEA-PREP-125` historical
  banner, `FIVE-YEAR-ROADMAP` Y1 + D-1, `LONGTERM-ROADMAP` Era-1,
  `HARD-GATES` parallel-track note, `PATH_FORWARD` baseline refresh
  pointer. D-2 (verified lowering) + D-4 (strict subset) unchanged.
- Stage A2 scoped (not yet coded, zero-`sorry` gate forbids stubs):
  straight-line `compile_correct` = `lowerProgram_WF` (done, Sprint 11)
  + A1 exec lemmas (this loop) + per-construct env-relation bridge
  (`lowerExpr`/`lowerStmts` vs `evalHIR`/`runHIRStmts`, one-directional,
  fuel-explicit, strict-subset contract). Next file builds on A1's
  `execInstrsFull_append` + `execFunc_single_block`.

**Not done (gates, noted):** G-1/G-3/G-7 (maintainer-only).
**Blocked (infra, noted not skipped):** `lake env lean` / `lake build`
verification + `git commit` — runner wedged (even trivial commands
time out after two 280s+ `lake env lean` attempts; likely orphaned lake
jobs). Re-run `lake build Morph` and commit all loop 134–135 edits
when the runner recovers. No new `sorry`/stubs added.

## Loop 136 — Stage A1 re-harden + A2 bridge scope (this pass)

**Request:** proceed all (all sprints, max rigor; skip hard gates by
noting). **Verdict:** G-1/G-3/G-7 maintainer-only — noted, not
attempted. Terminal still wedged (even `echo alive` times out), so
all work below is file-side; no build/commit attempted this pass.

**Work.**
- `Morph.lean`: removed duplicated `- /` close (`- /\n- /` → `- /`)
  that would have broken the root-module parse once the runner
  recovers.
- `Morph/MIRExecLemmas.lean` re-hardened without Lean feedback,
  against the `Morph.MIR` definitions read file-side:
  `execInstrsFull_append` nil case is now `simp [execInstrsFull]`
  (not bare `rfl`: `[] ++ l₂` + the `some fenv` match need reduction);
  cons case is `cases h : …` then `simp [h]` / `simp [h, ih]` (bare
  `rfl` / `exact ih` cannot fire while the scrutinee still occurs in
  the goal). `*_store` lemmas drop the fragile
  `Option.bind_some`-named steps for plain `simp [hsrc] at h`-style
  reduction (bind-lemma names differ across toolchains; `simp` closes
  `some`/`none` binds on its own). Agreement + `execBlockFuel_return`
  / `findBlock_singleton` / `execFunc_single_block` shapes re-checked
  against `evalInstrFull` / `execInstrsFull` / `execBlockFuel` /
  `findBlock` / `execFunc` — no statement changes, proofs only.
- Stage A2 bridge scoped file-side (not coded — zero-`sorry` gate
  forbids stub files). Sources: `HIRToMIR.lowerExpr` / `lowerBlock` /
  `lowerStmts` / `lowerProgram` + `lowerProgram_WF` (Sprint 11),
  `HIREval.evalHIR` (fuel-bounded big-step, `evalHIR 256` at statement
  level) + `HIRInterp.runHIRStmts` / `runHIRProgram` (1024 fuel, HEnv
  first-match-wins, `updateHEnv` no-introduction). Next preservation
  file proves, per construct, HIR-success ⇒ MIR-agreement under an
  env relation (HIR id ↦ value vs register ↦ same value, `ρ` /
  `RanIn`-style covering), composing via A1 `execInstrsFull_append`
  and concluding via `execFunc_single_block`; one-directional,
  fuel-explicit, strict-subset (D-4), verified-lowering default (D-2).
  Control flow (`whileLoop`/`match`/calls/multi-block CFG) stays out.

**Not done (gates, noted):** G-1/G-3/G-7 (maintainer-only).
**Blocked (infra, noted not skipped):** `lake build Morph` +
`git commit` for loops 134–136 — runner still wedged. Re-run build
then commit when it recovers. No new `sorry`/stubs added; no new
`.lean` files created this pass.

## Loop 137 — A2 env-relation groundwork (file-side, this pass)

**Request:** continue (all sprints, max rigor; gates noted not
attempted). Terminal still presumed wedged, so file-side only.

**Work — read `HIRToMIR` 370–700 (`RanIn` / freshness / use-check).**
- `RanIn ρ acc`: every register bound in `ρ` is in ambient `acc`
  (params ++ prefix defs). Lowering extends both in lockstep (`let`
  binds init result, appends its defs) — the invariant the A2 env
  relation inherits: HIR id ↦ value agrees with register ↦ same value
  wherever `ρ` covers the id, under `FreshAbove ρ supply`.
- `lower_mono` (supply only grows) + `lower_result_lt` (result `< s'`
  under `FreshAbove`) give freshness the bridge needs: child results
  stay below the next supply, so appended trailing `const`/`unop`/
  `binop` defs never collide with live registers.
- `lower_useCheck` concludes with `blockUseGo` directly (plus
  result-either-available-or-defined), composing via
  `blockUseGo_append` / `blockUseGo_mono` — the same combinators A1
  mirrors at execution level with `execInstrsFull_append`. So the A2
  per-construct bridge (`lit`/`var`/`unop`/`binop`/`let`/`block` /
  `exprStmt`/`varDecl`/`assign`/`returnStmt`/`nop`) follows the exact
  case tree of `lower_useCheck`: same induction, but the conclusion is
  env-agreement (`execInstrsFull` from a related `FullEnv` yields the
  `evalHIR` literal in the result register, store unchanged) instead of
  use-coverage. `lowerProgram_WF` + A1 lemmas are the base; no new
  axioms, one-directional, fuel-explicit, strict-subset.

**Not done (gates, noted):** G-1/G-3/G-7 maintainer-only.
**Blocked (infra):** build + commit for loops 134–137. No `sorry`/
stubs; no new `.lean` files.

## Loop 138 — `HIRToMIR` statement half read; A2 statement finalized (this pass)

**Request:** continue (all sprints, max rigor; gates noted not
attempted). File-side only; terminal still presumed wedged.

**Work — read `HIRToMIR` 699–995 (statement lowering + program closure).**
- `lowerStmts ρ supply lastVal (s :: rest)` cases: `exprStmt` lowers
  head expr, threads its register in as the rest's `lastVal`;
  `varDecl` lowers init, extends `ρ` with `(id, va)` (freshness via
  `lower_result_lt`, runtime no-shadowing via first-match-wins
  `getBv?`/`lookupHEnv`); `assign` lowers expr, moves the binding via
  `updAssoc` (in-place update, covered by `updAssoc_mem`);
  `returnStmt` lowers expr and closes (`Option.map_some` shape);
  `nop` is the identity. `break`/`continue`/`whileLoop`/`ifStmt`/
  `matchStmt` lower to `none` — strict-subset (D-4) at the statement
  level too.
- Program closure: `lowerProgram prog = some ⟨"main", [], [⟨0,
  [.const 0 .unit] ++ is, .return_ v⟩], 0, .unitType⟩` — one block,
  leading unit `const` (register 0), trailing `return_ v`. That is the
  exact shape A1's `execFunc_single_block` consumes, so the
  `compile_correct` conclusion is: for every `prog` with
  `lowerStmts [] 1 0 prog.stmts = some (ρ', v, is, s')` (all embedded
  exprs FirstOrder) and `runHIRProg…` success, `execFunc (fuel + 2)`
  of the lowered func yields `v`'s literal — via the statement-level
  env relation (`(id, u) ∈ ρ'` mirrors `(id, lit)` in `HEnv` with the
  same value) threaded through the literal/cons-identity echo of
  `lowerStmts_useCheck`.
- Statement-bridge obligations, concretely, per `lowerStmts` case:
  `nop` = env identity; `exprStmt` = expr bridge (child `is`) +
  continue with `lastVal := v0`; `varDecl` = expr bridge + push
  `(id, v)` on both sides; `assign` = expr bridge + `updateHEnv` (no
  introduction) matches `updAssoc`-covered relation; `returnStmt` =
  expr bridge + result is `v` (A1 `execBlockFuel_return` closes).

**Not done (gates, noted):** G-1/G-3/G-7 maintainer-only.
**Blocked (infra):** build + commit for loops 134–138. No `sorry`/
stubs; no new `.lean` files.

## Loop 139 — `lower_correct` closed: the Era-2 Stage A expr bridge is proved

**Request:** continue (all sprints, max rigor; gates noted not attempted).

**Work — `Morph/HIRToMIRCorrect.lean` now ends in a proved
`lower_correct` (zero `sorry`, zero warnings, `EXIT:0` from
`lake env lean`).** Both halves of one `lowerExpr.mutual_induct`, 17
arms:

- Expr half: `lowerExpr ρ supply e = some (v, is, s') → IsStraight e →
  FreshAbove ρ supply → RelEnv henv ρ fenv.env →
  execInstrsFull fenv is = some fenv' → ∃ w fuel,
  evalHIR fuel henv e = some (.lit w) ∧ fenv'.env v = some w ∧
  fenv'.store = fenv.store`.
- Block half is stated at `mapM` level
  (`es.mapM (evalHIR fuel henv) = some (vs.map HIR.Expr.lit)` plus
  `fenv'.env v = some (vs.getLastD .unit)`), converted back to
  `.block` evaluation with `block_eval_of_mapM` +
  `getLast_map_lit`; an empty block lowers to `(supply, [], supply)`
  and is the `some .unit` base case.

**New glue the proof needed (all in the same file):**
- `RelEnv_exec` / `lower_preserv_regs` /
  `lowerBlock_preserv_regs` — the env relation and any register
  below a sub-expression's starting supply survive running its
  emitted code (`execInstrsFull_preservLow` + `lower_isPure` +
  `lower_defs_gt`). This is what lets `ihB` see `fenv1.env` and lets
  the emitted `.binop` read `va` out of `fenv2`.
- `IsStraight_*` projection lemmas (`_unop_sub`, `_binop_sub_l/_r`,
  `_let_init/_body`, `_block_mem`) so arms never `cases` the
  `IsStraight` proof — that eliminated locals (`u`, `s`, `vb`, `vb'`)
  and broke the arms, whereas projections leave them intact.
- Step lemmas `evalHIR_unop_step` / `_binop_step` / `_let_step`,
  `evalInstrFull_unop_result` / `_binop_result`,
  `execInstrsFull_singleton_elim`, `mapM_evalHIR_mono`,
  `mapM_cons_eq`, `getLastD_cons_of_ne`; fuel stays existential and
  is shared across subterms with `evalHIR_mono` (no length-based
  bound — `.let` emits no instruction, so length is the wrong
  metric).

**Honest scope.** The bridge is one-directional (D-2/D-4) and
conditioned on MIR success: it does *not* claim `execInstrsFull`
succeeds whenever `evalHIR` does, and it does not claim the reverse
implication (a MIR run that succeeds on ill-typed input has no
guarantee). Statement/program half (`lowerStmts`, `lowerProgram`,
`compile_correct`) remains the next sprint, as does wiring the module
into the umbrella import if desired.

**Not done (gates, noted):** G-1 (billing/CI), G-3 (audit), G-7
(tag/announce) — maintainer/external only, not attempted. No new
`.lean` files. Environment note: the machine was heavily
oversubscribed (load 20–47 on 6 cores), so each `lean` invocation
took 4–14 minutes instead of ~3.

## Loop 140 — statement and program halves land: `lowerStmts_correct`, `compile_correct`

**Request:** continue (all sprints, max rigor; gates noted not attempted).

**Work — the statement layer is proved; `Morph/HIRToMIRCorrect.lean` is
2.1k lines, zero `sorry`, zero warnings, `lake env lean` exit 0.**

- `StraightStmts budget ss` — the statement fragment the lowering accepts
  (`exprStmt`, `varDecl`, `assign`, `returnStmt`, `nop`; control flow is
  rejected), each expression carrying both `IsStraight` and a
  `SLWeight e < budget` budget. Projections (`StraightStmts_exprStmt`,
  `_varDecl`, `_assign`, `_returnStmt`, `_nop`) instead of `cases`, for the
  same reason the `IsStraight_*` lemmas exist: `cases` eliminates locals the
  arm still needs.
- `evalHIR_budget` / `evalHIR_256` — the runner evaluates every expression
  position with a *fixed* `evalHIR 256`, so an unspecified fuel is useless to
  it. `SLWeight` (one unit per construct, `.block` pays the sum of its
  elements) bounds what an expression can demand, proved by induction on the
  budget with the subterm successes as an existential hypothesis — the first
  attempt inducted on the successful run's fuel and got the wrong direction
  (`max fuel weight ≤ 256` is false for large `fuel`), which is exactly the
  kind of mistake only a compile catches.
- `lowerStmts_correct` — if `lowerStmts ρ supply lastVal ss` succeeds, the
  emitted code runs, then `runHIRStmts` reaches a value that the lowering's
  result register holds, the store is untouched, and `RelEnv` still ties the
  final HIR environment to the final `ρ`. The accumulator invariant is a
  *register plus the literal in it* (`fenv.env lastVal = some acc`), so
  `exprStmt` can replace it with the new expression's register while
  `varDecl`/`assign` pass it through unchanged, exactly mirroring
  `runHIRStmts`' own accumulator.
- Assignment needed real bookkeeping: `rhoLookup_updAssoc_id` (the assigned
  name reads back as the new register),
  `rhoLookup_updAssoc_ne` (every other name is untouched), their `updateHEnv`
  twins `lookupHEnv_updateHEnv_id` / `_ne`, and `RelEnv_update` gluing them.
  The first attempt wrote this with `subst`, which silently eliminated the
  local named `id` and left the *identity function* in its place — the
  `Id`-shadowing trap in a new disguise. Rewritten with explicit `show`-based
  equation lemmas for `updAssoc`/`rhoLookup`, no substitution.
- `compile_correct` — `lowerProgram`'s shape (prologue `const 0 .unit`,
  single block, `return_ v`) feeds A1's `execFunc_single_block`:
  after `execInstrsFull_prologue` runs the prologue (`Env.update (fun _ =>
  none) 0 .unit`), the statement bridge supplies the HIR side and the
  register `v` read out of the final env is the same value. Stated
  conditioned on MIR success, honestly — one direction only (D-2/D-4).

**Honest scope.** Still not claimed: that the lowered code *cannot* fail
(needs a totality converse: pure-instruction execution succeeds whenever the
source evaluates — the natural next theorem), and the control-flow
statements remain out of the fragment by design. G-1/G-3/G-7 remain
maintainer-only, not attempted.

## Loop 141 — the converse: `lower_total`

**Request:** continue (all sprints, max rigor; gates noted not attempted).

**Work — `lower_total` proves the lowered code never stalls on the fragment.**

`lower_correct` consumes MIR success, so on its own it cannot say whether the
emitted instructions get *stuck*: every instruction can fail on an unbound
source register or an ill-typed operator application, and the forward theorem
is silent about which of those the lowering rules out. `lower_total` proves
the other direction for the straight-line fragment: if `evalHIR` succeeds, the
emitted code runs, the store is untouched, and the result register holds the
source value.

The statement needs care in one place. `evalHIR` on a variable read returns
whatever the environment holds — which need not be a literal, while the
lowering emits *no instructions* for a read, so there is nothing to stall on.
Stating the HIR hypothesis as "evaluates to a literal" would therefore be
false for a `let`-bound non-literal; stating it parametrically, with the
conclusion "runs, and *when* the value is a literal the register holds it",
is both true and sufficient. A second conjunct records that in this fragment
the value is always a literal, which is what makes the parametric form usable
in the `let` case: the body's environment relation `RelEnv` demands literal
bindings, so the init's literal-ness has to be recovered from the induction
hypothesis rather than assumed.

Machinery: `execInstrsFull_singleton` (a successful step gives a successful
one-instruction run — the forward proof only needed the converse),
decomposition lemmas for successful `evalHIR` on `unop`/`binop`/`let`/`block`
(the forward proof had the step form and needed the inverse), and
`mapM_cons_inv` for the block case. `getLast!_eq_getLastD` reconciles the two
"last element" notions `evalHIR` and `block_eval_of_mapM` use.

Cost of honesty: the `unop`/`binop` inversions enumerate `HIR.Expr`'s twelve
constructors, since a `match` on the *result* of an evaluation has to be
inspected one constructor at a time; the eleven impossible arms are all
`none = some _`.

**Result.** `Morph/HIRToMIRCorrect.lean`, 2.6k lines, zero `sorry`, zero
warnings, `lake env lean` exit 0 and `lake build Morph` green. What remains is
lifting this to statements and programs (that would let `compile_correct` drop
its MIR-success hypothesis) and the control-flow fragment.

**Follow-on corollary.** `lower_total_lit` is the form the statement layer
needs: the source value is supplied as the literal `w` ("the surrounding run
produced `w`") rather than existentially quantified, and the conclusion is the
three facts a statement-level induction can paste together — the emitted code
runs, the result register holds `w`, the store is untouched. `lowerStmts_total`
is then a mirror of `lowerStmts_correct` with its MIR-success hypothesis
replaced by an appeal to this lemma at each expression leaf, and its
`RelEnv henv' ρ' fenv'.env` conclusion conditioned on the HIR run actually
producing a value (with fuel exhausted the source stops early, so the
environment relation has accumulated bindings the run never made — the MIR
totality fact survives, the agreement fact does not).

## Loop 142 — program-level environment agreement, and what `lowerStmts_total` really costs

**Work.** `compile_correct_env` carries `lowerStmts_correct`'s last two
components out to the program level: the final machine environment satisfies
`RelEnv` against the source-interpreted environment, and the store is
untouched — what a caller needs to keep executing after the call, not just to
read the return value. Small: the statement theorem already had the facts; the
program theorem just wasn't asking for them.

**Finding — `lowerStmts_total` is not the mirror I assumed.** The plan written
up under Loop 141 was "replace `lowerStmts_correct`'s MIR-success hypothesis
with an appeal to `lower_total_lit` at each expression leaf". That does not
work, and it is worth recording why so the next attempt doesn't repeat it.

`lower_total` proves *MIR runs* from *HIR succeeds*: the emitted code's runtime
success is a conclusion drawn from source-side evidence. At the statement layer
that evidence is not available — `runHIRStmts` returns a flow and an
environment whether or not the source evaluated, and when its fuel runs out
mid-program the source has simply stopped, while the emitted code must still
run (that is the point of the theorem). So MIR totality at the statement layer
cannot be inherited from the expression-layer totality theorem; it needs its own
expression-level theorem with no HIR hypothesis at all:

  `lowerExpr_total : lowerExpr ρ supply e = some (v, is, s') → IsStraight e →
     FreshAbove ρ supply → (every register named by ρ is bound in fenv) →
     ∃ fenv', execInstrsFull fenv is = some fenv'`

which is a second full 17-arm `lowerExpr.mutual_induct`, one where each
instruction's success obligation is discharged syntactically — the register it
reads is either written earlier in `is` or comes from `ρ` — rather than handed
over by the source run. The statement-level theorem then mirrors
`lowerStmts_correct` with `lower_total_lit` for value agreement and
`lowerExpr_total` for totality, and its `RelEnv` conclusion stays conditioned
on the run producing a value, for the fuel-exhaustion reason recorded under
Loop 141.

That is a session of its own; not started here rather than left half-proved.

**Result.** `Morph/HIRToMIRCorrect.lean`, 2.7k lines, zero `sorry`, zero
warnings, `lake env lean` exit 0. Under the load this machine was carrying
(28 on 6 cores) a single elaboration of the file took ~9 minutes, which is the
practical limit on how many proof-fix cycles fit in one sitting.

## Loop 143 — A2 exit (`compile_total`), and why the Loop-142 plan was impossible

**Correction first.** Loop 142 recorded a plan for `lowerStmts_total`: a second
17-arm expression induction (`lowerExpr_total`) proving MIR totality with no HIR
hypothesis, keyed on a `Bound ρ fenv.env` side condition. That theorem is
**false**, so the plan would have spent a session on an unprovable goal. The
reason is the oracle: `MIR.evalUnOp`/`evalBinOp` are `Option`-valued, and
`evalUnop_glue`/`evalBinop_glue` say they stall *exactly* when
`Executable.evalUnop`/`evalBinop` stall. A program applying `unop` to a
mistyped literal therefore stalls in MIR, and no condition on the register file
can exclude it — what would be needed is a typing hypothesis the bridge does
not have. `Bound` was additionally unnecessary for the registers it was
introduced for: every register an emitted instruction reads is either written
earlier in the same instruction list (handed over by the induction hypothesis)
or comes from `ρ`. The operator oracle, not the register file, is the
unfixable half.

**What is true, and is what the safeguard asks for.** Carry the source run as a
hypothesis, so a source-side stall is excluded by the hypothesis instead of
asserted against the machine:

- `lowerStmts_total` — `lowerStmts_correct` with `execInstrsFull fenv is =
  some fenv'` moved from hypothesis to conclusion, and
  `runHIRStmts fuel henv ss (.value (.lit acc)) = (out, henv')` plus
  `runValue? out = some (.lit w)` supplied in its place. Each arm splits the
  source run: at `fuel = 0`, and at an expression that fails to evaluate, the
  run is stuck, so the value hypothesis is contradicted; otherwise
  `lower_total`'s second component produces the head instructions' run, the
  induction hypothesis produces the tail's, and `execInstrsFull_append`
  composes them.
- `compile_total` — the exit statement. `lowerProgram prog = some func`, the
  `StraightStmts 256` fragment contract, and a source run reaching `w` give
  `execFunc 2 func ⟨fun _ => none, store⟩ = some w`.

`lower_total_lit` turned out not to be the form the statement layer wants after
all. An intermediate expression statement may evaluate to a non-literal that a
later statement overwrites (the runner substitutes each fresh value into the
accumulator), so the head expression has no fixed literal to hand the lemma.
The sound form is still a literal — `lower_total`'s first conjunct proves it —
but the witness has to come from the lemma, so the arms use the existential
form. `lower_total_lit` stays as a derived corollary, not as the layer's tool.

**Two Lean notes, each worth one elaboration cycle (≈5 min under load).**
`obtain` patterns that discard a component (`⟨-, h⟩`) do not bind the remaining
names in this environment. `obtain` on an equality of pairs does not introduce
its components either; `congrArg Prod.fst`/`snd` plus `subst` is the reliable
form. Both were found by compiling, not by reading.

**Result.** `Morph/HIRToMIRTotal.lean`, 926 lines, zero `sorry`, zero warnings,
`lake env lean` exit 0. A2 exit met: forward totality proved at program level
with no MIR-success hypothesis, and no failure-coincidence claim made anywhere.

## Loop 144 — Stage B scope, and four measured MIR/CLIF mismatches

**Work.** Scoped Stage B (`docs/STAGEB-SCOPE.md`) against ADR-032 and
`STAGEA-PREP` §1. No code: the point was to find what "MIR→CLIF verified
lowering" actually costs by comparing the two value domains, instead of
assuming they compose.

**Four mismatches, measured.**

1. `Value.int : Int` is unbounded and `Executable.evalBinop` does plain `Int`
   arithmetic; CLIF i64/i32 wrap. MIR→CLIF is therefore *not* value-preserving
   in general, and the theorem needs a range hypothesis on **intermediate**
   values. That fixes the statement shape: by simulation over the instruction
   list, because a hypothesis about the values inside `execFunc`'s opaque result
   cannot be re-established per step.
2. Division. `#eval` says Lean's `Int` pair is Euclidean — `-7/2 = -4`,
   `-7%2 = 1`, `7/-2 = -3` — while CLIF's `sdiv`/`srem` truncate: `-7/2 = -3`,
   `-7%2 = -1`. They agree only on non-negative operands, which is exactly what
   a differential corpus of positive literals would have covered. Worth
   measuring precisely because testing would not have found it.
3. Division by zero is *defined* as `0` in MIR (`Executable.lean:84-85`) and
   traps in CLIF, so a direct `sdiv` would turn a defined MIR result into a
   machine trap. `div`/`mod` are rejected by the encoder in B1; the guarded
   Euclidean sequence is the way back in.
4. Shifts are unbounded in Lean and require `n < 64` in CLIF; and `Instr.const`
   admits string/float/pointer/tuple/closure payloads with no Stage B encoding.
   The last is syntactic, which is the good case — the encoder rejects rather
   than miscompiles.

**The architecture finding.** ADR-032's consequences say "`compiler` emits CLIF
from MIR", assuming the Rust crate's IR transcribes Lean's. It does not:
`compiler/src/codegen/morph_ir.rs` is a stack machine with locals and upvalues
(`LoadLocal`, `StoreUpvalue`, `PushStr`), Lean's MIR is SSA over `ValId`s with
blocks and terminators, and neither expresses the other's constructs. A Rust
MIR→CLIF pass would be a second independent lowering from a different input
language — doubling the unverified surface ADR-032 exists to minimise.
Corrected seam, as a dated amendment in the ADR: the **Lean executable renders
CLIF text** (`Main.lean` already hosts the command table), and Cranelift parses
and lowers it; `compiler/src/codegen` leaves the Stage B path.
`render_parse_id` proves the renderer injective, which is the strongest thing
provable about a boundary Lean cannot see across, and the scope doc describes it
as exactly that rather than as verified marshalling.

**Exit criterion, restated.** Stage B's proved half is B1–B5: the CLIF model
with an explicit `wrap`, the encoder for the reduced subset, per-operator
agreement lemmas, `clif_correct` composing with `compile_total`, and the
render/parse round-trip. B6–B8 (the flag, the Cranelift driver, the differential
corpus) are trusted and gated as such.

**Result.** No Lean changed, so nothing to re-elaborate. New:
`docs/STAGEB-SCOPE.md`; amended: ADR-032 consequences, and the Stage B line in
`docs/ERA2-BACKEND-SCOPE.md`.

## Loop 145 — Stage B item B1: the CLIF target model

**Work.** Landed `Morph/ClifTarget.lean`, the model the Stage B lowering will be
proved against (scope doc §4.1): ten instructions (`iconst`, `iadd`, `isub`,
`imul`, `icmp`, `band`, `bor`, `bnot`, `ishl`, `sshr`), a single-block `Func`
with one return register, a partial register file, and `run`/`runInstrs`.

Two decisions inside it, both consequences of loop 144's measurements:

- `wrap` makes fixed width explicit, and `wrap_eq_self` is the only fact the
  theorem will need from it — the range hypothesis converts to an equality
  exactly there. `wrap_bounds` is its companion so a step-wise simulation can
  re-establish the invariant when a clause introduces a fresh value.
- `ishl`/`sshr` stall outside `0 ≤ n < 64` in the model rather than inventing a
  convention CLIF does not have; the B3 agreement lemma discharges the check
  from the fragment's amount hypothesis. `sshr` is `Int` division by `2^n`,
  which is sound because Lean's Euclidean division by a positive divisor *is*
  floor division — the same argument as loop 144 §1.2, used in the opposite
  direction.

**Toolchain notes.** `norm_num` is not available in this import closure
(`Morph.MIR` does not pull Mathlib); `decide` proves the 64-bit numerals and
`omega` does the interval arithmetic, so the wrap lemmas need neither. `Value`
lives in `Morph.Core`, not at the root — an unqualified reference fails and
takes every subsequent `Env`/`.int` annotation with it, which is what the first
elaboration of this file actually reported.

**Result.** `lake env lean Morph/ClifTarget.lean` exit 0, zero warnings, no
`sorry`. B2 (the encoder), B3 (per-operator agreement), B4 (`clif_correct`) and
B5 (render/parse) remain; nothing here lowers MIR yet.

## Loop 146 — Stage B items B2/B3: the encoder and per-operator agreement

**Work.** `Morph/ClifLower.lean`: the MIR→CLIF encoder (`instrEncode`,
`instrEncodes`, `blockEncode`), its rejection lemmas, and thirteen `agree_*`
theorems — one per instruction in the fragment — each stating that the CLIF step
produces exactly the environment `MIR.evalInstr` produces.

**Fragment.** `const` (integer payloads), `.add/.sub/.mul`, the six int
comparisons, `.and/.or` on booleans, `.shl`, `.shr`, `.notb`, all in
single-block `return`-terminated bodies. Comparisons and boolean operators need
**no** hypothesis — they are exact for every input; arithmetic carries an i64
range hypothesis on the *result*, and shifts need the amount in `[0,64)`.

**Rejections, each with its reason in the file.** `.div`/`.mod` (Euclidean vs
truncating, `x/0 = 0` vs trap), `.andb`/`.orb`/`.xorb` (the oracle defines them
by **parity**, not bitwise — they agree with `band`/`bor` only on `{0,1}`),
`.not` (boolean negation is not `bnot`), `.copy` (CLIF has no copy: needs a
rename pass or a materialised zero register), non-integer `const` payloads, and
all memory/call/`phi` instructions.

**Three corrections the lemmas forced on B1's model**, all caught by the
per-operator proofs rather than by review:

1. `bnot` was boolean negation. CLIF's `bnot` is the i64 complement, which is
   `.notb`'s meaning (`-a - 1` under two's complement); boolean negation has no
   single-instruction encoding in this subset, so it is the *encoder* that must
   reject `.not`.
2. `sshr` was `a / 2^n`. Both `Int./` and `Int.shiftRight` are floor division by
   a positive divisor, so the arithmetic was right — but the oracle *is*
   `Int.shiftRight`, so using the same primitive makes the agreement
   definitional instead of a proof about division. `sshr` also needs no `wrap`:
   shifting right cannot overflow.
3. `.ne` was `a != b`. The oracle returns `!(a == b)`, and `bne` does not
   unfold to `!(==)` definitionally here.

**Toolchain notes.** `Int.pow 2 n` and `(2 : Int)^n` are *not* interchangeable
under `rfl` inside a nested `Option`/register argument, even though the bare
equation closes by `rfl` — the fix is to spell the model's shift the way the
oracle spells it, not to add a bridge. `Int.shiftRight_eq_div_pow` is the
lemma connecting the two readings. `MIR.Env.update` (which tests `x == dst`) and
`Clif.Env.set` (which tests `x = dst`) are equal by `Nat`'s lawful `BEq`, which
is what lets agreement be plain env equality with no renaming relation.

**Result.** `lake env lean Morph/ClifLower.lean` exit 0, zero warnings, no
`sorry`; `Morph.ClifTarget` rebuilt clean after the model corrections. B4
(`clif_simulate`/`clif_correct`, needing a range invariant threaded through the
instruction fold) and B5 (render/parse) remain.

## Loop 147 — Stage B item B4: the typed-trace simulation

**Work.** `Morph/ClifSimulate.lean`: `ValInRange` (i64-range int, or bool),
a 14-constructor `Step` relation recording what the fragment's typing judgement
knows, a `Trace` of such steps, and three theorems —

- `step_simulate` : one `Step` is exactly the CLIF instruction the encoder emits.
- `step_evalInstr` : one `Step` is the MIR transition it claims to be.
- `run_simulate` : a `Trace` plus its encoding yields the same environment
  (`clif_simulate`, folded over the instruction list).

**Why a certificate and not a hypothesis on `evalInstrFull`.** The obvious
statement — "if `evalInstrFull` succeeds then the CLIF step matches" — is not
provable at this layer: success does not expose the operand *values*, and the
range hypothesis is about them. Recovering them means inverting the `do`-chain
(`Option.bind`) case by case, which only re-derives what the caller already knew.
`Step` records it instead, the same shape as `StraightStmts` in Stage A: the
fragment owes the certificate, and the file proves the certificate suffices.
This is a premise, not a conclusion — in-range intermediates are still the
fragment's obligation, discharged outside Lean for now.

**Encoding change.** `instrEncodes` was a `do`-block; it is now an explicit
two-way `match` so `instrEncodes_cons` is invertible (`cases ... <;> simp`),
which is what the fold needs. Same function, easier to reason about.

**Two tactic lessons.** `simp_all` cannot substitute `c` from
`henc : instrEncode i = some c` because the equation it produces is oriented
`constructor = c`, so it rewrites the wrong way and leaves `match c with …`
stuck; `simp only […, Option.some.injEq] at henc ⊢` followed by `subst henc`
does the substitution explicitly. And a `do`-block definition needs to be named
in the simp set itself: unfolding `evalInstr` does not unfold `evalUnOp` nested
inside it, which is why the `.notb` case failed while every binop case passed.

**Result.** `lake env lean Morph/ClifSimulate.lean` exit 0, zero warnings, no
`sorry`; `Morph.ClifLower` still builds. **Not yet done:** the bridge from a
`Trace` to `MIR.execInstrsFull`/`evalInstrFull` (pure instructions must be shown
to preserve the store, then the block and `execFunc` wrapper), which is what
composes with `compile_total`; and the `blockEncode` inversion that turns
`run_simulate` into a statement about `Clif.run`.
## Loop 148 — Stage B item B4 closed: store bridge and program composition

**Work.** Two additions, both pure Lean.

1. *The store bridge* (`Morph/ClifSimulate.lean`). The fragment's instructions are
   pure — no `load`/`store`, no `alloc`, no `call` — so they act on the register
   file and leave `store` alone. `step_execInstrFull` states that: one `Step`
   implies the corresponding `MIR.evalInstrFull` transition, *pairing the same
   store on both sides*, and `trace_execInstrsFull` folds it over `Trace` to
   `MIR.execInstrsFull`. This is what a `Trace` has to say before
   `execInstrsFull_prologue` can be applied, and it is the last gap between the
   CLIF model and the statement layer of `compile_total`.

2. *The prologue transport.* `lowerProgram` prefixes the body with
   `.const 0 .unit`; CLIF has no unit value, so the encoder emits the body after
   the prologue and `Trace` starts at `update (fun _ => none) 0 .unit` while
   `Clif.run` starts at `fun _ => none`. `trace_transport` bridges them through
   `AgreesOnValues`, which is preserved by identical updates and holds for the
   prologue because `.unit` is a value no `Step` ever reads. The prologue is
   *dropped* from the emitted function, not mistranslated, and the note is in the
   file's header rather than only here.

`clif_correct` (block level) then composes these: encoder inversion
(`blockEncode_return`) → transport → `run_simulate` → `Clif.run`. And
`Morph/ClifCorrect.lean` states the program level as a **conjunction**:
`execFunc 2 (lowerProgram prog) = some (.int n) ∧ Clif.run cf = some (.int n)`,
with the MIR conjunct discharged by `compile_total` and the CLIF conjunct by
`clif_correct`, over the same `n` from the same HIR run. Neither conclusion is
compared to the other directly, so one side cannot hide a bug in the other, and
no failure-coincidence claim is made in either direction.

**What remains a premise.** `Trace` still carries the fragment's typing
certificate — integer operands, in-range results, shift amounts in `[0,64)`.
Nothing here proves that a given program satisfies it; that is the fragment's
obligation and is stated as such in the file header. So B4 says: *if* the body
stays inside the fragment and the encoder accepts it, the CLIF model returns what
the MIR returns. It does not say every lowering lands in the fragment.

**Tactic notes worth keeping.**
- `cases h : instrEncodes instrs` **generalizes the goal**, replacing
  `instrEncodes instrs` by the constructor term; a branch must therefore close the
  *generalized* goal (`exact ⟨rfl, rfl⟩`, not `⟨hc, rfl⟩`). `rw [← h1, ← h2]`
  then `exact ⟨rfl, rfl⟩` is the form that works.
- `simp only` matches syntactically: it will not whnf `Option.map f (some cs)` to
  `some (f cs)`, so expose the redex first (`Option.some.inj` on the equation,
  typed by ascription). `change` on an untyped `{…}` literal fails with
  "expected type is not known"; `change … (Func.mk cs ret) …` does not.
- A structure literal's projections do not reduce where a constructor
  application's do; destruct the structure (`cases cf with | mk is rc`) instead of
  projecting from a literal.

**Result.** `lake env lean Morph/ClifSimulate.lean` exit 0, no warnings, no
`sorry`; `lake build Morph.ClifCorrect` exit 0 (339 s). B4 is met at the body
level and at the program level. The prologue gap is documented rather than
papered over; `Trace`-coverage is B8's job, not B4's.
## Loop 149 — Stage B item B5: the printed form and its token stream

**Work.** `Morph/ClifRender.lean`. `toksInstr`/`toksFunc` print a `Func` as a
`List Tok` of self-delimiting units; `parseInstr`/`parseInstrs`/`parseFunc` read it
back. Proved:

- `parseInstr_toksInstr` — one instruction, with the tail carried through.
- `parseInstrs_toksInstrs` — the body, with `is.length` as the exact fuel.
- `parseFunc_toksFunc` — **B5's round trip**: `parseFunc (toksFunc f) = some f`.
- `parseFunc_toksFunc_append` — nothing may follow the return, so the printer's
  image is not merely accepted but accepted at exactly its own length.

**Why tokens and not bytes.** The units carry their payloads and each name fixes
its arity, so the parser needs no backtracking and no separators; that is what
makes totality and invertibility provable rather than merely true. The text
layer (`renderFunc`) is emitted for `cranelift-reader`, which ADR-032 §3 already
counts as trusted. Proving `parse (render f) = f` would mean writing a CLIF lexer
in Lean — new TCB for no new assurance about the compiler, since the reader of
the artifact is the Rust one either way. The grammar is written out at the top of
the file so the text is read against a specification; the round trip is stated
where it means something, which is the token stream.

**Tactic notes.** `::` binds tighter than `++`, so `a :: b ++ c` parses as
`(a :: b) ++ c`: an append written at the end of a printed stream lands *outside*
the cons, and a `show` in the "obvious" shape silently states a different goal
(and then `rw` cannot find its pattern). Write the tail in parentheses. A `match` on `some x` whose pattern needs a three-element list does
not reduce while an `++ [t]` is still in the scrutinee; `rfl` proves the list
identity (`[a, b] ++ [t] = [a, b, t]` holds definitionally) and one `rw` gets the
iota reduction.

**Result.** `lake build Morph.ClifRender` exit 0, no warnings, no `sorry`.

**Gate note.** G-1 (billing/CI) and G-3 (external audit) remain skipped as
instructed; B6–B8 carry the differential corpus that G-3 would otherwise want.
## Loop 150 — Stage B item B6: `morph build --codegen=cranelift`

**Work.** `Morph/ClifEmit.lean` (emitter + characterizations), `buildClif` and
`clifArtifactPath` in `Morph/Driver.lean`, one arm in `Main.lean`, goldens in
`Morph/Tests/Driver.lean`.

The pipeline is `parseProgram → toHIRProgram → lowerProgram → emitClif`, i.e.
B4's proved path with the simulator replaced by the encoder. What the CLI writes
is `renderFunc` of `blockEncode` of the block, and what it rejects is what
`blockEncode` rejects — the D-4 subset, not an approximation of it.

**The prologue decision.** `lowerProgram` always emits `.const 0 .unit` first,
and CLIF has no unit value. `emitBlock` requires that instruction and drops it,
and the characterization is `rfl` on exactly that shape:

- `emitBlock_prologue : emitBlock ⟨id, .const 0 .unit :: body, .return_ src⟩ = blockEncode ⟨id, body, .return_ src⟩`
- `emitClif_lowered : emitClif ⟨"main", [], [⟨0, .const 0 .unit :: body, .return_ v⟩], 0, .unitType⟩ = (blockEncode …).map renderFunc`

So the emitter is definitionally the encoder on real input; there is no third
path through the code that the proofs do not see. Dropping register 0 is sound
because it is that instruction's own destination (B4 starts the trace with 0 ↦
unit). A *converse* lemma ("any `some` comes from such a block") was attempted
and dropped: it needs a 15-way case split on `Value` to prove
`b.instrs = .const 0 .unit :: body`, and its only use is on `lowerProgram`
output, where `emitBlock_prologue` already gives the conclusion directly. Two
`rfl` lemmas that state the fact on the reachable shape beat one induction that
nobody calls.

**Three rejections, three messages.** Outside HIR (`toHIRProgram = none`),
outside the MIR fragment (`lowerProgram = none`), and inside MIR but
unencodable (`blockEncode = none`). Collapsing them would have been less code
and less information: the third is the one a user can act on by rewriting an
operator, the first two are "not stage B yet".

**Verified end-to-end, not only in Lean.** `lake build morph`, then the real
binary:

- `let y = 5; y` → exit 0, `main.clif` = `function %main() -> i64 { block0: %v1 =
  iconst.i64 5; return %v1 }` (prologue absent, as designed);
- `let x = 2; let y = 3; x * y + 1` → five instructions, `imul` then `iadd`;
- `let x = 7 / 2; x` → exit 1, D-4 message, **no artifact written**;
- `let y = 5; match none { … }` → exit 1, HIR-fragment message;
- `1 +` → exit 1, the parser's own message.

The goldens in `Morph/Tests/Driver.lean` pin the `Outcome` (hence the text, the
stream and the exit code) with `native_decide`, including `clifArtifactPath`
(`main.hum` → `main.clif`, `Compiler.v2.hum` → `Compiler.v2.clif`, `Makefile` →
`Makefile.clif`).

**Parser note, stated with its uncertainty.** A parse error surfaced at a
*comment* line, which in Lean means the term above it was unterminated rather
than the comment being bad. Collapsing the multi-line `++` inside `.value (…)`
to a single string made the file elaborate, so that string is now one line; but a
minimal reproduction of both suspicion candidates — the multi-line `++` and the
comment's `§`/apostrophe — parses cleanly on its own, so the *cause* was not
isolated and this note records the fix, not a diagnosis. The general lesson holds
regardless: when the reported position is not code, suspect the term above it.

**Result.** `lake env lean Morph/ClifEmit.lean` exit 0; `lake env lean
Morph/Tests/Driver.lean` exit 0; `lake build morph` exit 0.

**Gate note.** G-1/G-3/G-7 remain skipped. B7 (the Rust driver behind
`cranelift-reader`) is what turns this text into an object file; it consumes the
artifact, so the emitter's shape is its input contract.
## Loop 151 — Stage B: a unit-valued program emitted a non-CLIF artifact

**Found by** writing the stage-B corpus, not by reading the code: the first
in-subset example to try was a program with no trailing expression.

```
$ morph build --codegen=cranelift unit.hum     # let y = 5;
wrote unit.clif
$ cat unit.clif
function %main() -> i64 {
block0:
  %v1 = iconst.i64 5
  return %v0
}
```

`%v0` is the prologue's register. In B4's *model* that is coherent — the trace
starts at `update (fun _ => none) 0 .unit`, so register 0 is bound before the
block runs — but no instruction in the text defines it, so the function is not
CLIF: `cranelift-reader` reports an undefined value. `emitBlock`'s earlier gate
checked the prologue's *presence* and dropped it without checking whether the
returned register survived.

**Fix.** `emitBlock` refuses `src = 0`, since with the prologue present register
0 is exactly "the program's value is unit". `emitBlock_unit` states it, and the
existing characterizations gained the matching `src ≠ 0` premise
(`emitBlock_prologue`, `emitClif_lowered`), so nothing about the verified
encoding moved. The encoder rejection message now names unit-valued programs
first, and two goldens pin it (`let y = 5;` and the empty program).

**Why not encode unit.** There is nothing to encode it *to*: the function is
`-> i64` and CLIF has no unit value, so any spelling would be an invented
convention that B4's model does not claim. Rejection is the honest option and
keeps the rule the rest of Stage B follows — the text is narrower than the
model, and every narrowing is a case the CLI refuses by name.

**Incidental, and worth recording: the disk.** The machine is at 100% (under
100 MB free, load 20–60 from an unrelated build). A rebuild failed with
`failed to read file …/ClifEmit.olean, invalid header`: the earlier olean was
exactly 4096 bytes, i.e. truncated when the disk filled mid-write. Deleting the
stale olean and rebuilding fixed it. Two consequences: build artifacts should be
distrusted after a space failure, and B7 (which compiles `cranelift-codegen`,
needing GBs of `target/`) cannot be built on this machine until space exists.

**Result.** `lake env lean Morph/ClifEmit.lean` exit 0; `lake env lean
Morph/Tests/Driver.lean` exit 0; `lake build morph` exit 0; `unit.hum` and the
empty program exit 1 with the new message and leave no artifact.

**Gate note.** B7 is now blocked by *disk*, not by design: `cargo` reports
`database or disk is full` on the crate cache, `target/` would need GBs, and the
free space is under 300 MB. Recorded as infrastructure gate G-9 (local disk
capacity), skipped like G-1/G-3/G-7; the driver's design is written down in
Stage B's notes and the corpus is being built Lean-side, which needs no space.
## Loop 152 — the corpus finds an ill-typed artifact (and stage B gets fixtures)

**The corpus.** `tests/codegen/` now holds nine accepted programs and seven
rejects, with `check.sh` verifying them against the Lean binary alone: the
recorded `morph run` value, build exit 0, artifact written, no `return %v0`, and
for rejects the exact stderr message and no artifact. 16/16 green. Values were
measured and pasted; two rejects (`unary_minus`, `control_flow`) were classified
by measuring which gate fires rather than by assuming.

**The defect.** `let a = 3; let b = 5; a < b` was accepted and emitted

```
function %main() -> i64 {
block0:
  %v1 = iconst.i64 3
  %v2 = iconst.i64 5
  %v3 = icmp slt %v1, %v2
  return %v3
}
```

`run` prints `true`, and `Morph/ClifTarget.lean`'s `icmp` yields `.bool`, so B4's
model is consistent — but the *text* declares `-> i64` and returns an i8, and CLIF
has no implicit widening. `cranelift-codegen`'s verifier would have rejected it.

**Fix.** `allI64`: the body must contain no truth-valued MIR instruction
(`binop` with `eq/neq/lt/leq/gt/geq/and/or`, or `unop .not`). `emitBlock` refuses
otherwise and the encoder message now says "boolean- or unit-valued programs".
Three `rfl` corollaries (`allI64_no_lt/_and/_not`) show the gate is not vacuous,
and the characterizations gained the matching `allI64 body = true` premise.

**Why conservative rather than exact.** The exact test is "is the *returned*
register i64-typed", which needs a type per register (`lastDef` plus a type for
each instruction). The conservative test refuses a program that computes a
comparison and returns an integer. I chose sound-and-coarse: it cannot let an
ill-typed artifact out, its cost is a refused program rather than a wrong one, and
the corpus records the case (`rejects/boolean_value.hum` plus the note in the
README). The exact test is what a later type pass buys, and the corpus has a row
to prove it when it lands.

**Result.** `lake env lean Morph/ClifEmit.lean` exit 0; `lake env lean
Morph/Tests/Driver.lean` exit 0 (new boolean golden); `lake build morph` exit 0;
`tests/codegen/check.sh` 16/16.

**Note on the disk.** Free space came back to ~1.4 GB during this loop (it had
been at 27 MB), which is why B7 becomes worth attempting next; the earlier
corruption warning still stands.
## Loop 153 — B7 and B8: the artifact compiles, links, and agrees natively

**First: the printer was wrong, and nothing had checked it.** Pointing
`cranelift-reader` at our own output:

```
$ morph-clif mul_add.clif
morph-clif: CLIF reader rejected the artifact: 3: expected block header
```

The text printed `%v1 = iconst.i64 2`. CLIF spells SSA values `v1`; the `%` is
the *function* name in a `function %main() -> i64 {` header. That is the
wasm-text habit, and it survived B5 precisely because B5 proved the round trip
at the *token* level and recorded the text layer as "not inverted, trusted
reader". The trust was in the reader being the authority — but nobody had asked
it. Two lessons worth more than the fix: "delegated to a trusted component" is not
the same as "accepted by it", and the first honest test of a printer is to feed its
output to the real parser. Fixed by dropping the `%` in `Instr.text` and
`renderFunc`; the token-level proofs are untouched, because `Tok.reg` never had a
`%`. A hand-written module confirmed the desired syntax first, so the fix was
aimed at a known-good target.

**B7, the driver.** New workspace member `codegen/` (package `morph-codegen`, bin
`morph-clif`), pinning `cranelift-codegen`/`-reader`/`-object`/`-module`/`-native`
at `0.137.1` — the newest *stable* line; `0.138.0-rc.1` is a prerelease and is
not what a pinned, audited backend should be. It reads the artifact, requires
exactly one function of type `() -> i64`, compiles it, emits an object, links it
against an embedded two-line C runner and prints both paths.

Two choices that matter for the trust story: the function's own name never
reaches the object (the symbol comes from `declare_function("morph_main", …)`, so
the artifact stays a plain CLIF module and no text rewriting precedes the
reader); and the runner calls that symbol and prints the i64, so the program's
value is observable without exit-code truncation.

**B8, the differential.** `tests/codegen/native.sh` runs, for every accepted
corpus program: `morph build` → `morph-clif` → run the native executable →
compare stdout to the value `morph run` printed. That is the whole of Stage B's
unguarded surface in one line: the Lean value is produced by the verified
evaluator, the native value by Cranelift plus `cc`, and they must be equal.

```
ok       literal.hum: native 5 = lean 5
ok       mul_add.hum: native 7 = lean 7
...
ok       large.hum: native 1000000000 = lean 1000000000
ok       negative_chain.hum: native -86 = lean -86
---
9/9 programs agree natively
```

Nine of nine, including a negative value and one above 32 bits (a truncating
backend would show up there). This is evidence, not proof: ADR-032 §3's trust
boundary is unchanged, and the corpus is small and straight-line.

**Result.** `cargo build` and `cargo clippy --all-targets` clean (one `unused_mut`
fixed), `cargo fmt --check` clean, `tests/codegen/check.sh` 16/16,
`tests/codegen/native.sh` 9/9, `lake build morph` exit 0.

**Incidental.** The repo's untracked `.cargo/config.toml` sets
`target-dir = ~/.cache/cargo-target`, which is why no `target/` appears in the
tree and why the harness resolves the binary from `cargo metadata` rather than
assuming `./target/debug`. Free space recovered to ~29 GB, so G-9 (disk) closed
itself; G-1/G-3/G-7 remain skipped.

## Loop 154 — B9: the audit packet learns what stage B added

Closing item of Stage B, and the only one that is prose. `docs/AUDIT-PACKET-0.1.md`
gains a §6 between the golden-coverage section and the hard-gate section (old §7
becomes §8), covering:

- **trusted components, named.** `cranelift-reader`, `cranelift-codegen`,
  `cranelift-object`, `cranelift-module`, `cranelift-native` at 0.137.1, the
  system `cc`, and the embedded C runner in `codegen/src/main.rs`. An auditor
  cannot size a TCB that lists "Cranelift" as one word.
- **proved vs evidenced**, since Stage B's own scope note distinguishes them and
  the packet is where that distinction is easiest to lose.
- **the two defects that proofs missed**, as a precedent rather than an
  anecdote: `%v1` (wasm spelling) and an undefined `v0` for unit programs. Both
  were found by running the pipeline. The sentence the section lands on is
  "a mapping that says 'delegated to a trusted component' should be read as
  'unchecked by us', not 'accepted by it'".
- **stale-count honesty**: §2's 2081-theorem metric predates the `Clif*`
  modules. Rather than re-run the snapshot and inflate the packet, §6 says the
  counts are loop-125 numbers and that no claim depends on them. (Re-running is
  one command; saying so is cheaper than a number that will drift again.)

§5's reproduction block gains `cargo build -p morph-codegen`,
`tests/codegen/check.sh`, `tests/codegen/native.sh`, so every Stage B claim has a
command an auditor can paste.

**Result.** Commit `14f641f`, 7/7 pre-commit checks. Stage B (B1–B9) is closed:
all nine items are in `docs/STAGEB-SCOPE.md` §5 as met, and the exit criterion
of the stage — a proved lowering for straight-line code with a differential
harness under the unproved half — holds.

## Loop 155 — Stage C scope: control flow is a semantics problem first

Stage C per the roadmap is "calls/control flow, `morph test`, ABI lemmas
load-bearing". Scoping it before writing code (the loop-144 pattern) turned up
one fact that reorders the stage: **the first item is not codegen**.

- HIR already *has* branching semantics (`Morph/Interp.lean:101` `ifStmt`,
  `:93` `whileLoop`, flow values `broke`/`continued`). The oracle is not the
  gap.
- `lowerStmts` rejects control flow (`Morph/HIRToMIR.lean:334`), but that is the
  smaller half: `StraightStmts` (`Morph/HIRToMIRCore.lean:1584`) has no
  constructor for `if`, and it is the predicate `compile_total` takes as a
  hypothesis. Adding `if` to the lowerer without extending the predicate would
  produce programs that lower and are covered by no theorem. Contract and
  implementation have to move together.
- MIR can *express* branching — `execBlockFuel` follows `goto`/`branch` — but it
  cannot *execute a merge*: `phi` is `none` in both executors
  (`Morph/MIR.lean:451,530`), and `execInstrsFull` runs a block without knowing
  which edge was taken. Every `if` merges a value, so edge-parameterised
  execution (`prev : Option BlockId`, `phi` fires when `prev = some pred`) is the
  prerequisite for the entire stage.
- The CLIF model has no blocks at all (`Morph/ClifTarget.lean:110`, `run:214`),
  and `emitFunc` rejects multi-block functions. The printer, by contrast, already
  writes a block header — the text layer is ahead of the model, the reverse of
  Stage B's situation.
- Fuel: `compile_total` concludes `execFunc 2 func`, which is exactly a
  single-block run. Branching needs fuel derived from the oracle's own fuel, so
  the stage needs one arithmetic lemma ("a program of `k` statement steps runs
  within `2k + 2` blocks") cited everywhere rather than re-derived.
- `tests/codegen/manifest.tsv` has no branch in it, so branch lowering will have
  no evidence until C6 lands.

`docs/STAGEC-SCOPE.md` records this as nine work items (C1–C9), with C1
edge-environment semantics, C4 CLIF blocks running in parallel, and C9
`morph test` deliberately independent: it is a CLI command over the existing
oracle and shares no machinery with codegen, so it can ship while the hard items
are open — flagged in the note as exactly that, rather than as progress on
Stage C proper.

Two decisions the note makes but does not hide: B4's single-block trace theorem
is **not** rewritten (the block statement is new, and its base case must
reproduce B4), and `switch`/`matchStmt` stay rejected until a pattern compiler
exists, since a jump table is the only construct that would want one.

**Result.** Scope note only, no code, no gate moved. `morph test` (C9) and C1 are
the two items that can start independently.

## Loop 156 — C1: MIR learns which edge it came from

The first Stage C item, and the one the scope note said had to precede any
lowering: a merge block needs `phi`, and `phi` needs the incoming block.

**What landed** (`Morph/MIR.lean`):

- `execInstrsFullFrom (prev : Option BlockId)` — a `phi dst pred src` reads
  `src` when `prev = some pred` and is skipped otherwise. `pred` was already in
  the instruction, so no data was added, only the edge.
- `execBlockFrom fuel f prev b fenv` — `execBlockFuel`'s walk with `prev`
  threaded into the successor call (`some b.id`).
- `execFuncFrom fuel f fenv` — dispatches the entry block directly.
- Four lemmas: `execInstrsFullFrom_nil`, `_phi_none` (entry phis are dead),
  `_phi_hit`, `_phi_miss`, plus `execInstrsFullFrom_nonphi`,
  `execFuncFrom_eq` (entry dispatch adds no synthetic block) and
  `execBlockFrom_return` (the one-block shape C4's CLIF statement must
  reproduce).

**The decision that made this additive.** `execInstrsFull`, `execBlockFuel` and
`execFunc` are unchanged — not redefined as wrappers, not edited at all. The
scope note had asked for a compatibility lemma between the old and new
executors; keeping the old code intact makes that lemma unnecessary, because
everything proved about `execFunc` still applies to exactly the code it was
proved about. The alternative (one executor with an edge parameter, old name
defined as the `none` case) would have been shorter by one definition and would
have broken every proof that unfolds `execFunc`.

**Fuel accounting changed, deliberately.** `execFunc` spends two units per
straight-line program: one on the synthetic `goto`-entry block, one on the real
block. `execFuncFrom` dispatches the entry directly, so the same program costs
one. New executor, new accounting — but the constant now has to be derived once
for branching programs (§1.5 of the scope), so starting it from the honest value
rather than inheriting an artefact is worth the asymmetry.

**The test that matters** (`Morph/Tests/MIR.lean`): a diamond

```
block 0: cond = true            branch cond, block1, block2
block 1: v4 = 10                goto block3
block 2: v5 = 20                goto block3
block 3: phi v2 pred=1 v4 ; phi v2 pred=2 v5 ; return v2
```

- `execFuncFrom 3 fDiamond = some 10`
- with the condition flipped, `some 20`
- `execFunc 4 fDiamond = none` — the *old* executor stalls at the merge, which
  is the measured reason C1 could not be skipped
- an entry-block phi whose source is undefined is skipped, not stalled

Both phis write the same destination from different registers, so a merge that
fired every phi instead of only the incoming edge's would return 20 in both
runs — the test can fail.

**Result.** `lake build Morph.Tests` green (287 jobs), `Morph/MIR.lean` and
`Morph/Tests/MIR.lean` elaborate with zero warnings, no `sorry`. C2 (the
`StraightStmts`/`lowerStmts` extension for `ifStmt`) is now unblocked.

## Loop 157 — C2a: a fragment that admits `if` without breaking `compile_total`

C2 is "`if` in `StraightStmts` and `lowerStmts`". The first half of that sentence
is a trap: `StraightStmts` is `compile_total`'s hypothesis, so adding an `ifStmt`
constructor to it creates an `if` case in that theorem *the moment the
constructor exists*, and the tree is red until C3 lands. Two-phase commits are
not a thing here — every commit builds green.

**Resolution:** a new predicate, `Morph/HIRToMIRBranch.lean`.

- `BranchStep budget s` — one non-terminal statement: the Stage A cases
  (`exprStmt`/`varDecl`/`assign`/`nop`) plus `ifStmt`, whose arms are
  `BranchStmts` (mutually recursive, so nesting is inside the fragment by
  construction).
- `BranchStmts budget ss` — the list structure, with `returnStmt` as a
  *terminal* constructor that constrains no tail, mirroring both `runStmts`
  (which stops at a `return`) and `lowerStmts` (which never lowers the tail).
  Making `returnStmt` a step instead would have been simpler to write and wrong:
  a terminal shape is not a step.
- `straightStmts_to_branch` — every Stage A program is a Stage C program, so C3
  covers the old fragment rather than replacing it. This is the property an
  auditor should check first, because "Stage C extends Stage A" is the claim
  the roadmap makes.
- Three compile-time boundary facts: a two-arm `return` program is in; nested
  `if`s are in; `¬ BranchStmts 256 [whileLoop …]` is provable, so `while`'s
  absence is a theorem, not a comment.

**Two toolchain facts worth recording** (both cost a build cycle):

- a `mutual` block rejects `/--` doc comments between its declarations — the
  layout parser expects a declaration keyword next. Section comments (`/-! -/`)
  before and plain prose after are fine.
- `decide` cannot discharge `SLWeight e < 256`: `SLWeight` is a plain `def`, and
  `decide`'s reduction does not unfold it, so it reports the instance stuck on
  `SLWeight … |>.succ.ble 256`. `simp [SLWeight]` does.

**Why this is a commit and not a draft.** It is the contract C2b and C3 are
written against, it is checked by the compiler in three directions (in, nested,
out), and it changes nothing that already builds: `StraightStmts`,
`lowerStmts` and `compile_total` are untouched.

**Result.** `lake build Morph.HIRToMIRBranch` green, zero warnings, no `sorry`.
C2b (`lowerStmts` for `if`, merge block, phi per merged binding) is next, and it
is the first Stage C item that produces MIR with more than one block.

## Loop 158 — C2b: `if` becomes four blocks and a phi

The first Stage C item that emits MIR with more than one block.

**The lowering** (`Morph/HIRToMIRBranch.lean`): one worker, `lowerStmtsCFG`,
fills a caller-owned block and returns the rest.

```
entry:  <condition instrs>   branch vc, then, else
then:   <arm>                goto join            (or `return`, if the arm returned)
else:   <arm>                goto join
join:   phi vm then v_then
        phi vm else v_else
        <rest of the list, in the join block>
        return vm            (or `goto cont`, when the list is an arm)
```

Two parameters carry the design. `cont : Option MIR.BlockId` says what a
completed list does — `none` returns the accumulated value (a program body),
`some b` jumps to `b` (an arm, or a body tail after a join). That is what lets
one function serve both the program body and an arm, including a nested `if`
inside an arm, without a second copy of the statement walk. `arm : Bool` makes
an arm refuse `varDecl`/`assign`.

**Why binding arms are refused rather than approximated.** An arm that rebinds
changes the register file; the join would then need a phi *per merged binding*,
matching ids across two lists that can differ in length and order (`varDecl`
pushes, `assign` updates in place). Emitting the value phi and reusing the outer
register file would silently resolve a post-`if` lookup to the pre-`if` binding
— a miscompile, not a rejection. So `lowerStmtsCFG` returns `none`, `ArmStmts`
is the grammar that says which arms cannot reach that path, and the gap is
named as C2c. This is the same discipline as `lowerExpr`'s `none` cases and as
Stage B's four encoder narrowings: refuse loudly, widen later with the proof.

**One supply counter for both arms.** The then-arm allocates from `s1`; the
else-arm starts from the then-arm's final supply. Two arms cannot define the
same register, so a future binding merge will not have to disambiguate register
names across edges. Registers cost nothing here and the alternative is a class
of bug that only shows up when the two arms happen to allocate the same number.

**Evidence, and its limit.** Four `native_decide` facts: the lowered `if true {
10 } else { 20 }` is four blocks; it returns 10; flipping the constructor to
`false` returns 20; and the same program followed by `+ 5` returns 5, with the
value phi still executed at the join (the accumulator rule makes the *last*
expression the value, not the `if`). The arms differ deliberately, so a phi rule
that picked the wrong edge would fail the true/false pair. What is *not*
established: agreement with the HIR oracle. That is C3, and these tests would
pass even if the lowering agreed with a wrong oracle.

**Result.** `lake build Morph.HIRToMIRBranch` green, zero warnings, no `sorry`.
Found along the way: `BlockId` exists in both `Morph.Core` (memory blocks) and
`Morph.MIR` (basic blocks), so a file that opens both must qualify — the new
code uses `MIR.BlockId`. Next: C3 (the preservation theorem) or C2c (binding
merges), in either order; C4 (CLIF blocks) can run in parallel with both.

## Loop 159 — scope revision: the CLIF model needed block arguments, and C4b was missing

Reading `Morph/ClifCorrect.lean` and `Morph/ClifTarget.lean` again against the
loop-154 sketch of the CLIF block model produced two corrections, both recorded
in `docs/STAGEC-SCOPE.md` (§1.4, §4.3, §5.1).

**The sketch could not express a merge.** It proposed
`Term.jump (target : BlockId)` / `Term.brif (cond) (tt ff : BlockId)` with no
`Block` parameter list. The whole reason Stage C needs a join block is that the
`if`'s value has to cross an edge into it; a terminator with no arguments has
nowhere to put the value. CLIF's mechanism is the block argument —
`jump block3(v1)` into `block3(v1: i64):`, and `brif v0, block1(v1), block2(v2)`
with per-edge argument lists — and Cranelift's verifier requires that SSA shape.
A slot-reading model (one register file shared by all blocks) would have been
easier to prove and would have described a machine we do not emit. So `Block`
gains `params`, `jump`/`brif` gain argument lists, and `retSrc` leaves the
`Func` structure (`.ret` carries its register). The central lemma of C4b is
therefore **phi ↔ block argument**: MIR's `phi dst pred src` at the join is
`jump join(src)` plus `join(dst: i64):`, executed by parameter binding, not by
an instruction. That is also what makes the §3 "one-armed `if`" row expressible
— the untaken side passes the pre-branch value as a `brif` edge argument.

**The work-item table had no multi-block MIR→CLIF theorem.** C1–C9 contained
C4 (model), C5 (emitter), C6 (corpus) and nothing proving that a multi-block MIR
function and its CLIF encoding return the same value — the block-level B4. As
written, the branching path would have been *proved* to MIR and *evidenced*
from there, while the straight-line path is proved end to end: a narrower proof
for a wider fragment, which principle 1 of `docs/FIVE-YEAR-ROADMAP.md` forbids.
C4 is now C4a (model, with the base case reproducing B4) and C4b (the missing
arrow). C6's corpus is evidence for parse-and-run; it is not a substitute.

**Ordering settled.** C4a → C4b is the critical path for everything on the
target side; C3 is the long pole and independent of it, so they run in
parallel. C2c is not on C3's critical path (`ArmStmts` is the hypothesis), so it
waits behind C6 and the refusal gets pinned as a `rejects.tsv` row. Two hedges
are recorded before C3's main theorem is stated: an inert program parameter on
`execFuncFrom` (so C8's `Instr.call` is additive rather than a restatement of
C3), and fuel through `blockBound` rather than a literal (so C7 adds a
constructor instead of repairing constants).

**Also corrected as stale:** §2 prerequisite 2 had `StraightStmts` gaining
`ifStmt`; the tree did the opposite (a separate `BranchStmts`) and the reason is
now written down — `StraightStmts` is `compile_total`'s hypothesis, so extending
it would have left a red tree until C3. §4.1/§4.2 now match what actually
landed (`execFuncFrom`, `lowerStmtsCFG`) instead of the plan's names.

**No decision duplicated.** ADR-032 already records D-2/D-4 as confirmed, so
this revision does not open a new ADR; it narrows D-4's listing for control flow
in §3 and adds the audit question (Q5) about whether that listing should also
exist as a document-level fragment table.

## Loop 160 — C4a and the CFG encoder: a phi per edge is one parameter, not two

`Morph/ClifBlocks.lean` (C4a) and `Morph/ClifCfgEncode.lean` (C4b's encoder).

**The model.** `Morph.Clif.Cfg` adds `Term` (`ret`/`jump`/`brif`, with one
argument list per target, so `brif` has two), `Block` (`id`, `params`,
`instrs`, `term`), a `Func` of blocks plus an entry label, and a fuel-indexed
`run` that counts *blocks*, not instructions. The environment is threaded from
block to block with the target's parameters shadowing it; the docstring states
the two consequences of that choice (dominance is not enforced; parameter
binding is a shadow, which is exactly what the phi↔argument correspondence
needs). Entry parameters can never be bound, so they are unreadable — a
well-formedness obligation of the emitter, matching MIR's `phi` predecessor.

`run_singleBlockFunc` is the base case the scope demanded: on a one-block
function with `.ret`, `Cfg.run` equals Stage B's `Morph.Clif.run`. The
single-block surface is untouched, so B4 stays a theorem about it.

**The encoder.** `encodeFunc` maps a MIR CFG to `Cfg.Func`: leading phis become
parameters, the rest is `instrEncodes`, `return_`/`goto`/`branch` become
`ret`/`jump`/`brif` with per-edge arguments, `switch` is refused, the unit
prologue is stripped from the entry block as `emitBlock` does.

**The finding.** The C2b lowering emits *one phi per predecessor with the same
destination* — `phi 6 1 4`, `phi 6 2 5` — which is MIR's form (a phi per edge).
Mapping each phi to its own parameter produced `params := [6, 6]` on the join
while each edge passed a single argument, so the arity check refused every
`if`. The two forms are not isomorphic:

```
MIR:    join has one phi per predecessor, all with dst 6
CLIF:   join has one parameter (6), fed by 4 from one edge and 5 from the other
```

So `paramsOf` merges by destination in first-appearance order, and `edgeArgs`
reads, for each parameter, the phi that names the source edge for it. The
encoder also refuses two phis with the same destination *and* the same
predecessor (`noDupPairs`), because the edge's argument would be ambiguous; and
it refuses a parameter with no phi for an edge rather than emitting a short
argument list, which would turn a lowering bug into a runtime arity mismatch.

**The narrowing.** Literal boolean conditions (`if true { … }`) do not encode:
`.const (.bool b)` has no CLIF instruction in the subset, which
`Morph/ClifEmit.lean` already documents alongside division and `copy`. The HIR
and MIR paths run the same program fine, so this is a codegen-fragment
restriction, now pinned as a `native_decide` refusal and recorded as a §3 row.
Computed conditions (`1 < 2` → `icmp`) are in. Widening means a `bconst` /
`iconst.i8` instruction with its render/parse rows, not a lowering change.

**Evidence.** Five `native_decide` facts on real lowerings through
`lowerProgramCFG` → `encodeFunc` → `Cfg.run`: `if 1 < 2 { 10 } else { 20 }` is
10, `if 2 < 1 {…}` is 20, `if …; 0 + 5` is 5 (the join's own execution, so the
parameter really carried the arm's value), the literal-bool program is `none`,
and `switch`/late-phi encoders refuse. Plus four model-level examples in
`ClifBlocks` (diamond true/false, integer condition, arity mismatch, missing
argument).

**Result.** `lake build Morph.ClifCfgEncode` green, zero warnings, no `sorry`.
Next: C4b's theorem (needs a block-level MIR trace relation and the fuel bound
from §4.4), and C3's `blockBound` in parallel.

## Loop 161 — C5/C6: a branch runs natively, and the nested-arm phi was wrong

The branch path now reaches machine code: `morph build --codegen=cranelift` on
`if (1 < 2) { 10 } else { 20 }` writes CLIF text, `morph-clif` compiles it, and
the native binary prints the same value the verified evaluator prints. Corpus
`13/13` (9 straight-line + 4 branch).

**The text layer** (`Morph/ClifRender.lean`): `Cfg.funcText` prints
`block1(v4: i64):` (types on parameters), `jump block3(v5)` (no types on edge
arguments), and `brif v3, block1(v7), block2(v8)` — one argument list *per
target*, which is how two arms pass different values to one join parameter. The
Stage B token layer is deliberately not extended: it exists to prove B5's round
trip, and widening it would mean re-proving B5 for a syntax `cranelift-reader`
already owns. `emitCfg` composes `encodeFunc` with the printer, and
`buildClif` now falls through to it only when `lowerProgram` refuses, so
straight-line programs keep the *proved* Stage B path.

**Cranelift accepted the text on the first try**, including the three things the
Stage B corpus never exercised: forward block references (`brif` to a block
defined later in the text), block parameters with types, and `brif` on the i8
that a bare `icmp` produces.

**The bug.** `if (1 < 2) { if (3 < 4) { 7 } else { 8 } } else { 9 }` failed to
encode, and the reason was in C2b, not in the encoder: the join's phis used the
arm's *entry* block as their predecessor (`phi vm bThen …`), which is only the
block that jumps to the join when the arm is flat. An arm holding a nested `if`
ends in that `if`'s join, so the outer phi named a block whose terminator
branches into the arm instead, the phi never fired, and the join returned an
unbound register. That is a silent-wrong-answer bug for nested arms, and no
existing C2b test caught it because they all used one-block arms. Fixed by
taking the predecessor from the arm's last emitted block
(`Lt.blocks.getLast?.map (·.id)).getD bThen`), with the reason written at the
site and two `native_decide` regression tests (`nestedThenProg`,
`nestedElseProg`) that now execute 8 and 7.

Worth recording: the bug was found by *encoding* the program, not by running the
MIR. `execFuncFrom` would have returned `none` on the same program, but nothing
in the tree ran a nested-arm program until the corpus did. C6 is not polish.

**Also found and fixed:** `Lowered.blocks` was documented "reverse emission
order" while the code appends in forward order (`lowerProgramCFG` reverses for
printing). The predecessor fix depends on that order — `getLast?` is the exit
block only if the list is forward — so the docstring is corrected rather than
left to mislead the next proof.

**Result.** `lake build Morph.Tests` green (292 jobs), `native.sh` 13/13, no
`sorry`, no warnings. `morph build` golden for the branch text plus three
refusal goldens (binding arm, `while`, literal boolean condition) are in
`Morph/Tests/Driver.lean`.

## Loop 162 — C4b, first half: the merge is now a checked binding

`Morph/ClifCfgCorrect.lean`. The phi↔block-argument correspondence has two
halves; this is the binding one, and it is the half where a silent error would
live.

**What is proved.**

- `bindParams_nodup_mem` — for a duplicate-free parameter list, every
  `(parameter, argument)` pair the encoder zipped is what the resulting
  environment holds.
- `bindParams_not_mem` — binding parameters leaves every other register alone,
  which is what lets the simulation thread one environment across a block
  boundary.
- `paramsOf_nodup` — the encoder's parameter list has no repeats by
  construction (the fold appends a destination only when absent), which is
  exactly the hypothesis the binding lemma needs. This required a local
  `nodup_append_singleton` because the toolchain has no `Nodup (l ++ [x])`
  lemma that applies to a rewritten goal; the attempt is recorded because it
  cost two rounds of `rw` placement (`at h ⊢` fails when only `h` matches).
- `edgeArgs_length` — an encoded edge passes exactly one argument per parameter.

**A definition changed to make the proof possible.** `bindParams` was written
with `do`-notation; a `do` block elaborates to `Option.bind` and does not
reduce in a hypothesis, so every case needed a `simp` lemma about `bind` and
none of the lemmas were invertible. It is now an explicit two-way match — the
same idiom `instrEncodes` already documents ("written as an explicit two-way
match rather than a `do` block so `instrEncodes_cons` is invertible"). The
behaviour is identical; only the shape changed, and no theorem depended on it.

**Shadowing is the mechanism, not a detail.** `bindParams` binds parameters by
`Env.set`, so a parameter takes the edge's value even when an earlier block
wrote that register. That is what the phi↔argument correspondence needs: MIR's
`phi dst pred src` writes `dst` in a *global* environment, and the CLIF join
must bind `dst` from the edge instead — if the parameter did not shadow, the
join would read the stale value the non-taken arm's numbering happened to leave
behind. The two "not enforced" notes in `ClifBlocks` (dominance, shadow
semantics) are the price of the model that makes this true.

**What is not proved:** the simulation — that a block's instructions and
terminator step in lockstep with the CLIF model under `AgreesOnValues`. That
needs a block-level trace relation and is the next file. Until it lands, C4b is
half done and the branch path's evidence is C6's 13 native rows, not a theorem.

**Result.** `lake build Morph` green (467 jobs), `lake build Morph.Tests` green
(292 jobs), no `sorry`, no warnings.

## Loop 163 — C4b, second half: the pieces of the simulation

`Morph/ClifCfgSimulate.lean`. The binding lemma said *what* the join's
parameters hold once bound; the simulation needs three things it did not give:

1. **The instructions after the phis run in the second environment.**
   `trace_runInstrs_agree`: a `Trace`, its encoding, and an environment agreeing
   with the MIR one produce an agreeing result. The proof never inspects an
   instruction — `step_transport` gives the same `Step` in the agreeing
   environment, `step_simulate` gives the CLIF instruction for it — which is why
   it composes with the phi phase without a case analysis per opcode.
2. **The edge's arguments are aligned with the parameters.**
   `argsFor_get?` (with `edgeArg?`): the argument at a parameter's index is the
   `src` of the phi the encoder selected. This is the link from the encoder's
   `find?` to the `zip` the binding lemma consumes, and it is the lemma that
   would have caught the loop-160 mistake (one argument per *phi*) on paper
   rather than in an arity mismatch.
3. **Binding and evaluation are positional.** `evalArgs_get?`,
   `evalArgs_length`, `evalArgs_get?_isSome` and `bindParams_get?` restate the
   three lists — parameters, argument registers, argument values — in index
   form, so no list-length bookkeeping is needed to compose them.

They compose into `params_bound_get?`: for every parameter of the join, the
environment holds `edgeArg?`'s value **as read before binding**. That ordering
matters and is now a theorem rather than a reading of the code: `evalArgs` runs
on the entry environment while `bindParams` writes afterwards, so a parameter
that shadows a register the edge also reads still takes the edge's value.

**Toolchain notes worth keeping.** `List.get?` does not exist in this Lean build;
the accessor is `GetElem?`, so the lemmas are `List.getElem?_cons_zero` /
`_cons_succ` / `_nil` and the syntax is `xs[i]?`. `List.mem_of_getElem?` is the
membership lemma, and it returns a `Prop`, not a pair — the `.1` idiom from
`List.of_mem_zip` does not apply. `evalArgs`'s `do`-chain must be inverted with
`cases` on each `Option` (a scratch `evalArgs_cons`), because `split` only splits
`if`/`match`, not `Option.bind`.

**Still open:** the MIR-side phi fold (`execInstrsFullFrom` walks the leading
phis sequentially, reading each `src` from the environment the previous phi left
behind; matching it needs a `splitPhis` reconstruction lemma and either source/
destination disjointness or a sequential formulation), the terminator lemma, and
the fuel induction. The pieces are stated so none of them changes shape.

**Result.** `lake env lean Morph/ClifCfgSimulate.lean` green, no warnings; full
build and commit gate to follow.

## Loop 164 — C4b, MIR side: the phi phase has a canonical form

`Morph/ClifCfgSimulate.lean`. `execInstrsFullFrom` fires phis while walking a
block's instruction list, one at a time, in the order they appear. The encoder
reads them as a list. Comparing the two needed a normal form:

- `splitPhis_reconstruct` — a block **is** its leading phis followed by the rest,
  so looking at the pair loses nothing. This needed `phiInfo_toInstr` (a `Phi` is
  a projection of the instruction it came from).
- `phiFoldEnv` — the phi phase as a fold over `List Phi`: a matching phi writes
  its destination into the running environment, a non-matching one is skipped,
  and an unbound `src` fails — MIR's own condition.
- `execInstrsFullFrom_phiList` — the walk over the re-emitted phi list is exactly
  that fold, with the store untouched.
- `execInstrsFullFrom_split` — the walk over *any* block is the fold over its
  leading phis followed by the walk over the rest, in the folded environment.
  This is the shape the simulation composes: the fold supplies the parameters,
  and `trace_runInstrs_agree` applies to the rest.

**The fold is deliberately sequential.** Each phi reads its `src` from the
environment the previous phi produced, because that is what MIR does. The encoder
reads its arguments *once*, from the entry environment. The two agree only when
no phi reads a register another phi writes — a property of this lowering (arm
temporaries are never merge destinations), not of the definitions. Keeping the
fold sequential makes that a stated hypothesis for the next lemma instead of a
fact hidden inside a definition.

**Toolchain notes.** `split` cannot split `phiInfo`'s match on an opaque
instruction — rewriting `phiInfo` at a hypothesis reduces it to `none = some q`
and loses the constructor. The working idiom is `cases i <;> simp only [phiInfo]
at h <;> (try (cases h; rfl)) <;> simp_all`, which closes all non-phi
constructors and the phi one. Also: `splitPhis`'s `match` tells you *which*
branch was taken but not that `i = toInstr q`, so the equation has to be rewritten
in explicitly; without it the phi equation lemma does not match syntactically.

**Result.** `lake env lean Morph/ClifCfgSimulate.lean` green, no warnings.

**Still open:** the correspondence between `phiFoldEnv` and `bindParams` +
`paramsOf` (needs the no-read-of-a-write hypothesis made explicit, plus
uniqueness of a `(dst, pred)` phi from `noDupPairs`), the terminator lemma, and
the fuel induction.

## Loop 165 — sequencing: Stage C finishes before anything else starts

Maintainer direction: wait until Stage C is finished before starting work
outside it. That changes one thing in the plan and nothing in the order of the
items themselves.

`C9` (`morph test`) was the one item argued to ship early, on the grounds that it
is independent and pilot-facing. It is deferred to Stage C exit. The argument
that loses is not technical: shipping a driver command while C3 and C4b are open
makes the roadmap's H1 look partly delivered next to a proof that is not, which
is the shape the plan forbids (roadmap principle 1 — a narrower proof must never
stand for a wider fragment than it covers).

What does *not* move: C6's `rejects.tsv` rows are Stage C items (they pin the
refusals the stage makes), so they stay. The order inside Stage C is unchanged:
C4b (three lemmas) → hedges (program parameter, `blockBound`) → C3 → C2c → C7 →
C8 → C9.

## Loop 166 — the two pre-C3 hedges, and a measurement that corrects a belief

Both hedges from `docs/STAGEC-SCOPE.md` §5.1, paid before C3's theorem is
stated rather than after C4b. The order matters: both change the *signature* the
stage's statements mention, so paying them late means restating the two hardest
theorems in the stage.

**Hedge 1 — the executor knows its program (`Morph/MIR.lean`).**
`evalInstrFull` returns `none` for `Instr.call` because it is never told which
program it runs. C8 fixes that, and a C3/C4b stated against a program-blind
executor would be restated and re-proved when it does. Added
`execInstrsFullFromIn`, `execBlockFromIn`, `execFuncIn` — structural copies of
the C1 definitions with a `Program` parameter — and proved the parameter
**inert** (`execInstrsFullFromIn_eq`, `execBlockFromIn_eq`, `execFuncIn_eq`).
C8's diff becomes the `.call` case and one hypothesis ("the block contains no
call") instead of the stage. Pinned on the diamond program in
`Morph/Tests/MIR.lean`; every C1 lemma still applies unchanged.

**Hedge 2 — fuel is a function, not a literal (`Morph/HIRToMIRBranch.lean`).**
`armBlockBound`/`blockBound`, with two decisions that only pay off at C7: arms
combine by `max` (only one is traversed, and a flat "three per statement" bound
misses nesting), and the oracle's fuel is a parameter that is inert today and
load-bearing for `whileLoop`. Pins: `ifProg` = 4 (matching the lowered CFG's
four blocks), `nestedThenProg` = 7, an `if`-free body = 1.

**Finding (toolchain).** `HIR.Stmt` and `HIR.Expr` are mutually recursive, so
recursing into an arm goes through the *mutual* recursor and Lean compiles
`armBlockBound` as well-founded recursion. Consequences: `rfl` does not see its
equations, and `simp [armBlockBound]` makes no progress (the equation lemmas
exist, but not as definitional reductions). Rewrite with the explicit `[simp]`
lemmas or `armBlockBound.eq_def`. The nested `match s with` form was tried as a
fix and does **not** help — the mutual recursor is the cause, not the deep
pattern.

**Finding (measurement, correcting loop 164's note).** Loop 164 recorded
`Morph/ClifCfgCorrect.lean` as taking 6–10 minutes to elaborate, and this
session's roadmap review treated that as a throughput risk. Measured:
`lake env lean Morph/ClifCfgCorrect.lean` is **1.9 s** (`-Dprofiler=true`:
525 ms tactic execution, 388 ms import, 299 ms simp). The apparent hangs were
cold or contended Lake builds, not elaboration. Nothing about that file needs
restructuring; the rule it argued for (split files, prefer `simp only`) is
cheap regardless but is not load-bearing.

**Result.** `lake env lean Morph/MIR.lean`, `Morph/HIRToMIRBranch.lean`,
`Morph/Tests/MIR.lean` green, no warnings.

**Still open.** C4b's fold↔binding correspondence and its fuel induction; the
terminator lemma; `blockBound`'s bound lemma (C3 owes it, stated against the
executor); then C3 → C2c → C7 → C8 → C9.

## Loop 167 — the fold↔binding correspondence, and a gate the fold needed

**Goal.** Close the largest open half of C4b: show the join's block parameter
holds exactly what MIR's phi fold writes, on every list the encoder emits.

**Correspondence (`Morph/ClifCfgSimulate.lean`).** `phiFoldEnv_not_dst` (the
fold leaves other destinations alone), `phiFoldEnv_get` (the fold leaves `q`
holding its own entry `src`, under two explicit hypotheses), `edgeArg?_find`
(the encoder's `find?` names a witness phi), and `params_hold_fold` (the
parameter carries the fold's value). The two hypotheses are `huniq` (same
destination and edge ⟹ same source) and `hsep` (no matching phi reads a
register another matching phi writes) — taken as hypotheses rather than
derived from `noDupPairs`, because `hsep` does not follow from it: a swap
(`a := b`, `b := a` on one edge) passes `noDupPairs` and the sequential fold
miscompiles it. That counterexample forced the next decision.

**Decision — `noPhiChain` (`Morph/ClifCfgEncode.lean`).** Since the fold is
sequential, same-edge read-after-write (a chain, a swap, or a self-copy `x :=
x`) is a genuine encoder precondition, not a proof artifact. It is now a
second `Bool` gate in `encodeBlock` beside `noDupPairs`, so `encodeFunc`
refuses instead of miscompiling. `Morph/ClifCfgCorrect.lean` discharges both
hypotheses from the gates (`noDupPairs_huniq`, `noPhiChain_hsep`), and
`params_hold_fold_of_checks` is the form the block simulation consumes: no
extra assumptions on encoder output. Pinned on the real lowering — every
block of `lowerProgramCFG ifLtProg` passes both gates (`native_decide`).
Existing pins still encode; `lake build Morph`, `lake build Morph.Tests`, and
`tests/codegen/native.sh` (13/13) all green.

**Findings (toolchain).** `List.mem_iff_getElem?` is a two-component
existential (`∃ i, l[i]? = some a`), not three — the extra `hi` the first
attempt destructured does not exist. `cases h : e` substitutes `e` in the goal,
so the `false` branch wants `rfl`, not the equation. Implicit `{q}` binders do
not match an explicit-`∀` hypothesis shape at application time; the bridge
lemmas take `q`/`q'` explicitly. `by simp [hcon]` closes
`decide (q.src = q'.dst) = true`, no `decide_eq_true` needed.

**Result.** `lake env lean` green on `Morph/ClifCfgEncode.lean`,
`Morph/ClifCfgCorrect.lean`, `Morph/ClifCfgSimulate.lean`, no warnings.

**Still open.** C4b's terminator lemma (`encodeTerm` ↔ `return`/`goto`/`branch`),
the fuel induction (`execBlockFrom`/`execBlockFromIn` vs `runFuel`), and the
composed `cfg_correct`; then C3 → C2c → C7 → C8 → C9.

## Loop 168 — C4b terminator lemma: encodeTerm inversions + agreement across the join

**Goal.** Close the terminator half of C4b, leaving only the fuel induction and
the composed `cfg_correct`.

**Did.** `Morph/ClifCfgSimulate.lean`, new section "The terminator and the
agreement across an edge": `encodeTerm_return/goto/branch` (inversions pinning
each MIR terminator to its CLIF shape with the edge's arguments),
`runTerm_return_agree` (a `return` reads the same value through agreement),
`boolOf_asBool_agree` (both sides take the same `branch` edge),
`hreg_of_agree` (non-unit `src` reads are option-equalities, discharging the
merge lemmas' pointwise hypothesis), `agrees_after_edge` (agreement propagates
across a join: equality on parameters via `params_hold_fold`, untouched
elsewhere via `phiFoldEnv_not_dst`/`bindParams_not_mem`) plus the
`_of_checks` form consuming the encoder's gates directly.

**Findings (toolchain).** `Option.map f (some w)` needs `Option.map_some` in
the `simp only` set — definitional iota alone does not close it after a
hypothesis rewrite. `unfold runTerm` exposes the raw `match` rather than the
applied equation; `simp only [runTerm]` reduces it.

**Result.** `lake env lean` green on `Morph/ClifCfgSimulate.lean`, no warnings.

**Still open.** C4b's fuel induction (`execBlockFrom`/`execBlockFromIn` vs
`runFuel`) and the composed `cfg_correct`; then C3 → C2c → C7 → C8 → C9.

## Loop 169 — C4b threading fix: the successor starts from the post-body environment

**Goal.** Unblock the fuel induction: state the edge transfer so MIR and CLIF
thread the same environment.

**Found.** `runFuel` bound the successor's parameters onto the predecessor's
*pre-body* environment, discarding body writes — while MIR's `execBlockFrom`
threads the post-body `fenv'` and the module docstring promises post-body
threading ("a value defined in a block that dominates another is readable
there"). On the `ifLt` diamond the join's non-parameter registers diverged
(MIR saw the arm's writes, CLIF saw the entry's), so no full-agreement
induction could cross a join.

**Did.** `Morph/ClifBlocks.lean`: `runBlock` returns `Option (Env × Outcome)`,
`runFuel` binds onto `envPost`, `runFuel_succ` restated (`rfl`), doc notes the
threading contract. `run_singleBlockFunc` proof and all five `run` pins
re-checked by the kernel — unchanged behavior on straight-line shapes.

**Result.** `lake env lean` green on `Morph/ClifBlocks.lean`;
`Morph.ClifCfgEncode`, `Morph.ClifCfgSimulate`, `Morph.ClifRender` rebuild
green (the `runLowered` pins re-ran under the new threading).

**Still open.** C4b's body bridge (phi-free `execInstrsFullFrom` =
`execInstrsFull`), the single-block certificate step, the fuel induction, and
the composed `cfg_correct`; then C3 → C2c → C7 → C8 → C9.
