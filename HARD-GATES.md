# Hard Gates

> Everything this core pass cannot proceed past, with what unblocks it.
> Skipped per directive; recorded, never silently dropped. Updated as
> sprints run.

| # | Gate | Blocked by | Unblocks when | Disposition |
|---|---|---|---|---|
| G-1 | CI per push (lean-build, spec-validation, nightly, Pages) | GitHub billing spending limit (account-level, ROADMAP §2.4) | A maintainer resolves billing | Workflows verified correct by reading; cannot execute here |
| G-2 | GitHub Pages deploy + versioned spec index | Same billing gate (G-1) | Billing resolved | `site/` + `pages.yml` verified present and correct |
| G-3 | External audit of the soundness story (Era-1 exit) | Requires real external reviewers | Maintainers invite 2–3 reviewers | Cannot be produced from inside the repo |
| G-4 | Rust runtime (`compiler/`, `runtime/`, `cli/`) completion | Era-2+ 12-month track; needs backend/ISA decisions (ADRs) | Era-1 exit + backend ADR | Sprint 1 checks whether the workspace builds; no feature work here |
| G-5 | Standard library (§6.4: core types, collections, IO, concurrency) | Era-2 track, 7–11 weeks, needs runtime (G-4) | G-4 + Era-1 exit | Not started; not a current-core defect |
| G-6 | HIR `forLoop`/`doWhile` lowering | `doWhile` at-least-once vs `whileLoop`; `forLoop` iterator anonymous + unreachable (loop 78b) — no faithful 1:1 map on current evidence | A desugar-faithfulness proof vs surface semantics | Decided loop 112: both stay `none` with pinned theorems (`toHIRStmt_doWhile_none`, `toHIR_forLoop_none`); `ifStmt`/`matchStmt` closed 1:1 in the same sprint |
| G-7 | Morph 0.1 *release* publication | Release process is a maintainer action (tag, announce) | Maintainer cuts the release | This pass prepares everything releasable (version, changelog, stability policy all present) |
| G-8 | `test_none_when_absent` fails under `TMPDIR=$PWD/.tmp` | Harness artifact: `tempfile` under repo root lets `find_waivers_file` walk up to `spec-lint-waivers.toml` | Run pytest with clean `TMPDIR` (or `/tmp`) | Reproduced loop 112: `TMPDIR=$PWD/.tmp` → 835 passed + 1 failed; clean env → 836 passed; not a product defect |
