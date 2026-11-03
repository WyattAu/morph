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
| G-6 | HIR `forLoop`/`doWhile` lowering | `doWhile` at-least-once vs `whileLoop`; `forLoop` iterator anonymous + unreachable (loop 78b) — no faithful 1:1 map on current evidence | A desugar-faithfulness proof vs surface semantics | Decided loop 112, analysis loop 115 (below): both stay `none` with pinned theorems (`toHIRStmt_doWhile_none`, `toHIR_forLoop_none`, plus `runDoWhile_*` characterization pins in `Morph.Interp`); `ifStmt`/`matchStmt` closed 1:1 in loop 112 |
| G-7 | Morph 0.1 *release* publication | Release process is a maintainer action (tag, announce) | Maintainer cuts the release | This pass prepares everything releasable (version, changelog, stability policy all present); checklist below |

## G-7 release checklist (loop 117, for the maintainer)

Preconditions (all true as of loop 116): `lake build Morph Morph.Tests`
0/0, 0 sorries/stubs, pytest 836, lint 0/106, cross-refs 1704/0,
`CHANGELOG.md` 0.1.0 section accurate, `STABILITY.md` present,
`docs/AUDIT-PACKET-0.1.md` current.

1. `export TMPDIR=/tmp; bash scripts/regression-snapshot.sh` — confirm
   no regressions; keep the snapshot JSON as the tag's metrics record
   (ships to auditors per `docs/AUDIT-INVITES-0.1.md` item 3).
2. `git tag 0.1.0` on the verified commit; push tag.
3. Billing resolved (G-1) → CI/Pages run on the tag; confirm green.
4. Send audit invites with packet + snapshot + timeline (G-3).
5. Re-stamp release-pinned numbers: `SPECIFICATION_INDEX.md` and
   `site/docs/specs.html` still carry the 0.1.0 stamp ("170 spec
   modules, 1,094 spec theorems" vs 104 md files on disk) — update to
   measured values or mark the stamp historical (loop 121).
6. Announce (release notes = `CHANGELOG.md` 0.1.0 section).

Do NOT tag a commit with failing checks; do NOT fold post-0.1.0 loop work
(HIR `ifStmt`/`matchStmt`, `runDoWhile` pins — all `Unreleased`) into
0.1.0 notes. They belong to the next release section.
## G-6 analysis (loop 115) — why the rejection stands

**`doWhile`.** Three desugar candidates were checked against `runDoWhile`
(`Morph/Interp.lean`, now pinned by `runDoWhile_zero/body_stuck/broke/
continued/done_false/done_true`):

1. `body; whileLoop cond body` — unfaithful: `break`/`continue` in the
   leading copy propagate out of the sequence instead of completing the
   loop (`runDoWhile_body_broke`) or entering the cond check
   (`runDoWhile_body_continued`); a stuck leading copy also skips the
   `while` entirely rather than propagating mid-loop state.
2. `whileLoop (flag || cond) [assign flag false; body]` with a fresh flag
   — unfaithful: surface `or` is strict (`Executable.evalWithFuel`
   evaluates both operands), so a stuck `cond` aborts before the first
   body run, contradicting `runDoWhile_body_stuck` (body effects precede
   any cond evaluation).
3. Flag + lazy guard, `whileLoop (ifThenElse flag true cond) [...]` —
   `ifThenElse` evaluates only the taken branch, so entry is faithful;
   but adopting it needs (a) statement-level free-variables + a freshness
   side condition (no `stmtFreeVars` exists today), (b) a fuel-inequality
   agreement (the desugar costs `varDecl` + per-iteration `assign` fuel,
   while `agreeBoth` is same-fuel `∀ fuel`), and (c) env-extension
   reasoning for the persistent flag binding. A real compilation pass
   with new proof architecture, not a sprint tail — recorded, not built.

**`forLoop` (expression).** Second leg beyond loop 78b: iteration needs
statement context (`whileLoop` is `Stmt`-only; `HIR.Expr` has no iteration
form), so even a counter-desugar cannot target HIR without an
expression→statement phase split. Rejection stands on both legs.

| G-8 | `test_none_when_absent` fails under `TMPDIR=$PWD/.tmp` | Harness artifact: `tempfile` under repo root lets `find_waivers_file` walk up to `spec-lint-waivers.toml` | Run pytest with clean `TMPDIR` (or `/tmp`) | Reproduced loop 112: `TMPDIR=$PWD/.tmp` → 835 passed + 1 failed; clean env → 836 passed; not a product defect |
