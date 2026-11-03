# Morph Core Problems — Roadmap and Sprints

> Written 2026-11-02 (loop 111), closed out 2026-11-02 (loop 116). Scope:
> the Lean core, toolchain, gates, and docs the project itself lists as exit
> criteria or known problems. Frontier batches are frozen; Era-2+ tracks
> (Rust runtime, stdlib, backend) are gates, not sprints. Each sprint states
> its evidence, work, and exit check. Hard gates live in `HARD-GATES.md`.
> All seven sprints below are DONE; the baseline shows the closing state.

## Baseline (closing state, verified loop 116)

| Check | Result |
|---|---|
| `lake build Morph Morph.Tests` | 454 jobs, 0 errors, 0 warnings |
| `sorry` scan | 0 hits (Sprint 1 headers reworded; hooks pass) |
| Spec stubs | 0 (`example : True := trivial` absent) |
| Python pytest | 836 passed, clean `TMPDIR` (G-8 artifact otherwise) |
| Spec lint | 0 errors / 106 warnings (documented count) |
| Cross-refs | 1704 pass / 0 fail |
| Theorems | 2081 repo-wide, 1633 in Specs/ (Era-1 ≥1500 target met) |
| `SPEC_STATUS.md` | 68 modules, 1408 lemmas, 934 examples, regenerated loop 114 |
| `morph` CLI | eval/parse/check/run/run --hir/fmt/doc/version all present |
| Versioning | 0.1.0 + CHANGELOG + STABILITY.md present |

## Sprint 1 — Sorry-scan false positives (mine, blocking) — DONE (loop 111)

**Problem.** My nine batch `Lemmas.lean` headers say "No `sorry`, no
axioms". The pre-commit/CI scanner counts the literal word, so it reports
9 sorries and the pre-commit hook would block every commit.
**Work.** Reword all nine headers to "sorry-free". Delete root scratch
probes (`.tmp_probe6.lean`, `probe_shift.lean`) and `.tmp/` logs.
**Exit.** `grep -rn "sorry" Morph/ --include="*.lean"` empty; pre-commit
step 2 passes.

## Sprint 2 — Zero warnings — DONE (loop 111)

**Problem.** 2 build warnings, both mine (`BatchP4/Spec.lean`: unused `c`
in `disconnect`, unused `b` in `syncB`; already prefixed `_`).
**Work.** Rebuild and confirm 0 warnings.
**Exit.** `lake build` output contains no `warning: Morph/`.

## Sprint 3 — Contradiction #11: AbiDataRefinement overstatement — DONE (loop 111, commit `AbiDataRefinement` revision)

**Problem.** `Spec.lean` claims Status Complete / "None identified" with
`✓` on all three Props, while `Lemmas.lean` machine-checks two refutations
(`spec_layout_compatibility_false`, `spec_data_validation_false`).
A spec that asserts what its own lemmas refute is the one live soundness
defect in the corpus.
**Work.** Weaken the two Props to their validated conditional forms
(compatibility ⇒ equal ABI types; validity needs offsets + size match),
update the mapping summary/status/known-issues in `Spec.lean`, close the
`SPEC_CONTRADICTIONS.md` entry as resolved.
**Exit.** No `¬spec_*` theorem for any asserted Prop; spec text and proofs
agree; full build green.

## Sprint 4 — HIR statement coverage — DONE (loop 112; G-6 analysis loop 115)

**Problem.** Era-1 exit criteria ask for full-fragment lowering ("whatever
the surface supports, HIR represents"). Statements `ifStmt`/`matchStmt`
lower to `none` with pinned theorems; HIR expressions already have
`ifThenElse`/`match`, so the statement gap is a missing 1:1 mapping, not a
design unknown. (`doWhile`/`forLoop` need desugar-faithfulness analysis
against surface semantics first — gate inside the sprint.)
**Work.** Add `HIR.Stmt.ifStmt`/`matchStmt` + lowering + interpreter cases
+ preservation extension + CLI goldens; keep `none` for what cannot be
mapped faithfully, with the reason pinned as today.
**Exit.** `--hir` runs every statement the mapping covers; rejections stay
exact; preservation theorem covers the new cases; goldens updated.

## Sprint 5 — Depth audit of thin modules — DONE (loop 112 verdicts: complete as specified, no padding)

**Problem.** Era-1 demands the depth re-audit ("every lemma must be real").
Thinnest modules: `MachineRelation` (3 theorems), `Maths` (4),
`DualOptimization` (4). The audit question is coverage (does the Spec
promise more than the Lemmas deliver, à la #11), not count.
**Work.** Read each thin Spec end to end; prove only what the Spec already
asserts and is currently unproved; record everything else as an explicit
finding, not padding.
**Exit.** Each thin module gets a written verdict (complete / strengthened /
finding recorded); no new `sorry`; build green.

## Sprint 6 — Loop documentation and status drift — DONE (loops 113–114; `SPEC_STATUS.md` regenerated to 68 modules)

**Problem.** Loops 103–110 (BatchBCD/BatchFGH/BatchHIJ/P1–P5) shipped
briefs + ADR records but no `docs/RESEARCH-LOOPS-*.md` entries, breaking
the project's heartbeat convention; `SPEC_STATUS.md` predates my modules;
`CHANGELOG.md` has no entries past 0.1.0 work.
**Work.** Write `docs/RESEARCH-LOOPS-103-110.md`; regenerate
`SPEC_STATUS.md`; add CHANGELOG entries.
**Exit.** Every loop 103–110 has a dated entry; status/spec counts match
the tree; changelog lists the batches.

## Sprint 7 — Final verification — DONE (loop 116, this pass)

Rebuilt everything (454 jobs, 0 errors/warnings); pytest 836 passed;
spec lint 0 errors/106 warnings; cross-refs 1704/0; regression snapshot
vs loop-113 baseline shows only the expected counts drift (see heartbeat).
G-8 (`TMPDIR` harness artifact) disposition recorded in `HARD-GATES.md`.

## Explicitly out of scope (gates, see HARD-GATES.md)

Billing-blocked CI/Pages/nightly; external audit; Rust runtime completion;
standard library; HIR `forLoop` desugar if unfaithful; any item that needs
a maintainer decision mid-sprint (recorded, not built).
