# External audit packet — Morph 0.1.0

Review scope for an outside auditor. All claims below reproduce from a clean
checkout (see §5). Metrics current as of loop 116 (2026-11-03); the
tag-time regression snapshot JSON ships with the release materials (see
`docs/AUDIT-INVITES-0.1.md`).

## 1. What is being audited

The `morph` CLI and the verified pipeline behind it: surface source text in,
evaluated result out. The release surface is `CHANGELOG.md` 0.1.0; the
compatibility promises are `STABILITY.md`.

## 2. What is proved (and where)

- **Totality.** The parser (`Morph/Frontend/*`, loops 9/39), the direct
  evaluator (`Morph.Executable`, loop 38), and both statement interpreters
  (`Morph.Interp`, `Morph.Frontend.HIRInterp`) are proved total: failure is
  an `Outcome` value, never a crash or divergence.
- **Agreement.** HIR lowering agrees with direct evaluation on the
  first-order fragment (`Morph.Frontend.HIRInterp`: the `agreeBoth`
  triple — statements, `while` runs, match-arms — plus whole-program
  `runHIRProgram_preservation`, loops 88/112). Loop 112 added HIR
  `Stmt.ifStmt`/`Stmt.matchStmt` with 1:1 lowering; `doWhile`/`forLoop`
  stay rejected with pinned theorems and a recorded desugar-faithfulness
  analysis (`HARD-GATES.md` G-6, loop 115).
- **Type soundness.** Progress + preservation in
  `Morph/Proofs/TypeSoundness/`; bidirectional checking mode
  (`Morph/Specs/TypeSystem/InferenceSound.lean`).
- **Substitution theory.** Simultaneous substitution
  (`Morph/Specs/SimultaneousSubst/`), machine↔relation β-agreement
  (`Morph/Specs/MachineRelation`, loop 10).
- **Spec depth.** 2081 machine-checked theorems repo-wide, 1633 in
  `Specs/`, across 68 spec modules (`SPEC_STATUS.md`: 1408 Lemmas
  theorems, 934 examples), 0 `sorry`, 0 axioms, 0 build warnings. The loop-17 consolidation
  convention: superseded spec fragments keep a finding record in their
  `Lemmas.lean` rather than being deleted silently.

## 3. Trust base (what the proofs do NOT cover)

- The Lean 4.27 toolchain, mathlib/Batteries/Aesop pins
  (`lakefile.lean`, `lean-toolchain`), and the Lake build itself.
- The *spec text*: Lean `Prop`s state intent. `SPEC_CONTRADICTIONS.md`
  #11 (two overstated `AbiDataRefinement` Props) was **resolved in loop
  111**: `Spec.lean` now states the validated conditional forms, proved
  in `Lemmas.lean`; refutations retained in git history. Auditors should
  still treat mapping-summary ✓ marks as claims, not results, and
  spot-check others — #11 is the precedent for why.
- `morph check` checks elaboration only; checking against an expected type
  needs type-syntax parsing (named future work, `CHANGELOG.md`).
- The Python spec-lint tooling (`scripts/spec_tools/`): 836 tests, 96%
  coverage, 0 lint errors, 106 lint warnings, 0 broken cross-refs.
  Warnings are the accepted baseline, not failures (zero-warning gate
  covers Lean only).

## 4. Known issues handed to the auditor

1. `SPEC_CONTRADICTIONS.md` #11 — resolved loop 111 (see trust base
   above). Retained here so auditors can verify the resolution.
2. Statement `let` takes no type annotation; the elaborator fills a
   placeholder the pretty-printer now drops (loop 90). No user impact;
   recorded for the type-syntax work.
3. `morph doc` shows a statement's first line only (no source spans in the
   AST — documented limitation, `Morph/Frontend/DocComment.lean`).

## 5. How to reproduce

```bash
lake build Morph Morph.Tests  # 0 warnings, 0 errors (454 jobs)
lake build morph              # the CLI
unset TMPDIR; python3 -m pytest -q            # 836 passed
python3 scripts/spec_tools/cli/main.py lint spec  # 0 errors, 106 warnings (baseline)
bash scripts/cross-ref-validate.sh               # 1704 pass / 0 fail
bash scripts/regression-snapshot.sh              # metrics + no-regression verdict
```

Note (G-8): run pytest with a clean `TMPDIR` — `TMPDIR=$PWD/.tmp`
breaks one waiver test (harness artifact, not a product defect).

Entry points for reviewers: `Main.lean` (CLI) → `Morph/Driver.lean`
(pipeline) → `Morph/Frontend/Parser.lean`, `Morph/Executable.lean`,
`Morph/Frontend/HIRLower.lean`, `Morph/Frontend/HIRInterp.lean`;
golden error coverage in `Morph/Tests/Driver.lean`, `Morph/Tests/Typing.lean`.

## 6. Hard gate

**Sending review invitations is the hard gate for this sprint and is NOT
done here.** The packet above is the prep; invites (recipients, access,
timeline) require the maintainer. Do not mark Sprint 9 complete on packet
authorship alone.
