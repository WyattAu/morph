# External audit packet — Morph 0.1.0

Review scope for an outside auditor. All claims below reproduce from a clean
checkout (see §5). Metrics re-verified loop 125 (2026-11-03); the
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
- **HIR→MIR bridge.** `Morph/HIRToMIRCorrect.lean` (loops 139–142)
  connects the HIR evaluator to the MIR executor on the straight-line
  fragment: `lower_correct` (expressions), `lowerStmts_correct`
  (statements, carrying the environment relation and store preservation),
  `compile_correct` and `compile_correct_env` (programs: `lowerProgram`
  accepting a program whose emitted instructions run implies `execFunc`
  returns the HIR value and the final environment agrees on every binding,
  not just the result register). `lower_total` and `lower_total_lit` are
  the converse at expression level: if the HIR evaluates, the emitted
  code runs and leaves the store untouched. **Scope:** `IsStraight` only —
  single function, single block, no calls, no control flow. `lam`, `app`,
  `whileLoop` and `match` are rejected by the lowering, and MIR's `.call`
  rule is `none` (`Morph/MIR.lean`), so no claim is made about functions
  calling functions. Both directions are now stated: the `compile_correct`
  pair takes MIR success and concludes source agreement, while
  `compile_total` (A2 exit, loop 143) takes the source run and concludes
  `execFunc` returns the same value, with no MIR-success hypothesis. What is
  deliberately *not* proved is unconditional machine totality:
  `MIR.evalUnOp`/`evalBinOp` are partial exactly where the HIR oracle is
  (`evalUnop_glue`, `evalBinop_glue`), so a mistyped `unop` stalls both
  sides and an always-runs claim would be false without a typing hypothesis.
  No failure-coincidence claim is made anywhere (per the `ERA2-UNFREEZE`
  safeguard).
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
  coverage (96.14% measured loop 125), 0 lint errors, 105 lint warnings (19 waived), 0 broken cross-refs.
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
python3 scripts/spec_tools/cli/main.py lint spec  # 0 errors, 105 warnings (baseline; 19 waived)
bash scripts/cross-ref-validate.sh               # 1700 pass / 0 failbash scripts/regression-snapshot.sh             # metrics + no-regression verdict
cargo build -p morph-codegen                  # morph-clif (stage B item B7)
tests/codegen/check.sh                       # 16/16: corpus accept/reject, Lean only
tests/codegen/native.sh                      # 9/9: Lean value vs native value
```

The Stage B section (§6) is newer than the §2 metric counts: those were re-verified
at loop 125 and do not include the `Clif*` modules (loops 144–153). Re-running
`scripts/regression-snapshot.sh` refreshes them; no claim in §6 depends on the
counts.

Note (G-8): run pytest with a clean `TMPDIR` — `TMPDIR=$PWD/.tmp`
breaks one waiver test (harness artifact, not a product defect).

Entry points for reviewers: `Main.lean` (CLI) → `Morph/Driver.lean`
(pipeline) → `Morph/Frontend/Parser.lean`, `Morph/Executable.lean`,
`Morph/Frontend/HIRLower.lean`, `Morph/Frontend/HIRInterp.lean`;
golden error coverage in `Morph/Tests/Driver.lean`, `Morph/Tests/Typing.lean`.

## 6. Era-2 Stage B: what the Cranelift path claims (added loop 153)

The freeze on Era-2 implementation was lifted by maintainer directive
(`docs/ERA2-UNFREEZE.md`, loop 133), and Stage B is the first thing that landed
under it. Scope, subset and reject list: `docs/STAGEB-SCOPE.md`.

**Proved (B1–B6, pure Lean, 0 `sorry`).**

- The CLIF model (`Morph/ClifTarget.lean`) covers exactly the ten instructions
the encoder emits, each with an agreement lemma against the MIR oracle
(`Morph/ClifLower.lean`, B3), and the simulation is stated as a *trace*
(`Morph/ClifSimulate.lean`, B4): a typed step certificate in, `Clif.run` on the
same values out, transported to `execFunc` via `AgreesOnValues`.
- `clif_correct_program` (`Morph/ClifCorrect.lean`) composes that with
`compile_total` into one conjunction over the same HIR value. It is a
conjunction on purpose: no claim is made that a MIR failure implies a CLIF
failure (the `ERA2-UNFREEZE` safeguard).
- The printer/parser (`Morph/ClifRender.lean`, B5) round-trips at the *token*
level (`parseFunc_toksFunc`, `parseFunc_toksFunc_append`). The text layer is
delegated to `cranelift-reader`.
- The emitter (`Morph/ClifEmit.lean`, B6) is `rfl`-equal to `blockEncode` on the
shape `lowerProgram` produces, minus the unit prologue (CLIF has no unit value).

**Evidence only (B7–B8).** `codegen/` (bin `morph-clif`, package
`morph-codegen`) pins `cranelift-codegen` / `-reader` / `-object` / `-module` /
`-native` at **0.137.1** (newest stable line; `0.138.0-rc.1` is a prerelease and
was not taken). It reads the artifact, compiles it, emits an object, links
against a two-line C runner calling `morph_main`, and `tests/codegen/native.sh`
compares each native program's stdout against the value `morph run` printed:
**9/9 agree**, including a negative value and one above 32 bits.

New trusted components: `cranelift-reader`, `cranelift-codegen`,
`cranelift-object`, `cranelift-module`, `cranelift-native`, the system `cc`, and
the embedded C runner (`codegen/src/main.rs`).

**Precedent worth an auditor's attention.** The printer originally wrote `%v1`
where CLIF spells `v1`, so no artifact was readable; B5's proofs covered the
token stream and had delegated the text to the reader without ever asking it.
Both defects of this stage (that spelling, and a unit-valued program printing an
undefined `v0`) were found by *running the pipeline*, not by proofs, and both are
now pinned by goldens or corpus rows. Mappings that say "delegated to a trusted
component" should be read as "unchecked by us", not "accepted by it".

## 7. Era-2 scope for auditors to react to

- `docs/ERA2-BACKEND-SCOPE.md` (post-audit Stages A–D, open audit
  questions) + `docs/STAGEA-PREP-125.md` (Year-1 design-only positions:
  strict-subset `morph build` contract, verified-lowering default, MIR
  small-step gap). No Era-2 implementation lands until the audit
  publishes (Year-1 freeze).

## 8. Hard gate

**Sending review invitations is the hard gate for this sprint and is NOT
done here.** The packet above is the prep; invites (recipients, access,
timeline) require the maintainer. Do not mark Sprint 9 complete on packet
authorship alone.
