# Morph Five-Year Roadmap (2026-11 → 2031-11)

> The middle layer of the planning stack. `LONGTERM_ROADMAP.md` is the
> 10-year horizon (eras, outcomes). `PATH_FORWARD.md` is the execution
> view (phases, tasks). **This file is the 5-year program**: what happens
> in which year, on what evidence, gated by what decision — covering Era 1
> closeout through Era 3 and into the first pioneer year. Years 6–10 remain
> governed by the long-term doc.
>
> **Second edition, constructed 2026-11-25** — supersedes the loop-122
> (2026-11-03) edition. What changed and why: entry state re-measured
> (theorems 2081 → 2545, Stages A–C closed in the tree); the "blocked on
> billing" premise struck everywhere (public repo, free runners, CI
> observably green); D-2/D-3/D-4 recorded decided (ADR-032, loop 134);
> years re-timed to measured velocity (Stages B and C closed inside
> November). Further amendments by ADR only.

## 0. Entry state (measured 2026-11-25)

| Asset | State |
|---|---|
| Lean core | 309 `.lean` files (208 under `Specs/`), 2,545 theorem/lemma declarations (1,633 in `Specs/`, 704 core, 208 `Tests/` pins — counting per `scripts/regression-snapshot.sh`), 0 sorry / 0 stubs / 0 build warnings; `check-gates.sh` green |
| Proved chain | HIR run → MIR run (straight-line, branches, HIR→MIR calls) → CLIF text: `compile_total`, `lowerCallProg_correct`, `lowerProgramCFG_correct`; `morph test` goldens 13/13; codegen corpus 22/22 |
| Open technical item | Exactly one: C8 CLIF `call` encoder refused for want of the ABI decision (D-7); refusal proved as pins, encoder unblocked by the decision, not by more proof |
| Agreement story | `agreeBoth` triple + `runHIRProgram_preservation`; `ifStmt`/`matchStmt` 1:1; `doWhile`/`forLoop` rejected with recorded analysis (G-6) |
| Contradictions | All 11 resolved or adjudicated false positive (#11 resolved loop 111) |
| Python tooling | 844 tests, 96.06% coverage (gate: 95%); ruff + mypy clean on `spec_tools` scope; cross-refs 2027/2027; spec-links 992 markdown links, 0 broken |
| Rust workspace | `morph build --codegen=cranelift` exercised by `tests/codegen/check.sh` (22/22); 9/9 native differential under the trusted half (loop-153 record); full workspace test count last reported loop 122, not rebuilt in this environment |
| Stdlib | Seed only: `Morph/Stdlib.lean` (187 lines, unwired) |
| CI | Push pipeline green on the 2026-11-25 push (Lean Build + Spec Validation) with manual dispatch verified on both; nightly green 2026-11-21…24; Pages deploy-live verified by hand-trigger (rerun green after a transient artifact-listing failure, no repo change) |
| Stage D position | Scoped (`docs/STAGED-SCOPE.md`) + inventoried (`docs/STAGED-D1-INVENTORY.md`): executable memory/runtime models carry 0 theorems, `Specs/MemoryModel`'s 34 sit over a disconnected model, `borrow_preservation` is the one executable invariant; `HeapSafe` defined over `Memory.lean` blocks with success + boundary pins (S5, circulated for attack), D3 gated on the `stepActor` interface (D-8) |
| Audit | Packet current (`docs/AUDIT-PACKET-0.1.md`), invites templated, G-7 checklist ready — **no invites sent, no tag cut (G-3/G-7 open)** |
| Release | 0.1.0 prepared, never tagged |

Two pre-existing plans constrain this design. `impl/roadmap.md` +
`impl/overview.md` assume a C++ runtime, LLVM backend, and 12-month v1.0
— written pre-audit and stale (they cite "6 sorries" and "40+
modules", and no C++ exists in the tree). This roadmap does **not**
adopt their timeline; the backend question is settled (ADR-032:
Cranelift, verified lowering — D-2/D-3 done), and the C++ assumption is
dropped: any C++ introduction must justify itself against the existing
Rust code in a new ADR. `docs/ERA2-BACKEND-SCOPE.md` Stages A–C are
recorded closed; Stage D is the Year 1–2 technical spine.

## Principles (non-negotiable for all five years)

1. **Proof scope is never cut to meet a date.** Dates slip; the
   `compile_correct`-style theorems do not shrink. (Long-term rule:
   cut backend scope, never proof scope.)
2. **No Era-N implementation begins until Era-(N-1) exit gates are
   published.** The audit gate (G-3) freezes Year 2 compiler work; the
   1.0 freeze gates Year 3 runtime-proof work. Gates delay, never dilute.
3. **Metrics never regress without a published explanation.**
   Regression snapshots run per push now that runners are observed live
   (the "once runners exist" qualifier died 2026-11-25 with the billing
   story); the untracked `.reports/regression/snapshot-*.json` strays
   are committed or ignored by Y1 Q1 review.
4. **Annual review amends this file only by ADR.** The plan changes by
   decision, never by drift. Quarterly: score the table in §6.
5. **Docs are verified against live systems, not against each other.**
   A roadmap that contradicts the Actions tab is a bug at the same
   severity as a broken spec link (lesson of the 2026-11-25 billing
   correction). Quarterly review opens the Actions tab first.

## Year 1 (now → 2027-11): close Era 1, prove the heap core

**Theme:** convert the verified core into a verified *process*, and start
the memory story.

- Q1: first green push pipeline observed (in flight at construction);
  Pages deploy confirmed on a live run; versioned spec index live.
  D-7 (call ABI) decided → C8 encoder lands or the refusal stands with
  the rationale published. D-8 (`stepActor` interface) and D-9
  (`MemoryModel` verdict: bridge or supersede) decided.
- Q1–Q2: audit invites sent, 3-week review, findings published (G-3).
  Findings triage: each becomes a spec contradiction, named future work,
  or an accepted-baseline waiver — nothing evaporates.
- Q2: tag 0.1.0 per the G-7 checklist, announce. **Era-1 exit criteria
  check** (CI per push; 0/0/0; HIR end-to-end behind `--hir`; 0.1
  released; one audit published).
- Q2–Q4: Stage D core — D1 `HeapSafe` definition + preservation over
  `Memory.lean` ops; D2 borrow–heap agreement (building on the proved
  `borrow_preservation`); D3 `stepActor` invariant behind the D-8
  interface; D4 deadlock-freedom / channel safety with executable
  stuck-system witnesses. D5 (taint/OCap) starts if D2 lands early.
- Throughout: toolchain-churn duty (keep `lake build` green against
  Lean/mathlib updates). Amendment loop 133
  (`docs/ERA2-UNFREEZE.md`) still governs: gates block release/audit,
  not implementation.

**Exit criteria:** audit findings triaged with owners; 0.1 tagged;
D-7/D-8/D-9 decided; D1–D4 proved (D4 at minimum witness-style
progress). **If missed:** D5 and the 1.0 freeze slip to Y2 H2; theorem
scope is never cut to compensate.

Execution detail: [Year 1 sprints](YEAR1-SPRINTS.md) (S1–S26,
two-week sprints with per-sprint exit criteria, operating rules, and the
miss rules).

## Year 2 (2027-11 → 2028-11): 1.0 frozen, language complete

**Theme:** from proved fragment to standard-track language.

- H1 — D5: taint noninterference + OCap bridged to the evaluator with
  explicit attacker-observable equivalence (needs D2's no-aliasing —
  the load-bearing dependency of the whole Stage D).
- H1 — D-5 freeze list, pilot criteria, conformance harness grown out
  of `tests/codegen/corpus`.
- H1 — Toolchain UX: LSP v1 (hover/go-to/errors off the total
  pipeline), `morph fmt`/`doc` promoted from flags to defaults.
- H2 — Morph 1.0 + draft standard + conformance suite; 3–5 pilot users
  (≥1 external); "verified programming" tutorial path, every chapter
  `lake build`-checked.
- H2 — Generation-friendliness acceptance criteria (paradigm-agnostic —
  they serve LLM, diffusion, and JEPA-style predictors equally, so the
  language bets on verifiable generation, not on any one ML paradigm):
  every refusal/error is a stable machine-parseable value (code + span
  + violated predicate); `morph fmt` output is canonical; the AST has a
  stable serialized form for tooling (specified alongside LSP v1); each
  fragment predicate is published as a consumable emitter grammar. The
  existing corpus/pins/oracles stay generator-consumable.
- H2 — Control-plane thesis to test with pilots (not a commitment):
  Morph's ML-adjacent role is the harness around models, not the
  numerics inside them — actors for serving, capabilities for
  sandboxing untrusted (possibly model-generated) code, D5 taint
  tracking for training-data provenance. ML tensor/autodiff/GPU
  features are explicitly declined (C8 precedent: refuse what you
  cannot verify); if ever proposed, they go through the decision
  register with that refusal as the default.

**Exit criteria:** 1.0 + draft standard + conformance suite; LSP v1;
≥3 external pilots with published case studies (including every
soundness bug the pilots found). **If missed:** standard stays draft;
pilots extend, scope does not shrink.

## Year 3 (2028-11 → 2029-11): runtime proofs, certified builds

**Theme:** the language leaves the lab (Era 3 opens).

- Lean specification twins for the Rust runtime core (memory/scheduler/
  I/O); refinement proofs from twin to `ExecutionMachine` spec.
- `morph build --certify`: checkable (compiler version, program hash,
  preservation proof) artifact; third-party auditable.
- Differential matrix (targets × opt levels × runtimes) becomes a
  **blocking** gate; proof-checking time becomes a tracked budget
  (<30 min laptop check of the core).
- Debugger/profiler on fuel-indexed steps; packages v2 (proven
  resolution via `DependencySat`); FFI with machine-checked interfaces.
- Headline push: first safety-critical production deployment with the
  certificate as compliance evidence.

**Exit criteria:** certified builds; differential matrix blocking;
one safety-critical user *or* a published reset (per the long-term
rule: say so publicly if the platform bet fails).

## Year 4 (2029-11 → 2030-11): standard ratified, platform hardened

**Theme:** from project to institution.

- Morph 2.0 + ratified standard; conformance executable by third
  parties; funded second implementation compiling the suite.
- Foundation + RFC process + CVE-grade soundness-response policy.
- 100 production users; university pipeline (≥10 teaching, funded PhD
  fellowships for core-proofs work).
- Proof maintenance: 3-version Lean-toolchain compatibility window in
  CI; tactic library published so new proofs cost insight, not
  boilerplate.

**Exit criteria (program checklist):** end-to-end certificate for
tier-1 targets; ratified standard with ≥2 conforming implementations;
foundation-led governance; assumption ledger fits on one page.

## Year 5 (2030-11 → 2031-11): pioneer the former out-list

**Theme:** the institution does what the program deferred.

- First **verified optimization level** (`-O2` proofs for a tier-1
  target, via verified lowering per D-2 — never via a validation
  side-door); remaining levels stay translation-tested, explicitly so.
- **Self-hosted Morph compiler**: Morph-in-Morph for the verified
  fragment, compiling the core with its own certificate.
- **Hardware/ISA boundary proof** (RISC-V) for a tier-1 target,
  connecting `clif_correct_program`-style statements to the ISA model.
- Proof-carrying packages enforced (Year 3's v2 resolution proofs
  become a install-time requirement); Morph 3.0 edition system drafted.
- Regulatory acceptance pursued opportunistically (never a gate).

**Exit criteria:** `-O2` verified for tier-1; self-hosted fragment
compiles the core; ISA boundary proof for tier-1; edition system
drafted. Whatever misses stays tracked, not silently dropped.

## Explicitly OUT of the five years (tracked, not scheduled)

Million-programmer scale as a goal; regulatory acceptance as a
milestone; full 3.0 migration. These are watched at annual review, never
used to justify slipping a year.

## Decision register (dates are deadlines, not aspirations)

| # | Decision | Due | Decides | Default if missed |
|---|---|---|---|---|
| D-1 | ~~Billing / CI runners~~ RETIRED 2026-11-25 (premise false: public repo, runners free, CI runs) — kept as a one-line warning against unverified gates | — | Whether any gate is observable | Push unblocks observation; no clock pause was ever needed |
| D-2 | Translation validation vs verified lowering | DONE loop 134 (ADR-032) | Backend ADR shape | Verified lowering (conservative) |
| D-3 | Backend target + language (LLVM/Cranelift; C++ question) | DONE loop 134 (ADR-032: Cranelift) | Stage B direction | Single Rust-native backend, straight-line only; C++ stays out without a justifying ADR |
| D-4 | Supported-fragment contract for `morph build` | DONE (ADR-032 §Status, per `docs/STAGEC-SCOPE.md`) | What the pipeline theorems cover | Strict explicitly-listed subset |
| D-5 | 1.0 scope freeze | Y2 H1 (was Y3 H1 — pulled forward with Stage D) | What pilots evaluate | Freeze slips a quarter, never shrinks |
| D-6 | Foundation formation | Y4 | Governance home | Fiscal sponsorship as bridge |
| D-7 | Call ABI + layout for the C8 encoder | Y1 Q1 | Whether the CLIF `call` refusal lifts | DECIDED 2026-11-25: B+C (typed signatures per the Runtime marshal table, declared Morph-side) by maintainer direction, ahead of the S3 deadline; slices A (call model/text/encoder, refusal per-shape) and B1 (program threading + typed runner/stepIn + pins, emitter boundary pinned) in the tree, green; slice B2a (typed call agreement), B2b (program-aware emission + preamble), B2c (Evidence typed convergence), C1 (slotted returns + bool-call acceptance), C2 (body-type gate switch), D1 (named rendering), and D2 (whole-program emission), and C3a (slotted body gate, D-7 encoder closed) in the tree, green; driver path deferred (no surface syntax builds CallProg) |
| D-8 | `stepActor` interface: thread heap/stack or stay state-free | Y1 Q2 | What D3's invariant quantifies over | State-free reading wins (smaller claim); D3 restated to match |
| D-9 | `Specs/MemoryModel` verdict: bridge to executable or supersede | Y1 Q2 | What D1–D2 build on | Supersede: executable `Memory.lean` is authoritative, spec model cited as requirements only |

## Scoreboard (updated annually; next scoring: 2027-11)

| Metric | Now (2026-11-25) | Y1 | Y2 | Y3 | Y4 | Y5 |
|---|---|---|---|---|---|---|
| sorry / warnings (Lean) | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| Theorems | 2545 | ≥2600 | ≥3000 | ≥3800 | ≥4800 | ≥6000 |
| CI per push | Green (first green push pipeline 2026-11-25) | Green | Green | Green | Green + diff. matrix | Green, 3-ver compat |
| Pipeline theorem | HIR→MIR→CLIF exc. CLIF `call` | + call (D-7) | Frozen with 1.0 | Certified artifacts | Stable | Stable, first -O2 level |
| `morph build` | Flagged (`--codegen=cranelift`) | Flagged, broader fragment | General (1.0) | Certified `--certify` | Certified | Self-hosted fragment |
| Conformance suite | — | — | Draft + v1.0 | v2.0 | Ratified (2 impls) | Done |
| Production users | 0 | 0 | ≥3 pilots | ≥1 safety-critical* | 100 | 100+, institutions |
| Toolchain UX | CLI | CLI hardened | +fmt/doc defaults, LSP v1 | Debugger, pkgs v2 | Incremental | Stable |
| Governance | Team | Team + auditors | RFC process | RFC process | Foundation | Elected leadership |

\* or published reset per Year 3 exit criteria.

## Risks to this plan (beyond the long-term register)

| Risk | Why it bites here | Hedge |
|---|---|---|
| Audit demands rework that consumes Y1 | Year 1 clock assumes clean exit | Audit remediation is Y1 Q3–Q4 by design; Stage D design overlaps, proofs don't start on contested ground |
| D-7 ABI decision deadlocks | C8 encoder stays refused | Default fires by design: refusal pins stand, D-work proceeds (C8 is a leaf) |
| D-8/D-9 decided wrong | D1–D4 built on the wrong interface/model | Both are definitions-first items (`HeapSafe`, interface); wrong choices cost weeks, not eras — restate and re-prove |
| Single-maintainer bandwidth | 71-commit pushes, docs drift while code moves | Push per loop and let CI read every tree (true since 2026-11-25); docs-vs-reality is principle 5 |
| Lean churn breaks proofs mid-Stage-D | Proof repair crowds out D3–D5 | <30-min core check budget; 3-version window from Y4, best-effort before |
| Pilots find deep unsoundness in Y2 | 1.0 freeze slips | CVE-grade response (policy by Y4, practice from first finding); freeze slips, scope doesn't |

## Document relations

- This file schedules **outcomes by year**. Tasks live in
  `PATH_FORWARD.md`; horizon in `LONGTERM_ROADMAP.md`; backend scope in
  `docs/ERA2-BACKEND-SCOPE.md` (Stages A–C closed, D scoped in
  `docs/STAGED-SCOPE.md` + inventoried in `docs/STAGED-D1-INVENTORY.md`);
  release procedure in `HARD-GATES.md` G-7.
- `impl/roadmap.md` + `impl/overview.md` remain the Rust-implementation
  viewpoint; where they conflict with this file on timeline or backend
  language, **this file governs**. Mark them historical at the Y1 Q1
  review.
- Review cadence: quarterly score the table above *after opening the
  Actions tab* (principle 5); annually confirm or revise by ADR. First
  quarterly review: 2027-02.
