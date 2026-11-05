# Morph Five-Year Roadmap (2026-11 → 2031-11)

> The middle layer of the planning stack. `LONGTERM_ROADMAP.md` is the
> 10-year horizon (eras, outcomes). `PATH_FORWARD.md` is the execution
> view (phases, tasks). **This file is the 5-year program**: what happens
> in which year, on what evidence, gated by what decision — covering Era 1
> closeout through Era 3. Years 6–10 remain governed by the long-term doc.
>
> Entry state is measured at loop 122 (2026-11-03), not aspirational.
> Every number below reproduces from the tree.

## 0. Entry state (measured, loop 122)

| Asset | State |
|---|---|
| Lean core | 2081 theorems (1633 in Specs/), 68 spec modules, 0 sorry / 0 stubs / 0 warnings, 454 build jobs |
| Agreement story | `agreeBoth` triple + `runHIRProgram_preservation`; `ifStmt`/`matchStmt` 1:1; `doWhile`/`forLoop` rejected with recorded analysis (G-6) |
| Contradictions | All 11 resolved or adjudicated false positive (#11 resolved loop 111) |
| Python tooling | 836 tests, 96.08% coverage (gate: 95%), lint 0 errors / 105 warnings (19 waived), cross-refs 1700/0 |
| Rust workspace | Builds clean: `fmt --check` 0, `clippy -D warnings` 0, 218 tests pass. `compiler/` (lexer/parser/typeck, **no codegen**), `runtime/` (actor/fiber/scheduler/memory/io/sync/value), `cli/` |
| Stdlib | Seed only: `Morph/Stdlib.lean` (187 lines, unwired) |
| CI | Configs correct and red-on-arrival-free (loops 118/120), **runners blocked on billing (G-1)** |
| Audit | Packet current (`docs/AUDIT-PACKET-0.1.md`), invites templated, G-7 checklist ready — **no invites sent, no tag cut (G-3/G-7)** |
| Release | 0.1.0 prepared, never tagged |

Two pre-existing plans constrain this design. `impl/roadmap.md` +
`impl/overview.md` assume a C++ runtime, LLVM backend, and 12-month v1.0
— written pre-audit and partly stale (they cite "6 sorries" and "40+
modules", and no C++ exists in the tree). This roadmap does **not**
adopt their timeline; it treats the backend language choice as an open
ADR (see Year 2). `docs/ERA2-BACKEND-SCOPE.md` Stages A–D are adopted as
the Year 2–3 technical spine.

## Principles (non-negotiable for all five years)

1. **Proof scope is never cut to meet a date.** Dates slip; the
   `compile_correct`-style theorems do not shrink. (Long-term rule:
   cut backend scope, never proof scope.)
2. **No Era-N implementation begins until Era-(N-1) exit gates are
   published.** The audit gate (G-3) freezes Year 2 compiler work; the
   1.0 freeze gates Year 4 runtime-proof work. Gates delay, never dilute.
3. **Metrics never regress without a published explanation.**
   Regression snapshots stay per-push once runners exist.
4. **Annual review amends this file only by ADR.** The plan changes by
   decision, never by drift. Quarterly: score the table in §6.

## Year 1 (now → 2027-11): close Era 1

**Theme:** convert the verified core into a verified *process*.

- Q1: billing resolved (G-1) → CI green per push; Pages deploy; versioned
  spec index live. Any red-on-arrival found by live runners is fixed
  before feature work (loops 118/120 already cleared the known ones).
- Q1–Q2: audit invites sent, 3-week review, findings published (G-3).
  Findings triage: each becomes a spec contradiction, named future work,
  or an accepted-baseline waiver — nothing evaporates.
- Q2: tag 0.1.0 per the G-7 checklist (incl. the index/specs re-stamp),
  announce. **Era-1 exit criteria check** (CI per push; 0/0/0; HIR
  end-to-end behind `--hir`; 0.1 released; one audit published).
- Q3–Q4: audit-finding remediation + maintenance (toolchain-churn duty:
  keep `lake build` green against Lean/mathlib updates). **Amendment
  loop 133 (`docs/ERA2-UNFREEZE.md`):** the "no Era-2 implementation
  until audit publishes" rule is lifted by maintainer directive — Stage
  A/B implementation proceeds in parallel with the gate track. Original
  rule kept as history; audit design work (backend ADR drafts,
  translation-validation position) remains what the auditors react to.

**Exit criteria:** Era-1 gates all green; 0.1 tagged; audit findings
triaged with owners. **If missed (amended loop 133):** Year 2 proceeds
under `docs/ERA2-UNFREEZE.md` in parallel with the open gates; the gates
still block release/audit, not implementation.

## Year 2 (2027-11 → 2028-11): the verified compiler core

**Theme:** one composed correctness theorem for a real fragment.

- H1 — Stage A (`ERA2-BACKEND-SCOPE.md`): HIR→MIR for the first-order
  fragment, MIR small-step semantics (store- and call-aware — the
  current oracle is not), `compile_correct` AST→HIR→MIR. Depends on the
  audit's answer to the fragment-contract question.
- H1 — Backend ADR: LLVM vs Cranelift, decided on **proof-interface
  simplicity**, stating the trusted computing base per backend and
  whether the connection is verified lowering or translation validation
  (the audit's other open question). The impl/roadmap.md LLVM default
  and the C++ runtime assumption are **inputs, not decisions** — the
  tree contains a Rust runtime and zero C++; any C++ introduction must
  justify itself against the existing Rust code in the ADR.
- H2 — Stage B: single-backend lowering for straight-line code,
  `morph build` behind a flag, golden-tested like the existing commands.
- Throughout: Rust frontend grows toward the backend (AST→MIR mapping
  in `compiler/`, replacing the current parse+typecheck-only pipeline);
  differential testing Lean-vs-Rust starts as an advisory gate.

**Exit criteria:** `compile_correct` for the first-order fragment;
`morph build` produces binaries for straight-line code; backend ADR
published with TCB statement. **If missed:** cut to one target, never
cut the theorem.

## Year 3 (2028-11 → 2029-11): language complete, 1.0 frozen

**Theme:** from fragment to language, from program to standard.

- H1 — Stage C: calls/control flow through the pipeline, `morph test`
  (golden + property suites), ABI/layout lemmas load-bearing in
  codegen proofs (safe: #11 resolved loop 111).
- H1 — Toolchain UX: LSP v1 (hover/go-to/errors off the total
  pipeline), `morph fmt`/`doc` promoted from flags to defaults.
- H2 — Stage D: channel safety, deadlock-freedom, taint
  noninterference, OCap — proven against the executable evaluator with
  executable counterexamples. Package manager v1 on the `ModuleSystem`
  hash-determinism proofs.
- H2 — Morph 1.0 + draft standard + conformance suite; 3–5 pilot users
  (≥1 external); "verified programming" tutorial path, every chapter
  `lake build`-checked.

**Exit criteria:** 1.0 + draft standard + conformance suite; LSP v1;
≥3 external pilots with published case studies (including every
soundness bug the pilots found). **If missed:** standard stays draft;
pilots extend, scope does not shrink.

## Year 4 (2029-11 → 2030-11): runtime proofs, certified builds

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

## Year 5 (2030-11 → 2031-11): standard ratified, platform hardened

**Theme:** from project to institution.

- Morph 2.0 + ratified standard; conformance executable by third
  parties; funded second implementation compiling the suite.
- Foundation + RFC process + CVE-grade soundness-response policy.
- 100 production users; university pipeline (≥10 teaching, funded PhD
  fellowships for core-proofs work).
- Proof maintenance: 3-version Lean-toolchain compatibility window in
  CI; tactic library published so new proofs cost insight, not
  boilerplate.

**Exit criteria (5-year checklist):** end-to-end certificate for
tier-1 targets; ratified standard with ≥2 conforming implementations;
foundation-led governance; assumption ledger fits on one page.

## Explicitly OUT of the five years (Eras 4–5)

Proof-carrying packages enforced; hardware/ISA boundary proof (RISC-V);
verified optimizing backend (`-O2` proofs); self-hosted Morph compiler;
Morph 3.0 edition system; regulatory acceptance as a milestone (pursue
opportunistically from Year 4, never gate releases on it); a million
programmers. These are tracked, not scheduled.

## Decision register (dates are deadlines, not aspirations)

| # | Decision | Due | Decides | Default if missed |
|---|---|---|---|---|
| D-1 | Billing / CI runners | Y1 Q1 | Whether any gate is observable | Plan clock pauses; maintenance only (loop 133: clock paused, then unfreeze lifted the implementation freeze — gates still block release) |
| D-2 | Translation validation vs verified lowering | Y1 (audit) | Backend ADR shape | Verified lowering (conservative) |
| D-3 | Backend target + language (LLVM/Cranelift; C++ question) | Y2 H1 | Stage B direction | Single Rust-native backend, straight-line only |
| D-4 | Supported-fragment contract for `morph build` | Y2 H1 | What `compile_correct` covers | Strict explicitly-listed subset |
| D-5 | 1.0 scope freeze | Y3 H1 | What pilots evaluate | Freeze slips a quarter, never shrinks |
| D-6 | Foundation formation | Y4 | Governance home | Fiscal sponsorship as bridge |

## Scoreboard (updated annually; first scoring: 2027-11)

| Metric | Now (loop 122) | Y1 | Y2 | Y3 | Y4 | Y5 |
|---|---|---|---|---|---|---|
| sorry / warnings (Lean) | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| Theorems | 2081 | ≥2200 | ≥3000 | ≥4000 | ≥5000 | ≥6500 |
| CI per push | Blocked | Green | Green | Green | Green + diff. matrix | Green, 3-ver compat |
| `compile_correct` | — | — | First-order fragment | +calls/control flow | +opt levels tracked | Stable |
| `morph build` | — | — | Straight-line, flagged | General | Certified `--certify` | Certified |
| Conformance suite | — | — | — | Draft + v1.0 | v2.0 (2 impls) | Ratified |
| Production users | 0 | 0 | 0 | ≥3 pilots | ≥1 safety-critical* | 100 |
| Toolchain UX | CLI | CLI+fmt/doc | +`build`/`test` | LSP v1 | Debugger, pkgs v2 | Incremental |
| Governance | Team | Team + auditors | RFC process | RFC process | Foundation | Elected leadership |

\* or published reset per Year 4 exit criteria.

## Risks to this plan (beyond the long-term register)

| Risk | Why it bites here | Hedge |
|---|---|---|
| Audit demands rework that consumes Y1 | Year 2 clock assumes clean exit | Audit remediation is Y1 Q3–Q4 by design; Stage A prep (design only) overlaps |
| Backend ADR deadlocks (LLVM vs Cranelift) | Blocks all of Stage B | D-3 default: single Rust-native backend; decide by Y2 H1 or default fires |
| impl/roadmap.md expectations (12-mo v1.0, C++) | Stakeholder confusion vs this plan's Y3 1.0 / open backend language | This file supersedes it for timeline; mark impl/roadmap.md historical at Y1 review |
| Lean churn breaks proofs mid-Era-2 | Proof repair crowds out Stage A–C | <30-min core check budget; 3-version window from Y4, best-effort before |
| Pilots find deep unsoundness in Y3 | 1.0 freeze slips | CVE-grade response (policy by Y4, practice from first finding); freeze slips, scope doesn't |

## Document relations

- This file schedules **outcomes by year**. Tasks live in
  `PATH_FORWARD.md`; horizon in `LONGTERM_ROADMAP.md`; backend scope in
  `docs/ERA2-BACKEND-SCOPE.md`; release procedure in `HARD-GATES.md` G-7.
- `impl/roadmap.md` + `impl/overview.md` remain the Rust-implementation
  viewpoint; where they conflict with this file on timeline or backend
  language, **this file governs** pending the Y1 review ADR.
- Review cadence: quarterly score the table above; annually confirm or
  revise by ADR. First review: 2027-11.
