# Morph Long-Term Roadmap: The 10-Year Vision

> The destination this whole project is walking toward. `ROADMAP.md` is the
> status view (weeks–months), `PATH_FORWARD.md` is the execution view
> (what to do next); this file is the **horizon view** (years). It is
> deliberately balanced across the three pillars that must all win for
> Morph to matter: **verification depth**, **language & toolchain**, and
> **ecosystem & adoption**. A verified language nobody uses is a thesis; a
> popular language nobody verified is just another language.
>
> Lean 4 v4.27.0 | Lake 5.0.0 | mathlib4 + batteries + aesop

---

## The North Star

**By 2036, Morph is the first general-purpose programming language whose
entire execution story — from surface syntax to machine code to runtime
behavior — carries machine-checked proof, and whose toolchain is pleasant
enough that working programmers choose it anyway.**

Concretely, that means three audacious outcomes:

1. **A proof you can ship.** `lake build` on the Morph toolchain yields not
   just binaries but a checkable certificate: this compiler version
   preserves the semantics of every program it compiles, this runtime
   upholds the memory model, this standard library satisfies its specs.
2. **A language you can love.** Total syntax, helpful errors, fast feedback,
   LSP, debugger, packages — the table stakes of modern developer
   experience, all present.
3. **An ecosystem you can trust.** Production users in at least one
   safety-critical domain (e.g., smart contracts, medical devices,
   automotive, finance settlement), a published language standard with a
   conformance suite, and a foundation-grade governance story.

If any one pillar collapses, the vision fails. The eras below advance all
three in lockstep, with explicit exit criteria so we always know whether
we are on track.

---

## Baseline: Where We Stand (2026-10-30)

Verified current values (research loops 60–82):

| Metric | Value |
|---|---|
| `.lean` files / lines | 213 files / ~43k lines |
| Spec modules | 58 (all ship `Spec`/`Lemmas`/`Examples`) |
| Theorems / lemmas | 1160, **0 `sorry`**, **0 stubs**, **0 warnings** |
| Frontend | Total lexer (proven), fuel-monotone parser (full surface), name resolution as its own pass (idempotence + fixed-point proofs) |
| HIR | Lowering for the representable fragment (`some`/`none` contract), HIR evaluator + preservation proofs |
| Types | `inferType`/`checkType`/`synthType`/`unify` with soundness proofs |
| CLI | `morph eval` / `parse` / `run` / `check` (human-readable type errors) |
| Soundness | Preservation + progress, zero-warning gate, blocking pre-commit |
| Property tests | Plausible-based (`Morph/Tests/Property.lean`) |
| CI | Correct but **blocked on billing**; 26 broken spec links; Python spec-tools at 93.29% coverage |

In short: the **verified core calculus exists**. Everything after this is
scaling it outward (more language, real backend, real runtime) and upward
(real users, real standard).

---

## Era 1 — Lock the Foundation (Year 1: now → 2027-10)

**Theme:** convert the current lead into an unbreakable floor. No new
ambition until the gates are green and the depth re-audit is done.

### Verification depth
- Unblock CI (resolve billing) so all four workflows + Pages run per push.
- Depth re-audit of all 58 spec modules: every lemma must be *real*
  (loop 82 closed the "empty module" gap; this closes the "shallow lemma"
  gap). Target: ≥1500 theorems, still 0 sorry / 0 warnings.
- Regression snapshots (`.reports/regression/`): build metrics, theorem
  counts, and `morph` CLI golden outputs diffed per push; CI fails on
  regression.
- Spec integrity: fix the 26 broken cross-references; normalize or suppress
  the section-numbering lint; Python spec-tools coverage ≥95%.

### Language & toolchain
- Complete the HIR story: full-fragment lowering (whatever the surface
  supports, HIR represents), HIR type preservation end-to-end, and
  executable HIR evaluation wired into `morph run` behind a flag.
- Error-message quality pass: every type error and lowering rejection gets
  a golden test with a human-reviewed message.
- `morph fmt` (total pretty-printer, proven idempotent) and `morph doc`
  (API docs from source).

### Ecosystem & adoption
- Publish the documentation site (unblock Pages) + versioned spec index.
- Adopt semantic versioning for the language; publish Morph 0.1 with a
  changelog and a stability policy for the core calculus.
- First external eyes: invite 2–3 friendly reviewers (PL / verification
  background) for a public audit of the soundness story; publish findings.

**Exit criteria:** CI green per push; 0 sorry/0 warnings/0 broken links;
HIR end-to-end behind a flag; Morph 0.1 released; one external audit
published. **If missed:** do not start Era 2's backend work.

---

## Era 2 — The Verified Compiler (Years 2–3: → 2029-10)

**Theme:** turn the verified frontend into a verified *compiler* that emits
code for a real target, with the proof going all the way down.

### Verification depth
- **MIR + backend lowering proofs.** Introduce a machine-level IR with an
  explicit memory/ABI model; prove AST→HIR→MIR semantic preservation as a
  single composed theorem (`compile_correct`), not three folklore claims.
- **ABI & layout proofs:** struct layout, alignment, calling convention —
  today's `AbiAlignmentAlgebra`/`AbiDataRefinement` stubs become the
  load-bearing lemmas of code generation.
- **Concurrency & memory model:** channel safety, deadlock-freedom for the
  actor/process core; link the memory-acyclicity and affine-logic specs to
  the actual allocator interface.
- **Security proofs that bite:** taint-flow noninterference and the
  capability (OCap) model proven against the *executable* evaluator, with
  executable counterexamples for rejected programs.

### Language & toolchain
- **Native backend v1:** LLVM lowering (or Cranelift — decide in an ADR;
  criterion: proof-interface simplicity, not hype) for the first-order
  fragment; `morph build` produces binaries; `morph test` runs golden +
  property suites.
- **LSP v1:** hover types, go-to-definition, inline errors — powered by the
  same total pipeline (a total lexer/parser means the IDE never chokes on
  half-written code).
- **Effect system in the surface language:** the `MonadicEffect` spec
  becomes real syntax with handler semantics and lowering proofs.
- **Linear/affine types (opt-in):** resource disciplines from
  `MemoryAffineLogic` graduate into the typechecker behind a strict-mode
  flag, with borrow errors proven sound.

### Ecosystem & adoption
- **Morph 1.0 + language standard (draft):** freeze the core calculus and
  publish the standard as versioned spec documents with a conformance test
  suite (every `spec/language/*` gets executable assertions).
- **Package manager v1:** content-addressed registry reusing the
  `ModuleSystem` hash-determinism proofs (the registry *is* the module
  system, not a second one).
- **Pilot users:** 3–5 pilot projects, at least one outside our own team;
  publish case studies including every soundness bug the pilots found
  (there will be some — that is the point).
- **Education track:** a "verified programming" tutorial path where every
  chapter's claims are `lake build`-checked.

**Exit criteria:** `compile_correct` for the first-order fragment;
self-hosted `morph build` of the standard library; LSP v1 shipped; Morph
1.0 + draft standard + conformance suite; ≥3 external pilots. **If missed:**
cut backend scope (fewer targets), never cut proof scope.

---

## Era 3 — Runtime & Real-World Scale (Years 4–5: → 2031-10)

**Theme:** the language leaves the lab. Real runtime, real standard
library, real production load — with the proofs keeping pace.

### Verification depth
- **Verified runtime core:** the `impl/roadmap.md` Rust runtime (memory
  subsystem, M:N scheduler, I/O poller) gets a Lean specification twin;
  prove the runtime's observable behavior refines the execution-machine
  spec (`ExecutionMachine` Lemmas become refinement proofs, not just
  safety lemmas).
- **End-to-end certificate:** `morph build --certify` emits a checkable
  artifact tying (compiler version, program hash, preservation proof) —
  auditable by third parties without trusting our infrastructure.
- **Differential verification:** property-based differential testing
  between the Lean executable semantics, the native backend, and the
  runtime becomes a blocking gate (today's `tests/differential/manifest.tsv`
  grows into a matrix: targets × optimization levels × runtimes).
- **Proof performance:** proof-checking time and `lake build` time are
  tracked metrics with budgets; shard the proof corpus so a laptop still
  checks the core in <30 minutes.

### Language & toolchain
- **Full language:** closures-as-values everywhere, complete pattern
  exhaustiveness, modules/functors in surface syntax, `comptime`
  evaluation with fuel accounting users can reason about.
- **Debugger + profiler:** time-travel debugging on the executable
  semantics (fuel-indexed steps make this nearly free); allocation and
  fuel profilers that speak in source-level terms.
- **Package ecosystem v2:** version solver with proven resolution
  (`DependencySat` graduates into the solver), lockfiles, vendoring,
  private registries.
- **FFI with contracts:** foreign calls carry machine-checked interface
  specs; unverified FFI is explicit, fenced, and auditable.

### Ecosystem & adoption
- **First safety-critical deployment:** at least one production system in
  a regulated or high-stakes domain ships on Morph, with the certificate
  as part of its compliance evidence. This is the era's headline goal.
- **Morph 2.0 + ratified standard:** the standard graduates from draft
  with a multi-implementation conformance process (our compiler is
  implementation #1; fund or invite #2).
- **Foundation & governance:** establish a nonprofit home, RFC process,
  and a security-response policy with CVE handling for soundness bugs
  (treat an unsoundness like a memory-safety CVE: coordinated disclosure,
  advisory, patched release).
- **Commercial support lane:** at least one company offering Morph
  support/consulting that is not us — the true test of ecosystem health.

**Exit criteria:** certified builds; one safety-critical production user;
Morph 2.0 ratified; independent second implementation compiling the
conformance suite; foundation established. **If missed:** the language is
a research success but not yet a platform — say so publicly and reset.

---

## Era 4 — The Trust Platform (Years 6–7: → 2033-10)

**Theme:** Morph stops being "a language with proofs" and becomes "the
default answer when failure is expensive."

### Verification depth
- **Proof-carrying everything:** packages ship with their proofs;
  `morph audit <package>` replays any dependency's claims locally.
  Unsound package versions are unpublishable by construction.
- **Hardware boundary:** verified ABI down to the ISA model for at least
  one target (RISC-V — open spec, tractable model); prove the code
  generator respects the machine memory model, closing the last gap
  between Lean semantics and silicon behavior.
- **Continuous soundness fuzzing:** a standing red-team (people + automation)
  whose only job is breaking soundness; every escape becomes a regression
  proof within 30 days (SLA, published).
- **Proof reuse at scale:** library-level proof automation (domain tactics,
  `aesop` rule sets per spec module) so new proofs cost O(insight) rather
  than O(boilerplate); publish the tactic library for the Lean community.

### Language & toolchain
- **Incremental everything:** sub-second rebuilds via verified
  incrementality (name-resolution fixed-point proofs already hint at this);
  IDE feedback at keystroke latency on million-line codebases.
- **Verified optimizing backend:** at least the inliner, constant folding,
  and dead-code elimination carry preservation proofs; optimization levels
  are proof-producing (`-O2` ships strictly more certificate, not less).
- **Cross-compilation matrix:** tier-1 targets (x86-64, AArch64, RISC-V,
  WASM) with per-target conformance in the differential matrix.

### Ecosystem & adoption
- **Regulatory recognition:** the certificate artifact accepted as evidence
  in at least one certification regime (e.g., DO-178C-adjacent,
  IEC 62304, Common Criteria protection profile) — pursued jointly with
  the Era-3 deployment partner.
- **100 production users:** counted by registry activity + survey, with a
  public logo wall and annual user conference (MorphConf? — names TBD).
- **University pipeline:** ≥10 universities teaching with Morph in PL or
  verification courses; funded PhD fellowships for core-proofs work.

**Exit criteria:** hardware-boundary proof for one ISA; proof-carrying
packages enforced; 100 production users; regulatory acceptance in one
regime; red-team SLA met for 4 consecutive quarters.

---

## Era 5 — Ubiquity & Stewardship (Years 8–10: → 2036-10)

**Theme:** finish the north star and hand it to the world.

### Verification depth
- **The whole stack, one theorem:** a single top-level statement —
  *well-typed Morph programs compiled with certified toolchain T execute
  on hardware H with the semantics of the standard* — with all
  assumptions explicit, versioned, and minimal. Publish the assumption
  ledger (trusted base: Lean kernel, ISA model, hardware) as a living
  document; every release shrinks it or says why it can't.
- **Post-quantum & crypto agility:** the standard library's crypto and
  the package registry's signing migrate with proofs of the migration.
- **Long-term proof maintenance:** proofs must survive Lean toolchain
  upgrades; invest in proof porting automation and keep a 3-version
  compatibility window, tested in CI.

### Language & toolchain
- **Morph 3.0 (edition system):** breaking changes only via opt-in
  editions with machine-checked migration tooling (`morph migrate`
  proves behavior preservation for the auto-migrated 95%).
- **Self-hosting:** the production compiler is written in Morph and
  bootstraps from the Lean-verified core — the ultimate dogfood, and it
  collapses the trusted toolchain to the certificate chain.
- **Ubiquitous targets:** microcontrollers and browsers as tier-1;
  `morph build --target` covers the full span from firmware to cloud.

### Ecosystem & adoption
- **The standard is boring (in the best way):** ISO-style standardization
  process or equivalent; conformance suite executable by any third party;
  at least three independent implementations passing it.
- **A million programmers:** measured via toolchain downloads + registry
  accounts; the tutorial path from Era 2 is now a full interactive
  curriculum.
- **Succession:** governance, trademarks, and infrastructure are held by
  the foundation with elected leadership; the original team is no longer
  a single point of failure. This is a feature, and it is planned from
  Era 3, not improvised in Era 5.

**Exit criteria (the north-star checklist):** end-to-end certificate from
syntax to silicon for tier-1 targets; ratified international standard with
≥3 conforming implementations; self-hosted toolchain; foundation-led
governance; the assumption ledger fits on one page.

---

## Cross-Era Scoreboard

Tracked quarterly from Era 1 onward; published in `.reports/` next to the
existing spec-status report.

| Metric | Now | Era 1 | Era 2 | Era 3 | Era 4 | Era 5 |
|---|---|---|---|---|---|---|
| `sorry` / warnings | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| Theorems/lemmas | 1,160 | ≥1,500 | ≥3,000 | ≥5,000 | ≥8,000 | ≥12,000 |
| CI per push | Blocked | Green | Green | Green + differential matrix | Green + red-team SLA | Green, 3-version compat |
| `lake build` (core, laptop) | — | <60 min | <45 min | <30 min | <30 min | <30 min |
| Conformance suite passing | — | Draft | v1.0 | v2.0 (2 impls) | +ISA model | ≥3 impls, standard |
| Production users | 0 | 0 | ≥3 pilots | ≥1 safety-critical | ≥100 | Ubiquitous |
| Toolchain UX | CLI | CLI+fmt+doc | LSP v1, `build`/`test` | Debugger, packages v2 | Incremental, `-O` proofs | Self-hosted |
| Governance | Team | Team + auditors | RFC process | Foundation | Elected leadership | Independent |

Rules: metrics never regress without a published explanation; any era's
exit criteria may delay — but never dilute — the next era.

---

## Risks & Hedges

| Risk | Likelihood | Impact | Hedge |
|---|---|---|---|
| Lean/mathlib churn breaks proofs | High | High | Pin toolchains per era; fund upstream; 3-version CI window from Era 3 |
| Proof effort grows superlinearly | High | High | Tactic automation library; cut language scope before proof scope, always |
| Backend/ISA modeling stalls Era 2–3 | Medium | High | Two-backend strategy (LLVM + a simple verified toy backend that always works) |
| Nobody adopts despite quality | Medium | Fatal | Pilots from Era 1, not Era 3; DX resourced equally with proofs (balanced pillars) |
| Soundness escape in production | Medium | High | Red-team SLA; CVE-grade response policy; certificate makes blast radius auditable |
| Team/funding discontinuity | Medium | High | Foundation by Era 3; docs and ADRs make the project legible to successors |
| Regulatory paths move slowly | High | Medium | Start the conversation in Era 2 with pilot partners; never gate releases on regulators |

---

## Operating Cadence

- **Research loops continue** (`docs/RESEARCH-LOOPS-*.md`): the heartbeat
  of execution. Each loop states its hypothesis, ships, and reconciles
  `ROADMAP.md`/`PATH_FORWARD.md` numbers — as loops 60–82 already do.
- **Quarterly horizon review:** score the board above; promote or demote
  exactly one risk; confirm or revise the current era's exit criteria.
- **Annual vision review:** re-read this file; amend only with an ADR
  (the vision changes by decision, never by drift).
- **This file's promise:** it describes outcomes and exit criteria, not
  tasks. Tasks live in `PATH_FORWARD.md`. If this file ever contains a
  two-week task, it has failed.

---

*Written 2026-10-30. Next review: 2027-01-30 (quarterly), 2027-10-30 (annual).*
