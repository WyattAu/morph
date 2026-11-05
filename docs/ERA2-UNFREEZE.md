# Era-2 unfreeze — loop 133 decision (maintainer directive)

## Verdict

Era-1 cannot close in-round: G-1 (billing), G-3 (external audit), G-7
(tag + announce) are all maintainer/external-only actions. Per maintainer
directive ("if we can't get 1st era done this round we unfreeze era 2"),
**the Year-1 freeze on Era-2 implementation is lifted as of this loop.**

This does not close Era-1 or clear any gate — G-1/G-3/G-7 remain open and
still block the 0.1 release and audit. It only unblocks implementation
work that the freeze had queued.

## What the freeze blocked, now allowed

Per `docs/YEAR2-KICKOFF.md` §3 (the five-item blocked queue):

1. Stage A1: store- and call-aware MIR small-step semantics.
2. Stage A2: `compile_correct` for the first-order fragment.
3. Backend ADR (LLVM vs Cranelift, TCB, verified-lowering vs translation validation).
4. Stage B: single-backend straight-line lowering + flagged `morph build`.
5. Rust pipeline growth (AST→MIR, differential testing advisory).

## Safeguards (unchanged)

- Proof scope is never cut to meet a date (five-year roadmap principle 1).
- Defaults on silence remain D-2 (verified lowering) and D-4 (strict
  explicitly-listed subset) per `docs/STAGEA-PREP-125.md`.
- `compile_correct` stays one-directional (HIR-success-implies-MIR-agreement),
  like `agreeBoth` — failure coincidence is never claimed.
- Strict-subset `morph build` contract from STAGEA-PREP §1 governs what
  Stage B may accept.
- Era-1 gates still tracked in `HARD-GATES.md`; this file tracks the
  unfreeze only, not gate clearance.

## First work under the unfreeze (this loop)

Stage A1 groundwork in `Morph/MIRExecLemmas.lean`: sequential composition
for `execInstrsFull`, pure-instruction agreement between `evalInstr` and
`evalInstrFull`, and the single-block `execBlockFuel` reduction the
straight-line `compile_correct` will build on. No backend, no CLI, no
`morph build` yet.
