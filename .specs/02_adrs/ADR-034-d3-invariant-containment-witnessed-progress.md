# ADR-034: D3 Invariant — Crash Containment and Witnessed Progress

## Status

**Accepted** (2026-11-27, explicit maintainer decision ahead of the
`STAGE-D3-INVARIANT-MEMO.md` deadline of 2026-12-18 — stronger than the
rule-2 silence default). Revisable by a later maintainer call; a switch to
B or C costs the budget arithmetic or the bridge respectively, not a
refactor of what is proved.

## Decision

D3 (actor step safety) claims exactly two things, both already proved
against the real executable step (`Morph.Runtime.stepActor`, Reading A per
ADR-033):

1. **Crash containment.** A stuck step returns the input system verbatim —
   the failed evaluation touches no other actor's state, no mailbox, and
   the id counter (`stepActor_stuck_system_unchanged`,
   `Morph/ActorProgress.lean`).
2. **Witnessed progress.** A stuck step is always witnessed: the scheduled
   actor, its pool position, and its failing evaluation
   (`actors_progress`, same file — unconditional, no well-formedness
   hypotheses, witness-style per the roadmap's executable-counterexample
   demand).

The statement is **stronger than the §4 sketch** (`docs/STAGED-SCOPE.md`):
the sketch's `WFActors` hypothesis proved unnecessary at this strength — a
stuck step is witnessed whether or not the system is well-formed.

## Dispositions

- **B (mailbox boundedness):** queued as a D4-adjacent theorem after the
  `ActorStmts` fragment predicate lands. Its rigorous form requires the
  fragment's send/recv discipline (a design not yet made) — proving it
  now would state a claim whose statement changes when the discipline is
  designed.
- **C (ranked/WF bridge to `ActorDeadlock`):** stays in D4 per the memo.
  Runtime's actor step must be real before a bridge's dynamic half has
  anything to preserve.

## Why A is the most rigorous and robust option

- Both conjuncts are proved against the **real executable step** — the C8
  discipline: prove at the level where progress means something.
- The progress statement needs **no hypotheses** — there is no fragment to
  dispute, no discipline to dispute, no bridge axioms.
- The containment proof is **structural** (the stuck branch returns the
  input verbatim), so it survives the coming evaluation deepening: deeper
  integration makes more things stuck, and the stuck branch still returns
  the input verbatim.
- B and C would each rest on a grounding that does not exist yet (the
  fragment discipline; the bridge relation) — claims outrunning their
  proofs, which the pipeline's one-directional discipline forbids.

## What this ADR does not decide

- The `ActorStmts` fragment predicate (the remaining S16 work).
- The stuck-outcome shape refinements (fuel + stuck vs an outcome triple).
- The mailbox-boundedness theorem's statement (D4, after B's grounding).

## Evidence

- `Morph/ActorProgress.lean`: `actors_progress`,
  `stepActor_stuck_system_unchanged`, and the executable pins (empty pool
  steps, literal-state actors step idempotently, unbound variables stick
  with witnesses, fuel exhaustion sticks with witnesses).
- `Morph/Runtime.lean`: the Reading-A `stepActor` (ADR-033).
