# ADR-033: D-8/D-9 Provisional Defaults (Actor Step Interface; Memory Authority)

## Status

**Provisional** (loop 134 record, 2026-11-26). This is not a new decision:
`docs/STAGED-D8-D9-OPTIONS.md` (the S4 deliverable) set dated provisional
defaults under operating rule 2 — *"past [the end-of-S4] deadline, the
provisional defaults above proceed as provisional ADRs"*. The deadline has
passed (S4 ≈ wks 7–8; the tree is now past S9, wks 17–18) and no maintainer
call has landed, so this ADR records the defaults in the form the memo
specified. **Provisional means revisable by a maintainer call at any time**;
a wrong default costs a refactor, per the memo's own risk statement. Records
no gates; touches no audited surface (the audit packet is pinned at
`f24ee31`).

## Decision

### D-8 (actor step interface): Reading A — state-threading step

`stepActor (system) (turn) (_heap) (_stack) : ActorSystem × Heap × Stack`
keeps its state-threading signature (`Morph/Runtime.lean`); the body grows
into real evaluation with a **stuck outcome added to the return type** at
D3-drafting time (S16). Reading B (state-free scheduling step) is rejected
for the memo's stated reasons: the safety content would move into the
evaluator, which has no fragment predicate and no S16 drafting slot, and
`ActorDeadlock`'s proved stateful step relation (`progress_invariant`,
`ranked_not_deadlocked`) would need a translation layer to meet a
state-free scheduler.

Provisional-ADR consequence for D3: the preservation statement quantifies
over the threaded state, against the `ActorStmts` fragment predicate
(S16 drafting input, BranchStmts precedent).

### D-9 (memory authority): supersede — `Memory.lean` authoritative

`Memory.lean` is the authoritative executable memory model;
`Specs/MemoryModel` (34 theorems over a disconnected model) is
requirements-only. A `RelBorrowHeap`-style bridge is rejected for the
memo's stated reason: the 34 theorems touch neither executable model, so
the bridge would relate models that disagree by design. Provisional-ADR
consequence: D1's `HeapSafe` (S5, already landed) and D2's
`wfBorrow_heapSafe` agreement (S8, closed) stand over `Memory.lean` with
no bridge obligation.

## What this ADR does not decide

(Deferred by the memo to S16 drafting or maintainer calls; recorded here so
the deferral is explicit.)

- The **stuck-outcome shape** in `stepActor`'s return type (fuel + stuck vs
  an explicit outcome triple) — S16.
- The **`ActorStmts` fragment predicate** — S16, per the `BranchStmts`
  precedent (new constructors beside the old ones, never widening).
- The **global invariant** D3 preserves (mailbox boundedness vs crash
  containment) — §7 open question, maintainer call.
- **D5's quantifier level** (HIR evaluator vs MIR executor vs both) — §7 Q4,
  Year-2 work.
- Whether the provisional defaults become **permanent**: a maintainer call
  overrides this ADR trivially; until then the defaults govern D3–D5
  drafting.
