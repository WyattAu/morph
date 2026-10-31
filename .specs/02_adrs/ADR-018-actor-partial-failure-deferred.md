# ADR-018: Actor Partial Failure Is Out of Scope (Deferred)

## Status
**Proposed** (referenced by `spec/concurrency/actor_deadlock_freedom_spec.md`
§6 scope limits; no implementation yet).

## Context

The actor deadlock-freedom model (`spec/concurrency/actor_deadlock_freedom_spec.md`,
`Morph/Specs/ActorDeadlock/`) proves a progress invariant: a runnable actor
always exists. The wait-for relation abstracts over message ordering, delivery
latency, and scheduling. It does **not** model an actor crashing while other
actors wait on it — i.e., *partial failure*.

## Decision

Partial-failure modeling (crash-stop or crash-recovery actors, failure
detectors, supervision trees, and the resulting changes to the progress
invariant) is **deferred**: it is future research, not part of the Era 1
soundness story. Any future model must:

1. State the failure assumption explicitly (crash-stop vs. Byzantine is a
   different theorem, not a parameter tweak).
2. Re-prove or explicitly weaken `progress_invariant` under that assumption —
   the current invariant is *false* if a waited-on actor can crash silently.
3. Add executable counterexamples (an actor that crashes must be rejected or
   supervised by construction, per the project's executable-counterexample
   discipline).

## Consequences

- The current deadlock-freedom proofs remain valid **only** under the
  no-crash assumption; this is now recorded here instead of living as a
  bare cross-reference.
- When partial failure is modeled, this ADR is superseded by the ADR that
  introduces the failure model (expected Era 2, concurrency track).
- No code or proof changes required by this ADR.
