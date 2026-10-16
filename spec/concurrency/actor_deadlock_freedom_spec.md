# Actor Deadlock Freedom Specification

**Spec ID:** CONC-DF-001
**Version:** 1.0.0
**Status:** Formalized (Lean 4)
**Date:** 2026-10-16
**Formal Module:** `Morph/Specs/ActorDeadlock/`, `Morph/Specs/ConcurrencyProcessAlgebra/`
**Closes:** SG-004 (deadlock-freedom proof for the actor system)
**Related Specifications:** [`concurrency_process_algebra_spec.md`](./concurrency_process_algebra_spec.md),
[`layered_concurrency_spec.md`](./layered_concurrency_spec.md),
[`scheduler_randomized_stealing_spec.md`](./scheduler_randomized_stealing_spec.md)

---

## 1. Purpose

SG-004 asked for a deadlock-freedom proof for the actor system. The audit
behind SG-004 found that the concurrency specifications *asserted* the
properties instead of stating them: `isBlockedWaiting`, `isAcyclic`,
`formsCycle` and even `specDeadlockFreeTheorem` were defined as
`Prop := True`, and the corresponding lemmas were proved by `trivial`. A
`WaitForGraph` structure existed but nothing consumed it.

This specification supplies the missing content: an operational model of the
actor system as a wait-for graph, an invariant, and a deadlock-freedom
theorem over reachable states.

---

## 2. Research Basis (research loop 3)

| Source | Result used | Relevance |
|--------|-------------|-----------|
| Honda, Yoshida, Carbone. *Connection graphs: a method for proving deadlock freedom based on separation logic.* PACMPL 6(POPL), 2022 | Deadlock freedom of an asynchronous session is decidable from the *connection graph* of the global type | Provides the notion of "no cycle in the wait-for graph" as the exact criterion |
| Li, Wies. *Certified Implementability of Global Multiparty Protocols.* ITP 2025 | First mechanization of a precise implementability characterization (deadlock freedom + subprotocol fidelity) for asynchronous CSMs | Current state of the art — but over *abstract* communicating state machines, with no runtime/queue |
| Yoshida, *Programming Language Implementations with Multiparty Session Types* (survey) | Implementations "proved deadlock-freedom only at the type level" (△); only some additionally relate it to the projected configuration | The precise gap this specification closes: a theorem about a *runtime* with a scheduler |
| Gray, transaction wait-for graphs; Bernstein et al., distributed deadlock detection | A cycle in the wait-for graph is *exactly* deadlock | The classical result adopted as the modelling choice |

**Conclusion of the survey.** The mechanized state of the art stops at
communicating state machines; no implementation proves deadlock freedom for
its concrete scheduler. Morph's actor runtime does have an explicit scheduler
and mailboxes, so the property is provable — and worth proving, because an
agentic runtime that deadlocks has no observable failure mode other than a
hang.

---

## 3. Model

*CONC-R-001:* An actor system is a finite set `Sys.actors`, a set
`Sys.run` of actors able to take a step, and a wait relation
`Sys.waitOn : Actor → Option Actor` where `waitOn p = some q` means *p is
blocked until q serves it*. The wait relation is a function so that every
blocked actor has a unique successor.

*CONC-R-002:* Two transitions:

| Transition | Precondition | Effect |
|-----------|-------------|--------|
| `ask p q` | `p` runnable, `q ∈ actors`, `rank p < rank q` | `p` blocks waiting for `q` and leaves `run` |
| `serve q p` | `q` runnable, `waitOn p = some q` | `p` becomes runnable, the request is consumed; `q` stays runnable |

*CONC-R-003:* A **deadlock** is a state with `run = []`. Since both
transitions require a runnable actor, this is equivalent to "no transition is
enabled" (`deadlock_is_stuck`).

*CONC-R-004:* `WF s` (well-formed): every actor is blocked or runnable
(`Live`), and waits stay inside the system with no self-waits (`Closed`).

*CONC-R-005:* `Ranked s rank` (`rank : Actor → Nat`): every wait goes from a
strictly lower to a strictly higher rank.

---

## 4. Formal Results

| Theorem | Statement |
|---------|-----------|
| `chain_mem` | Following `k` wait steps stays inside `actors` |
| `chain_rank_ge'` / `chain_rank_lt` | Ranks strictly increase along the chain |
| `ranked_implies_progress` | `WF s → Ranked s rank → run ≠ []` — **deadlock freedom from a rank order**, by a bounded-rank argument (the chain would raise the rank past its own maximum) |
| `ranked_acyclic` | `Ranked s rank → Acyclic s` — the rank order makes the wait-for graph acyclic, the connection-graph criterion in concrete form |
| `WF_ask` / `WF_serve` / `Ranked_ask` / `Ranked_serve` | Well-formedness and the rank condition are invariants of both transitions |
| **`progress_invariant`** | **`WF s → Ranked s rank → ∀ s', Steps rank s s' → s'.run ≠ []`** — no execution, by any scheduler, reaches a deadlock |
| `deadlock_is_stuck` | A deadlocked state has no enabled transition |
| `bothRunning_deadlockFree` | `progress_invariant` instantiated on a concrete two-actor system |

The `True`-stubs in `ConcurrencyProcessAlgebra` are replaced:
`isBlockedWaiting`, `isBlocked`, `isBackpressureWait`, `isAcyclic`,
`formsCycle` now take the wait relation as an argument, and
`specDeadlockFreeTheorem` is a real statement discharged by
`progress_invariant`.

---

## 5. Why the rank order is the right condition

The classical criterion is "the wait-for graph has no cycle". That is a
*global* property, requiring a graph search at run time. `Ranked s rank` is
strictly stronger but **locally checkable**: at each `ask`, one comparison
`rank p < rank q` suffices. A runtime can therefore enforce deadlock freedom
by construction rather than by detection, and the proof above shows the
resulting system cannot deadlock.

The condition is not a restriction on expressible protocols: any protocol
whose wait-for graph is a DAG admits such a rank by topological order. What
it excludes is waiting on an actor that can only make progress by waiting on
you — which is a deadlock by definition.

---

## 6. Scope Limits

1. **Fairness is not claimed.** `progress_invariant` says a runnable actor
   always *exists*; scheduling it is a separate obligation (loop 8).
2. **Message ordering and delivery latency** are outside this model: the
   wait-for relation abstracts over them (a request is satisfied by a serve
   step regardless of queue position).
3. **Partial failure** (an actor crashing while others wait on it) is not
   modelled; ADR-018 territory.

---

## 7. Traceability

| Requirement | Formalized in |
|-------------|---------------|
| SG-004 deadlock freedom | `progress_invariant`, `specDeadlockFreeTheorem_holds` |
| CONC-REQ wait-for graph structure | `waitEdges`, `Acyclic`, `HasCycle` |
| CONC-REQ blocking detection | `Blocked`, `isBlockedWaiting`, `deadlock_is_stuck` |

---

## Change Log

| Version | Date | Change | Author |
|---------|------|--------|--------|
| 1.0.0 | 2026-10-16 | Initial: wait-for-graph model, `WF`/`Ranked` invariants, `progress_invariant`, replacement of the `True` stubs in `ConcurrencyProcessAlgebra` | Morph research loop 3 |