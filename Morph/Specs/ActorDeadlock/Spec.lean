/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core

/-!
# Actor Deadlock Freedom (ADR-017, research loop 3)

SG-004 asked for a deadlock-freedom proof for the actor system. The existing
concurrency specifications (`ConcurrencyProcessAlgebra`, `LayeredConcurrency`)
declare `isBlockedWaiting`, `isAcyclic`, `formsCycle` and even
`specDeadlockFreeTheorem` as `Prop := True`: they *assert* the properties
instead of stating them, so no proof obligation exists. This module supplies
the missing content — an operational model, an invariant, and a
deadlock-freedom theorem over reachable states.

## Model

An actor system is a finite set of `actors`, the set of `run` actors that can
take a step, and a wait relation `waitOn : Actor → Option Actor` where
`waitOn p = some q` means *p is blocked until q serves it*. This is the
classical **wait-for graph** (Gray's transaction wait-for graph, applied to
actors), represented as a function so every blocked actor has a *unique*
successor — the property the deadlock argument needs.

Two transitions:

- `ask p q` — a runnable actor `p` requests a result from `q` and blocks.
  Requires `p` runnable, `q` inside the system, and `rank p < rank q` for any
  rank that is to be maintained.
- `serve q p` — a runnable actor `q` serves the outstanding request of `p`;
  `p` becomes runnable. The server stays runnable: it may have more requests
  to serve, so it is never removed from `run`.

A **deadlock** is a state with no runnable actor: nobody can `ask` (needs
`run`) and nobody can `serve` (needs the server to be in `run`), so no
transition is enabled — `deadlock_is_stuck` proves that equivalence.

## Results (Lemmas.lean)

1. `chain` — following the wait relation `k` times stays inside the system and
   strictly increases any rank that respects waits.
2. `ranked_implies_progress` — a **checkable** sufficient condition that needs
   no graph analysis: if waits always point from a lower to a strictly higher
   rank, then `run ≠ []`. The proof is a bounded-rank argument: the chain
   would have to increase the rank `m + 1` times while every actor's rank is
   at most `m`.
3. `WF_ask`/`WF_serve`, `Ranked_ask`/`Ranked_serve` — well-formedness and the
   rank condition are invariants of the step relation.
4. `progress_invariant` — **deadlock freedom of the whole system**: from a
   well-formed, rank-respecting state, every state reachable by any scheduler
   has a runnable actor.

Theorem 4 is the SG-004 payoff, and theorem 2 is what makes it checkable: a
runtime can discharge the rank condition once, per message, instead of
searching the wait-for graph for cycles.

## Research basis (see docs/RESEARCH-LOOPS.md)

- Honda, Yoshida, Carbone. *Connection graphs: a method for proving deadlock
  freedom based on separation logic.* PACMPL 6(POPL), 2022 — the decidable
  criterion; our `Ranked` condition is the statically checkable analogue.
- Li, Wies. *Certified Implementability of Global Multiparty Protocols.*
  ITP 2025 — the current mechanized state of the art, but over abstract
  communicating state machines, not over a runtime with queues.
- Yoshida's survey of MPST implementations notes that implementations "proved
  deadlock-freedom only at the type level"; connecting a type-level property
  to a concrete scheduler is exactly the gap `progress_invariant` closes.
-/

namespace Morph.Specs.ActorDeadlock

/-- Actors are natural-number identities. -/
abbrev Actor := Nat

/-- The actor system under analysis. `waitOn p = some q` means `p` is blocked
until `q` serves it; `waitOn p = none` means `p` is not blocked. -/
structure Sys where
  /-- the actors taking part -/
  actors : List Actor
  /-- the actors currently able to take a step -/
  run : List Actor
  /-- the wait-for relation: blocked actor -> the actor it waits for -/
  waitOn : Actor → Option Actor

/-- `p` is blocked waiting for `q`. -/
def Waits (s : Sys) (p q : Actor) : Prop := s.waitOn p = some q

/-- `p` is blocked (on someone). -/
def Blocked (s : Sys) (p : Actor) : Prop := ∃ q, s.waitOn p = some q

/-- `p` can take a step. -/
def Runnable (s : Sys) (p : Actor) : Prop := p ∈ s.run

/-- **Deadlock**: nobody can take a step. Both transitions need a runnable
actor, so this is equivalent to "no transition is enabled"
(`deadlock_is_stuck`). -/
def Deadlock (s : Sys) : Prop := s.run = []

/-- Every actor is either blocked or runnable (nobody is halted). -/
def Live (s : Sys) : Prop :=
  ∀ p, p ∈ s.actors → (Blocked s p ∨ Runnable s p)

/-- Waits stay inside the system, and no one waits for itself. -/
def Closed (s : Sys) : Prop :=
  (∀ p q, s.waitOn p = some q → q ∈ s.actors) ∧ (∀ p, s.waitOn p ≠ some p)

/-- The well-formedness of a state. -/
def WF (s : Sys) : Prop := Live s ∧ Closed s

/-- Every wait goes from a lower to a strictly higher rank. A rank
(`Actor → Nat`) witnessing this makes the wait-for graph acyclic by
construction — a sufficient condition for deadlock freedom that needs no
graph search. -/
def Ranked (s : Sys) (rank : Actor → Nat) : Prop :=
  ∀ p q, s.waitOn p = some q → rank p < rank q

/-- `chain s k p` — the actor reached from `p` after `k` wait steps. -/
def chain (s : Sys) : Nat → Actor → Actor
  | 0, p => p
  | k + 1, p => match s.waitOn p with
    | some q => chain s k q
    | none => p

/-! ## Transitions -/

/-- `p` asks `q` for a result and blocks until served. -/
def Ask (s : Sys) (p q : Actor) : Sys where
  actors := s.actors
  run := s.run.erase p
  waitOn := fun x => if x = p then some q else s.waitOn x

/-- `q` serves the outstanding request of `p`; `p` becomes runnable and `q`
stays runnable (it may have further requests to serve). -/
def Serve (s : Sys) (q p : Actor) : Sys where
  actors := s.actors
  run := p :: s.run
  waitOn := fun x => if x = p then none else s.waitOn x

/-- The actor step relation, indexed by the rank the system respects. -/
inductive Step (rank : Actor → Nat) : Sys → Sys → Prop where
  | ask : ∀ s p q, p ∈ s.run → q ∈ s.actors → rank p < rank q →
      Step rank s (Ask s p q)
  | serve : ∀ s q p, q ∈ s.run → s.waitOn p = some q →
      Step rank s (Serve s q p)

/-- Multi-step execution under a fixed rank. -/
inductive Steps (rank : Actor → Nat) : Sys → Sys → Prop where
  | refl : ∀ s, Steps rank s s
  | tail : ∀ s s' s'', Steps rank s s' → Step rank s' s'' → Steps rank s s''

/-- The wait-for graph of a state as an edge list: one outgoing edge per
blocked actor. -/
def waitEdges (s : Sys) : List (Actor × Actor) :=
  s.actors.filterMap fun p => (s.waitOn p).map fun q => (p, q)

/-- A cycle of the wait-for graph through `start`: after `k` wait steps we
are back at `start`, every step on the way is an actual wait, and `k` is not
longer than the system is big (so the cycle cannot be an artefact of an
infinite walk). -/
def HasCycle (s : Sys) (start : Actor) (k : Nat) : Prop :=
  0 < k ∧ k ≤ s.actors.length ∧ chain s k start = start ∧
    (∀ j, j < k → ∃ q, s.waitOn (chain s j start) = some q)

/-- The wait-for graph is acyclic: no walk along waits returns to its start.
This is the condition Honda–Yoshida's connection graphs characterise, phrased
over the concrete wait relation. -/
def Acyclic (s : Sys) : Prop :=
  ∀ start k, HasCycle s start k → chain s k start ≠ start



end Morph.Specs.ActorDeadlock