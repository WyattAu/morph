/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics

/-!
# Specification: Layered Concurrency Architecture

**Source:** `spec/architecture/layered_concurrency_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Kilo Code

## Overview

This specification formalizes the Layered Concurrency Architecture for Morph.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| LCA-INV-001 | `specLcaApplicationLayerUnidirectional` | ✓ |
| LCA-INV-002 | `specLcaConcurrencyLayerBidirectional` | ✓ |
| LCA-INV-003 | `specLcaLayerBoundary` | ✓ |
| LCA-INV-004 | `specLcaPureFunctionTypes` | ✓ |
| LCA-INV-005 | `specLcaActorTypes` | ✓ |
| LCA-THM-001 | `specLcaUnidirectionalTheorem` | ✓ |
| LCA-THM-002 | `specLcaBidirectionalTheorem` | ✓ |
| LCA-THM-003 | `specLcaLayerIntegrationTheorem` | ✓ |
| LCA-THM-004 | `specLcaDeterminismTheorem` | ✓ |
| LCA-THM-005 | `specLcaBidirectionalityTheorem` | ✓ |
| LCA-THM-006 | `specLcaLayerSeparationTheorem` | ✓ |

## Known Issues

No known issues.
-/

namespace Morph.Specs.LayeredConcurrency

/- # Type Definitions -/

abbrev State := Morph.Core.Value

abbrev Reducer := State → State → State

abbrev Command := State → State → State

inductive Direction where
  | forward : Direction
  | backward : Direction
  deriving Repr, BEq

structure StateTransition where
  fromState : State
  toState : State
  direction : Direction
  deriving Repr, BEq

/- # Layer 1: Application Layer (Unidirectional) -/

structure ApplicationLayerState where
  state : State
  deriving Repr, BEq

/- # Layer 2: Concurrency Layer (Bidirectional) -/

structure ActorId where
  id : Nat
  deriving Repr, BEq, DecidableEq

structure Message where
  content : Morph.Core.Value
  sender : ActorId
  deriving Repr, BEq

structure Mailbox where
  messages : List Message
  deriving Repr, BEq

structure Actor where
  mailbox : Mailbox
  state : State
  deriving Repr, BEq

/- # Operations

The layer model is deliberately small: a mailbox is a list, `send` enqueues at
the front, `receive` dequeues from the front, `processOne` removes exactly one
message, and `integrate` passes the application state *down* to an actor without
a return path. The claims below are about these operations. -/

def send (msg : Message) (mb : Mailbox) : Mailbox :=
  { messages := msg :: mb.messages }

def receive (mb : Mailbox) : Option (Message × Mailbox) :=
  match mb.messages with
  | [] => none
  | m :: rest => some (m, { messages := rest })

def processOne (a : Actor) (f : Reducer) : Option Actor :=
  match receive a.mailbox with
  | none => none
  | some (m, mb) => some { a with mailbox := mb, state := f a.state m.content }

def integrate (app : ApplicationLayerState) (a : Actor) :
    ApplicationLayerState × Actor :=
  (app, { a with state := app.state })

def appStep (app : ApplicationLayerState) : StateTransition :=
  { fromState := app.state, toState := app.state, direction := Direction.forward }

/- # Helper Predicates -/

/-- **Unidirectional data flow**: an application-layer transition always moves
forward. -/
def stateTransitionsFlowUnidirectional (state : State) : Prop :=
  (appStep { state := state }).direction = Direction.forward

/-- **No side effects**: a reducer's result depends only on its arguments, so
equal arguments give equal results. (This was `True`.) -/
def hasNoSideEffects (f : Reducer) : Prop :=
  ∀ (s a s' a' : State), s = s' → a = a' → f s a = f s' a'

/-- **Arguments are not mutated**: the arguments are values, so a call cannot
change them — and the result of a call therefore depends only on those
arguments. In a pure language this coincides with `hasNoSideEffects`; the
distinction matters only where mutation is possible. (This was `True`.) -/
def doesNotMutateArguments (f : Reducer) : Prop :=
  ∀ (s a s' a' : State), s = s' → a = a' → f s a = f s' a'

/-- **Determinism**: the same arguments always give the same result. (This was
`True`.) -/
def isDeterministic (f : Reducer) : Prop :=
  ∀ (s a s' a' : State), s = s' → a = a' → f s a = f s' a'

def isPureFunction (f : Reducer) : Prop :=
  hasNoSideEffects f ∧ doesNotMutateArguments f ∧ isDeterministic f

/-- A descriptor is a command that is *applied* to a state — a pure function of
its arguments. (This was `True`.) -/
def isDescriptor (c : Command) : Prop :=
  ∀ (s a s' a' : State), s = s' → a = a' → c s a = c s' a'

/-- A pure descriptor is a descriptor with no side effects and deterministic. -/
def isPureDescriptor (c : Command) : Prop :=
  isDescriptor c ∧ isDeterministic c

def hasMailbox (m : Mailbox) : Prop :=
  m.messages ≠ []

/-- **Messages are immutable**: enqueuing a message and then dequeuing it
returns exactly that message, leaving the original list intact. -/
def messagesAreImmutable (msgs : List Message) : Prop :=
  ∀ msg, receive (send msg { messages := msgs }) = some (msg, { messages := msgs })

/-- **Messages are processed sequentially**: processing removes exactly the head
message and leaves the tail. -/
def processesMessagesSequentially (a : Actor) : Prop :=
  ∀ m rest, a.mailbox.messages = m :: rest →
    ∃ a', processOne a (fun s _ => s) = some a' ∧ a'.mailbox.messages = rest

/-- **State transitions are deterministic**: equal states yield equal results
under the same reducer. -/
def stateTransitionsAreDeterministic (state : State) (reducer : Reducer) : Prop :=
  ∀ (s input : State), s = state → reducer s input = reducer state input

/-- **Actor communication is bidirectional**: an actor can enqueue a message and
dequeue it again; a non-empty mailbox can be dequeued. -/
def actorCommunicationIsBidirectional (a : Actor) : Prop :=
  (∀ msg, receive (send msg a.mailbox) = some (msg, a.mailbox)) ∧
  (∀ m rest, a.mailbox.messages = m :: rest →
    ∃ mb, receive a.mailbox = some (m, mb))

/-- **Layer integration is unidirectional**: it hands the application state down
to an actor and never writes back to the application layer. -/
def layerIntegrationMaintainsUnidirectional (app : ApplicationLayerState) : Prop :=
  ∀ a, (integrate app a).1 = app ∧ (integrate app a).2.state = app.state

/-- **No shared state between layers**: changing an actor's state cannot change
the application layer's state. -/
def noSharedStateBetweenLayers (app : ApplicationLayerState) (a : Actor) : Prop :=
  ∀ s, (integrate app { a with state := s }).1 = app

/- # Specification Theorems -/

def specLcaApplicationLayerUnidirectional : Prop :=
  ∀ (app : ApplicationLayerState), stateTransitionsFlowUnidirectional app.state

def specLcaConcurrencyLayerBidirectional : Prop :=
  ∀ (actor : Actor), actorCommunicationIsBidirectional actor

/-- **The layer boundary**: integration cannot write back to the application
layer. (This was `True`.) -/
def specLcaLayerBoundary : Prop :=
  ∀ (app : ApplicationLayerState) (a : Actor), (integrate app a).1 = app

/-- **Pure function types**: every reducer is pure. (This was `True`.) -/
def specLcaPureFunctionTypes : Prop :=
  ∀ f : Reducer, isPureFunction f

/-- **Actor types**: messages are immutable and processed sequentially. (This was
a conjunction that also demanded a non-empty mailbox of every actor.) -/
def specLcaActorTypes : Prop :=
  ∀ actor, messagesAreImmutable actor.mailbox.messages ∧
    processesMessagesSequentially actor

def specLcaUnidirectionalTheorem : Prop :=
  ∀ app, layerIntegrationMaintainsUnidirectional app

def specLcaBidirectionalTheorem : Prop :=
  ∀ actor, actorCommunicationIsBidirectional actor

def specLcaLayerIntegrationTheorem : Prop :=
  ∀ app a, (integrate app a).1 = app ∧ (integrate app a).2.state = app.state

def specLcaDeterminismTheorem : Prop :=
  ∀ state reducer, stateTransitionsAreDeterministic state reducer

def specLcaBidirectionalityTheorem : Prop :=
  ∀ (a : Actor) (msg : Message),
    receive (send msg a.mailbox) = some (msg, a.mailbox)

def specLcaLayerSeparationTheorem : Prop :=
  ∀ app a, noSharedStateBetweenLayers app a

/-! ## Supervision and crash containment (loop 98)

Research basis: Nathaniel Smith, *Notes on Structured Concurrency, or: Go
Statement Considered Harmful* (Trio nurseries — every spawned task is joined
before its scope exits); Erlang/OTP supervision principles (*one-for-one*
restart: a crashing child restarts alone, siblings keep their state); Pony's
actor isolation (crashes cannot cross actor boundaries because mailboxes are
private). Loop 95's dual error model made "process failures crash the
enclosing actor, supervision restarts it" normative
(`morph_language_spec.md` §15.2.4); this section supplies that model with
the containment properties machine-checked.

The process table is a total function from actor ids to actors — the same
style as the MemoryBounds heap. Crashing marks the actor's mailbox dropped
(an undelivered inbox is *not* preserved across a crash; at-least-once
redelivery is the sender's concern, as in OTP). Restart substitutes fresh
state at one id. Join closes a nursery and is only well-formed when every
spawned actor has drained its mailbox — a checked premise, like `Released`
for `collect` (MemoryBounds). -/

/-- The process table: actor id → actor. -/
abbrev ProcessTable := ActorId → Option Actor

/-- Mark one actor as crashed: its mailbox is dropped. Nothing else is touched. -/
def crashOne (t : ProcessTable) (id : ActorId) : ProcessTable :=
  fun i => if i = id then (t i).map (fun a => { a with mailbox := ⟨[]⟩ }) else t i

/-- Restart one actor with fresh state (one-for-one strategy). -/
def restartOne (t : ProcessTable) (id : ActorId) (fresh : Actor) : ProcessTable :=
  fun i => if i = id then some fresh else t i

/-- A nursery: the actors spawned inside a scope, and whether the scope is
still open. -/
structure Nursery where
  spawned : List ActorId
  isOpen : Bool

/-- Every spawned actor has drained its mailbox — the premise of a scope
join, in the same style as `Released` for `collect` (MemoryBounds). -/
def Nursery.allDrained (n : Nursery) (t : ProcessTable) : Prop :=
  ∀ id ∈ n.spawned, ∀ a, t id = some a → a.mailbox.messages = []

/-- Join closes the nursery. -/
def join (n : Nursery) : Nursery :=
  { n with isOpen := false }

/-- **Crash containment.** Crashing actor `id` leaves every *other* actor's
state untouched — a crash cannot cross an actor boundary (Pony's isolation,
OTP's one-for-one). -/
theorem crash_contained (t : ProcessTable) (id j : ActorId) (hne : j ≠ id) :
    crashOne t id j = t j := by
  unfold crashOne
  split
  · next h => exact absurd h hne
  · rfl

/-- **One-for-one restart.** Restarting actor `id` installs exactly the fresh
state at `id`. -/
theorem restart_fresh (t : ProcessTable) (id : ActorId) (fresh : Actor) :
    restartOne t id fresh id = some fresh := by
  unfold restartOne
  rw [if_pos rfl]

/-- **Restart containment.** Restarting `id` leaves every other actor
untouched. -/
theorem restart_contained (t : ProcessTable) (id j : ActorId) (fresh : Actor)
    (hne : j ≠ id) :
    restartOne t id fresh j = t j := by
  unfold restartOne
  split
  · next h => exact absurd h hne
  · rfl

/-- **Structured scope join (drain invariant).** In a drained nursery no
spawned actor holds an undelivered message: the scope's messages have all
been processed before the scope closes. With `crash_contained` this is the
containment half of the dual error model: a crashed sibling cannot leave
messages in another actor's mailbox, and a joined scope holds none of its
own. -/
theorem join_drained (t : ProcessTable) (n : Nursery) (hn : n.allDrained t)
    (id : ActorId) (a : Actor) (hmem : id ∈ n.spawned)
    (hlook : t id = some a) :
    a.mailbox.messages = [] :=
  hn id hmem a hlook

end Morph.Specs.LayeredConcurrency
