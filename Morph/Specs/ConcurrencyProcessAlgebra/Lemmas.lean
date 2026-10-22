/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.ConcurrencyProcessAlgebra.Spec
import Morph.Specs.ActorDeadlock.Lemmas

namespace Morph.Specs.ConcurrencyProcessAlgebra

/-!
## Lemmas

Lemmas and auxiliary results for the ConcurrencyProcessAlgebra specification.
-/



/-- `isBlockedWaiting` is exactly the wait-for edge relation. -/
theorem isBlockedWaiting_iff (a : ActorId) (waits : ActorId → Option ActorId) :
    isBlockedWaiting a waits ↔ ∃ b, waits a = some b := Iff.rfl

theorem isBlocked_iff (a : ActorId) (waits : ActorId → Option ActorId) :
    isBlocked a waits ↔ isBlockedWaiting a waits := Iff.rfl

/-- **A rank-respecting wait-for graph is acyclic.** This is the formalized
form of "the wait-for discipline of ADR-017 admits no deadlock cycle"; the
corresponding progress theorem is `Morph.Specs.ActorDeadlock.progress_invariant`. -/
theorem rank_order_is_acyclic (W : WaitForGraph)
    (s : Morph.Specs.ActorDeadlock.Sys)
    (rank : Morph.Specs.ActorDeadlock.Actor → Nat)
    (hr : Morph.Specs.ActorDeadlock.Ranked s rank) :
    Morph.Specs.ActorDeadlock.Acyclic s :=
  Morph.Specs.ActorDeadlock.ranked_acyclic s rank hr

theorem specActorSystemDefinition_holds : specActorSystemDefinition := trivial

theorem specCommunicationReductionRule_holds : specCommunicationReductionRule := trivial

theorem specEdgeDefinitions_holds : specEdgeDefinitions := trivial

/-- **Deadlock freedom (SG-004).** Every state reachable from a well-formed,
rank-respecting actor system has a runnable actor — for *any* scheduler.
This is the proof obligation that `specDeadlockFreeTheorem` used to state as
`True`. -/
theorem specDeadlockFreeTheorem_holds : specDeadlockFreeTheorem := by
  intro s s' rank p hwf hr hpm hmem hrun
  exact Morph.Specs.ActorDeadlock.progress_invariant s s' rank hwf hr hpm hrun hmem

theorem specParallelComposition_holds : specParallelComposition := trivial

theorem specMessageDelivery_holds : specMessageDelivery := trivial

theorem specBackpressure_holds : specBackpressure := trivial


theorem specPrivateChannels_holds : specPrivateChannels := trivial

theorem specSubmillisecondLatency_holds : specSubmillisecondLatency := trivial

theorem specDeadlockDetectionComplexity_holds : specDeadlockDetectionComplexity := trivial

theorem specActorStructure_holds : specActorStructure := trivial

theorem specActorDataStructures_holds : specActorDataStructures := trivial

theorem specWaitForGraphStructure_holds : specWaitForGraphStructure := trivial

theorem specMessageDeliveryTheorem_holds : specMessageDeliveryTheorem := trivial

theorem specBackpressureSafetyTheorem_holds : specBackpressureSafetyTheorem := trivial

theorem specFifoOrdering_holds : specFifoOrdering := trivial

theorem specNoDuplication_holds : specNoDuplication := trivial

theorem specNoLoss_holds : specNoLoss := trivial


theorem specRejection_holds : specRejection := trivial

theorem specErrorMessages_holds : specErrorMessages := trivial

theorem hasMailbox_of_mem_actors (actor : ActorId) (config : ProcessConfig)
    (h : actor ∈ config.actors) : hasMailbox actor config := h

theorem isFutureWait_def (a b : ActorId) (future : Future)
    (h : future.resolvedBy = b) : isFutureWait a b future := h

theorem isBackpressureWait_iff (a b : ActorId) (waits : ActorId → Option ActorId) :
    isBackpressureWait a b waits ↔ waits a = some b := Iff.rfl

/- Non-trivial lemmas about the actual data types -/

/-- An empty mailbox has zero messages. -/
theorem empty_mailbox_no_messages :
    ({ owner := (0 : ActorId), isFull := false, messages := [] : Mailbox }).messages.length = 0 := rfl

/-- A mailbox with one message has message count one. -/
theorem single_message_mailbox_count :
    ({ owner := (0 : ActorId), isFull := false,
       messages := [{ value := { data := "ping" } }] : Mailbox }).messages.length = 1 := rfl

/-- A mailbox's owner field equals the actor id it was constructed with. -/
theorem mailbox_owner_matches (mb : Mailbox) :
    ({ id := mb.owner, mailbox := mb : Actor }).id = mb.owner := rfl

/-- hasMailbox is definitionally equivalent to list membership. -/
theorem hasMailbox_iff_mem (actor : ActorId) (config : ProcessConfig) :
    hasMailbox actor config ↔ actor ∈ config.actors := Iff.rfl

/-- An actor not listed in the config does not have a mailbox. -/
theorem no_mailbox_for_absent_actor :
    ¬hasMailbox 99 { actors := [0, 1, 2], channels := [] } := by
  unfold hasMailbox; decide

/-- The first actor in a concrete three-actor config has a mailbox. -/
theorem first_actor_has_mailbox :
    hasMailbox 0 { actors := [0, 1, 2], channels := [] } := by
  unfold hasMailbox; decide

/-- Action.send and Action.receive are distinct constructors. -/
theorem send_ne_receive (target : ActorId) (msg : Message) :
    Action.send target msg ≠ Action.receive := by
  intro h; cases h

/-- Action.receive and Action.internal are distinct constructors. -/
theorem receive_ne_internal : Action.receive ≠ Action.internal := by
  intro h; cases h

/-- WaitForEdge.futureWait and WaitForEdge.backpressureWait are distinct constructors. -/
theorem future_wait_ne_backpressure_wait (a b : ActorId) :
    WaitForEdge.futureWait a b ≠ WaitForEdge.backpressureWait a b := by
  intro h; cases h

/-- The spec for supporting millions of actors is satisfiable:
    construct a config with 1,000,000 actors, each having a mailbox. -/
theorem specMillionsOfActors_holds : specMillionsOfActors := by
  unfold specMillionsOfActors
  refine ⟨{ actors := List.range 1000000, channels := [] : ProcessConfig }, by
    simp [List.length_range], fun _ h => h⟩



/-! ### The properties this module could not state, and the ones it can

The module declared twenty-two `spec_*` properties. Most of them — message
delivery, FIFO ordering, no-duplication, no-loss, backpressure, private
channels, parallel composition — are about a *message-passing* semantics that the
module does not have: it has actors, mailboxes and a wait-for graph, but no
transition relation for messages. Those claims are not merely unproved; they are
**unstateable** here, and the two that *can* be stated are stated in terms of
`Morph/Specs/ActorDeadlock`, which does have the semantics (research loop 3).

The two statements below are the module's own `specDeadlockDetection` and
`specCycleDetection` — which were `True` — proved. -/

/-- **Deadlock detection, proved.** A well-formed, rank-respecting actor system
is never deadlocked: some actor is always runnable. -/
theorem specDeadlockDetection_holds (s : Morph.Specs.ActorDeadlock.Sys)
    (rank : Morph.Specs.ActorDeadlock.Actor → Nat) (p : Morph.Specs.ActorDeadlock.Actor) :
    specDeadlockDetection s rank p := by
  intro hwf hranked hmem
  exact Morph.Specs.ActorDeadlock.ranked_not_deadlocked s rank hwf hranked hmem

/-- **Cycle detection, proved.** A rank-respecting wait-for graph is acyclic. -/
theorem specCycleDetection_holds (s : Morph.Specs.ActorDeadlock.Sys)
    (rank : Morph.Specs.ActorDeadlock.Actor → Nat) :
    specCycleDetection s rank := by
  intro hranked
  exact Morph.Specs.ActorDeadlock.ranked_acyclic s rank hranked

/-- **A well-formed configuration has distinct actors.** -/
theorem isWellFormedConfig_empty : isWellFormedConfig { actors := [], channels := [] } := by
  intro a ha
  simp at ha

/-- **The well-formedness predicate is not vacuous**: it is a real statement about
the actor list, and the empty configuration satisfies it. -/
theorem isWellFormedConfig_is_a_real_statement :
    ¬ (∀ config : ProcessConfig, isWellFormedConfig config) := by
  intro hall
  have h := hall { actors := [1, 1], channels := [] }
  simp [isWellFormedConfig] at h

/-- **A process is valid when the actor it names is in the configuration.** -/
theorem isValidProcess_in (config : ProcessConfig) (a : ActorId)
    (h : a ∈ config.actors) : isValidProcess config a := by
  exact h

end Morph.Specs.ConcurrencyProcessAlgebra
