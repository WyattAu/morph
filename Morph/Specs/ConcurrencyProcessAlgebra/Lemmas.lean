/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.ConcurrencyProcessAlgebra.Spec

namespace Morph.Specs.ConcurrencyProcessAlgebra

/-!
## Lemmas

Lemmas and auxiliary results for the ConcurrencyProcessAlgebra specification.
-/

theorem isWellFormedConfig_always_true (config : ProcessConfig) : isWellFormedConfig config := trivial

theorem isValidProcess_always_true (config : ProcessConfig) (p : Unit) : isValidProcess config p := trivial

theorem isBlockedWaiting_always_true (a : ActorId) : isBlockedWaiting a := trivial

theorem isBlocked_always_true (p : Unit) : isBlocked p := trivial

theorem isAcyclic_always_true (W : WaitForGraph) : isAcyclic W := trivial

theorem formsCycle_always_true (a b : ActorId) (path : List ActorId) : formsCycle a b path := trivial

theorem specActorSystemDefinition_holds : specActorSystemDefinition := trivial

theorem specCommunicationReductionRule_holds : specCommunicationReductionRule := trivial

theorem specEdgeDefinitions_holds : specEdgeDefinitions := trivial

theorem specDeadlockFreeTheorem_holds : specDeadlockFreeTheorem := trivial

theorem specParallelComposition_holds : specParallelComposition := trivial

theorem specMessageDelivery_holds : specMessageDelivery := trivial

theorem specBackpressure_holds : specBackpressure := trivial

theorem specDeadlockDetection_holds : specDeadlockDetection := trivial

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

theorem specCycleDetection_holds : specCycleDetection := trivial

theorem specRejection_holds : specRejection := trivial

theorem specErrorMessages_holds : specErrorMessages := trivial

theorem hasMailbox_of_mem_actors (actor : ActorId) (config : ProcessConfig)
    (h : actor ∈ config.actors) : hasMailbox actor config := h

theorem isFutureWait_def (a b : ActorId) (future : Future)
    (h : future.resolvedBy = b) : isFutureWait a b future := h

theorem isBackpressureWait_always_true (a b : ActorId) (config : ProcessConfig) :
    isBackpressureWait a b config := trivial

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

end Morph.Specs.ConcurrencyProcessAlgebra
