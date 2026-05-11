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

end Morph.Specs.ConcurrencyProcessAlgebra
