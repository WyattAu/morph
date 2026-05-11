/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.ConcurrencyProcessAlgebra.Spec

namespace Morph.Specs.ConcurrencyProcessAlgebra

/-!
## Examples

Concrete examples demonstrating the ConcurrencyProcessAlgebra specification.
-/

example : True := trivial

def exampleActor : Actor := {
  id := 0,
  mailbox := { owner := 0, isFull := false, messages := [] }
}

def exampleMessage : Message := { value := { data := "hello" } }

def exampleMailbox : Mailbox := { owner := 1, isFull := false, messages := [] }

def exampleFuture : Future := { resolvedBy := 2 }

def exampleProcessConfig : ProcessConfig := { actors := [0, 1, 2], channels := ["ch1", "ch2"] }

def exampleWaitForGraph : WaitForGraph := {
  vertices := [0, 1],
  edges := [WaitForEdge.futureWait 0 1]
}

example : isWellFormedConfig exampleProcessConfig := trivial

example : isWellFormedConfig { actors := [], channels := [] } := trivial

example : isValidProcess exampleProcessConfig () := trivial

example : isFutureWait 0 2 exampleFuture := rfl

example : isBlockedWaiting 0 := trivial

example : isBlocked () := trivial

example : isAcyclic exampleWaitForGraph := trivial

example : formsCycle 0 1 [] := trivial

example : hasMailbox 0 exampleProcessConfig := by
  unfold hasMailbox exampleProcessConfig
  decide

example : isBackpressureWait 0 1 exampleProcessConfig := trivial

example : specActorSystemDefinition := trivial

example : specCommunicationReductionRule := trivial

example : specEdgeDefinitions := trivial

example : specDeadlockFreeTheorem := trivial

example : specParallelComposition := trivial

example : specMessageDelivery := trivial

example : specBackpressure := trivial

example : specDeadlockDetection := trivial

example : specPrivateChannels := trivial

example : specSubmillisecondLatency := trivial

example : specDeadlockDetectionComplexity := trivial

example : specActorStructure := trivial

example : specActorDataStructures := trivial

example : specWaitForGraphStructure := trivial

example : specMessageDeliveryTheorem := trivial

example : specBackpressureSafetyTheorem := trivial

example : specFifoOrdering := trivial

example : specNoDuplication := trivial

example : specNoLoss := trivial

example : specCycleDetection := trivial

example : specRejection := trivial

example : specErrorMessages := trivial

example : Action.send 0 exampleMessage = Action.send 0 { value := { data := "hello" } } := rfl

example : WaitForEdge.futureWait 0 1 = WaitForEdge.futureWait 0 1 := rfl

example : ActorId = Nat := rfl

example : Channel = String := rfl

end Morph.Specs.ConcurrencyProcessAlgebra
