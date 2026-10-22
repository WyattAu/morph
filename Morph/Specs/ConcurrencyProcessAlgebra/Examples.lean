/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.ConcurrencyProcessAlgebra.Lemmas

namespace Morph.Specs.ConcurrencyProcessAlgebra

/-!
## Examples

Concrete examples demonstrating the ConcurrencyProcessAlgebra specification.
-/

/-- Scenario: Actor 0 creates an empty mailbox, ready to receive messages. -/
def actor0 : Actor := {
  id := 0,
  mailbox := { owner := 0, isFull := false, messages := [] }
}

/-- Scenario: After Actor 0 sends "task-result" to Actor 1, Actor 1's mailbox has one message. -/
def actor1AfterReceive : Actor := {
  id := 1,
  mailbox := { owner := 1, isFull := false, messages := [{ value := { data := "task-result" } }] }
}

/-- After receiving, Actor 1's mailbox is no longer empty. -/
example : actor1AfterReceive.mailbox.messages.length = 1 := rfl

/-- Actor 0 starts with an empty mailbox. -/
example : actor0.mailbox.messages.length = 0 := rfl

/-- Scenario: A two-actor system communicating over a request channel. -/
def twoActorConfig : ProcessConfig := {
  actors := [0, 1],
  channels := ["request-channel"]
}

/-- Both actors have mailboxes in the two-actor config. -/
example : hasMailbox 0 twoActorConfig ∧ hasMailbox 1 twoActorConfig := by
  constructor <;> unfold hasMailbox <;> decide

/-- Scenario: Channel operation — actor 0 sends a greeting to actor 1. -/
def sendAction : Action := Action.send 1 { value := { data := "hello" } }

/-- The send action targets actor 1 with the greeting payload. -/
example : sendAction = Action.send 1 { value := { data := "hello" } } := rfl

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

example : isWellFormedConfig exampleProcessConfig := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [exampleProcessConfig]
  · rcases List.mem_cons.mp ha with rfl | ha
    · simp [exampleProcessConfig]
    · rcases List.mem_cons.mp ha with rfl | ha
      · simp [exampleProcessConfig]
      · simp at ha

example : isWellFormedConfig { actors := [], channels := [] } := by
  intro a ha
  exact absurd ha (by simp)

example : isValidProcess exampleProcessConfig 0 := by
  simp [isValidProcess]
  simp [exampleProcessConfig]

example : isFutureWait 0 2 exampleFuture := rfl

/-- A wait relation in which actor 0 waits for actor 2 and nobody else waits. -/
def exampleWaits : ActorId → Option ActorId :=
  fun a => if a = 0 then some 2 else none

example : isBlockedWaiting 0 exampleWaits := by
  unfold isBlockedWaiting
  exact ⟨2, rfl⟩

example : ¬ isBlockedWaiting 1 exampleWaits := by
  unfold isBlockedWaiting
  rintro ⟨b, hb⟩
  simp [exampleWaits] at hb

example : isBlocked 0 exampleWaits := by
  unfold isBlocked isBlockedWaiting
  exact ⟨2, rfl⟩

example : hasMailbox 0 exampleProcessConfig := by
  unfold hasMailbox exampleProcessConfig
  decide

example : isBackpressureWait 0 2 exampleWaits := by
  unfold isBackpressureWait
  rfl

example : specActorSystemDefinition := specActorSystemDefinition_holds

example : specCommunicationReductionRule := specCommunicationReductionRule_holds

example : specEdgeDefinitions := specEdgeDefinitions_holds

example : specDeadlockFreeTheorem := specDeadlockFreeTheorem_holds

example : specParallelComposition := specParallelComposition_holds

example : specMessageDelivery := specMessageDelivery_holds

example : specBackpressure := specBackpressure_holds

/-- The module's own `specDeadlockDetection`, now a real statement about a
rank-respecting actor system — and proved in `Lemmas.lean`. -/
example (s : Morph.Specs.ActorDeadlock.Sys)
    (rank : Morph.Specs.ActorDeadlock.Actor → Nat)
    (p : Morph.Specs.ActorDeadlock.Actor) :
    specDeadlockDetection s rank p :=
  specDeadlockDetection_holds s rank p

example : specPrivateChannels := specPrivateChannels_holds

example : specSubmillisecondLatency := specSubmillisecondLatency_holds

example : specDeadlockDetectionComplexity := specDeadlockDetectionComplexity_holds

example : specActorStructure := specActorStructure_holds

example : specActorDataStructures := specActorDataStructures_holds

example : specWaitForGraphStructure := specWaitForGraphStructure_holds

example : specMessageDeliveryTheorem := specMessageDeliveryTheorem_holds

example : specBackpressureSafetyTheorem := specBackpressureSafetyTheorem_holds

example : specFifoOrdering := specFifoOrdering_holds

example : specNoDuplication := specNoDuplication_holds

example : specNoLoss := specNoLoss_holds

/-- And `specCycleDetection`: a rank-respecting wait-for graph is acyclic. -/
example (s : Morph.Specs.ActorDeadlock.Sys)
    (rank : Morph.Specs.ActorDeadlock.Actor → Nat) :
    specCycleDetection s rank :=
  specCycleDetection_holds s rank

example : specRejection := specRejection_holds

example : specErrorMessages := specErrorMessages_holds

example : Action.send 0 exampleMessage = Action.send 0 { value := { data := "hello" } } := rfl

example : WaitForEdge.futureWait 0 1 = WaitForEdge.futureWait 0 1 := rfl

example : ActorId = Nat := rfl

example : Channel = String := rfl

end Morph.Specs.ConcurrencyProcessAlgebra
