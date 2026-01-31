/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ConcurrencyProcessAlgebra.Spec

namespace Morph.Specs.ConcurrencyProcessAlgebra.Examples

/- # Examples for Concurrency & Process Algebra -/

/-- Example process configuration with two actors -/
def exampleProcessConfig : ProcessConfig :=
  { actors := [0, 1]
    channels := ["ch1", "ch2"] }

/-- Example actor with mailbox and behavior -/
def exampleActor : Actor :=
  { id := 0
    mailbox := { owner := 0, isFull := false, messages := [] }
    behavior := fun msg =>
      match msg.value.data with
      | "ping" => .send 1 { content := { data := "pong" }, sender := 0 }
      | "pong" => .send 1 { content := { data := "ping" }, sender := 0 }
      | _ => .internal
    state := { data := "idle" } }

/-- Example processes for parallel composition -/
def exampleProcess1 : Process :=
  .input "ch1" (.output "ch1" { data := "msg1" } (.input "ch2" (.output "ch2" { data := "msg2" } (.input "ch1" (.output "ch1" { data := "msg3" } (.input "ch2" (.output "ch2" { data := "msg3" } ))

def exampleProcess2 : Process :=
  .output "ch1" { data := "msg1" } (.input "ch1" (.output "ch1" { data := "msg2" } (.input "ch2" (.output "ch2" { data := "msg2" } (.input "ch1" (.output "ch1" { data := "msg3" } (.input "ch2" (.output "ch2" { data := "msg3" } )

/-- Verify actor system definition -/
example verifyActorSystemDefinition : specActorSystemDefinition exampleProcessConfig exampleProcess1 exampleProcess2 := by
  unfold specActorSystemDefinition
  constructor
  · unfold isWellFormedConfig
    intro a1 a2 h_neq h_a1_in h_a2_in
    cases h_a1_in
    rfl
    cases h_a2_in
    rfl
  · unfold isValidProcess
    rfl
  · unfold isValidProcess
    rfl

/-- Verify communication reduction rule -/
example verifyCommunicationReductionRule : specCommunicationReductionRule exampleProcess1 := by
  unfold specCommunicationReductionRule
  constructor
  · rfl
  · rfl
  · constructor
    rfl
    rfl
    rfl

/-- Verify wait-for graph is acyclic -/
example verifyAcyclicWaitForGraph : isAcyclic { vertices := [0, 1], edges := [] } := by
  unfold isAcyclic
  intro a b h_edge
  contradiction

/-- Verify parallel composition -/
example verifyParallelComposition : specParallelComposition exampleProcess1 exampleProcess2 := by
  unfold specParallelComposition
  constructor
  · unfold isWellFormedConfig
    intro a1 a2 h_neq h_a1_in h_a2_in
    cases h_a1_in
    rfl
    cases h_a2_in
    rfl
  · unfold isValidProcess
    rfl
  · unfold isValidProcess
    rfl
  · rfl

/-- Verify message delivery -/
example verifyMessageDelivery : specMessageDelivery 0 1 { content := { data := "test" } } exampleProcessConfig := by
  unfold specMessageDelivery
  constructor
  · rfl
  · rfl
  · rfl
  · constructor
    rfl
    rfl
    rfl

/-- Verify backpressure -/
example verifyBackpressure : specBackpressure 0 1 { content := { data := "test" } } exampleProcessConfig := by
  unfold specBackpressure
  constructor
  · rfl
  · rfl
  · constructor
    rfl
    rfl
    rfl
  · unfold isBlocked
    rfl

/-- Verify deadlock detection -/
example verifyDeadlockDetection : specDeadlockDetection { vertices := [0, 1], edges := [] } exampleProcessConfig := by
  unfold specDeadlockDetection
  constructor
  · unfold isWellFormedConfig
    intro a1 a2 h_neq h_a1_in h_a2_in
    cases h_a1_in
    rfl
    cases h_a2_in
    rfl
  · constructor
    · constructor
      rfl
      rfl
    · constructor
      rfl
      rfl

/-- Verify private channels -/
example verifyPrivateChannels : specPrivateChannels (.newChannel (.input "ch1" (.output "ch1" { data := "msg1" } )) (.input "ch1" (.output "ch1" { data := "msg2" } ) "ch1" { vertices := [0, 1], channels := ["ch1"] } := by
  unfold specPrivateChannels
  intro P Q R x h_new h_x_in R
  unfold Process.newChannel at h_new
  unfold isValidProcess at h_new
  unfold Process.input at R
  intro h_P_eq
  contradiction

/-- Verify millions of actors -/
example verifyMillionsOfActors : specMillionsOfActors { actors := List.range 1000000, channels := List.range 1000000 } := by
  unfold specMillionsOfActors
  constructor
  · rfl
  · intro actor h_in
    unfold hasMailbox
    rfl

/-- Verify submillisecond latency -/
example verifySubmillisecondLatency : specSubmillisecondLatency 0 1 { content := { data := "test" } } { actors := [0, 1], channels := ["ch1"] } := by
  unfold specSubmillisecondLatency
  constructor
  · unfold isWellFormedConfig
    intro a1 a2 h_neq h_a1_in h_a2_in
    cases h_a1_in
    rfl
    cases h_a2_in
    rfl
  · rfl
  · rfl
  · constructor
    exists 500
      constructor
      · apply Nat.lt_of_add_right
        rfl
        apply Nat.zero_le
      · constructor
        rfl
        rfl
        rfl

/-- Verify deadlock detection complexity -/
example verifyDeadlockDetectionComplexity : specDeadlockDetectionComplexity { vertices := List.range 100000, edges := [] } { actors := List.range 100000, channels := List.range 100000 } := by
  unfold specDeadlockDetectionComplexity
  constructor
  · unfold isWellFormedConfig
    intro a1 a2 h_neq h_a1_in h_a2_in
    cases h_a1_in
    rfl
    cases h_a2_in
    rfl
  · rfl
  · constructor
    exists 100
      constructor
      · rfl
      · intro a b h_edge
        constructor
          rfl
          rfl

/-- Verify actor structure -/
example verifyActorStructure : specActorStructure exampleActor := by
  unfold specActorStructure
  rfl

/-- Verify actor data structures -/
example verifyActorDataStructures : specActorDataStructures exampleActor 10 := by
  unfold specActorDataStructures
  constructor
  · rfl
  · constructor
    rfl

/-- Verify wait-for graph structure -/
example verifyWaitForGraphStructure : specWaitForGraphStructure { vertices := [0, 1], edges := [] } := by
  unfold specWaitForGraphStructure
  intro a h_edge
  cases h_edge
  | .futureWait _ _ =>
    rfl
  | .backpressureWait _ _ =>
    rfl

/-- Verify message delivery theorem -/
example verifyMessageDeliveryTheorem : specMessageDeliveryTheorem 0 1 { content := { data := "test" } } { actors := [0, 1], channels := ["ch1"] } := by
  unfold specMessageDeliveryTheorem
  constructor
  · unfold specMessageDelivery
  constructor
    rfl
    rfl
    rfl
    rfl

/-- Verify backpressure safety theorem -/
example verifyBackpressureSafetyTheorem : specBackpressureSafetyTheorem 0 1 { content := { data := "test" } } { actors := [0, 1], channels := ["ch1"] } := by
  unfold specBackpressureSafetyTheorem
  constructor
  · unfold specBackpressure
  constructor
    rfl
    rfl
    rfl
    constructor
    rfl
    rfl
    rfl

/-- Verify FIFO ordering -/
example verifyFifoOrdering : specFifoOrdering { owner := 0, isFull := false, messages := [{ value := { data := "msg1" }, { value := { data := "msg2" } ] } := by
  unfold specFifoOrdering
  intro msg1 msg2
  constructor
  · rfl
  · rfl
  · rfl
  · rfl

/-- Verify no duplication -/
example verifyNoDuplication : specNoDuplication { owner := 0, isFull := false, messages := [{ value := { data := "msg1" }, { value := { data := "msg2" } ] } := by
  unfold specNoDuplication
  intro msg
  constructor
  · rfl
  · rfl

/-- Verify no loss -/
example verifyNoLoss : specNoLoss { owner := 0, isFull := false, messages := [{ value := { data := "msg1" }, { value := { data := "msg2" } ] } := by
  unfold specNoLoss
  intro msg
  constructor
  · rfl
  · constructor
    rfl

/-- Verify cycle detection -/
example verifyCycleDetection : specCycleDetection { vertices := [0, 1], edges := [] } := by
  unfold specCycleDetection
  intro a b h_edge
  contradiction

/-- Verify rejection -/
example verifyRejection : specRejection { vertices := [0, 1], edges := [] } { actors := [0, 1], channels := ["ch1"] } := by
  unfold specRejection
  constructor
  · intro a b h_edge
    constructor
      rfl
      rfl
  · intro h_exists
    cases h_exists
    | intro path h_cycle =>
      unfold isAcyclic at h_cycle
      intro a' b' h_edge'
      contradiction

/-- Verify error messages -/
example verifyErrorMessages : specErrorMessages { vertices := [0, 1], edges := [] } { actors := [0, 1], channels := ["ch1"] } := by
  unfold specErrorMessages
  constructor
  · intro a b h_edge
    constructor
      rfl
      rfl
  · intro h_exists
    cases h_exists
    | intro path h_cycle =>
      unfold isWellFormedConfig at h_cycle
      intro a1 a2 h_neq h_a1_in h_a2_in
      cases h_a1_in
      rfl
      cases h_a2_in
      rfl

end Morph.Specs.ConcurrencyProcessAlgebra.Examples
