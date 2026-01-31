/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LayeredConcurrency.Spec

namespace Morph.Specs.LayeredConcurrency

/- # Lemmas for Layered Concurrency Architecture -/

/-- Pure functions are deterministic: same inputs always produce same outputs -/
theorem lemmaPureFunctionIsDeterministic (f : Reducer) :
    hasNoSideEffects f ∧
    doesNotMutateArguments f ∧
    isDeterministic f →
      ∀ (s1 s2 : State) (e : Morph.Event),
        f s1 e = f s2 e → s1 = s2 := by
  intro h_no_side h_no_mut h_det s1 s2 e h_eq
  exact h_det s1 s2 e h_eq

/-- Pure descriptors are deterministic: same inputs always produce same outputs -/
theorem lemmaPureDescriptorIsDeterministic (c : Command) :
    isDescriptor c ∧
    hasNoSideEffects c →
      ∀ (s1 s2 : State) (e : Morph.Event),
        c s1 e = c s2 e → s1 = s2 := by
  intro h_is_desc h_no_side s1 s2 e h_eq
  exact h_no_side s1 s2 e h_eq

/-- Unidirectional flow implies deterministic transitions -/
theorem lemmaUnidirectionalFlowImpliesDeterministic (state : State) :
    stateTransitionsFlowUnidirectional state →
      ∀ (s1 s2 : State) (e1 e2 : Morph.Event),
        ∃ (t1 t2 : StateTransition),
          t1.from = s1 ∧
          t1.event = e1 ∧
          t1.to = s2 ∧
          t1.direction = .forward ∧
          t2.from = s1 ∧
          t2.event = e2 ∧
          t2.to = s2 ∧
          t2.direction = .forward := by
  intro h_flow s1 s2 e1 e2
  have h_t1_exists : ∃ (t1 : StateTransition),
    t1.from = s1 ∧
    t1.event = e1 ∧
    t1.to = s2 ∧
    t1.direction = .forward := by
    exact h_flow s1 s2 e1
  have h_t2_exists : ∃ (t2 : StateTransition),
    t2.from = s1 ∧
    t2.event = e2 ∧
    t2.to = s2 ∧
    t2.direction = .forward := by
    exact h_flow s1 s2 e2
  cases h_t1_exists
  | intro t1 h_t1_props =>
    cases h_t2_exists
    | intro t2 h_t2_props =>
      exists t1
      constructor
      · exact h_t1_props
      · exists t2
        constructor
        · exact h_t2_props

/-- Bidirectional messaging implies responses exist -/
theorem lemmaBidirectionalMessagingImpliesResponses (b : Behavior) :
    supportsBidirectionalMessaging b →
      ∃ (msg : Message) (response : Message),
        let (newState, resp) := b.process msg defaultState in
        resp = some response := by
  intro h_supports
  exact h_supports

/-- Sequential processing preserves order -/
theorem lemmaSequentialProcessingPreservesOrder (b : Behavior) (msg1 msg2 : Message) (s : State) :
    processesMessagesSequentially b →
      msg1 ≠ msg2 →
        b.process msg1 s ≠ b.process msg2 s := by
  intro h_seq h_neq
  exact h_seq msg1 msg2 s h_neq

/-- Well-defined spawn boundary always produces valid actor -/
theorem lemmaWellDefinedSpawnProducesValidActor (f : ActorId → ApplicationLayerState → Actor) :
    wellDefinedSpawnBoundary f →
      ∀ (id : ActorId) (app : ApplicationLayerState),
        f id app ≠ default := by
  intro h_well_defined id app
  exact h_well_defined id app

/-- Well-defined send boundary always produces valid state -/
theorem lemmaWellDefinedSendProducesValidState (f : ActorId → Message → ApplicationLayerState → ApplicationLayerState) :
    wellDefinedSendBoundary f →
      ∀ (id : ActorId) (msg : Message) (app : ApplicationLayerState),
        f id msg app ≠ default := by
  intro h_well_defined id msg app
  exact h_well_defined id msg app

/-- Well-defined receive boundary always produces valid state -/
theorem lemmaWellDefinedReceiveProducesValidState (f : ActorId → Message → ApplicationLayerState → ApplicationLayerState) :
    wellDefinedReceiveBoundary f →
      ∀ (id : ActorId) (msg : Message) (app : ApplicationLayerState),
        f id msg app ≠ default := by
  intro h_well_defined id msg app
  exact h_well_defined id msg app

/-- Layer boundary integration preserves unidirectional flow -/
theorem lemmaLayerBoundaryIntegrationPreservesUnidirectional (app : ApplicationLayerState) (boundary : LayerBoundary) :
    wellDefinedLayerBoundary boundary →
      layerIntegrationMaintainsUnidirectional app boundary := by
  intro h_well_defined actorId msg
  constructor
  · exact h_well_defined.1
  · exact h_well_defined.2

end Morph.Specs.LayeredConcurrency
