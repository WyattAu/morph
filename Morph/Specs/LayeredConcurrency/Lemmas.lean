/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LayeredConcurrency.Spec

namespace Morph.Specs.LayeredConcurrency

/-!
# LayeredConcurrency: the layer operations, real

Research loop 27. Target: `Morph/Specs/LayeredConcurrency/`.

**What was there.** Fourteen `Prop := True` advertisements, and a set of
predicates that were tautologies in disguise:
`stateTransitionsFlowUnidirectional state := ∀ s, s = state → s = state`,
and `hasNoSideEffects`/`isDeterministic`/`isDescriptor` all of the form
`equal arguments → equal results` (true for *every* function, which is the
point of a pure language, but they were being checked rather than derived).

**What is here.** A small but real layer model — `send`, `receive`,
`processOne`, `integrate`, `appStep` — and the fourteen claims as statements
about it:

* `messagesAreImmutable` — enqueue then dequeue returns the message and leaves
  the list intact;
* `processesMessagesSequentially` — `processOne` removes exactly the head;
* `stateTransitionsAreDeterministic` — equal states give equal reducer results;
* `actorCommunicationIsBidirectional` — enqueue/dequeue round-trips, and a
  non-empty mailbox dequeues;
* `layerIntegrationMaintainsUnidirectional` and `noSharedStateBetweenLayers` —
  `integrate` writes down to the actor and never back to the application;
* the eight `specLca*` theorems, each proved from the above.

**What changed in the spec.** `stateTransitionsFlowUnidirectional` now says the
application step's direction is `forward` (it was `s = s`), and
`specLcaActorTypes` no longer demands a non-empty mailbox of *every* actor —
that conjunction was false for the empty actor, so it could only ever have been
"proved" by the empty mailbox being excluded from the domain, which it was not.
-/

theorem hasMailbox_cons (msg : Message) :
  hasMailbox { messages := msg :: [] } := by
  unfold hasMailbox; simp

theorem hasMailbox_nil :
  ¬hasMailbox { messages := [] } := by
  unfold hasMailbox; simp

theorem hasMailbox_iff (m : Mailbox) :
  hasMailbox m ↔ m.messages ≠ [] := Iff.rfl

/-- **Purity is a theorem about the language, not a property to be checked.**
Every function in a pure language is pure: equal arguments give equal results,
a call cannot disturb the state it was given, and the same arguments always give
the same result. The module's `isPureFunction` was a conjunction of three
`True` predicates, so "GA-002: the SSUS pattern preserves referential
transparency" was *Validated* for a trivial reason — there are no effects to
preserve transparency against. The predicates are now real statements, and this
theorem says they all hold. -/
theorem isPureFunction_of_pure_language (f : Reducer) :
  isPureFunction f := by
  refine ⟨?_, ?_, ?_⟩
  · intro s a s' a' hs ha
    simp only [hs, ha]
  · intro s a s' a' hs ha
    simp only [hs, ha]
  · intro s a s' a' hs ha
    simp only [hs, ha]

/-- **A descriptor is pure, for the same reason.** -/
theorem isPureDescriptor_of_pure_language (c : Command) : isPureDescriptor c := by
  refine ⟨?_, ?_⟩
  · intro s a s' a' hs ha
    simp only [hs, ha]
  · intro s a s' a' hs ha
    simp only [hs, ha]

/-- **Unidirectional data flow**: the application transition always moves
forward. -/
theorem stateTransitionsFlowUnidirectional_holds (state : State) :
    stateTransitionsFlowUnidirectional state := by
  rfl

theorem specLcaApplicationLayerUnidirectional_holds :
  specLcaApplicationLayerUnidirectional := by
  intro app
  exact stateTransitionsFlowUnidirectional_holds app.state

theorem direction_cases (d : Direction) :
  d = Direction.forward ∨ d = Direction.backward := by
  cases d <;> simp

/-! ## The layer operations, proved -/

theorem messagesAreImmutable_holds (msgs : List Message) :
    messagesAreImmutable msgs := by
  intro msg
  rfl

theorem processesMessagesSequentially_holds (a : Actor) :
    processesMessagesSequentially a := by
  intro m rest h
  refine ⟨{ a with mailbox := { messages := rest } }, ?_, rfl⟩
  simp [processOne, receive, h]

theorem stateTransitionsAreDeterministic_holds (state : State) (reducer : Reducer) :
    stateTransitionsAreDeterministic state reducer := by
  intro s input h
  rw [h]

theorem actorCommunicationIsBidirectional_holds (a : Actor) :
    actorCommunicationIsBidirectional a := by
  constructor
  · intro msg
    rfl
  · intro m rest h
    exact ⟨{ messages := rest }, by simp [receive, h]⟩

theorem layerIntegrationMaintainsUnidirectional_holds (app : ApplicationLayerState) :
    layerIntegrationMaintainsUnidirectional app := by
  intro a
  exact ⟨rfl, rfl⟩

theorem noSharedStateBetweenLayers_holds (app : ApplicationLayerState) (a : Actor) :
    noSharedStateBetweenLayers app a := by
  intro s
  rfl

theorem specLcaConcurrencyLayerBidirectional_holds :
  specLcaConcurrencyLayerBidirectional := by
  intro a
  exact actorCommunicationIsBidirectional_holds a

theorem specLcaLayerBoundary_holds : specLcaLayerBoundary := by
  intro app a
  rfl

theorem specLcaPureFunctionTypes_holds : specLcaPureFunctionTypes :=
  isPureFunction_of_pure_language

theorem specLcaActorTypes_holds : specLcaActorTypes := by
  intro actor
  exact ⟨messagesAreImmutable_holds actor.mailbox.messages,
    processesMessagesSequentially_holds actor⟩

theorem specLcaUnidirectionalTheorem_holds : specLcaUnidirectionalTheorem :=
  layerIntegrationMaintainsUnidirectional_holds

theorem specLcaBidirectionalTheorem_holds : specLcaBidirectionalTheorem :=
  actorCommunicationIsBidirectional_holds

theorem specLcaLayerIntegrationTheorem_holds : specLcaLayerIntegrationTheorem := by
  intro app a
  exact ⟨rfl, rfl⟩

theorem specLcaDeterminismTheorem_holds : specLcaDeterminismTheorem :=
  stateTransitionsAreDeterministic_holds

theorem specLcaBidirectionalityTheorem_holds : specLcaBidirectionalityTheorem := by
  intro a msg
  rfl

theorem specLcaLayerSeparationTheorem_holds : specLcaLayerSeparationTheorem :=
  noSharedStateBetweenLayers_holds

end Morph.Specs.LayeredConcurrency
