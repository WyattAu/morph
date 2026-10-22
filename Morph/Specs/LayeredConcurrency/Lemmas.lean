/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LayeredConcurrency.Spec

namespace Morph.Specs.LayeredConcurrency

/-!
## Lemmas

Lemmas and auxiliary results for the LayeredConcurrency specification.
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

/-- **Unidirectional data flow**: a transition depends only on the state it is
given. -/
theorem stateTransitionsFlowUnidirectional_holds (state : State) :
    stateTransitionsFlowUnidirectional state := by
  intro s hs
  exact hs

theorem specLcaApplicationLayerUnidirectional_holds :
  specLcaApplicationLayerUnidirectional := by
  intro app
  exact stateTransitionsFlowUnidirectional_holds app.state

theorem specLcaConcurrencyLayerBidirectional_holds :
  specLcaConcurrencyLayerBidirectional := by
  unfold specLcaConcurrencyLayerBidirectional; intro _; trivial

theorem direction_cases (d : Direction) :
  d = Direction.forward ∨ d = Direction.backward := by
  cases d <;> simp

end Morph.Specs.LayeredConcurrency
