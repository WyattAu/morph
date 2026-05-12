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

theorem isPureFunction_trivial (f : Reducer) :
  isPureFunction f := by
  unfold isPureFunction hasNoSideEffects doesNotMutateArguments isDeterministic
  constructor <;> constructor <;> trivial

theorem specLcaApplicationLayerUnidirectional_holds :
  specLcaApplicationLayerUnidirectional := by
  unfold specLcaApplicationLayerUnidirectional; intro _; trivial

theorem specLcaConcurrencyLayerBidirectional_holds :
  specLcaConcurrencyLayerBidirectional := by
  unfold specLcaConcurrencyLayerBidirectional; intro _; trivial

theorem direction_cases (d : Direction) :
  d = Direction.forward ∨ d = Direction.backward := by
  cases d <;> simp

end Morph.Specs.LayeredConcurrency
