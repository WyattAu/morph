/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LayeredConcurrency.Spec

namespace Morph.Specs.LayeredConcurrency

/-!
## Examples

Concrete examples demonstrating the LayeredConcurrency specification.
-/

def actor1 : Actor := {
  mailbox := { messages := [] },
  state := Morph.Core.Value.int 0
}

def msg0 : Message := {
  content := Morph.Core.Value.int 1,
  sender := { id := 0 }
}

def actor2 : Actor := {
  mailbox := { messages := [msg0] },
  state := Morph.Core.Value.int 1
}

example : actor1.mailbox.messages = [] := rfl

example : actor2.mailbox.messages.length = 1 := rfl

theorem forward_ne_backward : Direction.forward ≠ Direction.backward := by
  intro h; cases h

def transition1 : StateTransition := {
  fromState := Morph.Core.Value.int 0,
  toState := Morph.Core.Value.int 1,
  direction := Direction.forward
}

example : transition1.direction = Direction.forward := rfl

end Morph.Specs.LayeredConcurrency
