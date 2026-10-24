/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.StrictStateUnidirectional.Spec

namespace Morph.Specs.StrictStateUnidirectional

/-!
## Examples

Concrete examples for the StrictStateUnidirectional specification.
-/

example : !!true = true := by simp

example : !!false = false := by simp

example : true && true = true := rfl

example : true && false = false := rfl

example : false || true = true := rfl

example : false || false = false := rfl

/-- A two-state chain: the target is reachable from the source, not the
reverse, and a state reaches itself. -/
def chain : StateGraph :=
  { states := [{ id := 1 }, { id := 2 }]
  , transitions := [{ src := { id := 1 }, dst := { id := 2 }, label := "next" }]
  , initial := { id := 1 } }

example : StateGraph.reachable chain { id := 1 } { id := 2 } = true := by native_decide

example : StateGraph.reachable chain { id := 2 } { id := 1 } = false := by native_decide

example : StateGraph.reachable chain { id := 2 } { id := 2 } = true := by native_decide

end Morph.Specs.StrictStateUnidirectional
