/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.MonadicEffect

/-!
## Lemmas

Lemmas for the MonadicEffect specification.
This module will contain proofs about monadic effects,
effect handlers, and effect composition.
-/

theorem option_bind_none (f : α → Option β) : Option.bind (none : Option α) f = none := rfl

theorem option_bind_some (a : α) (f : α → Option β) :
  Option.bind (some a) f = f a := rfl

end Morph.Specs.MonadicEffect
