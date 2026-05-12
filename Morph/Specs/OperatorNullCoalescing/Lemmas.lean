/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.OperatorNullCoalescing

/-!
## Lemmas

Lemmas for the OperatorNullCoalescing specification.
This module will contain proofs about the null-coalescing operator `??`,
short-circuit evaluation, and option/nullable composition.
-/

theorem option_getOrDeref_some (a : α) (default : α) :
  (some a).getD default = a := rfl

theorem option_getOrDeref_none (default : α) :
  (none : Option α).getD default = default := rfl

theorem option_orelse_some (a : α) (b : Option α) :
  (some a).orElse (fun () => b) = some a := rfl

theorem option_orelse_none (b : Option α) :
  (none : Option α).orElse (fun () => b) = b := rfl

end Morph.Specs.OperatorNullCoalescing
