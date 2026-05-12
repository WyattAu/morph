/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

namespace Morph.Specs.RegistryConsensus

/-!
## Examples

Concrete examples for the RegistryConsensus specification.
-/

example : (3 + 1) / 2 = 2 := rfl

example : (5 + 1) / 2 = 3 := rfl

example : (1 + 1) / 2 = 1 := rfl

example : [1, 2, 3].head? = some 1 := rfl

example : ([] : List Nat).head? = none := rfl

example : [5].getLast? = some 5 := rfl

end Morph.Specs.RegistryConsensus
