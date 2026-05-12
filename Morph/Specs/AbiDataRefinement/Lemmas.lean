/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.AbiDataRefinement.Spec

namespace Morph.Specs.AbiDataRefinement

/-!
## Lemmas

Lemmas and auxiliary results for the AbiDataRefinement specification.
-/

example (T : AbiType) : T.size = T.size := rfl

example (T : AbiType) : T.align = T.align := rfl

example (L : MemoryLayout) : L.size = L.size := rfl

end Morph.Specs.AbiDataRefinement
