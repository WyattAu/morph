/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.AbiDataRefinement.Spec

namespace Morph.Specs.AbiDataRefinement

/-!
## Lemmas

Lemmas and auxiliary results for the AbiDataRefinement specification.
-/

/-! ### Structural Properties -/

theorem abiType_size_eq (T : AbiType) : T.size = T.size := rfl

theorem abiType_align_eq (T : AbiType) : T.align = T.align := rfl

theorem memoryLayout_size_eq (L : MemoryLayout) : L.size = L.size := rfl

/-! ### Layout Validation -/

theorem validateLayout_empty_offsets (L : MemoryLayout) :
  L.offsets = [] → validateLayout L = false := by
  intro h; unfold validateLayout; simp [h]

end Morph.Specs.AbiDataRefinement
