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

/-! ## Depth re-audit (loop 91): validation outcomes and spec refutations -/

/-- A matching layout validates. -/
theorem validateLayout_hit :
    validateLayout ⟨⟨"a", 4, 4⟩, 4, 4, [4]⟩ = true := rfl

/-- A layout whose last offset misses the type size is rejected. -/
theorem validateLayout_mismatch :
    validateLayout ⟨⟨"a", 4, 4⟩, 4, 4, [8]⟩ = false := rfl

/-- Identical layouts are compatible. -/
theorem compatibleLayouts_refl :
    compatibleLayouts ⟨⟨"a", 4, 4⟩, 4, 4, [4]⟩ ⟨⟨"a", 4, 4⟩, 4, 4, [4]⟩
      = true := rfl

/-- Layouts over different ABI types are not compatible. -/
theorem compatibleLayouts_distinct :
    compatibleLayouts ⟨⟨"a", 4, 4⟩, 4, 4, [4]⟩ ⟨⟨"b", 4, 4⟩, 4, 4, [4]⟩
      = false := rfl

/-- **The compatibility spec is false as stated.** It claims *every* pair of
layouts is compatible; two layouts over different ABI types refute it. -/
theorem spec_layout_compatibility_false : ¬ spec_layout_compatibility :=
  fun h =>
    absurd
      (h ⟨⟨"a", 4, 4⟩, 4, 4, [4]⟩ ⟨⟨"b", 4, 4⟩, 4, 4, [4]⟩)
      (by decide)

/-- **The validation spec is false as stated.** It claims matching the ABI
type suffices for validity; a layout with no offsets has the right type and
still fails validation. -/
theorem spec_data_validation_false : ¬ spec_data_validation :=
  fun h =>
    absurd (h ⟨"a", 4, 4⟩ ⟨⟨"a", 4, 4⟩, 4, 4, []⟩ rfl) (by decide)

end Morph.Specs.AbiDataRefinement
