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

/-! ## Depth re-audit (loop 91) and resolution (loop 111)

Loop 91 pinned the validation outcomes and refuted the unconditional spec
forms. Loop 111 states the validated conditionals and proves them below;
the refutations are retained in git history. -/

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

/-- Refinement check agrees with the characterization. -/
theorem spec_type_refinement_holds : spec_type_refinement := by
  intro T L
  simp only [refinesLayout, decide_eq_true_eq]

/-- A matching type with offsets and size match validates. -/
theorem spec_data_validation_holds : spec_data_validation := by
  intro T L hT hlen hlast
  simp only [validateLayout, if_pos hlen, hlast, hT, decide_eq_true_eq]

/-- Compatibility names the agreement. -/
theorem spec_layout_compatibility_holds : spec_layout_compatibility := by
  intro L1 L2 h
  simp only [compatibleLayouts, decide_eq_true_eq] at h
  have e := h
  subst e
  exact ⟨rfl, rfl, rfl, rfl⟩

end Morph.Specs.AbiDataRefinement
