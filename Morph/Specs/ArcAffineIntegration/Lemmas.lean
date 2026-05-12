/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ArcAffineIntegration.Spec

namespace Morph.Specs.ArcAffineIntegration

open Morph.Specs.CommonTypes

/-!
## Lemmas

Lemmas and auxiliary results for the ArcAffineIntegration specification.
-/

theorem transition_iso_val : transition .iso .val = true := rfl

theorem transition_val_ref : transition .val .ref = true := rfl

theorem transition_ref_weak : transition .ref .weak = true := rfl

theorem transition_iso_weak : transition .iso .weak = false := rfl

theorem transition_val_iso : transition .val .iso = false := rfl

theorem capability_cases (c : Capability) :
  c = .iso ∨ c = .val ∨ c = .ref ∨ c = .weak := by
  cases c <;> simp

theorem strongReferences_empty (o : ObjectId) :
  (strongReferences o defaultReferenceGraph).length = 0 := by
  unfold strongReferences defaultReferenceGraph; simp

end Morph.Specs.ArcAffineIntegration
