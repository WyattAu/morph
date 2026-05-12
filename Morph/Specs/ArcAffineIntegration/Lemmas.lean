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

/-! ### Capability Transition Table -/

theorem transition_iso_val : transition .iso .val = true := rfl

theorem transition_val_ref : transition .val .ref = true := rfl

theorem transition_ref_weak : transition .ref .weak = true := rfl

theorem transition_iso_weak : transition .iso .weak = false := rfl

theorem transition_val_iso : transition .val .iso = false := rfl

theorem transition_ref_iso : transition .ref .iso = false := rfl

theorem transition_weak_iso : transition .weak .iso = false := rfl

theorem transition_weak_val : transition .weak .val = false := rfl

theorem transition_weak_ref : transition .weak .ref = false := rfl

theorem transition_ref_val : transition .ref .val = false := rfl

/-! ### Capability Exhaustiveness -/

theorem capability_cases (c : Capability) :
  c = .iso ∨ c = .val ∨ c = .ref ∨ c = .weak := by
  cases c <;> simp

/-! ### Reference Graph -/

theorem strongReferences_empty (o : ObjectId) :
  (strongReferences o defaultReferenceGraph).length = 0 := by
  unfold strongReferences defaultReferenceGraph; simp

/-! ### Capability Predicates -/

theorem isIso_iso : isIso .iso := rfl

theorem isVal_val : isVal .val := rfl

theorem isRef_ref : isRef .ref := rfl

theorem isWeak_weak : isWeak .weak := rfl

theorem isIso_not_val : ¬isIso .val := by unfold isIso; simp

theorem isVal_not_ref : ¬isVal .ref := by unfold isVal; simp

theorem isRef_not_weak : ¬isRef .weak := by unfold isRef; simp

theorem isWeak_not_iso : ¬isWeak .iso := by unfold isWeak; simp

/-! ### ARC Operations -/

theorem arcOperation_cases (op : ARCOperations) :
  match op with
  | .retain _ => True
  | .release _ => True
  | .tryRetain _ => True := by
  cases op <;> simp

end Morph.Specs.ArcAffineIntegration
