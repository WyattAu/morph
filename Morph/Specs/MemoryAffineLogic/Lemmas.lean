/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryAffineLogic.Spec

namespace Morph.Specs.MemoryAffineLogic

open Morph.Specs.CommonTypes

/-!
## Lemmas

Lemmas and auxiliary results for the MemoryAffineLogic specification.
-/

theorem variableCount_empty (x : String) :
  variableCount { variables := [], resources := [] } x = 0 := by
  unfold variableCount; rfl

theorem resourceCount_empty (x : String) :
  resourceCount { variables := [], resources := [] } x = 0 := by
  unfold resourceCount; rfl

theorem isWellFormedContext_empty :
  isWellFormedContext { variables := [], resources := [] } := by
  unfold isWellFormedContext variableCount; intro _; simp

theorem joinContexts_empty_right (Γ : AffineContext) :
  joinContexts Γ { variables := [], resources := [] } = Γ := by
  unfold joinContexts; simp [List.append_nil]

theorem joinContexts_empty_left (Γ : AffineContext) :
  joinContexts { variables := [], resources := [] } Γ =
  { variables := Γ.variables, resources := Γ.resources } := by
  unfold joinContexts; simp [List.nil_append]

theorem getVariableType_none (x : String) :
  getVariableType { variables := [], resources := [] } x = none := by
  unfold getVariableType; simp

theorem isAffineTypeM_unit : isAffineTypeM .unit := trivial

theorem isAffineTypeM_nat : isAffineTypeM .nat := trivial

theorem isAffineTypeM_bool : isAffineTypeM .bool := trivial

theorem isAffineTypeM_arrow (a b : MorphType) : isAffineTypeM (.arrow a b) := trivial

theorem isLinearType_base (t : MorphType) : isLinearType (.base t) := trivial

theorem isLinearType_unit : ¬isLinearType .unit := by unfold isLinearType; simp

end Morph.Specs.MemoryAffineLogic
