/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryAffineLogic.Spec

namespace Morph.Specs.MemoryAffineLogic

open Morph.Specs.CommonTypes

/-!
## Examples

Concrete examples demonstrating the MemoryAffineLogic specification.
-/

def emptyCtx : AffineContext := { variables := [], resources := [] }

def ctx1 : AffineContext := { variables := [("x", .nat)], resources := [] }

example : isWellFormedContext emptyCtx := by
  unfold isWellFormedContext variableCount emptyCtx; intro x; simp [List.filter]

example : isAffineTypeM .nat := trivial

example : isAffineTypeM (.arrow .nat .bool) := trivial

example : isLinearType (.base .nat) := trivial

example : ¬isLinearType .nat := by unfold isLinearType; simp

example : emptyCtx.variables = [] := rfl

example : ctx1.variables.length = 1 := rfl

end Morph.Specs.MemoryAffineLogic
