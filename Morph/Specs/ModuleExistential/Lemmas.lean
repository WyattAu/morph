/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ModuleExistential.Spec

namespace Morph.Specs.ModuleExistential

/-!
## Lemmas

Lemmas and auxiliary results for the ModuleExistential specification.
-/

theorem visibility_cases (v : Visibility) :
  v = .visPrivate ∨ v = .visPublic ∨ v = .visInternal := by
  cases v <;> simp

theorem IsPrivateModule_iff (mod : ModuleDecl) :
  IsPrivateModule mod ↔ mod.visibility = .visPrivate := Iff.rfl

theorem IsPublicModule_iff (mod : ModuleDecl) :
  IsPublicModule mod ↔ mod.visibility = .visPublic := Iff.rfl

theorem defaultEnv_empty : defaultEnv = [] := rfl

theorem ModuleEnv_contains_empty (sym : String) :
  ModuleEnv.contains [] sym = false := by
  unfold ModuleEnv.contains; simp

theorem ModuleEnv_getType_empty (sym : String) :
  ModuleEnv.getType [] sym = none := by
  unfold ModuleEnv.getType; simp

theorem accessRule_cases (r : AccessRule) :
  r = .allow ∨ r = .deny := by
  cases r <;> simp

theorem AccessControl_isAllowed_empty (mod : ModuleId) (sym : String) :
  AccessControl.isAllowed { entries := [] } mod sym = false := by
  unfold AccessControl.isAllowed; simp

end Morph.Specs.ModuleExistential
