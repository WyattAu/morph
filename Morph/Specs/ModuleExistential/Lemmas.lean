/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ModuleExistential.Spec

namespace Morph.Specs.ModuleExistential

/-!
## Lemmas

Lemmas and auxiliary results for the ModuleExistential specification.
-/

/-! ### Visibility -/

theorem visibility_cases (v : Visibility) :
  v = .visPrivate ∨ v = .visPublic ∨ v = .visInternal := by
  cases v <;> simp

theorem IsPrivateModule_iff (mod : ModuleDecl) :
  IsPrivateModule mod ↔ mod.visibility = .visPrivate := Iff.rfl

theorem IsPublicModule_iff (mod : ModuleDecl) :
  IsPublicModule mod ↔ mod.visibility = .visPublic := Iff.rfl

theorem IsInternalModule_iff (mod : ModuleDecl) :
  IsInternalModule mod ↔ mod.visibility = .visInternal := Iff.rfl

/-! ### Environment -/

theorem defaultEnv_empty : defaultEnv = [] := rfl

theorem ModuleEnv_contains_empty (sym : String) :
  ModuleEnv.contains [] sym = false := by
  unfold ModuleEnv.contains; simp

theorem ModuleEnv_contains_cons (sym : String) (typ : TypeWithVisibility) (rest : ModuleEnv) :
  ModuleEnv.contains ((sym, typ) :: rest) sym = true := by
  unfold ModuleEnv.contains; simp

theorem ModuleEnv_getType_empty (sym : String) :
  ModuleEnv.getType [] sym = none := by
  unfold ModuleEnv.getType; simp

theorem ModuleEnv_getType_cons_found (sym : String) (typ : TypeWithVisibility) (rest : ModuleEnv) :
  ModuleEnv.getType ((sym, typ) :: rest) sym = some typ := by
  unfold ModuleEnv.getType; simp

/-! ### Access Control -/

theorem accessRule_cases (r : AccessRule) :
  r = .allow ∨ r = .deny := by
  cases r <;> simp

theorem AccessControl_isAllowed_empty (mod : ModuleId) (sym : String) :
  AccessControl.isAllowed { entries := [] } mod sym = false := by
  unfold AccessControl.isAllowed; simp

/-! ### Type Visibility -/

theorem TypeWithVisibility_isPublic_iff (t : TypeWithVisibility) :
  t.isPublic ↔ t.visibility = .visPublic := Iff.rfl

theorem TypeWithVisibility_isPrivate_iff (t : TypeWithVisibility) :
  t.isPrivate ↔ t.visibility = .visPrivate := Iff.rfl

end Morph.Specs.ModuleExistential
