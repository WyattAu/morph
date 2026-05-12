/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LicenseDeonticLogic.Spec

namespace Morph.Specs.LicenseDeonticLogic

/-!
## Lemmas

Lemmas and auxiliary results for the LicenseDeonticLogic specification.
-/

theorem gplLicense_name : gplLicense.name = "GPL" := rfl

theorem predicateType_cases (pt : PredicateType) :
  pt = .permission ∨ pt = .obligation ∨ pt = .prohibition := by
  cases pt <;> simp

theorem action_cases (a : Action) :
  a = .linkStatic ∨ a = .linkDynamic ∨ a = .modify ∨ a = .distribute ∨
  a = .commercialUse ∨ a = .closeSource ∨ a = .openSource := by
  cases a <;> simp

theorem checkCompatibility_cases (root dep : License) :
  checkCompatibility root dep = .compatible ∨ checkCompatibility root dep = .incompatible := by
  cases checkCompatibility root dep <;> simp

end Morph.Specs.LicenseDeonticLogic
