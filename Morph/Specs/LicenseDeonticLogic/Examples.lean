/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LicenseDeonticLogic.Spec

namespace Morph.Specs.LicenseDeonticLogic

/-!
## Examples

Concrete examples demonstrating the LicenseDeonticLogic specification.
-/

def mitLicense : License := {
  name := "MIT",
  predicates := [
    { predicateType := .permission, action := .modify, value := true },
    { predicateType := .permission, action := .distribute, value := true },
    { predicateType := .permission, action := .commercialUse, value := true }
  ],
  actions := [.modify, .distribute, .commercialUse]
}

example : gplLicense.name = "GPL" := rfl

example : mitLicense.predicates.length = 3 := rfl

example : PredicateType.permission ≠ PredicateType.obligation := by
  intro h; cases h

example : Action.linkStatic ≠ Action.linkDynamic := by
  intro h; cases h

end Morph.Specs.LicenseDeonticLogic
