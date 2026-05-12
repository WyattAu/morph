/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ModuleExistential.Spec

namespace Morph.Specs.ModuleExistential

/-!
## Examples

Concrete examples demonstrating the ModuleExistential specification.
-/

def coreMod : ModuleDecl := {
  id := { name := "Core" },
  visibility := .visPublic,
  exports := ["init", "config"]
}

def internalMod : ModuleDecl := {
  id := { name := "Internal" },
  visibility := .visInternal,
  exports := ["helper"]
}

def privateMod : ModuleDecl := {
  id := { name := "Private" },
  visibility := .visPrivate,
  exports := ["secret"]
}

example : IsPublicModule coreMod := rfl

example : IsPrivateModule privateMod := rfl

example : IsInternalModule internalMod := rfl

example : coreMod.exports.length = 2 := rfl

example : coreMod.id.name = "Core" := rfl

example : AccessRule.allow ≠ AccessRule.deny := by
  intro h; cases h

end Morph.Specs.ModuleExistential
