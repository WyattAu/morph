/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ModuleSystem.Spec

namespace Morph.Specs.ModuleSystem

/-!
## Examples

Concrete examples demonstrating the ModuleSystem specification.
-/

def id_core : ModuleId := { hash := "abc123", version := 1 }

def mod_core : Module := {
  id := id_core,
  name := "core",
  declarations := [],
  dependencies := []
}

def id_utils : ModuleId := { hash := "def456", version := 2 }

def mod_utils : Module := {
  id := id_utils,
  name := "utils",
  declarations := [],
  dependencies := [id_core]
}

/-- Version 1 satisfies exact constraint 1. -/
example : satisfiesConstraint 1 (.exact 1) = true := rfl

/-- Version 2 does not satisfy exact constraint 1. -/
example : satisfiesConstraint 2 (.exact 1) = false := rfl

/-- Version 3 satisfies atLeast 2. -/
example : satisfiesConstraint 3 (.atLeast 2) = true := rfl

/-- Version 1 does not satisfy atLeast 2. -/
example : satisfiesConstraint 1 (.atLeast 2) = false := rfl

/-- Version 1 satisfies atMost 2. -/
example : satisfiesConstraint 1 (.atMost 2) = true := rfl

/-- Version 3 does not satisfy atMost 2. -/
example : satisfiesConstraint 3 (.atMost 2) = false := rfl

/-- Version 2 satisfies range 1 3. -/
example : satisfiesConstraint 2 (.range 1 3) = true := rfl

/-- Version 0 does not satisfy range 1 3. -/
example : satisfiesConstraint 0 (.range 1 3) = false := rfl

/-- Version 4 does not satisfy range 1 3. -/
example : satisfiesConstraint 4 (.range 1 3) = false := rfl

/-- Adding a module to the link table makes it the first entry. -/
example : (addToLinkTable [] mod_core).head? = some (id_core, mod_core) := by
  simp [addToLinkTable, mod_core, id_core]

/-- Symbol mangling produces the expected format. -/
example : mangleSymbol { hash := "hash1", version := 2 } "myFunc" = "hash1_v2_myFunc" := rfl

/-- computeModuleHash returns the input string. -/
example : computeModuleHash "source code" = "source code" := rfl

/-- Loading from a non-existent file returns none. -/
example : loadModuleFromFile "/nonexistent/path" = none := rfl

/-- Resolving from an empty link table returns none. -/
example : resolveModule [] { hash := "x", version := 0 } = none := by
  simp [resolveModule, List.find?]

/-- Searching an empty registry by name returns an empty list. -/
example : searchRegistryByName [] "anything" = [] := rfl

/-- Searching an empty registry by tag returns an empty list. -/
example : searchRegistryByTag [] "anything" = [] := rfl

end Morph.Specs.ModuleSystem
