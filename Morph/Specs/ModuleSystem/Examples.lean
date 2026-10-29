/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ModuleSystem.Lemmas

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

/-! ## Loop 70: well-formed tables, workspaces, and mangling

A concrete two-module workspace (`core` with no dependencies, `utils`
depending on `core`), built and verified with the loop-70 theorems. -/

/-- `core` alone: a one-entry table is well formed. -/
def table1 : LinkTable := addToLinkTable [] mod_core

theorem table1_wf : WellFormed table1 := by
  refine wellFormed_add [] mod_core ?_ ?_ ?_
  · simp
  · simp [mod_core]
  · exact ⟨by simp [keysMatch], by simp [keyNodup], by simp [depsResolved]⟩

/-- Adding `utils`, which depends on `core`, keeps the table well formed. -/
def table2 : LinkTable := addToLinkTable table1 mod_utils

theorem id_utils_ne_id_core : id_utils ≠ id_core := by decide

theorem table2_wf : WellFormed table2 := by
  refine wellFormed_add table1 mod_utils ?_ ?_ table1_wf
  · intro hmem
    unfold table1 addToLinkTable at hmem
    simp only [List.map_cons, List.mem_cons, List.map_nil, List.not_mem_nil,
      or_false] at hmem
    exact id_utils_ne_id_core hmem
  · intro d hd
    simp [mod_utils] at hd
    subst hd
    simp [moduleInLinkTable, addToLinkTable, table1, id_core]
    decide

/-- `utils` is in the table, so its dependency on `core` resolves. -/
theorem mem_table2_utils : mod_utils ∈ table2.map Prod.snd := by
  unfold table2 addToLinkTable
  exact List.mem_cons_self

example : (resolveModule table2 id_core).isSome = true :=
  wellFormed_deps_resolve table2_wf (m := mod_utils) mem_table2_utils
    (by simp [mod_utils])

/-- `core` is a member of the table, under its own id. -/
theorem mem_table2_core : (id_core, mod_core) ∈ table2 := by
  unfold table2 table1 addToLinkTable
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- `core` resolves to exactly the module that was stored. -/
example : resolveModule table2 id_core = some mod_core :=
  resolveModule_eq_some_of_mem_of_keyNodup table2_wf.2.1 mem_table2_core

/-- Name resolution finds the stored module. -/
def wsConfig : WorkspaceConfig :=
  { searchPaths := ["."], excludePatterns := [], maxDepth := 8 }

def ws : Workspace :=
  { root := "/home/dev/app", modules := table2, config := wsConfig }

theorem ws_namesNodup : namesNodup ws.modules := by
  unfold namesNodup ws table2
  simp [mod_utils]
  decide

theorem ws_wf : workspaceWellFormed ws :=
  ⟨by decide, by decide, table2_wf, ws_namesNodup⟩

example : resolveModuleByName ws "core" = some mod_core :=
  resolveModuleByName_eq_some_of_mem_of_namesNodup (w := ws) (m := mod_core)
    table2_wf.1 (workspace_namesNodup ws_wf) mem_table2_core

/-- Mangling the structured way: the components stay recoverable. -/
example : mangleName id_core "f" = { hash := "abc123", version := 1, symbol := "f" } := rfl

example : renderMangled (mangleName id_core "f") = "abc123_v1_f" := rfl

/-- But the textual form collides: these two `(hash, version, symbol)` triples
render to the same string. -/
example : mangleSymbol { hash := "a", version := 1 } "b_v2_c" =
    mangleSymbol { hash := "a_v1_b", version := 2 } "c" := by native_decide

end Morph.Specs.ModuleSystem
