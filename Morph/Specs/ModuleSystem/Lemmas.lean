/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ModuleSystem.Spec

namespace Morph.Specs.ModuleSystem

/-!
## Lemmas

Lemmas and auxiliary results for the ModuleSystem specification.
-/

/-! ### Link Table Properties -/

theorem moduleInLinkTable_empty (id : ModuleId) :
    moduleInLinkTable [] id = false := rfl

theorem resolveModule_empty (id : ModuleId) :
    resolveModule [] id = none := rfl

theorem addToLinkTable_head (table : LinkTable) (mod : Module) :
    (addToLinkTable table mod).head? = some (mod.id, mod) := rfl

/-! ### Registry Search Properties -/

theorem searchRegistryByName_empty (name : String) :
    searchRegistryByName [] name = [] := rfl

theorem searchRegistryByTag_empty (tag : String) :
    searchRegistryByTag [] tag = [] := rfl

/-! ### Visibility Exhaustiveness -/

theorem visibility_cases (v : Visibility) :
    v = .visPrivate ∨ v = .visPublic ∨ v = .visInternal := by
  cases v <;> simp

/-! ### Version Constraint Properties -/

theorem satisfiesConstraint_exact_refl (v : Nat) :
    satisfiesConstraint v (.exact v) = true := by
  unfold satisfiesConstraint; simp

example : satisfiesConstraint 2 (.atLeast 2) = true := by native_decide

example : satisfiesConstraint 2 (.atMost 2) = true := by native_decide

example : satisfiesConstraint 3 (.atLeast 2) = true := by native_decide

example : satisfiesConstraint 1 (.atMost 2) = true := by native_decide

example : satisfiesConstraint 2 (.range 1 3) = true := rfl

example : satisfiesConstraint 0 (.range 1 3) = false := rfl

example : satisfiesConstraint 4 (.range 1 3) = false := rfl

/-! ### Module Id Properties -/

theorem createModuleId_hash (content : String) (version : Nat) :
    (createModuleId content version).hash = content := rfl

theorem createModuleId_version (content : String) (version : Nat) :
    (createModuleId content version).version = version := rfl

/-! ### Symbol Mangling -/

example : mangleSymbol { hash := "h1", version := 2 } "f" = "h1_v2_f" := rfl

/-! ### VersionConstraint Exhaustiveness -/

theorem versionConstraint_cases (c : VersionConstraint) :
    match c with
    | .exact _ => True
    | .atLeast _ => True
    | .atMost _ => True
    | .range _ _ => True := by
  cases c <;> simp

end Morph.Specs.ModuleSystem
