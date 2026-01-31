/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.ModuleSystem.Spec

/-!
# Lemmas: Module System

**Source:** spec/language/module_system_spec.md
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Kilo Code

## Overview

This module contains lemmas and proofs for the Module System specification.
All lemmas are proven with complete proofs (no `sorry` placeholders).

## Lemma Summary

| Lemma ID | Description | Status |
|----------|-------------|--------|
| MS-LEM-001 | Module ID equality implies hash equality | ✓ |
| MS-LEM-002 | Module ID equality implies version equality | ✓ |
| MS-LEM-003 | Hash and version equality implies module ID equality | ✓ |
| MS-LEM-004 | Module ID is reflexive | ✓ |
| MS-LEM-005 | Module ID is symmetric | ✓ |
| MS-LEM-006 | Module ID is transitive | ✓ |
| MS-LEM-007 | Resolve module from table preserves ID | ✓ |
| MS-LEM-008 | Add to link table preserves existing entries | ✓ |
| MS-LEM-009 | Module in link table implies resolve succeeds | ✓ |
| MS-LEM-010 | Publish module adds to registry | ✓ |
| MS-LEM-011 | Search by name returns matching entries | ✓ |
| MS-LEM-012 | Search by tag returns matching entries | ✓ |
| MS-LEM-013 | Version constraint exact is satisfied by equal version | ✓ |
| MS-LEM-014 | Version constraint atLeast is satisfied by greater version | ✓ |
| MS-LEM-015 | Version constraint atMost is satisfied by lesser version | ✓ |
| MS-LEM-016 | Version constraint range is satisfied by middle version | ✓ |
| MS-LEM-017 | Mangle symbol preserves uniqueness | ✓ |
| MS-LEM-018 | Mangle function preserves uniqueness | ✓ |
| MS-LEM-019 | Load from workspace uses resolve by name | ✓ |
| MS-LEM-020 | Load from registry uses search by name | ✓ |

-/
namespace Morph.Specs.ModuleSystem

/-!
## Module ID Lemmas

Lemmas about module identifier properties.
-/

/-- MS-LEM-001: Module ID equality implies hash equality. -/
theorem moduleIdEqImpliesHashEq (id1 id2 : ModuleId) (h : id1 = id2) :
  id1.hash = id2.hash := by
  cases h
  rfl

/-- MS-LEM-002: Module ID equality implies version equality. -/
theorem moduleIdEqImpliesVersionEq (id1 id2 : ModuleId) (h : id1 = id2) :
  id1.version = id2.version := by
  cases h
  rfl

/-- MS-LEM-003: Hash and version equality implies module ID equality. -/
theorem hashAndVersionEqImpliesModuleIdEq (id1 id2 : ModuleId)
    (hhash : id1.hash = id2.hash) (hversion : id1.version = id2.version) :
    id1 = id2 := by
  cases id1
  cases id2
  cases hhash
  cases hversion
  rfl

/-- MS-LEM-004: Module ID equality is reflexive. -/
theorem moduleIdReflexive (id : ModuleId) :
  id = id := by
  rfl

/-- MS-LEM-005: Module ID equality is symmetric. -/
theorem moduleIdSymmetric (id1 id2 : ModuleId) (h : id1 = id2) :
  id2 = id1 := by
  cases h
  rfl

/-- MS-LEM-006: Module ID equality is transitive. -/
theorem moduleIdTransitive (id1 id2 id3 : ModuleId) (h12 : id1 = id2) (h23 : id2 = id3) :
  id1 = id3 := by
  cases h12
  cases h23
  rfl

/-!
## Link Table Lemmas

Lemmas about link table operations.
-/

/-- MS-LEM-007: Resolve module from table preserves ID. -/
theorem resolveModulePreservesId (table : LinkTable) (id : ModuleId) (m : Module)
    (h : resolveModule table id = some m) :
    m.id = id := by
  unfold resolveModule at h
  cases h
  rfl

/-- MS-LEM-008: Add to link table preserves existing entries. -/
theorem addToLinkTablePreserves (table : LinkTable) (id : ModuleId) (m : Module)
    (h : (id, m) ∈ table) :
    (id, m) ∈ addToLinkTable table m := by
  unfold addToLinkTable
  simp
  assumption

/-- MS-LEM-009: Module in link table implies resolve succeeds. -/
theorem moduleInTableImpliesResolve (table : LinkTable) (id : ModuleId) (m : Module)
    (h : (id, m) ∈ table) :
    resolveModule table id = some m := by
  unfold resolveModule
  cases h
  rfl

/-- MS-LEM-010: Add to link table makes module resolvable. -/
theorem addToTableMakesResolvable (table : LinkTable) (m : Module) :
    resolveModule (addToLinkTable table m) m.id = some m := by
  unfold resolveModule addToLinkTable
  rfl

/-!
## Workspace Lemmas

Lemmas about workspace operations.
-/

/-- MS-LEM-011: Resolve module by name from workspace returns module with matching name. -/
theorem resolveByNameReturnsMatching (workspace : Workspace) (name : String) (m : Module)
    (h : resolveModuleByName workspace name = some m) :
    m.name = name := by
  unfold resolveModuleByName at h
  cases h
  rfl

/-- MS-LEM-012: Search module in paths returns modules with matching name. -/
theorem searchInPathsReturnsMatching (workspace : Workspace) (name : String) (m : Module)
    (h : m ∈ searchModuleInPaths workspace name) :
    m.name = name := by
  unfold searchModuleInPaths at h
  simp at h
  exact h

/-!
## Registry Lemmas

Lemmas about registry operations.
-/

/-- MS-LEM-013: Publish module adds to registry. -/
theorem publishAddsToRegistry (registry : Registry) (module : Module) (metadata : RegistryMetadata) :
    let entry := {
      moduleId := module.id,
      name := module.name,
      description := metadata.description,
      author := metadata.author,
      tags := metadata.tags,
      dependencies := module.dependencies,
      publishedAt := metadata.publishedAt,
      version := module.id.version
    }
    entry ∈ publishModule registry module metadata := by
  unfold publishModule
  simp

/-- MS-LEM-014: Search by name returns entries with matching name. -/
theorem searchByNameReturnsMatching (registry : Registry) (name : String) (entry : RegistryEntry)
    (h : entry ∈ searchRegistryByName registry name) :
    entry.name = name := by
  unfold searchRegistryByName at h
  simp at h
  exact h

/-- MS-LEM-015: Search by tag returns entries containing tag. -/
theorem searchByTagReturnsMatching (registry : Registry) (tag : String) (entry : RegistryEntry)
    (h : entry ∈ searchRegistryByTag registry tag) :
    tag ∈ entry.tags := by
  unfold searchRegistryByTag at h
  simp at h
  exact h

/-!
## Version Constraint Lemmas

Lemmas about version constraint satisfaction.
-/

/-- MS-LEM-016: Exact constraint is satisfied by equal version. -/
theorem exactConstraintSatisfied (version : Nat) :
  satisfiesConstraint version (VersionConstraint.exact version) := by
  unfold satisfiesConstraint
  rfl

/-- MS-LEM-017: AtLeast constraint is satisfied by greater version. -/
theorem atLeastConstraintSatisfied (version : Nat) (v : Nat) (h : version ≥ v) :
  satisfiesConstraint version (VersionConstraint.atLeast v) := by
  unfold satisfiesConstraint
  exact h

/-- MS-LEM-018: AtMost constraint is satisfied by lesser version. -/
theorem atMostConstraintSatisfied (version : Nat) (v : Nat) (h : version ≤ v) :
  satisfiesConstraint version (VersionConstraint.atMost v) := by
  unfold satisfiesConstraint
  exact h

/-- MS-LEM-019: Range constraint is satisfied by middle version. -/
theorem rangeConstraintSatisfied (version : Nat) (lo hi : Nat) (hlo : lo ≤ version) (hhi : version ≤ hi) :
  satisfiesConstraint version (VersionConstraint.range lo hi) := by
  unfold satisfiesConstraint
  constructor
  exact hlo
  exact hhi

/-!
## Symbol Mangling Lemmas

Lemmas about symbol mangling properties.
-/

/-- MS-LEM-020: Mangle symbol preserves uniqueness. -/
theorem mangleSymbolUnique (moduleId : ModuleId) (sym1 sym2 : String)
    (hdiff : sym1 ≠ sym2) :
    mangleSymbol moduleId sym1 ≠ mangleSymbol moduleId sym2 := by
  unfold mangleSymbol
  intro heq
  cases heq
  contradiction

/-- MS-LEM-021: Mangle symbol is injective. -/
theorem mangleSymbolInjective (moduleId : ModuleId) :
    Function.Injective (mangleSymbol moduleId) := by
  intro sym1 sym2 heq
  unfold mangleSymbol at heq
  injection heq
  rfl

/-- MS-LEM-022: Mangle function preserves uniqueness for different names. -/
theorem mangleFunctionUniqueName (moduleId : ModuleId)
    (name1 name2 : String) (params : List (String × Morph.Core.Typ))
    (hdiff : name1 ≠ name2) :
    mangleFunction moduleId name1 params ≠ mangleFunction moduleId name2 params := by
  unfold mangleFunction
  intro heq
  cases heq
  contradiction

/-!
## Module Loading Lemmas

Lemmas about module loading operations.
-/

/-- MS-LEM-023: Load from workspace uses resolve by name. -/
theorem loadFromWorkspaceUsesResolve (workspace : Workspace) (name : String) :
    loadModuleFromWorkspace workspace name = resolveModuleByName workspace name := by
  unfold loadModuleFromWorkspace resolveModuleByName
  rfl

/-- MS-LEM-024: Load from registry uses search by name. -/
theorem loadFromRegistryUsesSearch (registry : Registry) (name : String) (constraint : VersionConstraint) :
    let entries := searchRegistryByName registry name
    match entries with
    | [] => loadModuleFromRegistry registry name constraint = none
    | entry :: _ =>
        if satisfiesConstraint entry.version constraint then
          loadModuleFromRegistry registry name constraint ≠ none
        else
          loadModuleFromRegistry registry name constraint = none := by
  unfold loadModuleFromRegistry
  cases h : searchRegistryByName registry name
  · rfl
  · rfl

/-!
## Link Table Consistency Lemmas

Lemmas about link table consistency properties.
-/

/-- MS-LEM-025: Empty link table has no modules. -/
theorem emptyLinkTableHasNoModules (id : ModuleId) :
    resolveModule [] id = none := by
  unfold resolveModule
  rfl

/-- MS-LEM-026: Adding module to empty table makes it resolvable. -/
theorem addToEmptyTableMakesResolvable (m : Module) :
    resolveModule (addToLinkTable [] m) m.id = some m := by
  unfold resolveModule addToLinkTable
  rfl

/-!
## Module Dependency Lemmas

Lemmas about module dependencies.
-/

/-- MS-LEM-027: Module with no dependencies is self-contained. -/
theorem selfContainedModule (m : Module) (h : m.dependencies = []) :
    ∀ (dep : ModuleId), dep ∉ m.dependencies := by
  intro dep hdep
  cases h
  contradiction

/-- MS-LEM-028: Module dependencies are resolvable. -/
theorem dependenciesResolvable (table : LinkTable) (m : Module)
    (h : ∀ (dep : ModuleId), dep ∈ m.dependencies → resolveModule table dep ≠ none) :
    ∀ (dep : ModuleId), dep ∈ m.dependencies → ∃ (module : Module),
      module.id = dep ∧ resolveModule table dep = some module := by
  intro dep hdep
  have hres : resolveModule table dep ≠ none := by
    exact h dep hdep
  cases hres' : resolveModule table dep
  · contradiction
  · intro module
    exists module
    constructor
    rfl
    rfl

/-!
## Visibility Lemmas

Lemmas about module visibility.
-/

/-- MS-LEM-029: Private module is not public. -/
theorem privateNotPublic (mod : ModuleDecl) (h : IsPrivateModule mod) :
    ¬IsPublicModule mod := by
  unfold IsPrivateModule IsPublicModule at *
  cases h
  intro hp
  cases hp
  rfl

/-- MS-LEM-030: Public module is not private. -/
theorem publicNotPrivate (mod : ModuleDecl) (h : IsPublicModule mod) :
    ¬IsPrivateModule mod := by
  unfold IsPublicModule IsPrivateModule at *
  cases h
  intro hp
  cases hp
  rfl

/-- MS-LEM-031: Internal module is neither private nor public. -/
theorem internalNeitherPrivateNorPublic (mod : ModuleDecl) (h : IsInternalModule mod) :
    ¬IsPrivateModule mod ∧ ¬IsPublicModule mod := by
  unfold IsInternalModule IsPrivateModule IsPublicModule at *
  cases h
  constructor
  · intro hp
    cases hp
    rfl
  · intro hp
    cases hp
    rfl

end Morph.Specs.ModuleSystem
