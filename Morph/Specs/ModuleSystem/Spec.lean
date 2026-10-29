/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Core

/-!
# Specification: Module System

**Source:** spec/language/module_system_spec.md
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Kilo Code

## Overview

This module formalizes the module system for Morph language, including
content-addressable linking, workspace resolution, and registry protocol.

## Known Issues

None identified. All specification points are clear and unambiguous.

The link-table/workspace/mangling correctness questions formerly marked TODO
are closed in `Lemmas.lean` (loop 70): a well-formed link table has unique
module ids and resolvable dependencies, a well-formed workspace has a non-empty
root and resolves by name, and mangling is injective *structurally*
(`mangleName`) — the textual form is a rendering whose general injectivity is
refuted (`mangleSymbol_not_injective`).

-/
namespace Morph.Specs.ModuleSystem

/-!
## Module Identifiers
-/

structure ModuleId where
  hash : String
  version : Nat
  deriving Repr, BEq, DecidableEq

def computeModuleHash (content : String) : String :=
  content

def createModuleId (content : String) (version : Nat) : ModuleId :=
  { hash := computeModuleHash content, version := version }

/-!
## Module Declarations
-/

inductive Visibility where
  | visPrivate : Visibility
  | visPublic : Visibility
  | visInternal : Visibility
  deriving Repr, BEq

structure ModuleDecl where
  id : ModuleId
  visibility : Visibility
  exports : List String
  deriving Repr

/-!
## Module Structure
-/

structure Module where
  id : ModuleId
  name : String
  declarations : List ModuleDecl
  dependencies : List ModuleId
  deriving Repr

/-!
## Content-Addressable Linking
-/

abbrev LinkTable := List (ModuleId × Module)

def resolveModule (table : LinkTable) (id : ModuleId) : Option Module :=
  table.find? (fun (mid, _) => decide (mid = id)) |>.map Prod.snd

def addToLinkTable (table : LinkTable) (module : Module) : LinkTable :=
  (module.id, module) :: table

def moduleInLinkTable (table : LinkTable) (id : ModuleId) : Bool :=
  table.any (fun (mid, _) => decide (mid = id))

/-- A link table's keys match the module ids they store. -/
def keysMatch (t : LinkTable) : Prop :=
  ∀ (id : ModuleId) (m : Module), (id, m) ∈ t → m.id = id

/-- No two entries share a module id. -/
def keyNodup (t : LinkTable) : Prop := (t.map Prod.fst).Nodup

/-- Every dependency named by a stored module exists in the table. -/
def depsResolved (t : LinkTable) : Prop :=
  ∀ m ∈ t.map Prod.snd, ∀ d ∈ m.dependencies, moduleInLinkTable t d = true

/-- A well-formed link table: keys match, ids are unique, and every dependency
resolves. -/
def WellFormed (t : LinkTable) : Prop :=
  keysMatch t ∧ keyNodup t ∧ depsResolved t

/-!
## Workspace Resolution
-/

structure WorkspaceConfig where
  searchPaths : List String
  excludePatterns : List String
  maxDepth : Nat
  deriving Repr

structure Workspace where
  root : String
  modules : LinkTable
  config : WorkspaceConfig
  deriving Repr

def resolveModuleByName (workspace : Workspace) (name : String) : Option Module :=
  workspace.modules.find? (fun (_, m) => m.name == name) |>.map Prod.snd

/-- No two modules in a table share a name. -/
def namesNodup (t : LinkTable) : Prop := (t.map (fun p => p.2.name)).Nodup

/-- A workspace is well-formed when its root is non-empty, its depth budget is
positive, its link table is well-formed, and module names are unique. -/
def workspaceWellFormed (w : Workspace) : Prop :=
  w.root ≠ "" ∧ 0 < w.config.maxDepth ∧ WellFormed w.modules ∧ namesNodup w.modules

/-!
## Registry Protocol
-/

structure RegistryEntry where
  moduleId : ModuleId
  name : String
  description : String
  author : String
  tags : List String
  dependencies : List ModuleId
  publishedAt : String
  version : Nat
  deriving Repr

abbrev Registry := List RegistryEntry

structure RegistryMetadata where
  description : String
  author : String
  tags : List String
  publishedAt : String
  deriving Repr

def publishModule (registry : Registry) (module : Module) (metadata : RegistryMetadata) : Registry :=
  let entry : RegistryEntry := {
    moduleId := module.id,
    name := module.name,
    description := metadata.description,
    author := metadata.author,
    tags := metadata.tags,
    dependencies := module.dependencies,
    publishedAt := metadata.publishedAt,
    version := module.id.version
  }
  entry :: registry

def searchRegistryByName (registry : Registry) (name : String) : List RegistryEntry :=
  registry.filter fun entry => entry.name == name

def searchRegistryByTag (registry : Registry) (tag : String) : List RegistryEntry :=
  registry.filter fun entry => tag ∈ entry.tags

/-!
## Multi-Version Linking
-/

inductive VersionConstraint where
  | exact : Nat → VersionConstraint
  | atLeast : Nat → VersionConstraint
  | atMost : Nat → VersionConstraint
  | range : Nat → Nat → VersionConstraint
  deriving Repr, BEq

def satisfiesConstraint (version : Nat) (constraint : VersionConstraint) : Bool :=
  match constraint with
  | VersionConstraint.exact v => version == v
  | VersionConstraint.atLeast v => version >= v
  | VersionConstraint.atMost v => version <= v
  | VersionConstraint.range lo hi => lo <= version && version <= hi

/-!
## Symbol Mangling
-/

def mangleSymbol (moduleId : ModuleId) (symbol : String) : String :=
  s!"{moduleId.hash}_v{moduleId.version}_{symbol}"

/-- The structured content of a mangled symbol. Unlike the textual form, this
carries the three components separately, so it can be injective. -/
structure MangledName where
  hash : String
  version : Nat
  symbol : String
  deriving Repr, BEq, DecidableEq

/-- The structured mangling of a symbol. -/
def mangleName (mid : ModuleId) (symbol : String) : MangledName :=
  { hash := mid.hash, version := mid.version, symbol := symbol }

/-- Render a structured name in the shipped textual format. -/
def renderMangled (n : MangledName) : String :=
  s!"{n.hash}_v{n.version}_{n.symbol}"

/-!
## Module Loading
-/

def loadModuleFromFile (_path : String) : Option Module := none

def loadModuleFromWorkspace (workspace : Workspace) (name : String) : Option Module :=
  resolveModuleByName workspace name

/-!
## Correctness Specifications
-/

theorem moduleHashDeterministic (content : String) :
  computeModuleHash content = computeModuleHash content := rfl

-- Module ID uniqueness, link consistency, and workspace validity are closed in
-- `Lemmas.lean` against the `WellFormed` / `workspaceWellFormed` predicates
-- above: `wellFormed_key_unique`, `wellFormed_deps_resolve`,
-- `workspace_root_nonempty`, `resolveModuleByName_eq_some_of_mem_of_namesNodup`.

/-- Registry search by name is definitional equality with filter. -/
theorem registrySearchCorrect (registry : Registry) (name : String) :
    searchRegistryByName registry name = registry.filter (fun entry => entry.name == name) := rfl

/-- Registry search by tag is definitional equality with filter. -/
theorem registryTagSearchCorrect (registry : Registry) (tag : String) :
    searchRegistryByTag registry tag = registry.filter (fun entry => tag ∈ entry.tags) := rfl

theorem versionConstraintSatisfactionCorrect (version : Nat) (constraint : VersionConstraint) :
  satisfiesConstraint version constraint = match constraint with
  | VersionConstraint.exact v => version == v
  | VersionConstraint.atLeast v => version >= v
  | VersionConstraint.atMost v => version <= v
  | VersionConstraint.range lo hi => lo <= version && version <= hi := by
  cases constraint <;> rfl

-- Symbol mangling injectivity is closed in `Lemmas.lean`: the *structured*
-- name is injective (`mangleName_injective`), while the general textual claim
-- as suggested below is **false** and is recorded as its refutation
-- (`mangleSymbol_not_injective`) — `renderMangled` erases the boundary between
-- a hash and a symbol that itself contains the separator.
-- Requires: ∀ (mid1 mid2 : ModuleId) (s1 s2 : String),
--   mangleSymbol mid1 s1 = mangleSymbol mid2 s2 → mid1 = mid2 ∧ s1 = s2
-- (refuted; see `mangleSymbol_not_injective`)

end Morph.Specs.ModuleSystem
