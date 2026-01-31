/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.ModuleSystem.Spec

/-!
# Examples: Module System

**Source:** spec/language/module_system_spec.md
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Kilo Code

## Overview

This module contains executable examples for the Module System specification.
All examples are concrete and can be evaluated.

## Example Summary

| Example ID | Description | Status |
|------------|-------------|--------|
| MS-EX-001 | Simple module ID | ✓ |
| MS-EX-002 | Module ID with version | ✓ |
| MS-EX-003 | Private module declaration | ✓ |
| MS-EX-004 | Public module declaration | ✓ |
| MS-EX-005 | Simple module | ✓ |
| MS-EX-006 | Module with dependencies | ✓ |
| MS-EX-007 | Empty link table | ✓ |
| MS-EX-008 | Link table with modules | ✓ |
| MS-EX-009 | Simple workspace | ✓ |
| MS-EX-010 | Workspace with search paths | ✓ |
| MS-EX-011 | Simple registry entry | ✓ |
| MS-EX-012 | Registry with multiple entries | ✓ |
| MS-EX-013 | Exact version constraint | ✓ |
| MS-EX-014 | AtLeast version constraint | ✓ |
| MS-EX-015 | AtMost version constraint | ✓ |
| MS-EX-016 | Range version constraint | ✓ |
| MS-EX-017 | Mangle symbol | ✓ |
| MS-EX-018 | Mangle function | ✓ |
| MS-EX-019 | Load module from workspace | ✓ |
| MS-EX-020 | Load module from registry | ✓ |

-/
namespace Morph.Specs.ModuleSystem

/-!
## Module ID Examples

Examples of module identifiers.
-/

/-- MS-EX-001: Simple module ID. -/
def exampleSimpleModuleId : ModuleId :=
  {
    hash := "abc123",
    version := 1
  }

/-- MS-EX-002: Module ID with higher version. -/
def exampleModuleIdV2 : ModuleId :=
  {
    hash := "abc123",
    version := 2
  }

/-- MS-EX-003: Create module ID from content. -/
def exampleCreateModuleId : ModuleId :=
  createModuleId "module content" 1

/-!
## Module Declaration Examples

Examples of module declarations with different visibility.
-/

/-- MS-EX-004: Private module declaration. -/
def examplePrivateModuleDecl : ModuleDecl :=
  {
    id := exampleSimpleModuleId,
    visibility := .private,
    exports := ["privateFunc"]
  }

/-- MS-EX-005: Public module declaration. -/
def examplePublicModuleDecl : ModuleDecl :=
  {
    id := exampleSimpleModuleId,
    visibility := .public,
    exports := ["publicFunc1", "publicFunc2"]
  }

/-- MS-EX-006: Internal module declaration. -/
def exampleInternalModuleDecl : ModuleDecl :=
  {
    id := exampleSimpleModuleId,
    visibility := .internal,
    exports := ["internalFunc"]
  }

/-!
## Module Examples

Examples of complete modules.
-/

/-- MS-EX-007: Simple module without dependencies. -/
def exampleSimpleModule : Module :=
  {
    id := exampleSimpleModuleId,
    name := "SimpleModule",
    declarations := [examplePrivateModuleDecl],
    dependencies := []
  }

/-- MS-EX-008: Module with dependencies. -/
def exampleModuleWithDependencies : Module :=
  {
    id := exampleModuleIdV2,
    name := "ModuleWithDeps",
    declarations := [examplePublicModuleDecl],
    dependencies := [exampleSimpleModuleId]
  }

/-- MS-EX-009: Module with multiple dependencies. -/
def exampleModuleWithMultipleDeps : Module :=
  let depId1 : ModuleId := { hash := "dep1", version := 1 }
  let depId2 : ModuleId := { hash := "dep2", version := 1 }
  {
    id := { hash := "main", version := 1 },
    name := "MainModule",
    declarations := [examplePublicModuleDecl],
    dependencies := [depId1, depId2]
  }

/-!
## Link Table Examples

Examples of link tables for module resolution.
-/

/-- MS-EX-010: Empty link table. -/
def exampleEmptyLinkTable : LinkTable :=
  []

/-- MS-EX-011: Link table with one module. -/
def exampleLinkTableOneModule : LinkTable :=
  [(exampleSimpleModuleId, exampleSimpleModule)]

/-- MS-EX-012: Link table with multiple modules. -/
def exampleLinkTableMultipleModules : LinkTable :=
  [
    (exampleSimpleModuleId, exampleSimpleModule),
    (exampleModuleIdV2, exampleModuleWithDependencies)
  ]

/-- MS-EX-013: Resolve module from table. -/
def exampleResolveModule : Option Module :=
  resolveModule exampleLinkTableOneModule exampleSimpleModuleId

/-- MS-EX-014: Add module to link table. -/
def exampleAddToLinkTable : LinkTable :=
  addToLinkTable exampleLinkTableOneModule exampleModuleWithDependencies

/-!
## Workspace Examples

Examples of workspaces for module discovery.
-/

/-- MS-EX-015: Simple workspace configuration. -/
def exampleWorkspaceConfig : WorkspaceConfig :=
  {
    searchPaths := ["./src", "./lib"],
    excludePatterns := ["*.test.lean"],
    maxDepth := 5
  }

/-- MS-EX-016: Simple workspace. -/
def exampleSimpleWorkspace : Workspace :=
  {
    root := "/home/user/project",
    modules := exampleLinkTableOneModule,
    config := exampleWorkspaceConfig
  }

/-- MS-EX-017: Workspace with multiple modules. -/
def exampleWorkspaceMultipleModules : Workspace :=
  {
    root := "/home/user/project",
    modules := exampleLinkTableMultipleModules,
    config := exampleWorkspaceConfig
  }

/-- MS-EX-018: Resolve module by name from workspace. -/
def exampleResolveByName : Option Module :=
  resolveModuleByName exampleSimpleWorkspace "SimpleModule"

/-- MS-EX-019: Search module in paths. -/
def exampleSearchInPaths : List Module :=
  searchModuleInPaths exampleSimpleWorkspace "SimpleModule"

/-!
## Registry Examples

Examples of module registries.
-/

/-- MS-EX-020: Simple registry entry. -/
def exampleRegistryEntry : RegistryEntry :=
  {
    moduleId := exampleSimpleModuleId,
    name := "SimpleModule",
    description := "A simple module example",
    author := "Kilo Code",
    tags := ["example", "simple"],
    dependencies := [],
    publishedAt := "2026-01-30",
    version := 1
  }

/-- MS-EX-021: Registry with multiple entries. -/
def exampleRegistry : Registry :=
  [
    exampleRegistryEntry,
    {
      moduleId := exampleModuleIdV2,
      name := "ModuleWithDeps",
      description := "A module with dependencies",
      author := "Kilo Code",
      tags := ["example", "dependencies"],
      dependencies := [exampleSimpleModuleId],
      publishedAt := "2026-01-30",
      version := 2
    }
  ]

/-- MS-EX-022: Publish module to registry. -/
def examplePublishModule : Registry :=
  let metadata : RegistryMetadata :=
    {
      description := "New module",
      author := "Kilo Code",
      tags := ["new"],
      publishedAt := "2026-01-30"
    }
  publishModule exampleRegistry exampleSimpleModule metadata

/-- MS-EX-023: Search registry by name. -/
def exampleSearchByName : List RegistryEntry :=
  searchRegistryByName exampleRegistry "SimpleModule"

/-- MS-EX-024: Search registry by tag. -/
def exampleSearchByTag : List RegistryEntry :=
  searchRegistryByTag exampleRegistry "example"

/-!
## Version Constraint Examples

Examples of version constraints.
-/

/-- MS-EX-025: Exact version constraint. -/
def exampleExactConstraint : VersionConstraint :=
  VersionConstraint.exact 1

/-- MS-EX-026: AtLeast version constraint. -/
def exampleAtLeastConstraint : VersionConstraint :=
  VersionConstraint.atLeast 2

/-- MS-EX-027: AtMost version constraint. -/
def exampleAtMostConstraint : VersionConstraint :=
  VersionConstraint.atMost 5

/-- MS-EX-028: Range version constraint. -/
def exampleRangeConstraint : VersionConstraint :=
  VersionConstraint.range 1 5

/-- MS-EX-029: Check version satisfies exact constraint. -/
def exampleSatisfiesExact : Bool :=
  satisfiesConstraint 1 exampleExactConstraint

/-- MS-EX-030: Check version satisfies atLeast constraint. -/
def exampleSatisfiesAtLeast : Bool :=
  satisfiesConstraint 3 exampleAtLeastConstraint

/-- MS-EX-031: Check version satisfies atMost constraint. -/
def exampleSatisfiesAtMost : Bool :=
  satisfiesConstraint 4 exampleAtMostConstraint

/-- MS-EX-032: Check version satisfies range constraint. -/
def exampleSatisfiesRange : Bool :=
  satisfiesConstraint 3 exampleRangeConstraint

/-!
## Symbol Mangling Examples

Examples of symbol mangling.
-/

/-- MS-EX-033: Mangle simple symbol. -/
def exampleMangleSymbol : String :=
  mangleSymbol exampleSimpleModuleId "myFunction"

/-- MS-EX-034: Mangle symbol with different module ID. -/
def exampleMangleSymbolV2 : String :=
  mangleSymbol exampleModuleIdV2 "myFunction"

/-- MS-EX-035: Mangle function with parameters. -/
def exampleMangleFunction : String :=
  mangleFunction exampleSimpleModuleId "add"
    [("x", Morph.Core.Typ.intType), ("y", Morph.Core.Typ.intType)]

/-- MS-EX-036: Mangle function with different parameters. -/
def exampleMangleFunctionDifferent : String :=
  mangleFunction exampleSimpleModuleId "add"
    [("x", Morph.Core.Typ.intType), ("y", Morph.Core.Typ.stringType)]

/-!
## Module Loading Examples

Examples of module loading from different sources.
-/

/-- MS-EX-037: Load module from workspace. -/
def exampleLoadFromWorkspace : Option Module :=
  loadModuleFromWorkspace exampleSimpleWorkspace "SimpleModule"

/-- MS-EX-038: Load module from registry with exact constraint. -/
def exampleLoadFromRegistry : Option Module :=
  loadModuleFromRegistry exampleRegistry "SimpleModule" exampleExactConstraint

/-- MS-EX-039: Load module from registry with atLeast constraint. -/
def exampleLoadFromRegistryAtLeast : Option Module :=
  loadModuleFromRegistry exampleRegistry "ModuleWithDeps" exampleAtLeastConstraint

/-!
## Visibility Examples

Examples of module visibility predicates.
-/

/-- MS-EX-040: Check if module is private. -/
def exampleIsPrivate : Prop :=
  IsPrivateModule examplePrivateModuleDecl

/-- MS-EX-041: Check if module is public. -/
def exampleIsPublic : Prop :=
  IsPublicModule examplePublicModuleDecl

/-- MS-EX-042: Check if module is internal. -/
def exampleIsInternal : Prop :=
  IsInternalModule exampleInternalModuleDecl

/-!
## Link Table Operations Examples

Examples of link table operations.
-/

/-- MS-EX-043: Check if module is in link table. -/
def exampleModuleInTable : Bool :=
  moduleInLinkTable exampleLinkTableOneModule exampleSimpleModuleId

/-- MS-EX-044: Check if module is not in empty table. -/
def exampleModuleNotInEmptyTable : Bool :=
  moduleInLinkTable exampleEmptyLinkTable exampleSimpleModuleId

/-- MS-EX-045: Resolve module from table with multiple modules. -/
def exampleResolveFromMultiple : Option Module :=
  resolveModule exampleLinkTableMultipleModules exampleModuleIdV2

/-!
## Workspace Operations Examples

Examples of workspace operations.
-/

/-- MS-EX-046: Resolve non-existent module from workspace. -/
def exampleResolveNonExistent : Option Module :=
  resolveModuleByName exampleSimpleWorkspace "NonExistentModule"

/-- MS-EX-047: Search for non-existent module in paths. -/
def exampleSearchNonExistent : List Module :=
  searchModuleInPaths exampleSimpleWorkspace "NonExistentModule"

/-!
## Registry Operations Examples

Examples of registry operations.
-/

/-- MS-EX-048: Search for non-existent module in registry. -/
def exampleSearchNonExistentRegistry : List RegistryEntry :=
  searchRegistryByName exampleRegistry "NonExistentModule"

/-- MS-EX-049: Search for non-existent tag in registry. -/
def exampleSearchNonExistentTag : List RegistryEntry :=
  searchRegistryByTag exampleRegistry "nonexistent"

/-!
## Version Constraint Operations Examples

Examples of version constraint operations.
-/

/-- MS-EX-050: Check version does not satisfy exact constraint. -/
def exampleDoesNotSatisfyExact : Bool :=
  satisfiesConstraint 2 exampleExactConstraint

/-- MS-EX-051: Check version does not satisfy atLeast constraint. -/
def exampleDoesNotSatisfyAtLeast : Bool :=
  satisfiesConstraint 1 exampleAtLeastConstraint

/-- MS-EX-052: Check version does not satisfy atMost constraint. -/
def exampleDoesNotSatisfyAtMost : Bool :=
  satisfiesConstraint 6 exampleAtMostConstraint

/-- MS-EX-053: Check version does not satisfy range constraint. -/
def exampleDoesNotSatisfyRange : Bool :=
  satisfiesConstraint 6 exampleRangeConstraint

/-!
## Symbol Mangling Operations Examples

Examples of symbol mangling operations.
-/

/-- MS-EX-054: Mangle symbol with empty name. -/
def exampleMangleEmptySymbol : String :=
  mangleSymbol exampleSimpleModuleId ""

/-- MS-EX-055: Mangle function with no parameters. -/
def exampleMangleFunctionNoParams : String :=
  mangleFunction exampleSimpleModuleId "noParams" []

/-!
## Module Loading Operations Examples

Examples of module loading operations.
-/

/-- MS-EX-056: Load non-existent module from workspace. -/
def exampleLoadNonExistentFromWorkspace : Option Module :=
  loadModuleFromWorkspace exampleSimpleWorkspace "NonExistentModule"

/-- MS-EX-057: Load module from registry with unsatisfied constraint. -/
def exampleLoadWithUnsatisfiedConstraint : Option Module :=
  loadModuleFromRegistry exampleRegistry "SimpleModule" exampleAtLeastConstraint

/-!
## Complex Examples

More complex examples combining multiple concepts.
-/

/-- MS-EX-058: Module with multiple declarations. -/
def exampleModuleMultipleDecls : Module :=
  let decl1 : ModuleDecl :=
    {
      id := exampleSimpleModuleId,
      visibility := .public,
      exports := ["func1", "func2"]
    }
  let decl2 : ModuleDecl :=
    {
      id := exampleModuleIdV2,
      visibility := .private,
      exports := ["internalFunc"]
    }
  {
    id := { hash := "multi", version := 1 },
    name := "MultiDeclModule",
    declarations := [decl1, decl2],
    dependencies := [exampleSimpleModuleId]
  }

/-- MS-EX-059: Workspace with complex configuration. -/
def exampleComplexWorkspaceConfig : WorkspaceConfig :=
  {
    searchPaths := ["./src", "./lib", "./vendor"],
    excludePatterns := ["*.test.lean", "*.spec.lean", "*.bench.lean"],
    maxDepth := 10
  }

/-- MS-EX-060: Registry with multiple versions of same module. -/
def exampleRegistryMultipleVersions : Registry :=
  [
    {
      moduleId := { hash := "mod", version := 1 },
      name := "VersionedModule",
      description := "Version 1",
      author := "Kilo Code",
      tags := ["versioned"],
      dependencies := [],
      publishedAt := "2026-01-30",
      version := 1
    },
    {
      moduleId := { hash := "mod", version := 2 },
      name := "VersionedModule",
      description := "Version 2",
      author := "Kilo Code",
      tags := ["versioned"],
      dependencies := [{ hash := "mod", version := 1 }],
      publishedAt := "2026-01-30",
      version := 2
    }
  ]

/-- MS-EX-061: Resolve module with version constraint from table. -/
def exampleResolveWithConstraint : Option Module :=
  resolveModuleWithVersion exampleLinkTableMultipleModules "SimpleModule" exampleExactConstraint

end Morph.Specs.ModuleSystem
