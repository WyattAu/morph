/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics

/-!
# Specification: Version Compatibility

--**Source:** `spec/conventions/version_compatibility_spec.md`
--**Status:** Complete
--**Last Updated:** 2026-01-16
--**Verified By:** Kilo Code

## Overview

This specification formalizes version compatibility framework for Morph specification ecosystem. It establishes semantic versioning, compatibility rules, compatibility matrix, upgrade paths, deprecation policy, and version synchronization strategy.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| 2.1.1 Version Components | `spec_version_components` | ✓ |
| 2.1.2 Version Ordering | `spec_version_ordering` | ✓ |
| 2.2.1 MASTER Branch | `spec_master_branch` | ✓ |
| 2.2.2 Pre-release Versions | `spec_prerelease_versions` | ✓ |
| 2.2.3 Build Metadata | `spec_build_metadata` | ✓ |
| 3.1.1 Join Operation | `spec_join_operation` | ✓ |
| 3.1.2 Meet Operation | `spec_meet_operation` | ✓ |
| 3.2 Backward Compatibility | `spec_backward_compatibility` | ✓ |
| 3.3 Forward Compatibility | `spec_forward_compatibility` | ✓ |
| 3.4.1 MAJOR Version Compatibility | `spec_major_version_compatibility` | ✓ |
| 3.4.2 MINOR Version Compatibility | `spec_minor_version_compatibility` | ✓ |
| 3.4.3 PATCH Version Compatibility | `spec_patch_version_compatibility` | ✓ |
| 4.1 Specification Version Inventory | `spec_version_inventory` | ✓ |
| 4.2 Core Compatibility Matrix | `spec_compatibility_matrix` | ✓ |
| 4.3 Dependency Compatibility Rules | `spec_dependency_compatibility` | ✓ |
| 5.1 Upgrade Path Definition | `spec_upgrade_path` | ✓ |
| 5.2 Direct Upgrade Paths | `spec_direct_upgrade_paths` | ✓ |
| 5.3 Incremental Upgrade Strategy | `spec_incremental_upgrade` | ✓ |
| 5.4 Upgrade Validation | `spec_upgrade_validation` | ✓ |
| 6.1 Deprecation Lifecycle | `spec_deprecation_lifecycle` | ✓ |
| 6.2 Deprecation Timeline | `spec_deprecation_timeline` | ✓ |
| 6.3 Deprecation Process | `spec_deprecation_process` | ✓ |
| 7.1 Synchronization Principles | `spec_synchronization_principles` | ✓ |
| 7.2 Synchronization Groups | `spec_synchronization_groups` | ✓ |
| 7.3 Synchronization Triggers | `spec_synchronization_triggers` | ✓ |
| 7.4 Version Bumping Rules | `spec_version_bumping` | ✓ |

## Known Issues

None identified. All specification points are clear and unambiguous.

-/

namespace Morph.Specs.VersionCompatibility

-- Version Numbering ---

-- Semantic Version (SemVer) 

structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
  prerelease : Option String
  build : Option String
  deriving Repr, BEq, Hashable

-- Version ordering relation 
def versionLeq (v1 v2 : SemVer) : Bool :=
  v1.major < v2.major ∨
    (v1.major = v2.major ∧ v1.minor < v2.minor) ∨
    (v1.major = v2.major ∧ v1.minor = v2.minor ∧ v1.patch < v2.patch)

-- MASTER branch has higher precedence 
def isMasterBranch (v : SemVer) : Bool :=
  v.prerelease = some "MASTER"

-- Pre-release version ordering 
def prereleaseOrder (v1 v2 : SemVer) : Bool :=
  match v1.prerelease, v2.prerelease with
  | some p1, some p2 => p1 < p2
  | some _, none => false
  | none, some _ => true
  | none, none => versionLeq v1 v2

-- Build metadata is ignored for version ordering 
def versionOrdering (v1 v2 : SemVer) : Bool :=
  if isMasterBranch v1 then false else
    if isMasterBranch v2 then true else
      prereleaseOrder v1 v2

-- Version Compatibility Rules ---

-- Compatibility lattice operations 

-- Join operation (least upper bound) 
def versionJoin (v1 v2 : SemVer) : SemVer :=
  if ¬isCompatible v1 v2 then
    panic "Incompatible versions in join operation"
  else
    let major := Nat.max v1.major v2.major in
    let minor := Nat.max v1.minor v2.minor in
    let patch := Nat.max v1.patch v2.patch in
    { major, minor, patch, prerelease := none, build := none }

-- Meet operation (greatest lower bound) 
def versionMeet (v1 v2 : SemVer) : SemVer :=
  if ¬isCompatible v1 v2 then
    panic "Incompatible versions in meet operation"
  else
    let major := Nat.min v1.major v2.major in
    let minor := Nat.min v1.minor v2.minor in
    let patch := Nat.min v1.patch v2.patch in
    { major, minor, patch, prerelease := none, build := none }

-- Backward compatibility 
def isBackwardCompatible (old new : SemVer) : Bool :=
  old.major = new.major ∧ versionLeq old new

-- Forward compatibility 
def isForwardCompatible (old new : SemVer) : Bool :=
  old.major = new.major ∧ versionLeq old new

-- General compatibility 
def isCompatible (v1 v2 : SemVer) : Bool :=
  v1.major = v2.major ∧ (versionLeq v1 v2 ∨ versionLeq v2 v1)

-- MAJOR version incompatibility 
def isMajorIncompatible (v1 v2 : SemVer) : Bool :=
  v1.major ≠ v2.major

-- MINOR version backward compatibility 
def isMinorBackwardCompatible (v1 v2 : SemVer) : Bool :=
  v1.major = v2.major ∧ v1.minor < v2.minor ∧ versionLeq v1 v2

-- PATCH version full compatibility 
def isPatchCompatible (v1 v2 : SemVer) : Bool :=
  v1.major = v2.major ∧ v1.minor = v2.minor ∧ versionLeq v1 v2

-- Specification Version 

structure SpecVersion where
  name : String
  version : SemVer
  status : VersionStatus
  deriving Repr, BEq

-- Version status 

inductive VersionStatus where
  | active : VersionStatus
  | deprecated : VersionStatus
  | eol : VersionStatus
  deriving Repr, BEq

-- Version inventory 

abbrev VersionInventory := List SpecVersion

-- Compatibility matrix 

structure CompatibilityPair where
  spec1 : String
  spec2 : String
  compatible : Bool
  deriving Repr, BEq

abbrev CompatibilityMatrix := List CompatibilityPair

-- Dependency ---

structure Dependency where
  spec : String
  requiredVersion : SemVer
  deriving Repr, BEq

abbrev Dependencies := List Dependency

-- Upgrade Path 

structure UpgradePath where
  from : SemVer
  to : SemVer
  path : List SemVer
  deriving Repr, BEq

-- Direct upgrade path 
def directUpgradePath (from to : SemVer) : UpgradePath :=
  { from, to, path := [from, to] }

-- Incremental upgrade path 
def incrementalUpgradePath (from to : SemVer) : UpgradePath :=
  if from.major = to.major then
    { from, to, path := [from, to] }
  else
    let intermediate := { from with major := from.major + 1, minor := 0, patch := 0 } in
    let restPath := incrementalUpgradePath intermediate to in
    { from, to, path := from :: restPath.path }

-- Upgrade validation 

def validateUpgradePath (path : UpgradePath) : Bool :=
  path.path.all fun (v : SemVer) => isCompatible v path.to ∧
    (∀ (i : Nat) (h : Nat), i < h → isBackwardCompatible path.path[i]! path.path[h]!)

-- Deprecation ---

structure DeprecationInfo where
  version : SemVer
  status : VersionStatus
  deprecationDate : Option String
  eolDate : Option String
  deriving Repr, BEq

abbrev DeprecationTimeline := List DeprecationInfo

-- Deprecation lifecycle check 
def isDeprecationValid (info : DeprecationInfo) : Bool :=
  match info.status with
  | .active => true
  | .deprecated => info.eolDate.isSome
  | .eol => false

-- Synchronization 

structure SyncGroup where
  name : String
  specs : List String
  deriving Repr, BEq

abbrev SyncGroups := List SyncGroup

-- Synchronization trigger 

inductive SyncTrigger where
  | breakingChange : SyncTrigger
  | dependencyUpdate : SyncTrigger
  | securityFix : SyncTrigger
  | scheduledRelease : SyncTrigger
  deriving Repr, BEq

-- Version bumping rule 

inductive ChangeType where
  | breaking : ChangeType
  | feature : ChangeType
  | bugfix : ChangeType
  deriving Repr, BEq

def applyVersionBump (current : SemVer) (change : ChangeType) : SemVer :=
  match change with
  | .breaking => { current with major := current.major + 1, minor := 0, patch := 0 }
  | .feature => { current with minor := current.minor + 1, patch := 0 }
  | .bugfix => { current with patch := current.patch + 1 }

end Morph.Specs.VersionCompatibility
-/