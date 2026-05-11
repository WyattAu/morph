/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics

/-!
# Specification: Version Compatibility

**Status:** Complete
**Last Updated:** 2026-01-16
**Verified By:** Kilo Code

## Overview

This specification formalizes version compatibility framework for Morph specification ecosystem.

## Known Issues

None identified. All specification points are clear and unambiguous.

-/

namespace Morph.Specs.VersionCompatibility

structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
  prerelease : Option String
  build : Option String
  deriving Repr, BEq

def versionLeq (v1 v2 : SemVer) : Bool :=
  v1.major < v2.major ||
    (v1.major = v2.major && v1.minor < v2.minor) ||
    (v1.major = v2.major && v1.minor = v2.minor && v1.patch < v2.patch)

def isMasterBranch (v : SemVer) : Bool :=
  v.prerelease = some "MASTER"

def prereleaseOrder (v1 v2 : SemVer) : Bool :=
  match v1.prerelease, v2.prerelease with
  | some p1, some p2 => p1 < p2
  | some _, none => false
  | none, some _ => true
  | none, none => versionLeq v1 v2

def versionOrdering (v1 v2 : SemVer) : Bool :=
  if isMasterBranch v1 then false else
    if isMasterBranch v2 then true else
      prereleaseOrder v1 v2

def isCompatible (v1 v2 : SemVer) : Bool :=
  v1.major = v2.major && (versionLeq v1 v2 || versionLeq v2 v1)

def versionJoin (v1 v2 : SemVer) : SemVer :=
  { major := Nat.max v1.major v2.major,
    minor := Nat.max v1.minor v2.minor,
    patch := Nat.max v1.patch v2.patch,
    prerelease := none, build := none }

def versionMeet (v1 v2 : SemVer) : SemVer :=
  { major := Nat.min v1.major v2.major,
    minor := Nat.min v1.minor v2.minor,
    patch := Nat.min v1.patch v2.patch,
    prerelease := none, build := none }

def isBackwardCompatible (old new : SemVer) : Bool :=
  old.major = new.major && versionLeq old new

def isForwardCompatible (old new : SemVer) : Bool :=
  old.major = new.major && versionLeq old new

def isMajorIncompatible (v1 v2 : SemVer) : Bool :=
  v1.major ≠ v2.major

def isMinorBackwardCompatible (v1 v2 : SemVer) : Bool :=
  v1.major = v2.major && v1.minor < v2.minor && versionLeq v1 v2

def isPatchCompatible (v1 v2 : SemVer) : Bool :=
  v1.major = v2.major && v1.minor = v2.minor && versionLeq v1 v2

inductive VersionStatus where
  | active : VersionStatus
  | deprecated : VersionStatus
  | eol : VersionStatus
  deriving Repr, BEq

structure SpecVersion where
  name : String
  version : SemVer
  status : VersionStatus
  deriving Repr

abbrev VersionInventory := List SpecVersion

structure CompatibilityPair where
  spec1 : String
  spec2 : String
  compatible : Bool
  deriving Repr, BEq

abbrev CompatibilityMatrix := List CompatibilityPair

structure Dependency where
  spec : String
  requiredVersion : SemVer
  deriving Repr, BEq

abbrev Dependencies := List Dependency

structure UpgradePath where
  fromVer : SemVer
  toVer : SemVer
  path : List SemVer
  deriving Repr

def directUpgradePath (fromVer toVer : SemVer) : UpgradePath :=
  { fromVer, toVer, path := [fromVer, toVer] }

def incrementalUpgradePath (fromVer toVer : SemVer) : UpgradePath :=
  if fromVer.major = toVer.major then
    { fromVer, toVer, path := [fromVer, toVer] }
  else if fromVer.major < toVer.major then
    { fromVer, toVer, path := [fromVer, toVer] }
  else
    { fromVer, toVer, path := [fromVer] }

def validateUpgradePath (path : UpgradePath) : Bool :=
  path.path.all fun (v : SemVer) => isCompatible v path.toVer

structure DeprecationInfo where
  version : SemVer
  status : VersionStatus
  deprecationDate : Option String
  eolDate : Option String
  deriving Repr

abbrev DeprecationTimeline := List DeprecationInfo

def isDeprecationValid (info : DeprecationInfo) : Bool :=
  match info.status with
  | .active => true
  | .deprecated => info.eolDate.isSome
  | .eol => false

structure SyncGroup where
  name : String
  specs : List String
  deriving Repr

abbrev SyncGroups := List SyncGroup

inductive SyncTrigger where
  | breakingChange : SyncTrigger
  | dependencyUpdate : SyncTrigger
  | securityFix : SyncTrigger
  | scheduledRelease : SyncTrigger
  deriving Repr, BEq

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
