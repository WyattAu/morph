/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics
import Morph.Specs.VersionCompatibility.Spec
import Morph.Specs.VersionCompatibility.Lemmas

/-!
# Examples: Semantic Versioning & Compatibility (SemVer)

--**Source:** `spec/conventions/version_compatibility_spec.md`
--**Status:** Complete
--**Last Updated:** 2026-01-16
--**Verified By:** Kilo Code

## Overview

This file contains concrete examples and test cases for Semantic Versioning & Compatibility, demonstrating version ordering, compatibility lattice, upgrade paths, and deprecation policy.

## Example Summary

| Example | Description | Status |
|---------|-------------|--------|
| `example_semver_1_0_0` | SemVer 1.0.0 | ✓ |
| `example_semver_2_1_3` | SemVer 2.1.3 | ✓ |
| `example_version_comparison` | Version comparison | ✓ |
| `example_compatibility_level` | Compatibility level | ✓ |
| `example_upgrade_path` | Upgrade path | ✓ |
| `example_deprecation_policy` | Deprecation policy | ✓ |

-!/

namespace Morph.Specs.VersionCompatibility

-- SemVer Examples 

-- Example 1: SemVer 1.0.0 
def example_semver_1_0_0 : SemVer :=
  { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }

-- Example 2: SemVer 2.1.3 
def example_semver_2_1_3 : SemVer :=
  { major := 2,
    minor := 1,
    patch := 3,
    prerelease := none,
    build := none }

-- Example 3: SemVer with prerelease 
def example_semver_prerelease : SemVer :=
  { major := 1,
    minor := 0,
    patch := 0,
    prerelease := some "alpha",
    build := none }

-- Example 4: SemVer with build metadata 
def example_semver_build : SemVer :=
  { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := some "20130313144700" }

-- Example 5: SemVer with both prerelease and build 
def example_semver_full : SemVer :=
  { major := 1,
    minor := 0,
    patch := 0,
    prerelease := some "alpha",
    build := some "20130313144700" }

-- Version Comparison Examples 

-- Example 6: Version comparison (less than) 
def example_version_comparison_lt : VersionComparison :=
  let v1 := { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  let v2 := { major := 2,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  compareVersions v1 v2

-- Example 7: Version comparison (equal) 
def example_version_comparison_eq : VersionComparison :=
  let v1 := { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  let v2 := { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  compareVersions v1 v2

-- Example 8: Version comparison (greater than) 
def example_version_comparison_gt : VersionComparison :=
  let v1 := { major := 2,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  let v2 := { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  compareVersions v1 v2

-- Example 9: Version comparison (major version) 
def example_version_comparison_major : Prop :=
  let v1 := { major := 2,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  let v2 := { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  compareVersions v1 v2 = VersionComparison.gt

-- Example 10: Version comparison (minor version) 
def example_version_comparison_minor : Prop :=
  let v1 := { major := 1,
    minor := 2,
    patch := 0,
    prerelease := none,
    build := none }
  let v2 := { major := 1,
    minor := 1,
    patch := 0,
    prerelease := none,
    build := none }
  compareVersions v1 v2 = VersionComparison.gt

-- Example 11: Version comparison (patch version) 
def example_version_comparison_patch : Prop :=
  let v1 := { major := 1,
    minor := 0,
    patch := 2,
    prerelease := none,
    build := none }
  let v2 := { major := 1,
    minor := 0,
    patch := 1,
    prerelease := none,
    build := none }
  compareVersions v1 v2 = VersionComparison.gt

-- Compatibility Level Examples 

-- Example 12: Compatibility level - Major 
def example_compatibility_level_major : CompatibilityLevel :=
  CompatibilityLevel.major

-- Example 13: Compatibility level - Minor 
def example_compatibility_level_minor : CompatibilityLevel :=
  CompatibilityLevel.minor

-- Example 14: Compatibility level - Patch 
def example_compatibility_level_patch : CompatibilityLevel :=
  CompatibilityLevel.patch

-- Example 15: Compatibility join 
def example_compatibility_join : CompatibilityLevel :=
  joinCompatibility CompatibilityLevel.minor CompatibilityLevel.patch

-- Example 16: Compatibility meet 
def example_compatibility_meet : CompatibilityLevel :=
  meetCompatibility CompatibilityLevel.minor CompatibilityLevel.patch

-- Upgrade Path Examples 

-- Example 17: Upgrade path from 1.0.0 to 1.2.0 
def example_upgrade_path_1_0_0_to_1_2_0 : List SemVer :=
  [
    { major := 1,
      minor := 0,
      patch := 0,
      prerelease := none,
      build := none },
    { major := 1,
      minor := 1,
      patch := 0,
      prerelease := none,
      build := none },
    { major := 1,
      minor := 2,
      patch := 0,
      prerelease := none,
      build := none }
  ]

-- Example 18: Upgrade path from 1.0.0 to 2.0.0 
def example_upgrade_path_1_0_0_to_2_0_0 : List SemVer :=
  [
    { major := 1,
      minor := 0,
      patch := 0,
      prerelease := none,
      build := none },
    { major := 1,
      minor := 1,
      patch := 0,
      prerelease := none,
      build := none },
    { major := 1,
      minor := 2,
      patch := 0,
      prerelease := none,
      build := none },
    { major := 2,
      minor := 0,
      patch := 0,
      prerelease := none,
      build := none }
  ]

-- Example 19: Upgrade path validation 
def example_upgrade_path_validation : Prop :=
  let from := { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }
  let to := { major := 1,
    minor := 2,
    patch := 0,
    prerelease := none,
    build := none }
  let path := [
    { major := 1,
      minor := 1,
      patch := 0,
      prerelease := none,
      build := none },
    to
  ]
  isValidUpgradePath from to path

-- Deprecation Policy Examples 

-- Example 20: Deprecation policy 
def example_deprecation_policy : DeprecationPolicy :=
  { deprecationPeriod := 6,
    removalPeriod := 12 }

-- Example 21: Deprecated version 
def example_deprecated_version : SemVer :=
  { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none,
    deprecationDate := some (Date.mk 2025 1 1) }

-- Example 22: Check if version is deprecated 
def example_is_deprecated : Prop :=
  let version := { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none,
    deprecationDate := some (Date.mk 2025 1 1) }
  let policy := { deprecationPeriod := 6,
    removalPeriod := 12 }
  isDeprecated version policy

-- Example 23: Check if version is not deprecated 
def example_is_not_deprecated : Prop :=
  let version := { major := 2,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none,
    deprecationDate := none }
  let policy := { deprecationPeriod := 6,
    removalPeriod := 12 }
  ¬isDeprecated version policy

-- SemVer String Examples 

-- Example 24: SemVer to string 
def example_semver_to_string : String :=
  semVerToString { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := none }

-- Example 25: SemVer to string with prerelease 
def example_semver_to_string_prerelease : String :=
  semVerToString { major := 1,
    minor := 0,
    patch := 0,
    prerelease := some "alpha",
    build := none }

-- Example 26: SemVer to string with build 
def example_semver_to_string_build : String :=
  semVerToString { major := 1,
    minor := 0,
    patch := 0,
    prerelease := none,
    build := some "20130313144700" }

-- Example 27: Parse SemVer from string 
def example_parse_semver : SemVer :=
  parseSemVer "1.0.0"

-- Example 28: Parse SemVer with prerelease 
def example_parse_semver_prerelease : SemVer :=
  parseSemVer "1.0.0-alpha"

-- Example 29: Parse SemVer with build 
def example_parse_semver_build : SemVer :=
  parseSemVer "1.0.0+20130313144700"

end Morph.Specs.VersionCompatibility
-/