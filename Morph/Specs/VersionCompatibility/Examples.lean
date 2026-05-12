/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.VersionCompatibility.Spec

namespace Morph.Specs.VersionCompatibility

/-!
## Examples

Concrete examples demonstrating the VersionCompatibility specification.
-/

def v1_0_0 : SemVer := { major := 1, minor := 0, patch := 0, prerelease := none, build := none }

def v1_2_3 : SemVer := { major := 1, minor := 2, patch := 3, prerelease := none, build := none }

def v2_0_0 : SemVer := { major := 2, minor := 0, patch := 0, prerelease := none, build := none }

example : v1_0_0.major = 1 := rfl

example : v1_2_3.minor = 2 := rfl

example : v2_0_0.major = 2 := rfl

example : applyVersionBump v1_0_0 .breaking = { major := 2, minor := 0, patch := 0, prerelease := none, build := none } := rfl

example : applyVersionBump v1_0_0 .feature = { major := 1, minor := 1, patch := 0, prerelease := none, build := none } := rfl

example : applyVersionBump v1_2_3 .bugfix = { major := 1, minor := 2, patch := 4, prerelease := none, build := none } := rfl

example : isMajorIncompatible v1_0_0 v2_0_0 = true := rfl

example : isCompatible v1_0_0 v1_2_3 = true := rfl

end Morph.Specs.VersionCompatibility
