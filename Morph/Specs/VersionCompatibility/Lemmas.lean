/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.VersionCompatibility.Spec

namespace Morph.Specs.VersionCompatibility

/-!
## Lemmas

Lemmas and auxiliary results for the VersionCompatibility specification.
-/

theorem applyVersionBump_breaking (v : SemVer) :
  (applyVersionBump v .breaking).major = v.major + 1 := rfl

theorem applyVersionBump_feature (v : SemVer) :
  (applyVersionBump v .feature).minor = v.minor + 1 := rfl

theorem applyVersionBump_bugfix (v : SemVer) :
  (applyVersionBump v .bugfix).patch = v.patch + 1 := rfl

end Morph.Specs.VersionCompatibility
