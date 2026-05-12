/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.VersionCompatibility.Spec

namespace Morph.Specs.VersionCompatibility

/-!
## Lemmas

Lemmas and auxiliary results for the VersionCompatibility specification.
-/

/-! ### Version Bump Properties -/

theorem applyVersionBump_breaking (v : SemVer) :
  (applyVersionBump v .breaking).major = v.major + 1 := rfl

theorem applyVersionBump_feature (v : SemVer) :
  (applyVersionBump v .feature).minor = v.minor + 1 := rfl

theorem applyVersionBump_bugfix (v : SemVer) :
  (applyVersionBump v .bugfix).patch = v.patch + 1 := rfl

theorem applyVersionBump_breaking_resets_minor (v : SemVer) :
  (applyVersionBump v .breaking).minor = 0 := rfl

theorem applyVersionBump_breaking_resets_patch (v : SemVer) :
  (applyVersionBump v .breaking).patch = 0 := rfl

theorem applyVersionBump_feature_resets_patch (v : SemVer) :
  (applyVersionBump v .feature).patch = 0 := rfl

theorem applyVersionBump_preserves_prerelease_breaking (v : SemVer) :
  (applyVersionBump v .breaking).prerelease = v.prerelease := rfl

theorem applyVersionBump_preserves_prerelease_feature (v : SemVer) :
  (applyVersionBump v .feature).prerelease = v.prerelease := rfl

theorem applyVersionBump_preserves_prerelease_bugfix (v : SemVer) :
  (applyVersionBump v .bugfix).prerelease = v.prerelease := rfl

/-! ### Change Type Exhaustiveness -/

theorem changeType_cases (c : ChangeType) :
  c = .breaking ∨ c = .feature ∨ c = .bugfix := by
  cases c <;> simp

/-! ### Version Status Exhaustiveness -/

theorem versionStatus_cases (s : VersionStatus) :
  s = .active ∨ s = .deprecated ∨ s = .eol := by
  cases s <;> simp

/-! ### Version Join/Meet Algebra -/

theorem versionJoin_major (v1 v2 : SemVer) :
  (versionJoin v1 v2).major = Nat.max v1.major v2.major := rfl

theorem versionJoin_minor (v1 v2 : SemVer) :
  (versionJoin v1 v2).minor = Nat.max v1.minor v2.minor := rfl

theorem versionJoin_patch (v1 v2 : SemVer) :
  (versionJoin v1 v2).patch = Nat.max v1.patch v2.patch := rfl

theorem versionJoin_prerelease_none (v1 v2 : SemVer) :
  (versionJoin v1 v2).prerelease = none := rfl

theorem versionJoin_build_none (v1 v2 : SemVer) :
  (versionJoin v1 v2).build = none := rfl

theorem versionMeet_major (v1 v2 : SemVer) :
  (versionMeet v1 v2).major = Nat.min v1.major v2.major := rfl

theorem versionMeet_minor (v1 v2 : SemVer) :
  (versionMeet v1 v2).minor = Nat.min v1.minor v2.minor := rfl

theorem versionMeet_patch (v1 v2 : SemVer) :
  (versionMeet v1 v2).patch = Nat.min v1.patch v2.patch := rfl

theorem versionMeet_prerelease_none (v1 v2 : SemVer) :
  (versionMeet v1 v2).prerelease = none := rfl

theorem versionMeet_build_none (v1 v2 : SemVer) :
  (versionMeet v1 v2).build = none := rfl

/-! ### Upgrade Path Properties -/

theorem directUpgradePath_nonempty (fromVer toVer : SemVer) :
  (directUpgradePath fromVer toVer).path.length = 2 := rfl

theorem directUpgradePath_starts_at (fromVer toVer : SemVer) :
  (directUpgradePath fromVer toVer).path.head? = some fromVer := rfl

theorem directUpgradePath_ends_at (fromVer toVer : SemVer) :
  (directUpgradePath fromVer toVer).path.getLast? = some toVer := rfl

/-! ### Deprecation Properties -/

theorem isDeprecationValid_active (info : DeprecationInfo) :
  info.status = .active → isDeprecationValid info = true := by
  intro h; unfold isDeprecationValid; simp [h]

theorem isDeprecationValid_eol (info : DeprecationInfo) :
  info.status = .eol → isDeprecationValid info = false := by
  intro h; unfold isDeprecationValid; simp [h]

/-! ### Sync Trigger Exhaustiveness -/

theorem syncTrigger_cases (t : SyncTrigger) :
  t = .breakingChange ∨ t = .dependencyUpdate ∨
  t = .securityFix ∨ t = .scheduledRelease := by
  cases t <;> simp

/-! ### Version Compatibility -/

theorem isCompatible_refl_false (v : SemVer) :
    isCompatible v v = false := by
  unfold isCompatible; simp [versionLeq]

end Morph.Specs.VersionCompatibility
