# REQ-002: Dependency Version Alignment

**Status:** Draft  
**Priority:** High (P1)  
**Category:** Dependencies / Build System  
**Created:** 2026-01-31  
**Phase:** Phase 5 - Requirement Sharding

---

## 1. Overview

This requirement addresses the critical version mismatch between the Lean 4.28.0-rc1 toolchain and the project's dependencies, which are currently pinned to v4.10.0 versions. This 18 minor version gap causes complete build failure due to API incompatibilities.

---

## 2. Background

The Morph project specifies Lean 4.28.0-rc1 as its toolchain in the [`lean-toolchain`](../../lean-toolchain) file, but all direct dependencies in [`lakefile.toml`](../../lakefile.toml) are pinned to v4.10.0 versions.

### Current State

| Component | Current Version | File |
|-----------|----------------|------|
| Lean Toolchain | v4.28.0-rc1 | [`lean-toolchain`](../../lean-toolchain) |
| batteries | v4.10.0 | [`lakefile.toml`](../../lakefile.toml) |
| aesop | v4.10.0 | [`lakefile.toml`](../../lakefile.toml) |
| mathlib4 | v4.10.0 | [`lakefile.toml`](../../lakefile.toml) |

### Problems

1. **Critical Version Mismatch (RISK-COMP-001):** The 18 minor version gap causes complete build failure due to API incompatibilities, type signature changes, and breaking changes in Lean 4 core library.

2. **Breaking Changes in mathlib4 (RISK-COMP-004):** Major changes between v4.10.0 and v4.28.0-rc1 include module reorganization, theorem renaming, type class hierarchy updates, and proof automation strategy modifications.

3. **Type Signature Changes in Batteries (RISK-COMP-005):** Function parameter types, return types, implicit parameter requirements, and type class instance requirements may have changed.

4. **Aesop Automation Compatibility Issues (RISK-COMP-006):** Changes in proof search strategies, modifications to tactic syntax, updates to configuration options, and changes in default behavior.

### Related Documents

- [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) (Section 4.3)
- [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) (Section 2.3)
- [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) (RISK-COMP-001, RISK-COMP-004, RISK-COMP-005, RISK-COMP-006)
- [ADR-001: Lean 4.28.0-rc1 Migration](../../02_adrs/ADR-001-lean-4.28.0-rc1-migration.md)
- [ADR-003: Dependency Version Alignment](../../02_adrs/ADR-003-dependency-version-alignment.md)

---

## 3. Functional Requirements

### 3.1 FR-002.1: Update Lean Toolchain to v4.28.0-rc1

**Description:** Ensure the Lean toolchain is correctly set to v4.28.0-rc1.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Toolchain version is v4.28.0-rc1 | `cat lean-toolchain` returns `leanprover/lean4:v4.28.0-rc1` |
| Toolchain is available | `lean --version` returns v4.28.0-rc1 |

**Implementation Notes:**

- The toolchain is already set to v4.28.0-rc1 in [`lean-toolchain`](../../lean-toolchain)
- Verify the toolchain is correctly installed and available
- No changes required if already correct

### 3.2 FR-002.2: Update Batteries to v4.28.0-Compatible Version

**Description:** Update the batteries dependency from v4.10.0 to a version compatible with Lean 4.28.0-rc1.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Batteries version is v4.28.0-compatible | `grep batteries lakefile.toml` shows compatible version |
| Batteries compiles with v4.28.0-rc1 | `lake build Batteries` succeeds |
| No type errors from batteries | Build output contains no batteries-related type errors |

**Implementation Notes:**

- Research the batteries repository for v4.28.0-compatible tags/branches
- Choose the most recent stable version compatible with Lean 4.28.0-rc1
- Prefer official releases over development branches
- Update [`lakefile.toml`](../../lakefile.toml) with the new version
- Run `lake update` to regenerate [`lake-manifest.json`](../../lake-manifest.json)

### 3.3 FR-002.3: Update Aesop to v4.28.0-Compatible Version

**Description:** Update the aesop dependency from v4.10.0 to a version compatible with Lean 4.28.0-rc1.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Aesop version is v4.28.0-compatible | `grep aesop lakefile.toml` shows compatible version |
| Aesop compiles with v4.28.0-rc1 | `lake build Aesop` succeeds |
| No tactic errors from aesop | Build output contains no aesop-related tactic errors |

**Implementation Notes:**

- Research the aesop repository for v4.28.0-compatible tags/branches
- Choose the most recent stable version compatible with Lean 4.28.0-rc1
- Prefer official releases over development branches
- Update [`lakefile.toml`](../../lakefile.toml) with the new version
- Run `lake update` to regenerate [`lake-manifest.json`](../../lake-manifest.json)

### 3.4 FR-002.4: Update Mathlib4 to v4.28.0-Compatible Version

**Description:** Update the mathlib4 dependency from v4.10.0 to a version compatible with Lean 4.28.0-rc1.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Mathlib4 version is v4.28.0-compatible | `grep mathlib lakefile.toml` shows compatible version |
| Mathlib4 compiles with v4.28.0-rc1 | `lake build Mathlib` succeeds |
| No import errors from mathlib4 | Build output contains no mathlib4-related import errors |

**Implementation Notes:**

- Research the mathlib4 repository for v4.28.0-compatible tags/branches
- Choose the most recent stable version compatible with Lean 4.28.0-rc1
- Prefer official releases over development branches
- Update [`lakefile.toml`](../../lakefile.toml) with the new version
- Run `lake update` to regenerate [`lake-manifest.json`](../../lake-manifest.json)

### 3.5 FR-002.5: Update Lake Manifest

**Description:** Regenerate the lake-manifest.json with the updated dependency versions.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Lake manifest is regenerated | `lake update` completes successfully |
| Manifest contains updated versions | `cat lake-manifest.json` shows new dependency versions |
| All dependencies resolve | `lake configure` succeeds |

**Implementation Notes:**

- Run `lake update` to regenerate [`lake-manifest.json`](../../lake-manifest.json)
- Verify all dependency versions are correctly reflected
- Clean build artifacts: `lake clean && rm -rf .lake/packages`

### 3.6 FR-002.6: Update Code for New Dependency Versions

**Description:** Update all code that uses the updated dependencies to be compatible with the new versions.

#### 3.6.1 FR-002.6.1: Update Mathlib4 Imports

**Description:** Update all mathlib4 imports to match the new module structure in the updated version.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| All imports resolve | No import errors in build output |
| Theorem references are correct | No unknown identifier errors for mathlib4 theorems |
| Type class instances are valid | No type class instance errors |

**Implementation Notes:**

- Create a mapping of old to new module paths
- Update import statements across all specification files
- Rename theorem references to current names
- Update type class instance declarations

#### 3.6.2 FR-002.6.2: Update Batteries Usage

**Description:** Update all code that uses batteries to be compatible with the new version.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| All batteries functions resolve | No unknown identifier errors for batteries functions |
| Type signatures match | No type mismatch errors from batteries usage |

**Implementation Notes:**

- Identify all batteries usage in the codebase
- Update function calls to match new signatures
- Add explicit type annotations where needed
- Replace deprecated functions with current equivalents

#### 3.6.3 FR-002.6.3: Update Aesop Configurations

**Description:** Update all aesop configurations to be compatible with the new version.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| All aesop tactics resolve | No tactic errors in build output |
| Proof automation works | All proofs using aesop complete successfully |

**Implementation Notes:**

- Review all aesop usage in the codebase
- Update tactic syntax to current version
- Adjust aesop configurations as needed
- Replace deprecated tactics with current equivalents

---

## 4. Non-Functional Requirements

### 4.1 NFR-002.1: Version Stability

**Description:** The selected dependency versions should be stable and well-tested.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Versions are official releases | Use tagged releases, not development branches |
| Versions are compatible | Verify release notes mention Lean 4.28.0-rc1 compatibility |

### 4.2 NFR-002.2: Minimal Breaking Changes

**Description:** Minimize the impact of breaking changes from dependency updates.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Breaking changes are documented | Document all breaking changes encountered |
| Migration path is clear | Provide clear instructions for updating code |

### 4.3 NFR-002.3: Backward Compatibility

**Description:** Changes must not break existing functionality that does not depend on the updated dependencies.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No regressions in unaffected code | All code not using updated dependencies still compiles |
| Test suite passes | All tests in [`Morph/Tests/`](../../Morph/Tests/) pass |

---

## 5. Dependencies

### 5.1 Internal Dependencies

| Requirement | Dependency Type | Description |
|-------------|-----------------|-------------|
| REQ-001 | Precedes | Critical errors must be resolved before dependency updates |
| REQ-003 | Follows | Syntax standards compliance depends on compilation working |
| REQ-004 | Follows | Deprecated API remediation depends on compilation working |

### 5.2 External Dependencies

| Dependency | Target Version | Status |
|------------|----------------|--------|
| Lean Toolchain | v4.28.0-rc1 | Already configured |
| batteries | v4.28.0-compatible | To be determined |
| aesop | v4.28.0-compatible | To be determined |
| mathlib4 | v4.28.0-compatible | To be determined |

---

## 6. Verification Plan

### 6.1 Pre-Implementation Verification

```bash
# Verify current dependency versions
grep -A 10 "\[dependencies\]" lakefile.toml

# Verify toolchain version
cat lean-toolchain

# Check for dependency usage
grep -r "import.*Batteries" Morph/
grep -r "import.*Mathlib" Morph/
grep -r "aesop\|aesop!" Morph/
```

### 6.2 Post-Implementation Verification

```bash
# Verify dependency versions are updated
grep -A 10 "\[dependencies\]" lakefile.toml

# Verify Lake manifest is updated
cat lake-manifest.json | grep -A 5 "rev"

# Verify Lake configuration
lake configure

# Verify all dependencies compile
lake build

# Verify no type errors
lake build 2>&1 | grep "type mismatch" || echo "No type errors"

# Verify no import errors
lake build 2>&1 | grep "unknown identifier" || echo "No import errors"
```

### 6.3 Regression Testing

```bash
# Run full test suite
lake build Morph.Tests.*

# Verify no regressions
lake build
```

---

## 7. Success Metrics

| Metric | Target | Measurement Method |
|--------|--------|-------------------|
| Dependency Version Alignment | 100% | All dependencies at v4.28.0-compatible versions |
| Compilation Success | 100% | `lake build` exit code |
| Type Errors | 0 | `lake build` error output |
| Import Errors | 0 | `lake build` error output |
| Deprecation Warnings | 0 | `lake build` warning output |

---

## 8. Related Documents

| Document | Type | Reference |
|----------|------|-----------|
| [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) | Current State | Section 4.3 |
| [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) | Future State | Section 2.3 |
| [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) | Threat Model | RISK-COMP-001, RISK-COMP-004, RISK-COMP-005, RISK-COMP-006 |
| [ADR-001: Lean 4.28.0-rc1 Migration](../../02_adrs/ADR-001-lean-4.28.0-rc1-migration.md) | ADR | Phase 1 |
| [ADR-003: Dependency Version Alignment](../../02_adrs/ADR-003-dependency-version-alignment.md) | ADR | Full document |

---

## 9. Change History

| Date | Version | Author | Description |
|------|---------|--------|-------------|
| 2026-01-31 | 1.0 | System | Initial requirement specification |

---

## 10. Appendix: Version Research

### A.1 Target Versions (To Be Determined)

| Package | Target Version | Commit/Tag | Notes |
|---------|----------------|------------|-------|
| batteries | TBD | TBD | Research pending |
| aesop | TBD | TBD | Research pending |
| mathlib4 | TBD | TBD | Research pending |

### A.2 Breaking Changes Summary (To Be Populated)

| Dependency | Breaking Changes | Migration Notes |
|------------|------------------|-----------------|
| batteries | TBD | TBD |
| aesop | TBD | TBD |
| mathlib4 | TBD | TBD |

### A.3 Migration Checklist

- [ ] Research available v4.28.0-compatible versions for each dependency
- [ ] Select target versions and document rationale
- [ ] Update [`lakefile.toml`](../../lakefile.toml) with new versions
- [ ] Run `lake update` to regenerate [`lake-manifest.json`](../../lake-manifest.json)
- [ ] Clean build artifacts
- [ ] Update mathlib4 imports across all specification files
- [ ] Update batteries usage across all files
- [ ] Update aesop configurations across all files
- [ ] Verify Lake configuration succeeds
- [ ] Verify all modules compile
- [ ] Run full test suite
- [ ] Document all breaking changes encountered
- [ ] Update project documentation
