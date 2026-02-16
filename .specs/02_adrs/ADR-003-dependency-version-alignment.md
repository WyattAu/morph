# ADR-003: Dependency Version Alignment

**Status:** Accepted  
**Date:** 2026-01-31  
**Decision Type:** Technical  
**Related ADRs:** ADR-001, ADR-002  
**Related Documents:** [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md), [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md), [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md)

---

## Context

The Morph project specifies Lean 4.28.0-rc1 as its toolchain, but all direct dependencies in [`lakefile.toml`](../../lakefile.toml) are pinned to v4.10.0 versions. This 18 minor version gap creates significant compatibility issues and is the root cause of the build failures.

### Current State

| Package | Current Version | Target Version | Purpose |
|---------|----------------|----------------|---------|
| batteries | v4.10.0 | v4.28.0-compatible | Standard library extensions |
| aesop | v4.10.0 | v4.28.0-compatible | Automation for Lean proofs |
| mathlib4 | v4.10.0 | v4.28.0-compatible | Mathematical library |

### Current lakefile.toml

```toml
[dependencies]
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.10.0" }
aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.10.0" }
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.10.0" }
```

### Problems

1. **Critical Version Mismatch (RISK-COMP-001):** The 18 minor version gap between toolchain and dependencies causes complete build failure due to API incompatibilities.

2. **Breaking Changes in mathlib4 (RISK-COMP-004):** Major changes between v4.10.0 and v4.28.0-rc1 include:
   - Reorganization of module structure
   - Renaming of theorems and definitions
   - Changes to type class hierarchies
   - Updates to proof automation strategies

3. **Type Signature Changes in Batteries (RISK-COMP-005):** Function parameter types, return types, implicit parameter requirements, and type class instance requirements may have changed.

4. **Aesop Automation Compatibility Issues (RISK-COMP-006):** Changes in proof search strategies, modifications to tactic syntax, updates to configuration options, and changes in default behavior.

5. **Deprecation Warnings:** Current mathlib4 lakefile.lean shows deprecation warnings for `Lake.Package.name` and `String.trim`.

### Alternatives Considered

#### Alternative 1: Downgrade Toolchain to v4.10.0

**Pros:**
- Immediate compatibility with existing dependencies
- Minimal code changes required
- Stable, production-ready toolchain

**Cons:**
- Forfeits access to Lean 4.28.0-rc1 improvements
- Does not address the architectural decision to use v4.28.0-rc1
- Contradicts [ADR-001](./ADR-001-lean-4.28.0-rc1-migration.md)
- May require future migration anyway

#### Alternative 2: Maintain Mixed Versions

**Pros:**
- Gradual migration path
- Can test compatibility incrementally

**Cons:**
- Unsupported configuration
- Unpredictable behavior
- Increased maintenance burden
- No clear path to resolution
- Lake does not support this configuration

#### Alternative 3: Update Dependencies to v4.28.0-Compatible Versions (Chosen)

**Pros:**
- Aligns with Lean 4.28.0-rc1 toolchain
- Access to latest features and bug fixes
- Future-proof codebase
- Consistent versioning across ecosystem
- Enables use of latest Lean 4 APIs

**Cons:**
- Significant migration effort required
- Breaking changes across all files
- May require code updates for API changes
- Potential for new bugs in newer dependency versions

---

## Decision

**Update all direct dependencies to versions compatible with Lean 4.28.0-rc1.**

### Implementation Plan

#### Phase 1: Research and Version Selection

1. **Research Available Versions**
   - Check batteries repository for v4.28.0-compatible tags/branches
   - Check aesop repository for v4.28.0-compatible tags/branches
   - Check mathlib4 repository for v4.28.0-compatible tags/branches

2. **Select Target Versions**
   - Choose the most recent stable version compatible with Lean 4.28.0-rc1
   - Prefer official releases over development branches
   - Document the selected versions

3. **Verify Compatibility**
   - Check release notes for breaking changes
   - Review migration guides if available
   - Test with a minimal example

#### Phase 2: Dependency Update

1. **Update lakefile.toml**
   ```toml
   [dependencies]
   batteries = { git = "https://github.com/leanprover-community/batteries", rev = "TARGET_VERSION" }
   aesop = { git = "https://github.com/JLimperg/aesop", rev = "TARGET_VERSION" }
   mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "TARGET_VERSION" }
   ```

2. **Update Lake Manifest**
   - Run `lake update` to regenerate lake-manifest.json
   - Verify the updated versions are correctly reflected

3. **Clean Build Artifacts**
   ```bash
   lake clean
   rm -rf .lake/packages
   ```

#### Phase 3: Code Migration

1. **Update mathlib4 Imports**
   - Create a mapping of old to new module paths
   - Update import statements across all specification files
   - Rename theorem references to current names
   - Update type class instance declarations

2. **Update Batteries Usage**
   - Identify all batteries usage in the codebase
   - Update function calls to match new signatures
   - Add explicit type annotations where needed
   - Replace deprecated functions with current equivalents

3. **Update Aesop Configurations**
   - Review all aesop usage in the codebase
   - Update tactic syntax to current version
   - Adjust aesop configurations as needed
   - Replace deprecated tactics with current equivalents

4. **Fix Deprecation Warnings**
   - Replace `Lake.Package.name` with `baseName`, `keyName`, or `prettyName`
   - Replace `String.trim` with `String.trimAscii`
   - Update type signatures if needed

#### Phase 4: Verification

1. **Lake Configuration**
   ```bash
   lake configure
   ```
   - Verify Lake workspace configures successfully
   - Verify no dependency errors

2. **Compilation**
   ```bash
   lake build
   ```
   - Verify all modules compile without errors
   - Verify zero type errors
   - Verify zero deprecation warnings

3. **Testing**
   - Run all tests in [`Morph/Tests/`](../../Morph/Tests/)
   - Execute all examples in specification directories
   - Verify all proofs complete successfully

---

## Consequences

### Positive Consequences

1. **Version Alignment:** All dependencies aligned with Lean 4.28.0-rc1 toolchain, eliminating version mismatch issues.

2. **Access to Latest Features:** New features and improvements in batteries, aesop, and mathlib4.

3. **Bug Fixes:** Access to bug fixes and security improvements in newer dependency versions.

4. **Ecosystem Compatibility:** Consistent with the broader Lean 4 ecosystem, making collaboration easier.

5. **Future-Proofing:** The codebase will be positioned to adopt future Lean 4 and dependency updates more easily.

6. **Reduced Technical Debt:** Comprehensive resolution of version mismatch issues.

### Negative Consequences

1. **Migration Effort:** Significant effort required to update all code to be compatible with new dependency versions.

2. **Breaking Changes:** All files may require changes due to breaking changes in dependencies.

3. **Learning Curve:** Team members need to learn new APIs and patterns introduced in newer dependency versions.

4. **Potential for New Bugs:** Newer dependency versions may introduce new bugs or regressions.

5. **Proof Re-verification:** All proofs may need to be re-verified due to changes in mathlib4 theorems and aesop automation.

6. **Build Time Changes:** Build times may increase or decrease depending on changes in dependency implementations.

### Neutral Consequences

1. **Dependency Size:** Newer versions may be larger or smaller than current versions.

2. **API Surface:** API surface may expand or contract, affecting available functionality.

3. **Documentation:** Documentation for newer versions may be more or less complete than for v4.10.0.

---

## Status

**Accepted** - This decision has been approved and implementation is in progress.

### Implementation Status

| Phase | Status | Notes |
|-------|--------|-------|
| Phase 1: Research and Version Selection | Pending | Need to identify target versions |
| Phase 2: Dependency Update | Pending | Depends on Phase 1 |
| Phase 3: Code Migration | Pending | Depends on Phase 2 |
| Phase 4: Verification | Pending | Depends on Phase 3 |

### Prerequisites

- [ADR-001: Lean 4.28.0-rc1 Migration](./ADR-001-lean-4.28.0-rc1-migration.md) must be accepted
- [ADR-002: ProofWidgets Dependency Removal](./ADR-002-proofwidgets-removal.md) should be completed first to unblock Lake configuration

---

## References

- [Batteries Repository](https://github.com/leanprover-community/batteries)
- [Aesop Repository](https://github.com/JLimperg/aesop)
- [Mathlib4 Repository](https://github.com/leanprover-community/mathlib4)
- [Lake Documentation](https://github.com/leanprover/lake)
- [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) - Current state analysis
- [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) - Target state definition
- [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) - Risk analysis (RISK-COMP-004, RISK-COMP-005, RISK-COMP-006)
- [ADR-001: Lean 4.28.0-rc1 Migration](./ADR-001-lean-4.28.0-rc1-migration.md)
- [ADR-002: ProofWidgets Dependency Removal](./ADR-002-proofwidgets-removal.md)

---

## Appendix: Version Research

This section will be updated with the results of Phase 1 research.

### Target Versions (To Be Determined)

| Package | Target Version | Commit/Tag | Notes |
|---------|----------------|------------|-------|
| batteries | TBD | TBD | Research pending |
| aesop | TBD | TBD | Research pending |
| mathlib4 | TBD | TBD | Research pending |

### Breaking Changes Summary (To Be Populated)

| Dependency | Breaking Changes | Migration Notes |
|------------|------------------|-----------------|
| batteries | TBD | TBD |
| aesop | TBD | TBD |
| mathlib4 | TBD | TBD |
