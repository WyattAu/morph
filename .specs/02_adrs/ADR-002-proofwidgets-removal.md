# ADR-002: ProofWidgets Dependency Removal

**Status:** Accepted  
**Date:** 2026-01-31  
**Decision Type:** Technical  
**Related ADRs:** ADR-001, ADR-003  
**Related Documents:** [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md), [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md), [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md)

---

## Context

The ProofWidgets4 dependency (version v0.0.84) is a transitive dependency inherited from the `leanprover-community` dependency group. It has configuration errors in its lakefile.lean that are incompatible with Lean 4.28.0-rc1, making it a blocking error that prevents the Lake workspace from configuring.

### Current State

| Property | Value |
|-----------|-------|
| Package | ProofWidgets4 |
| Version | v0.0.84 |
| Type | Transitive (inherited from leanprover-community) |
| Repository | https://github.com/leanprover-community/ProofWidgets4 |
| Commit | ef8377f31b5535430b6753a974d685b0019d0681 |

### Affected Files (7 total)

The following files are directly affected by the ProofWidgets configuration error:

1. [`Morph/Executable.lean`](../../Morph/Executable.lean)
2. [`Morph/Specs/AbiAlignmentAlgebra/Lemmas.lean`](../../Morph/Specs/AbiAlignmentAlgebra/Lemmas.lean)
3. [`Morph/Specs/AbiDataRefinement/Examples.lean`](../../Morph/Specs/AbiDataRefinement/Examples.lean)
4. [`Morph/Specs/AbiDataRefinement/Lemmas.lean`](../../Morph/Specs/AbiDataRefinement/Lemmas.lean)
5. [`Morph/Specs/ConcurrencyProcessAlgebra/Examples.lean`](../../Morph/Specs/ConcurrencyProcessAlgebra/Examples.lean)
6. [`Morph/Specs/ConcurrencyProcessAlgebra/Lemmas.lean`](../../Morph/Specs/ConcurrencyProcessAlgebra/Lemmas.lean)
7. [`Morph/Specs/ConcurrencyProcessAlgebra/Spec.lean`](../../Morph/Specs/ConcurrencyProcessAlgebra/Spec.lean)

### Specific Errors in ProofWidgets

| Line | Error | Description |
|------|-------|-------------|
| 17 | `BuildJob` type unknown | Missing import or open statement |
| 31 | Application type mismatch | `Hash` vs `String` expected for `BuildTrace.mk` |
| 45, 47 | `BuildJob` type unknown | Missing import or open statement |
| 55 | Cannot synthesize implicit argument | `BuildJob` cannot be synthesized |
| 65 | `BuildJob` type unknown | Missing import or open statement |
| 77 | Invalid field notation on `BuildJob` | Field does not exist |
| 83 | Invalid field `afterReleaseAsync` | Field does not exist in `Lake.Package` |
| 114, 117 | Declaration uses 'sorry' | Incomplete proofs |

### Problems

1. **Blocking Configuration Error (RISK-COMP-002):** Lake workspace configuration fails completely, preventing all compilation.

2. **Cascading Failures:** 7 files directly affected, with potential for cascading failures in dependent modules.

3. **Incompatibility with Lean 4.28.0-rc1:** The ProofWidgets v0.0.84 lakefile.lean uses APIs that have changed or been removed in Lean 4.28.0-rc1.

4. **Transitive Dependency:** ProofWidgets is not a direct dependency of Morph, making it difficult to control or update directly.

5. **Incomplete Proofs:** The ProofWidgets lakefile.lean contains `sorry` declarations, indicating incomplete development.

### Alternatives Considered

#### Alternative 1: Update ProofWidgets to v4.28.0-Compatible Version

**Pros:**
- Preserves ProofWidgets functionality if needed
- Maintains compatibility with upstream ecosystem

**Cons:**
- ProofWidgets may not have a v4.28.0-compatible version available
- As a transitive dependency, updating requires modifying dependency trees
- May require forking or waiting for upstream updates
- Adds maintenance burden for a potentially unused feature
- The v0.0.84 version has incomplete proofs, suggesting instability

#### Alternative 2: Fork and Fix ProofWidgets

**Pros:**
- Immediate control over the dependency
- Can fix the specific compatibility issues

**Cons:**
- Significant maintenance overhead
- Diverges from upstream, creating long-term debt
- Requires ongoing synchronization with upstream changes
- Not sustainable for a transitive dependency

#### Alternative 3: Exclude ProofWidgets via Lake Configuration

**Pros:**
- Can selectively exclude the dependency
- Maintains other dependencies from the same group

**Cons:**
- Lake may not support fine-grained exclusion of transitive dependencies
- May break other dependencies that rely on ProofWidgets
- Complex configuration that may not be supported

#### Alternative 4: Remove ProofWidgets Dependency (Chosen)

**Pros:**
- Immediate resolution of blocking error
- Simplifies dependency tree
- Reduces maintenance burden
- No ongoing synchronization requirements
- Cleaner build configuration

**Cons:**
- Loss of ProofWidgets functionality if it was being used
- May affect other dependencies that depend on ProofWidgets
- Requires verification that ProofWidgets is not needed

---

## Decision

**Remove the ProofWidgets4 dependency** from the Morph project's dependency tree.

### Implementation Plan

#### Phase 1: Verification

1. **Check for ProofWidgets Usage**
   ```bash
   grep -r "import.*ProofWidgets" Morph/
   grep -r "ProofWidgets" Morph/
   ```

2. **Identify Dependent Packages**
   - Determine which direct dependencies import ProofWidgets
   - Assess impact of removal on those dependencies

3. **Confirm Removal Impact**
   - Verify no Morph code uses ProofWidgets
   - Verify no critical functionality depends on ProofWidgets

#### Phase 2: Dependency Removal

1. **Update lakefile.toml**
   - Remove any direct references to ProofWidgets
   - Exclude ProofWidgets from dependency groups if possible

2. **Update lake-manifest.json**
   - Remove ProofWidgets entry from the manifest
   - Clean up associated build artifacts

3. **Clean Build Artifacts**
   ```bash
   rm -rf .lake/packages/proofwidgets
   lake clean
   ```

#### Phase 3: Verification

1. **Lake Configuration**
   ```bash
   lake configure
   ```
   - Verify Lake workspace configures successfully
   - Verify no ProofWidgets-related errors

2. **Compilation**
   ```bash
   lake build
   ```
   - Verify all modules compile without errors
   - Verify the 7 previously affected files now compile

3. **Testing**
   - Run all tests in [`Morph/Tests/`](../../Morph/Tests/)
   - Execute all examples in specification directories
   - Verify no functionality is broken

---

## Consequences

### Positive Consequences

1. **Blocking Error Resolved:** Lake workspace will configure successfully, enabling compilation.

2. **Simplified Dependency Tree:** Removing an unnecessary transitive dependency reduces complexity and potential for future conflicts.

3. **Reduced Maintenance Burden:** No need to track ProofWidgets updates or compatibility issues.

4. **Cleaner Build Configuration:** Fewer dependencies mean faster builds and less surface area for bugs.

5. **No Incomplete Proofs:** Eliminates the risk of incomplete proofs from the ProofWidgets lakefile.lean.

6. **Enables Lean 4.28.0-rc1 Migration:** Removes a critical blocker for the overall migration (see [ADR-001](./ADR-001-lean-4.28.0-rc1-migration.md)).

### Negative Consequences

1. **Loss of ProofWidgets Functionality:** If Morph was using ProofWidgets features, those features will be unavailable.

2. **Potential Dependency Conflicts:** Other dependencies may have implicit dependencies on ProofWidgets that could cause issues.

3. **Limited Interactive Features:** ProofWidgets provides interactive UI elements for Lean 4; removing it may limit interactive development experience.

4. **Re-introduction Complexity:** If ProofWidgets functionality is needed later, re-introducing it may be complex.

### Neutral Consequences

1. **Build Size:** Slightly smaller build artifacts due to one fewer dependency.

2. **Dependency Resolution:** Slightly faster dependency resolution.

3. **Editor Integration:** May affect editor features that rely on ProofWidgets for interactive elements.

---

## Status

**Accepted** - This decision has been approved and implementation is in progress.

### Implementation Status

| Phase | Status | Notes |
|-------|--------|-------|
| Phase 1: Verification | Pending | Need to verify ProofWidgets is not used |
| Phase 2: Dependency Removal | Pending | Depends on Phase 1 |
| Phase 3: Verification | Pending | Depends on Phase 2 |

### Prerequisites

- [ADR-001: Lean 4.28.0-rc1 Migration](./ADR-001-lean-4.28.0-rc1-migration.md) must be accepted
- [ADR-003: Dependency Version Alignment](./ADR-003-dependency-version-alignment.md) may need to be coordinated

---

## References

- [ProofWidgets4 Repository](https://github.com/leanprover-community/ProofWidgets4)
- [Lake Documentation](https://github.com/leanprover/lake)
- [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) - Current state analysis
- [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) - Target state definition
- [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) - Risk analysis (RISK-COMP-002)
- [ADR-001: Lean 4.28.0-rc1 Migration](./ADR-001-lean-4.28.0-rc1-migration.md)
- [ADR-003: Dependency Version Alignment](./ADR-003-dependency-version-alignment.md)
