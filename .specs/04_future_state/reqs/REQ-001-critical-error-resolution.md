# REQ-001: Critical Error Resolution

**Status:** Draft  
**Priority:** Critical (P0)  
**Category:** Build System / Compilation  
**Created:** 2026-01-31  
**Phase:** Phase 5 - Requirement Sharding

---

## 1. Overview

This requirement addresses the critical blocking errors that prevent the Morph project from compiling on Lean 4.28.0-rc1. These errors must be resolved before any other remediation work can proceed.

---

## 2. Background

The Morph project currently has two critical blocking errors:

1. **Unterminated comment** in [`Morph/Specs/ArcAffineIntegration/Examples.lean`](../../Morph/Specs/ArcAffineIntegration/Examples.lean:237)
2. **ProofWidgets dependency incompatibility** causing Lake workspace configuration to fail

These errors are documented in:
- [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) (Section 2.2)
- [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) (RISK-COMP-002, RISK-COMP-007)
- [ADR-002: ProofWidgets Dependency Removal](../../02_adrs/ADR-002-proofwidgets-removal.md)

---

## 3. Functional Requirements

### 3.1 FR-001.1: Fix Unterminated Comment

**Description:** The file [`Morph/Specs/ArcAffineIntegration/Examples.lean`](../../Morph/Specs/ArcAffineIntegration/Examples.lean:237) contains an unterminated comment at line 237 that prevents the file from being parsed.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Comment is properly terminated | File parses without syntax errors |
| File compiles successfully | `lean --make Morph/Specs/ArcAffineIntegration/Examples.lean` exits with code 0 |
| No syntax errors in output | No "unterminated comment" error messages |

**Implementation Notes:**

- The file ends without a closing comment delimiter (`-/` or `--`)
- The fix should add the appropriate closing delimiter at the end of the file
- Verify the comment structure to determine the correct closing delimiter

### 3.2 FR-001.2: Remove ProofWidgets Dependency

**Description:** The ProofWidgets4 dependency (version v0.0.84) has configuration errors in its lakefile.lean that are incompatible with Lean 4.28.0-rc1. This dependency must be removed from the project's dependency tree.

**Affected Files (7 total):**

1. [`Morph/Executable.lean`](../../Morph/Executable.lean)
2. [`Morph/Specs/AbiAlignmentAlgebra/Lemmas.lean`](../../Morph/Specs/AbiAlignmentAlgebra/Lemmas.lean)
3. [`Morph/Specs/AbiDataRefinement/Examples.lean`](../../Morph/Specs/AbiDataRefinement/Examples.lean)
4. [`Morph/Specs/AbiDataRefinement/Lemmas.lean`](../../Morph/Specs/AbiDataRefinement/Lemmas.lean)
5. [`Morph/Specs/ConcurrencyProcessAlgebra/Examples.lean`](../../Morph/Specs/ConcurrencyProcessAlgebra/Examples.lean)
6. [`Morph/Specs/ConcurrencyProcessAlgebra/Lemmas.lean`](../../Morph/Specs/ConcurrencyProcessAlgebra/Lemmas.lean)
7. [`Morph/Specs/ConcurrencyProcessAlgebra/Spec.lean`](../../Morph/Specs/ConcurrencyProcessAlgebra/Spec.lean)

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| ProofWidgets removed from dependency tree | `grep -r "ProofWidgets" .lake/packages/` returns empty |
| Lake workspace configures successfully | `lake configure` exits with code 0 |
| No ProofWidgets-related errors | Build output contains no ProofWidgets error messages |
| All 7 affected files compile | All affected files compile without errors |

**Implementation Notes:**

- ProofWidgets is a transitive dependency inherited from `leanprover-community`
- Verify no Morph code directly imports or uses ProofWidgets functionality
- Remove ProofWidgets entry from [`lake-manifest.json`](../../lake-manifest.json)
- Clean build artifacts: `rm -rf .lake/packages/proofwidgets && lake clean`

### 3.3 FR-001.3: Resolve Lake Configuration Errors

**Description:** After removing ProofWidgets, ensure the Lake workspace configures successfully without any configuration errors.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Lake workspace configures | `lake configure` exits with code 0 |
| No configuration errors | Build output contains no configuration error messages |
| All dependencies resolve | All dependencies in lake-manifest.json are valid |

**Implementation Notes:**

- Run `lake configure` and verify successful completion
- Check for any remaining dependency configuration issues
- Ensure all remaining dependencies are compatible with Lean 4.28.0-rc1

---

## 4. Non-Functional Requirements

### 4.1 NFR-001.1: Backward Compatibility

**Description:** Changes must not break existing functionality that does not depend on the errors being fixed.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No regressions in unaffected files | All files not affected by changes still compile |
| Test suite passes | All tests in [`Morph/Tests/`](../../Morph/Tests/) pass |

### 4.2 NFR-001.2: Minimal Changes

**Description:** Only the minimal changes necessary to fix the errors should be made.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Changes are localized | Only affected files are modified |
| No unnecessary refactoring | Code review confirms minimal changes |

---

## 5. Dependencies

### 5.1 Internal Dependencies

| Requirement | Dependency Type | Description |
|-------------|-----------------|-------------|
| REQ-002 | Follows | Dependency version alignment depends on critical errors being resolved |
| REQ-003 | Follows | Syntax standards compliance depends on compilation working |
| REQ-004 | Follows | Deprecated API remediation depends on compilation working |

### 5.2 External Dependencies

| Dependency | Version | Status |
|------------|---------|--------|
| Lean Toolchain | v4.28.0-rc1 | Already configured |
| Lake | Latest compatible | Required for configuration |

---

## 6. Verification Plan

### 6.1 Pre-Implementation Verification

```bash
# Verify current error state
lean --make Morph/Specs/ArcAffineIntegration/Examples.lean 2>&1 | grep "unterminated comment"

# Verify ProofWidgets presence
grep -r "ProofWidgets" .lake/packages/

# Verify Lake configuration failure
lake configure 2>&1 | head -20
```

### 6.2 Post-Implementation Verification

```bash
# Verify unterminated comment is fixed
lean --make Morph/Specs/ArcAffineIntegration/Examples.lean

# Verify ProofWidgets removal
grep -r "ProofWidgets" .lake/packages/ || echo "ProofWidgets removed"

# Verify Lake configuration
lake configure

# Verify affected files compile
lake build Morph.Specs.ArcAffineIntegration
lake build Morph.Specs.AbiAlignmentAlgebra
lake build Morph.Specs.AbiDataRefinement
lake build Morph.Specs.ConcurrencyProcessAlgebra
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
| Syntax Errors | 0 | `lake build` error output |
| Configuration Errors | 0 | `lake configure` error output |
| Affected Files Compiled | 7/7 | Individual file compilation |
| Total Compilation Success | 100% | `lake build` exit code |

---

## 8. Related Documents

| Document | Type | Reference |
|----------|------|-----------|
| [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) | Current State | Section 2.2 |
| [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) | Future State | Section 2.1 |
| [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) | Threat Model | RISK-COMP-002, RISK-COMP-007 |
| [ADR-001: Lean 4.28.0-rc1 Migration](../../02_adrs/ADR-001-lean-4.28.0-rc1-migration.md) | ADR | Phase 1 |
| [ADR-002: ProofWidgets Dependency Removal](../../02_adrs/ADR-002-proofwidgets-removal.md) | ADR | Full document |

---

## 9. Change History

| Date | Version | Author | Description |
|------|---------|--------|-------------|
| 2026-01-31 | 1.0 | System | Initial requirement specification |

---

## 10. Appendix: Error Details

### A.1 ProofWidgets Configuration Errors

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

### A.2 Unterminated Comment Details

| File | Line | Issue |
|------|------|-------|
| [`Morph/Specs/ArcAffineIntegration/Examples.lean`](../../Morph/Specs/ArcAffineIntegration/Examples.lean) | 237 | File ends without closing comment delimiter |
