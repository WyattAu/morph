# Morph Language Lean 4.28.0-rc1 Migration - Execution Graph

**Phase 9 - Tasking**
**Generated:** 2026-01-31
**Purpose:** Comprehensive task breakdown for executing the Morph project migration to Lean 4.28.0-rc1

---

## Executive Summary

This document defines the complete execution graph of tasks for the Morph project migration from Lean 4.10.0 to Lean 4.28.0-rc1. The tasks are organized into batches matching the migration process, with clear priorities, dependencies, and acceptance criteria.

### Task Overview

| Batch | Description | Task Count | Priority | Status |
|-------|-------------|------------|----------|--------|
| Batch 1 | Critical Error Resolution | 3 | P0 (Critical) | ⏳ Pending |
| Batch 2 | Dependency Version Alignment | 4 | P1 (High) | ⏳ Pending |
| Batch 3 | Code Standards Compliance | 3 | P2 (Medium) | ⏳ Pending |
| Batch 4 | Deprecated API Remediation | 2 | P2 (Medium) | ⏳ Pending |
| Batch 5 | Verification | 3 | P0 (Critical) | ⏳ Pending |

**Total Tasks:** 15

---

## Batch 1: Critical Error Resolution (P0)

### TASK-001: Fix Unterminated Comment in ArcAffineIntegration/Examples.lean

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-001 |
| **Title** | Fix Unterminated Comment in ArcAffineIntegration/Examples.lean |
| **Priority** | Critical (P0) |
| **Estimated Effort** | 0.5 hours |
| **Assignee Role** | Lean Developer |
| **Dependencies** | None |
| **Related Requirements** | REQ-001 (FR-001.1), REQ-003 (FR-003.1) |
| **Related Risks** | RISK-COMP-007 |

#### Description

The file [`Morph/Specs/ArcAffineIntegration/Examples.lean`](../Morph/Specs/ArcAffineIntegration/Examples.lean:237) contains an unterminated comment at line 237 that prevents the file from being parsed. This is a blocking error that must be resolved before any other migration work can proceed.

#### Task Steps

1. Open [`Morph/Specs/ArcAffineIntegration/Examples.lean`](../Morph/Specs/ArcAffineIntegration/Examples.lean:237)
2. Identify the unterminated comment structure
3. Add the appropriate closing comment delimiter (`-/` or `--`) at the end of the file
4. Save the file
5. Verify the file parses without syntax errors

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| Comment is properly terminated | File parses without syntax errors |
| File compiles successfully | `lean --make Morph/Specs/ArcAffineIntegration/Examples.lean` exits with code 0 |
| No syntax errors in output | No "unterminated comment" error messages |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-001-critical-error-resolution.md`](./04_future_state/reqs/REQ-001-critical-error-resolution.md) (Section 3.1)
- [`.specs/04_future_state/reqs/REQ-003-syntax-standards-compliance.md`](./04_future_state/reqs/REQ-003-syntax-standards-compliance.md) (Section 3.1)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (TS-001)

---

### TASK-002: Remove ProofWidgets Dependency from lakefile.lean

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-002 |
| **Title** | Remove ProofWidgets Dependency from lakefile.lean |
| **Priority** | Critical (P0) |
| **Estimated Effort** | 1 hour |
| **Assignee Role** | DevOps Engineer |
| **Dependencies** | TASK-001 |
| **Related Requirements** | REQ-001 (FR-001.2) |
| **Related Risks** | RISK-COMP-002 |

#### Description

The ProofWidgets4 dependency (version v0.0.84) has configuration errors in its lakefile.lean that are incompatible with Lean 4.28.0-rc1. This dependency must be removed from the project's dependency tree. ProofWidgets is a transitive dependency inherited from `leanprover-community` and is not directly used by Morph code.

#### Task Steps

1. Verify no Morph code directly imports or uses ProofWidgets functionality
2. Remove ProofWidgets entry from [`lake-manifest.json`](../lake-manifest.json)
3. Remove ProofWidgets entry from [`lakefile.lean`](../lakefile.lean) if present
4. Clean build artifacts: `rm -rf .lake/packages/proofwidgets && lake clean`
5. Run `lake configure` to verify workspace configuration succeeds
6. Verify all affected files compile

#### Affected Files (7 total)

1. [`Morph/Executable.lean`](../Morph/Executable.lean)
2. [`Morph/Specs/AbiAlignmentAlgebra/Lemmas.lean`](../Morph/Specs/AbiAlignmentAlgebra/Lemmas.lean)
3. [`Morph/Specs/AbiDataRefinement/Examples.lean`](../Morph/Specs/AbiDataRefinement/Examples.lean)
4. [`Morph/Specs/AbiDataRefinement/Lemmas.lean`](../Morph/Specs/AbiDataRefinement/Lemmas.lean)
5. [`Morph/Specs/ConcurrencyProcessAlgebra/Examples.lean`](../Morph/Specs/ConcurrencyProcessAlgebra/Examples.lean)
6. [`Morph/Specs/ConcurrencyProcessAlgebra/Lemmas.lean`](../Morph/Specs/ConcurrencyProcessAlgebra/Lemmas.lean)
7. [`Morph/Specs/ConcurrencyProcessAlgebra/Spec.lean`](../Morph/Specs/ConcurrencyProcessAlgebra/Spec.lean)

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| ProofWidgets removed from dependency tree | `grep -r "ProofWidgets" .lake/packages/` returns empty |
| Lake workspace configures successfully | `lake configure` exits with code 0 |
| No ProofWidgets-related errors | Build output contains no ProofWidgets error messages |
| All 7 affected files compile | All affected files compile without errors |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-001-critical-error-resolution.md`](./04_future_state/reqs/REQ-001-critical-error-resolution.md) (Section 3.2)
- [ADR-002: ProofWidgets Dependency Removal](./02_adrs/ADR-002-proofwidgets-removal.md)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (TS-002)

---

### TASK-003: Clean Lake Cache and Regenerate Manifest

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-003 |
| **Title** | Clean Lake Cache and Regenerate Manifest |
| **Priority** | Critical (P0) |
| **Estimated Effort** | 0.5 hours |
| **Assignee Role** | DevOps Engineer |
| **Dependencies** | TASK-002 |
| **Related Requirements** | REQ-001 (FR-001.3) |
| **Related Risks** | RISK-COMP-002 |

#### Description

After removing ProofWidgets, ensure the Lake workspace configures successfully and the manifest is regenerated without any configuration errors. This task validates that the critical error resolution is complete.

#### Task Steps

1. Clean all Lake build artifacts: `lake clean`
2. Remove all package directories: `rm -rf .lake/packages`
3. Run `lake configure` and verify successful completion
4. Run `lake update` to regenerate [`lake-manifest.json`](../lake-manifest.json)
5. Check for any remaining dependency configuration issues
6. Verify all remaining dependencies are compatible with Lean 4.28.0-rc1

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| Lake workspace configures | `lake configure` exits with code 0 |
| No configuration errors | Build output contains no configuration error messages |
| All dependencies resolve | All dependencies in lake-manifest.json are valid |
| Lake manifest is regenerated | `lake update` completes successfully |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-001-critical-error-resolution.md`](./04_future_state/reqs/REQ-001-critical-error-resolution.md) (Section 3.3)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (IT-BLD-001, IT-BLD-002)

---

## Batch 2: Dependency Version Alignment (P1)

### TASK-010: Verify Lean Toolchain at v4.28.0-rc1

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-010 |
| **Title** | Verify Lean Toolchain at v4.28.0-rc1 |
| **Priority** | High (P1) |
| **Estimated Effort** | 0.25 hours |
| **Assignee Role** | DevOps Engineer |
| **Dependencies** | TASK-003 |
| **Related Requirements** | REQ-002 (FR-002.1) |
| **Related Risks** | RISK-COMP-001 |

#### Description

Ensure the Lean toolchain is correctly set to v4.28.0-rc1. The toolchain is already configured in [`lean-toolchain`](../lean-toolchain), but this task verifies it is correctly installed and available.

#### Task Steps

1. Verify [`lean-toolchain`](../lean-toolchain) contains `leanprover/lean4:v4.28.0-rc1`
2. Verify `lean --version` returns v4.28.0-rc1
3. If toolchain is not available, install it using `elan`
4. Document any toolchain installation issues

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| Toolchain version is v4.28.0-rc1 | `cat lean-toolchain` returns `leanprover/lean4:v4.28.0-rc1` |
| Toolchain is available | `lean --version` returns v4.28.0-rc1 |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-002-dependency-version-alignment.md`](./04_future_state/reqs/REQ-002-dependency-version-alignment.md) (Section 3.1)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (IT-DEP-001)

---

### TASK-011: Update Batteries to v4.28.0-Compatible Version

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-011 |
| **Title** | Update Batteries to v4.28.0-Compatible Version |
| **Priority** | High (P1) |
| **Estimated Effort** | 2 hours |
| **Assignee Role** | DevOps Engineer |
| **Dependencies** | TASK-010 |
| **Related Requirements** | REQ-002 (FR-002.2) |
| **Related Risks** | RISK-COMP-001, RISK-COMP-005 |

#### Description

Update the batteries dependency from v4.10.0 to a version compatible with Lean 4.28.0-rc1. This task involves researching the available versions, selecting the most recent stable version, and updating the project configuration.

#### Task Steps

1. Research the batteries repository for v4.28.0-compatible tags/branches
2. Choose the most recent stable version compatible with Lean 4.28.0-rc1
3. Prefer official releases over development branches
4. Update [`lakefile.toml`](../lakefile.toml) with the new version
5. Update [`lakefile.lean`](../lakefile.lean) with the new version if present
6. Run `lake update` to regenerate [`lake-manifest.json`](../lake-manifest.json)
7. Verify batteries compiles with v4.28.0-rc1

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| Batteries version is v4.28.0-compatible | `grep batteries lakefile.toml` shows compatible version |
| Batteries compiles with v4.28.0-rc1 | `lake build Batteries` succeeds |
| No type errors from batteries | Build output contains no batteries-related type errors |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-002-dependency-version-alignment.md`](./04_future_state/reqs/REQ-002-dependency-version-alignment.md) (Section 3.2)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (IT-DEP-002, TS-003)

---

### TASK-012: Update Aesop to v4.28.0-Compatible Version

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-012 |
| **Title** | Update Aesop to v4.28.0-Compatible Version |
| **Priority** | High (P1) |
| **Estimated Effort** | 2 hours |
| **Assignee Role** | DevOps Engineer |
| **Dependencies** | TASK-011 |
| **Related Requirements** | REQ-002 (FR-002.3) |
| **Related Risks** | RISK-COMP-001, RISK-COMP-006 |

#### Description

Update the aesop dependency from v4.10.0 to a version compatible with Lean 4.28.0-rc1. This task involves researching the available versions, selecting the most recent stable version, and updating the project configuration.

#### Task Steps

1. Research the aesop repository for v4.28.0-compatible tags/branches
2. Choose the most recent stable version compatible with Lean 4.28.0-rc1
3. Prefer official releases over development branches
4. Update [`lakefile.toml`](../lakefile.toml) with the new version
5. Update [`lakefile.lean`](../lakefile.lean) with the new version if present
6. Run `lake update` to regenerate [`lake-manifest.json`](../lake-manifest.json)
7. Verify aesop compiles with v4.28.0-rc1

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| Aesop version is v4.28.0-compatible | `grep aesop lakefile.toml` shows compatible version |
| Aesop compiles with v4.28.0-rc1 | `lake build Aesop` succeeds |
| No tactic errors from aesop | Build output contains no aesop-related tactic errors |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-002-dependency-version-alignment.md`](./04_future_state/reqs/REQ-002-dependency-version-alignment.md) (Section 3.3)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (IT-DEP-003, TS-003)

---

### TASK-013: Update Mathlib4 to v4.28.0-Compatible Version

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-013 |
| **Title** | Update Mathlib4 to v4.28.0-Compatible Version |
| **Priority** | High (P1) |
| **Estimated Effort** | 4 hours |
| **Assignee Role** | DevOps Engineer |
| **Dependencies** | TASK-012 |
| **Related Requirements** | REQ-002 (FR-002.4) |
| **Related Risks** | RISK-COMP-001, RISK-COMP-004 |

#### Description

Update the mathlib4 dependency from v4.10.0 to a version compatible with Lean 4.28.0-rc1. This is the most complex dependency update due to the extensive breaking changes in mathlib4 between v4.10.0 and v4.28.0-rc1.

#### Task Steps

1. Research the mathlib4 repository for v4.28.0-compatible tags/branches
2. Choose the most recent stable version compatible with Lean 4.28.0-rc1
3. Prefer official releases over development branches
4. Update [`lakefile.toml`](../lakefile.toml) with the new version
5. Update [`lakefile.lean`](../lakefile.lean) with the new version if present
6. Run `lake update` to regenerate [`lake-manifest.json`](../lake-manifest.json)
7. Clean build artifacts: `lake clean && rm -rf .lake/packages`
8. Verify mathlib4 compiles with v4.28.0-rc1

#### Breaking Changes to Document

- Module reorganization
- Theorem renaming
- Type class hierarchy updates
- Proof automation strategy modifications

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| Mathlib4 version is v4.28.0-compatible | `grep mathlib lakefile.toml` shows compatible version |
| Mathlib4 compiles with v4.28.0-rc1 | `lake build Mathlib` succeeds |
| No import errors from mathlib4 | Build output contains no mathlib4-related import errors |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-002-dependency-version-alignment.md`](./04_future_state/reqs/REQ-002-dependency-version-alignment.md) (Section 3.4)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (IT-DEP-004, TS-003)

---

## Batch 3: Code Standards Compliance (P2)

### TASK-020: Verify Comment Syntax Across All Files

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-020 |
| **Title** | Verify Comment Syntax Across All Files |
| **Priority** | Medium (P2) |
| **Estimated Effort** | 2 hours |
| **Assignee Role** | Lean Developer |
| **Dependencies** | TASK-013 |
| **Related Requirements** | REQ-003 (FR-003.2) |
| **Related Risks** | RISK-COMP-007, RISK-COMP-008 |

#### Description

Ensure all comments in the codebase use correct Lean 4 comment syntax. This task scans all `.lean` files for deprecated comment patterns and verifies correct usage.

#### Task Steps

1. Scan all `.lean` files for deprecated comment patterns
2. Verify all line comments use `--`
3. Verify all block comments use `/- ... -/`
4. Verify all module docstrings use `/-! ... -/`
5. Fix any incorrect comment syntax found
6. Verify all files compile successfully

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| All line comments use `--` | No deprecated line comment syntax found |
| All block comments use `/- ... -/` | No deprecated block comment syntax found |
| Module docstrings use `/-! ... -/` | All module docstrings use correct syntax |
| No unterminated comments | All files parse without syntax errors |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-003-syntax-standards-compliance.md`](./04_future_state/reqs/REQ-003-syntax-standards-compliance.md) (Section 3.2)
- [`.specs/01_standards/coding_standards.md`](./01_standards/coding_standards.md)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (UT-SYN-001)

---

### TASK-021: Verify Indentation and Formatting

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-021 |
| **Title** | Verify Indentation and Formatting |
| **Priority** | Medium (P2) |
| **Estimated Effort** | 2 hours |
| **Assignee Role** | Lean Developer |
| **Dependencies** | TASK-020 |
| **Related Requirements** | REQ-003 (FR-003.3, FR-003.5, FR-003.6) |
| **Related Risks** | RISK-QUAL-001 |

#### Description

Ensure all files use consistent formatting as specified in the coding standards: 2-space indentation, no tabs, no trailing whitespace, and lines not exceeding 100 characters.

#### Task Steps

1. Verify all `.lean` files use 2 spaces for indentation
2. Replace any tabs with 2 spaces
3. Remove trailing whitespace from all lines
4. Ensure all files end with a single newline character
5. Verify no lines exceed 100 characters
6. Break long lines at logical points where needed
7. Verify all files compile successfully

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| All indentation uses 2 spaces | No tabs found in `.lean` files |
| Indentation is consistent | No mixed indentation (spaces and tabs) |
| No trailing whitespace | No lines end with spaces or tabs |
| Files end with newline | All files end with a single newline character |
| No lines exceed 100 characters | All lines are 100 characters or less |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-003-syntax-standards-compliance.md`](./04_future_state/reqs/REQ-003-syntax-standards-compliance.md) (Sections 3.3, 3.5, 3.6)
- [`.specs/01_standards/coding_standards.md`](./01_standards/coding_standards.md)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (UT-SYN-002, UT-SYN-003, UT-SYN-004)

---

### TASK-022: Verify Naming Conventions

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-022 |
| **Title** | Verify Naming Conventions |
| **Priority** | Medium (P2) |
| **Estimated Effort** | 3 hours |
| **Assignee Role** | Lean Developer |
| **Dependencies** | TASK-021 |
| **Related Requirements** | REQ-003 (FR-003.4) |
| **Related Risks** | RISK-QUAL-001 |

#### Description

Ensure all identifiers follow Lean 4 naming conventions as specified in the coding standards. This task verifies that types, functions, and constants follow the appropriate naming patterns.

#### Task Steps

1. Verify all inductive, structure, and class names use PascalCase
2. Verify all function/definition names use camelCase
3. Verify constants use lowerCamelCase or UPPER_CASE as appropriate
4. Verify names are descriptive and convey meaning
5. Fix any naming convention violations found
6. Verify all files compile successfully

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| Types use PascalCase | All inductive, structure, class names use PascalCase |
| Functions use camelCase | All function/definition names use camelCase |
| Constants follow conventions | Constants use lowerCamelCase or UPPER_CASE |
| Names are descriptive | No single-letter or cryptic names (except in specific contexts) |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-003-syntax-standards-compliance.md`](./04_future_state/reqs/REQ-003-syntax-standards-compliance.md) (Section 3.4)
- [`.specs/01_standards/coding_standards.md`](./01_standards/coding_standards.md)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (UT-SYN-005)

---

## Batch 4: Deprecated API Remediation (P2)

### TASK-030: Replace Lake.Package.name with baseName/keyName/prettyName

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-030 |
| **Title** | Replace Lake.Package.name with baseName/keyName/prettyName |
| **Priority** | Medium (P2) |
| **Estimated Effort** | 2 hours |
| **Assignee Role** | DevOps Engineer |
| **Dependencies** | TASK-022 |
| **Related Requirements** | REQ-004 (FR-004.1) |
| **Related Risks** | RISK-COMP-008 |

#### Description

Replace all uses of the deprecated `Lake.Package.name` API with the appropriate replacement (`baseName`, `keyName`, or `prettyName`). The `Lake.Package.name` field has been deprecated in favor of more specific fields.

#### Task Steps

1. Search for all uses of `Lake.Package.name` in the codebase
2. For each use, determine the appropriate replacement:
   - Use `baseName` when referring to the package's base identifier
   - Use `keyName` when using the package as a map key
   - Use `prettyName` when displaying the package name to users
3. Replace each `Lake.Package.name` with the appropriate replacement
4. Verify no `Lake.Package.name` usage remains
5. Verify build output contains no deprecation warnings

#### Replacement Reference

| Replacement | Purpose |
|-------------|---------|
| `baseName` | The base name of the package (e.g., "mathlib") |
| `keyName` | The key used to reference the package (e.g., "mathlib") |
| `prettyName` | The human-readable name (e.g., "Mathlib") |

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| No `Lake.Package.name` usage | `grep -r "Lake.Package.name" .lake/packages/` returns empty |
| Build output contains no deprecation warnings | `lake build` contains no "deprecated" warnings |
| All package names are correctly referenced | Package names resolve correctly |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-004-deprecated-api-remediation.md`](./04_future_state/reqs/REQ-004-deprecated-api-remediation.md) (Section 3.1)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (TS-005)

---

### TASK-031: Replace String.trim with String.trimAscii

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-031 |
| **Title** | Replace String.trim with String.trimAscii |
| **Priority** | Medium (P2) |
| **Estimated Effort** | 2 hours |
| **Assignee Role** | Lean Developer |
| **Dependencies** | TASK-030 |
| **Related Requirements** | REQ-004 (FR-004.2) |
| **Related Risks** | RISK-COMP-008 |

#### Description

Replace all uses of the deprecated `String.trim` API with `String.trimAscii`. The key difference is in the return type: `String.trimAscii` returns `String.Slice` instead of `String`.

#### Task Steps

1. Search for all uses of `String.trim` in the codebase
2. For each use, replace `String.trim` with `String.trimAscii`
3. Update type signatures to handle the `String.Slice` return type
4. If a `String` is needed instead of `String.Slice`, use `.toString` on the slice
5. Verify no `String.trim` usage remains
6. Verify build output contains no deprecation warnings

#### Type Signature Change

| Function | Return Type | Description |
|----------|--------------|-------------|
| `String.trim` (deprecated) | `String → String` | Returns a trimmed string |
| `String.trimAscii` (current) | `String → String.Slice` | Returns a string slice |

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| No `String.trim` usage | `grep -r "String.trim" .lake/packages/` returns empty |
| Build output contains no deprecation warnings | `lake build` contains no "deprecated" warnings |
| String trimming works correctly | All string trimming operations produce correct results |

#### Related Documents

- [`.specs/04_future_state/reqs/REQ-004-deprecated-api-remediation.md`](./04_future_state/reqs/REQ-004-deprecated-api-remediation.md) (Section 3.2)
- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (TS-005)

---

## Batch 5: Verification (P0)

### TASK-040: Run Full Test Suite

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-040 |
| **Title** | Run Full Test Suite |
| **Priority** | Critical (P0) |
| **Estimated Effort** | 2 hours |
| **Assignee Role** | QA Lead |
| **Dependencies** | TASK-031 |
| **Related Requirements** | All requirements |
| **Related Risks** | All risks |

#### Description

Run the full test suite to verify that all migration work is successful and no regressions have been introduced. This task executes all test scenarios defined in the test plan.

#### Task Steps

1. Run `lake build` and record compilation time
2. Run all unit tests and record results
3. Run all integration tests and record results
4. Run all regression tests and record results
5. Run all smoke tests and record results
6. Document test results in test report
7. Verify zero critical failures

#### Test Categories

1. **Unit Tests:** Syntax validation, type checking, import resolution
2. **Integration Tests:** Dependency configuration, Lake build, module compilation
3. **Regression Tests:** No new errors, previously working code
4. **Smoke Tests:** Critical functionality

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| All unit tests pass | Unit test suite exits with code 0 |
| All integration tests pass | Integration test suite exits with code 0 |
| All regression tests pass | Regression test suite exits with code 0 |
| All smoke tests pass | Smoke test suite exits with code 0 |
| Zero critical failures | No critical test failures |

#### Related Documents

- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (Full document)
- [`.specs/05_migration/rollback_plan.md`](./05_migration/rollback_plan.md) (Rollback triggers)

---

### TASK-041: Verify All Modules Compile

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-041 |
| **Title** | Verify All Modules Compile |
| **Priority** | Critical (P0) |
| **Estimated Effort** | 1 hour |
| **Assignee Role** | QA Lead |
| **Dependencies** | TASK-040 |
| **Related Requirements** | All requirements |
| **Related Risks** | RISK-COMP-001, RISK-COMP-003 |

#### Description

Verify that all modules in the Morph project compile successfully with zero errors. This task validates that the migration has not broken any module compilation.

#### Task Steps

1. Run `lake build` and verify exit code is 0
2. Verify all Core Foundation modules compile
3. Verify all Memory domain modules compile
4. Verify all Concurrency domain modules compile
5. Verify all Security domain modules compile
6. Verify all Build System domain modules compile
7. Verify all ABI domain modules compile
8. Verify all Language Features domain modules compile

#### Module Domains

| Domain | Modules | Priority |
|--------|---------|----------|
| Core Foundation | CommonTypes, GLOSSARY, MorphLanguage | Critical |
| Memory | MemoryModel, MemoryAcyclicity, MemoryAffineLogic | High |
| Concurrency | LayeredConcurrency, ConcurrencyProcessAlgebra, SchedulingModes, SchedulerRandomizedStealing | High |
| Security | SecurityFlow, SecurityOCap, LicenseDeonticLogic | High |
| Build System | BuildLattice, DependencySat, ModuleSystem, ModuleExistential | Medium |
| ABI | AbiAlignmentAlgebra, AbiDataRefinement | Medium |
| Language Features | 21 modules | Medium |

#### Acceptance Criteria

| Criterion | Verification Method |
|-----------|---------------------|
| All modules compile | `lake build` exits with code 0 |
| Zero compilation errors | `lake build` error output contains 0 errors |
| All domain modules compile | All domain modules verified |

#### Related Documents

- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (IT-MOD-001 through IT-MOD-007, TS-004)
- [`.specs/04_future_state/reqs/index.md`](./04_future_state/reqs/index.md) (Module domains)

---

### TASK-042: Verify Zero Errors and Zero Warnings

| Attribute | Value |
|-----------|-------|
| **Task ID** | TASK-042 |
| **Title** | Verify Zero Errors and Zero Warnings |
| **Priority** | Critical (P0) |
| **Estimated Effort** | 1 hour |
| **Assignee Role** | QA Lead |
| **Dependencies** | TASK-041 |
| **Related Requirements** | All requirements |
| **Related Risks** | All risks |

#### Description

Verify that the build completes with zero errors and zero warnings. This is the final verification task that confirms the migration is complete and successful.

#### Task Steps

1. Run `lake build` and capture full output
2. Count total errors: `lake build 2>&1 | grep -c "error:" || echo "0"`
3. Count total warnings: `lake build 2>&1 | grep -c "warning:" || echo "0"`
4. Verify no specific error types:
   - No type errors
   - No import errors
   - No syntax errors
   - No tactic errors
5. Verify no specific warning types:
   - No deprecated warnings
   - No unused variable warnings
   - No discarded term warnings
6. Document final build metrics
7. Create migration completion report

#### Success Metrics

| Metric | Target | Measurement Method |
|--------|--------|-------------------|
| Syntax Errors | 0 | `lake build` error output |
| Type Errors | 0 | `lake build` error output |
| Import Errors | 0 | `lake build` error output |
| Tactic Errors | 0 | `lake build` error output |
| Deprecated Warnings | 0 | `lake build` warning output |
| Unused Variable Warnings | 0 | `lake build` warning output |
| Compilation Success | 100% | `lake build` exit code |

#### Acceptance Criteria

| Criterion | Measurement | Pass Condition |
|-----------|-------------|---------------|
| Zero errors | Error count | 0 errors |
| Zero warnings | Warning count | 0 warnings |
| Build succeeds | Exit code | Exit code 0 |
| All modules compile | Module compilation | All modules compile |

#### Related Documents

- [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) (TS-004, TS-005)
- [`.specs/05_migration/rollback_plan.md`](./05_migration/rollback_plan.md) (Rollback triggers)

---

## Task Dependency Graph

```
Batch 1: Critical Error Resolution (P0)
├─ TASK-001: Fix Unterminated Comment
├─ TASK-002: Remove ProofWidgets Dependency (depends on TASK-001)
└─ TASK-003: Clean Lake Cache (depends on TASK-002)

Batch 2: Dependency Version Alignment (P1)
├─ TASK-010: Verify Lean Toolchain (depends on TASK-003)
├─ TASK-011: Update Batteries (depends on TASK-010)
├─ TASK-012: Update Aesop (depends on TASK-011)
└─ TASK-013: Update Mathlib4 (depends on TASK-012)

Batch 3: Code Standards Compliance (P2)
├─ TASK-020: Verify Comment Syntax (depends on TASK-013)
├─ TASK-021: Verify Indentation (depends on TASK-020)
└─ TASK-022: Verify Naming Conventions (depends on TASK-021)

Batch 4: Deprecated API Remediation (P2)
├─ TASK-030: Replace Lake.Package.name (depends on TASK-022)
└─ TASK-031: Replace String.trim (depends on TASK-030)

Batch 5: Verification (P0)
├─ TASK-040: Run Full Test Suite (depends on TASK-031)
├─ TASK-041: Verify All Modules Compile (depends on TASK-040)
└─ TASK-042: Verify Zero Errors and Zero Warnings (depends on TASK-041)
```

---

## Effort Estimation Summary

| Batch | Total Effort | Critical Path |
|-------|--------------|---------------|
| Batch 1: Critical Error Resolution | 2 hours | 2 hours |
| Batch 2: Dependency Version Alignment | 8.25 hours | 8.25 hours |
| Batch 3: Code Standards Compliance | 7 hours | 7 hours |
| Batch 4: Deprecated API Remediation | 4 hours | 4 hours |
| Batch 5: Verification | 4 hours | 4 hours |
| **Total** | **25.25 hours** | **25.25 hours** |

---

## Risk Mitigation

### Rollback Triggers

| Trigger Type | Condition | Severity | Rollback To |
|--------------|-----------|----------|-------------|
| Critical Build Failure | Lake workspace configuration fails | Critical | Batch 1 start |
| Critical Build Failure | All modules fail to compile | Critical | Batch 1 start |
| Dependency Incompatibility | Updated dependencies cause type errors | Critical | Batch 2 start |
| Syntax Errors After Migration | New syntax errors introduced | High | Batch 3 start |
| Test Failures | Critical tests fail | Medium | Batch 3 start |

### Rollback Procedures

Rollback procedures are defined in [`.specs/05_migration/rollback_plan.md`](./05_migration/rollback_plan.md) and include:

1. **Pre-Migration Backup:** Complete backup of project state before migration
2. **Phase-Specific Checkpoints:** Backup at each batch completion
3. **Rollback Scenarios:** Detailed procedures for each rollback scenario
4. **Verification:** Post-rollback verification procedures

---

## Related Documents

| Document | Type | Reference |
|----------|------|-----------|
| [`.specs/04_future_state/reqs/`](./04_future_state/reqs/) | Requirements | All requirements |
| [`.specs/04_future_state/design/`](./04_future_state/design/) | Design | Design documents |
| [`.specs/04_future_state/test_plan.md`](./04_future_state/test_plan.md) | Test Plan | Test scenarios |
| [`.specs/05_migration/rollback_plan.md`](./05_migration/rollback_plan.md) | Rollback Plan | Rollback procedures |
| [`.specs/01_standards/coding_standards.md`](./01_standards/coding_standards.md) | Standards | Coding standards |
| [`.specs/03_threat_model/analysis.md`](./03_threat_model/analysis.md) | Threat Model | Risk analysis |

---

## Change Log

| Date | Version | Author | Description |
|------|---------|--------|-------------|
| 2026-01-31 | 1.0 | System | Initial task execution graph created |
