# REQ-003: Syntax Standards Compliance

**Status:** Draft  
**Priority:** Medium (P2)  
**Category:** Code Quality / Standards  
**Created:** 2026-01-31  
**Phase:** Phase 5 - Requirement Sharding

---

## 1. Overview

This requirement ensures that all files in the Morph project follow Lean 4 syntax standards, including correct comment syntax, proper indentation, and consistent naming conventions. This requirement addresses syntax issues that may have been introduced during the version migration or existed in the original codebase.

---

## 2. Background

The Morph project must adhere to Lean 4 coding standards to ensure maintainability, readability, and compatibility with the Lean 4.28.0-rc1 toolchain. While no deprecated syntax was detected in the project's own files, there is one known syntax error that needs to be fixed.

### Current State

| File | Issue | Line |
|------|--------|------|
| [`Morph/Specs/ArcAffineIntegration/Examples.lean`](../../Morph/Specs/ArcAffineIntegration/Examples.lean:237) | Unterminated comment | 237 |

### Coding Standards Reference

The coding standards are defined in [`.specs/01_standards/coding_standards.md`](../01_standards/coding_standards.md):

| Standard | Requirement | Reference |
|----------|--------------|------------|
| File Header | Copyright and SPDX license header | Lines 66-73 |
| Module Documentation | Complete docstring with status, mapping summary | Lines 76-107 |
| Namespace Declaration | All definitions within namespace | Lines 108-119 |
| Indentation | 2 spaces, no tabs | Lines 419-424 |
| Line Length | Max 100 characters | Lines 425-430 |
| Trailing Whitespace | None | Lines 439-441 |
| Naming Conventions | PascalCase for types, camelCase for functions | Lines 468-506 |

### Related Documents

- [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) (Section 3)
- [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) (Section 3.3)
- [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) (RISK-COMP-007, RISK-COMP-008)
- [`.specs/01_standards/coding_standards.md`](../01_standards/coding_standards.md)

---

## 3. Functional Requirements

### 3.1 FR-003.1: Fix Unterminated Comment

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

### 3.2 FR-003.2: Verify Comment Syntax

**Description:** Ensure all comments in the codebase use correct Lean 4 comment syntax.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| All line comments use `--` | No deprecated line comment syntax found |
| All block comments use `/- ... -/` | No deprecated block comment syntax found |
| Module docstrings use `/-! ... -/` | All module docstrings use correct syntax |

**Implementation Notes:**

- Lean 4 supports multiple comment syntaxes, but some older patterns may be deprecated
- Use `--` for single-line comments
- Use `/- ... -/` for multi-line comments
- Use `/-! ... -/` for module-level documentation
- Scan all `.lean` files for deprecated comment patterns

### 3.3 FR-003.3: Verify Indentation

**Description:** Ensure all files use consistent indentation (2 spaces, no tabs) as specified in the coding standards.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| All indentation uses 2 spaces | No tabs found in `.lean` files |
| Indentation is consistent | No mixed indentation (spaces and tabs) |
| EditorConfig is respected | [`.editorconfig`](../../.editorconfig) settings are followed |

**Implementation Notes:**

- The project has an [`.editorconfig`](../../.editorconfig) file that specifies indentation rules
- Verify all `.lean` files use 2 spaces for indentation
- Replace any tabs with 2 spaces
- Ensure indentation is consistent throughout each file

### 3.4 FR-003.4: Verify Naming Conventions

**Description:** Ensure all identifiers follow Lean 4 naming conventions as specified in the coding standards.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Types use PascalCase | All inductive, structure, class names use PascalCase |
| Functions use camelCase | All function/definition names use camelCase |
| Constants use lowerCamelCase or UPPER_CASE | Constants follow appropriate naming |
| Names are descriptive | No single-letter or cryptic names (except in specific contexts) |

**Implementation Notes:**

- PascalCase for types: `MyType`, `MyInductive`
- camelCase for functions: `myFunction`, `myDefinition`
- UPPER_CASE for constants: `MY_CONSTANT`
- Descriptive names that convey meaning
- Avoid abbreviations unless widely understood

### 3.5 FR-003.5: Verify Line Length

**Description:** Ensure all lines are within the maximum line length (100 characters) as specified in the coding standards.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No lines exceed 100 characters | All lines are 100 characters or less |
| Long lines are properly broken | Complex expressions are split across multiple lines |

**Implementation Notes:**

- Maximum line length is 100 characters
- Break long lines at logical points
- Use indentation to improve readability of multi-line expressions
- Consider extracting complex expressions to named functions

### 3.6 FR-003.6: Verify Trailing Whitespace

**Description:** Ensure no lines have trailing whitespace.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No trailing whitespace | No lines end with spaces or tabs |
| Files end with newline | All files end with a single newline character |

**Implementation Notes:**

- Remove trailing whitespace from all lines
- Ensure all files end with a single newline character
- Use editor or linter to automatically detect and fix trailing whitespace

### 3.7 FR-003.7: Verify File Headers

**Description:** Ensure all files have the required copyright and SPDX license header.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| All `.lean` files have copyright header | Copyright notice present at top of file |
| All `.lean` files have SPDX license | SPDX license identifier present |
| Headers are consistent | Header format matches coding standards |

**Implementation Notes:**

- Required header format (from coding standards):
  ```lean
  -- Copyright (c) 2024 The Morph Authors. All rights reserved.
  -- Released under Apache 2.0 license as described in the file LICENSE.
  ```
- Add headers to any files that are missing them
- Ensure headers are consistent across all files

### 3.8 FR-003.8: Verify Module Documentation

**Description:** Ensure all files have complete module documentation with status and mapping summary.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| All files have `/-! ... -/` module docstring | Module documentation present |
| Documentation includes status | Status field (e.g., "Draft", "Stable") is specified |
| Documentation includes mapping summary | Summary of module contents is provided |

**Implementation Notes:**

- Module docstring format:
  ```lean
  /-!
  # Module Title

  Status: [Draft | Stable | Experimental]

  Brief description of the module's purpose and contents.

  ## Main Definitions

  - Definition1: Description
  - Definition2: Description

  ## Main Theorems

  - Theorem1: Description
  - Theorem2: Description
  -/
  ```
- Add module docstrings to any files that are missing them
- Ensure docstrings are complete and accurate

---

## 4. Non-Functional Requirements

### 4.1 NFR-003.1: Consistency

**Description:** All files should follow consistent coding standards.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Standards are applied uniformly | No file deviates from coding standards |
| Code review confirms consistency | Peer review confirms consistent application |

### 4.2 NFR-003.2: Automation

**Description:** Use automated tools to detect and fix syntax standards violations where possible.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Linter is configured | Lean linter or equivalent tool is configured |
| CI/CD includes syntax checks | Syntax standards are checked in CI/CD pipeline |
| Pre-commit hooks are configured | Syntax checks run before commits |

### 4.3 NFR-003.3: Minimal Changes

**Description:** Only the minimal changes necessary to fix syntax standards violations should be made.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Changes are localized | Only syntax violations are fixed |
| No unnecessary refactoring | Code review confirms minimal changes |

---

## 5. Dependencies

### 5.1 Internal Dependencies

| Requirement | Dependency Type | Description |
|-------------|-----------------|-------------|
| REQ-001 | Precedes | Critical errors must be resolved before syntax standards compliance |
| REQ-002 | Precedes | Dependency updates must be complete before syntax standards compliance |
| REQ-004 | Independent | Deprecated API remediation can proceed in parallel |

### 5.2 External Dependencies

| Dependency | Version | Status |
|------------|---------|--------|
| Lean Toolchain | v4.28.0-rc1 | Required for syntax checking |
| EditorConfig | Latest | Required for editor integration |

---

## 6. Verification Plan

### 6.1 Pre-Implementation Verification

```bash
# Check for unterminated comments
grep -rn "/-[^!]" Morph/ | head -20

# Check for tabs
grep -P "\t" Morph/*.lean

# Check for trailing whitespace
grep -rn " $" Morph/*.lean

# Check for long lines
awk 'length > 100' Morph/*.lean

# Check for missing file headers
head -3 Morph/*.lean | grep -L "Copyright"

# Check for missing module documentation
head -20 Morph/*.lean | grep -L "/-!"
```

### 6.2 Post-Implementation Verification

```bash
# Verify no unterminated comments
lean --make Morph/Specs/ArcAffineIntegration/Examples.lean

# Verify no tabs
grep -P "\t" Morph/*.lean || echo "No tabs found"

# Verify no trailing whitespace
grep -rn " $" Morph/*.lean || echo "No trailing whitespace found"

# Verify no long lines
awk 'length > 100' Morph/*.lean || echo "No long lines found"

# Verify all files have headers
head -3 Morph/*.lean | grep "Copyright" | wc -l

# Verify all files have module documentation
head -20 Morph/*.lean | grep "/-!" | wc -l

# Verify all files compile
lake build
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
| Unterminated Comments | 0 | File parsing |
| Tabs in Files | 0 | `grep -P "\t"` |
| Trailing Whitespace | 0 | `grep -rn " $"` |
| Lines Exceeding 100 Characters | 0 | `awk 'length > 100'` |
| Files with Headers | 100% | Header presence check |
| Files with Module Documentation | 100% | Module docstring presence check |

---

## 8. Related Documents

| Document | Type | Reference |
|----------|------|-----------|
| [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) | Current State | Section 3 |
| [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) | Future State | Section 3.3 |
| [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) | Threat Model | RISK-COMP-007, RISK-COMP-008 |
| [`.specs/01_standards/coding_standards.md`](../01_standards/coding_standards.md) | Coding Standards | Full document |

---

## 9. Change History

| Date | Version | Author | Description |
|------|---------|--------|-------------|
| 2026-01-31 | 1.0 | System | Initial requirement specification |

---

## 10. Appendix: Syntax Standards Checklist

### A.1 File Structure Checklist

- [ ] File has copyright header
- [ ] File has SPDX license identifier
- [ ] File has module documentation (`/-! ... -/`)
- [ ] Module documentation includes status
- [ ] Module documentation includes mapping summary
- [ ] File ends with newline

### A.2 Comment Syntax Checklist

- [ ] Line comments use `--`
- [ ] Block comments use `/- ... -/`
- [ ] Module docstrings use `/-! ... -/`
- [ ] No unterminated comments
- [ ] No deprecated comment patterns

### A.3 Formatting Checklist

- [ ] Indentation uses 2 spaces (no tabs)
- [ ] Indentation is consistent
- [ ] No trailing whitespace
- [ ] No lines exceed 100 characters
- [ ] Long lines are properly broken

### A.4 Naming Checklist

- [ ] Types use PascalCase
- [ ] Functions use camelCase
- [ ] Constants use lowerCamelCase or UPPER_CASE
- [ ] Names are descriptive
- [ ] No cryptic abbreviations (except widely understood)

### A.5 Tools and Automation

- [ ] [`.editorconfig`](../../.editorconfig) is configured
- [ ] Linter is configured for Lean
- [ ] CI/CD includes syntax checks
- [ ] Pre-commit hooks are configured
- [ ] Editor settings respect coding standards
