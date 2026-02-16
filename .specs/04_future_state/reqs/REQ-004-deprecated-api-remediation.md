# REQ-004: Deprecated API Remediation

**Status:** Draft  
**Priority:** Medium (P2)  
**Category:** Code Quality / Compatibility  
**Created:** 2026-01-31  
**Phase:** Phase 5 - Requirement Sharding

---

## 1. Overview

This requirement addresses the replacement of deprecated APIs in the Morph project's dependencies and build configuration. While the project's own code does not currently use deprecated APIs, the mathlib4 dependency has deprecation warnings in its lakefile.lean that should be addressed.

---

## 2. Background

The current mathlib4 dependency (v4.10.0) has deprecation warnings in its lakefile.lean. These warnings will be resolved when mathlib4 is updated to a v4.28.0-compatible version as part of REQ-002, but this requirement documents the specific deprecated APIs that need to be addressed.

### Current State

| Deprecated API | Location | Line | Warning |
|----------------|-----------|------|---------|
| `Lake.Package.name` | `.lake/packages/mathlib/lakefile.lean` | 104:13, 104:24, 124:23 | Use `baseName`, `keyName`, or `prettyName` instead |
| `String.trim` | `.lake/packages/mathlib/lakefile.lean` | 121:53 | Use `String.trimAscii` instead |

**Note:** Type signature change: `String → String.Slice` instead of `String → String`

### Related Documents

- [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) (Section 2.3.1)
- [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) (Section 2.4)
- [ADR-003: Dependency Version Alignment](../../02_adrs/ADR-003-dependency-version-alignment.md)

---

## 3. Functional Requirements

### 3.1 FR-004.1: Replace Lake.Package.name

**Description:** Replace all uses of the deprecated `Lake.Package.name` API with the appropriate replacement (`baseName`, `keyName`, or `prettyName`).

**Context:**

The `Lake.Package.name` field has been deprecated in favor of more specific fields:

| Replacement | Purpose |
|-------------|---------|
| `baseName` | The base name of the package (e.g., "mathlib") |
| `keyName` | The key used to reference the package (e.g., "mathlib") |
| `prettyName` | The human-readable name (e.g., "Mathlib") |

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No `Lake.Package.name` usage | `grep -r "Lake.Package.name" .lake/packages/` returns empty |
| Build output contains no deprecation warnings | `lake build` contains no "deprecated" warnings |
| All package names are correctly referenced | Package names resolve correctly |

**Implementation Notes:**

- This deprecation is in the mathlib4 dependency's lakefile.lean
- The fix will be applied when mathlib4 is updated to a v4.28.0-compatible version
- If the updated version still has this issue, it should be reported upstream
- For custom lakefile.lean files, use the appropriate replacement:
  - Use `baseName` when referring to the package's base identifier
  - Use `keyName` when using the package as a map key
  - Use `prettyName` when displaying the package name to users

### 3.2 FR-004.2: Replace String.trim with String.trimAscii

**Description:** Replace all uses of the deprecated `String.trim` API with `String.trimAscii`.

**Context:**

The `String.trim` function has been deprecated in favor of `String.trimAscii`. The key difference is in the return type:

| Function | Return Type | Description |
|----------|--------------|-------------|
| `String.trim` (deprecated) | `String → String` | Returns a trimmed string |
| `String.trimAscii` (current) | `String → String.Slice` | Returns a string slice |

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No `String.trim` usage | `grep -r "String.trim" .lake/packages/` returns empty |
| Build output contains no deprecation warnings | `lake build` contains no "deprecated" warnings |
| String trimming works correctly | All string trimming operations produce correct results |

**Implementation Notes:**

- This deprecation is in the mathlib4 dependency's lakefile.lean
- The fix will be applied when mathlib4 is updated to a v4.28.0-compatible version
- If the updated version still has this issue, it should be reported upstream
- For custom code using `String.trim`, update to `String.trimAscii` and adjust for the `String.Slice` return type
- If a `String` is needed instead of `String.Slice`, use `.toString` on the slice

### 3.3 FR-004.3: Verify No Deprecated APIs in Project Code

**Description:** Ensure that the project's own code does not use any deprecated APIs.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No deprecated API usage in project code | `lake build` contains no deprecation warnings from project files |
| All APIs used are current | All APIs used are documented as current in Lean 4.28.0-rc1 |

**Implementation Notes:**

- Scan all `.lean` files in the Morph project for deprecated API usage
- Pay special attention to files that use:
  - Lake build system APIs
  - Lean 4 standard library functions
  - Metaprogramming APIs
- Replace any deprecated APIs found with their current equivalents
- Document any breaking changes encountered

### 3.4 FR-004.4: Update Type Signatures for API Changes

**Description:** Update any type signatures that have changed due to deprecated API replacements.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No type errors from API changes | `lake build` contains no type errors |
| All type signatures are correct | Type annotations match the new API signatures |

**Implementation Notes:**

- Some deprecated API replacements have different type signatures
- The most notable change is `String.trim` → `String.trimAscii` (returns `String.Slice` instead of `String`)
- Update function signatures to match the new API
- Add explicit type annotations where needed to help the type checker
- Verify that all type class instances are still satisfied

### 3.5 FR-004.5: Document Deprecated API Replacements

**Description:** Document all deprecated API replacements made during the remediation process.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| All replacements are documented | Documentation lists each deprecated API and its replacement |
| Migration notes are provided | Documentation includes notes on how to migrate |
| Breaking changes are highlighted | Documentation highlights any breaking changes |

**Implementation Notes:**

- Create a migration guide for deprecated API replacements
- Include before/after examples for each replacement
- Document any breaking changes and how to handle them
- Update project documentation to reflect the new APIs
- Consider adding comments in code explaining complex replacements

---

## 4. Non-Functional Requirements

### 4.1 NFR-004.1: Backward Compatibility

**Description:** Deprecated API replacements should maintain backward compatibility where possible.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| No breaking changes in public APIs | Public API signatures remain unchanged |
| Existing functionality is preserved | All existing tests pass |

### 4.2 NFR-004.2: Minimal Changes

**Description:** Only the minimal changes necessary to replace deprecated APIs should be made.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Changes are localized | Only deprecated API calls are replaced |
| No unnecessary refactoring | Code review confirms minimal changes |

### 4.3 NFR-004.3: Future-Proofing

**Description:** Choose API replacements that are likely to remain stable.

**Acceptance Criteria:**

| Criterion | Verification Method |
|-----------|---------------------|
| Replacement APIs are stable | Replacement APIs are documented as stable |
| No experimental features | Replacement APIs are not marked as experimental |

---

## 5. Dependencies

### 5.1 Internal Dependencies

| Requirement | Dependency Type | Description |
|-------------|-----------------|-------------|
| REQ-001 | Precedes | Critical errors must be resolved before deprecated API remediation |
| REQ-002 | Precedes | Dependency updates will resolve most deprecation warnings |
| REQ-003 | Independent | Syntax standards compliance can proceed in parallel |

### 5.2 External Dependencies

| Dependency | Version | Status |
|------------|---------|--------|
| Lean Toolchain | v4.28.0-rc1 | Required for current API documentation |
| Lake | Latest compatible | Required for build system APIs |

---

## 6. Verification Plan

### 6.1 Pre-Implementation Verification

```bash
# Check for deprecated Lake.Package.name usage
grep -rn "Lake.Package.name" .lake/packages/

# Check for deprecated String.trim usage
grep -rn "String.trim" .lake/packages/

# Check for deprecation warnings in build output
lake build 2>&1 | grep -i "deprecated"

# Check for deprecated APIs in project code
grep -rn "deprecated" Morph/
```

### 6.2 Post-Implementation Verification

```bash
# Verify no deprecated Lake.Package.name usage
grep -rn "Lake.Package.name" .lake/packages/ || echo "No deprecated Lake.Package.name usage found"

# Verify no deprecated String.trim usage
grep -rn "String.trim" .lake/packages/ || echo "No deprecated String.trim usage found"

# Verify no deprecation warnings
lake build 2>&1 | grep -i "deprecated" || echo "No deprecation warnings found"

# Verify all modules compile
lake build

# Verify no type errors
lake build 2>&1 | grep "type mismatch" || echo "No type errors found"
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
| Deprecated API Usage | 0 | `grep -r "deprecated"` |
| Deprecation Warnings | 0 | `lake build` warning output |
| Type Errors from API Changes | 0 | `lake build` error output |
| Compilation Success | 100% | `lake build` exit code |

---

## 8. Related Documents

| Document | Type | Reference |
|----------|------|-----------|
| [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) | Current State | Section 2.3.1 |
| [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) | Future State | Section 2.4 |
| [ADR-003: Dependency Version Alignment](../../02_adrs/ADR-003-dependency-version-alignment.md) | ADR | Full document |

---

## 9. Change History

| Date | Version | Author | Description |
|------|---------|--------|-------------|
| 2026-01-31 | 1.0 | System | Initial requirement specification |

---

## 10. Appendix: Deprecated API Reference

### A.1 Lake.Package.name Deprecation

**Deprecated API:** `Lake.Package.name`

**Replacements:**

| Replacement | Use Case | Example |
|-------------|-----------|---------|
| `baseName` | Base package identifier | `pkg.baseName` |
| `keyName` | Package map key | `pkg.keyName` |
| `prettyName` | Human-readable name | `pkg.prettyName` |

**Migration Example:**

```lean
-- Before (deprecated)
let name := pkg.name

-- After (current)
let name := pkg.prettyName  -- or baseName/keyName as appropriate
```

### A.2 String.trim Deprecation

**Deprecated API:** `String.trim`

**Replacement:** `String.trimAscii`

**Type Signature Change:**

| Function | Return Type |
|----------|--------------|
| `String.trim` (deprecated) | `String → String` |
| `String.trimAscii` (current) | `String → String.Slice` |

**Migration Example:**

```lean
-- Before (deprecated)
let trimmed := String.trim s

-- After (current)
let trimmed := (String.trimAscii s).toString
```

### A.3 Migration Checklist

- [ ] Identify all uses of deprecated APIs
- [ ] Replace `Lake.Package.name` with appropriate replacement
- [ ] Replace `String.trim` with `String.trimAscii`
- [ ] Update type signatures for API changes
- [ ] Verify no deprecation warnings remain
- [ ] Verify no type errors from API changes
- [ ] Run full test suite
- [ ] Document all deprecated API replacements
- [ ] Update project documentation
- [ ] Report upstream issues if dependency still has deprecated APIs

### A.4 Known Deprecated APIs

| Deprecated API | Replacement | Status |
|----------------|--------------|--------|
| `Lake.Package.name` | `baseName`, `keyName`, `prettyName` | In mathlib4 dependency |
| `String.trim` | `String.trimAscii` | In mathlib4 dependency |

**Note:** This list will be updated as additional deprecated APIs are discovered during the remediation process.
