# DESIGN-003: Migration Process Design

**Design ID:** DESIGN-003  
**Title:** Migration Process Design for Lean 4.28.0-rc1  
**Status:** Draft  
**Created:** 2026-01-31  
**Phase:** Phase 6 - Technical Design  
**Related Requirements:** REQ-001, REQ-002, REQ-003  
**Related ADRs:** ADR-001, ADR-002, ADR-003

---

## 1. Overview

This design document defines the step-by-step migration process for upgrading the Morph project from its current state to Lean 4.28.0-rc1 compatibility. It includes verification checkpoints, rollback procedures, and risk mitigation strategies to ensure a successful migration.

---

## 2. Design Goals

1. **Systematic Approach:** Clear, ordered steps for migration
2. **Verification:** Checkpoints to validate progress at each stage
3. **Rollback Safety:** Ability to revert changes if issues arise
4. **Risk Mitigation:** Identify and address potential issues proactively
5. **Documentation:** Comprehensive record of migration process

---

## 3. Migration Phases

The migration process is divided into four phases:

| Phase | Description | Duration Estimate | Dependencies |
|-------|-------------|-------------------|--------------|
| Phase 1: Preparation | Environment setup and analysis | 1-2 days | None |
| Phase 2: Dependency Alignment | Update dependencies to v4.28.0-compatible versions | 2-3 days | Phase 1 |
| Phase 3: Code Migration | Update code for compatibility | 5-10 days | Phase 2 |
| Phase 4: Verification | Testing and validation | 2-3 days | Phase 3 |

---

## 4. Phase 1: Preparation

### 4.1 Phase Goals

- Establish baseline understanding of current state
- Set up migration environment
- Create backup of current state
- Document current configuration

### 4.2 Pre-Migration Checklist

| Task | Command/Action | Verification |
|------|----------------|--------------|
| Verify current toolchain | `cat lean-toolchain` | Shows `leanprover/lean4:v4.28.0-rc1` |
| Verify current dependencies | `grep -A 10 "\[dependencies\]" lakefile.toml` | Shows current versions |
| Verify Lake configuration | `lake configure` | Succeeds without errors |
| Create backup branch | `git checkout -b backup/pre-migration` | Branch created |
| Document current state | `lake build 2>&1 | tee build.log` | Build log saved |

### 4.3 Environment Setup

```bash
# Ensure Lean 4.28.0-rc1 is available
lean --version
# Expected output: Lean (version 4.28.0-rc1)

# Ensure Lake is available
lake --version
# Expected output: Lake (version X.X.X)

# Clean build artifacts
lake clean
rm -rf .lake/packages
```

### 4.4 Baseline Documentation

Create a baseline document:

```markdown
# Migration Baseline - YYYY-MM-DD

## Current State

- Lean Toolchain: v4.28.0-rc1
- batteries: v4.10.0
- aesop: v4.10.0
- mathlib: v4.10.0

## Build Status

- Build Status: [Passing | Failing]
- Error Count: N
- Warning Count: N

## Known Issues

- List any known issues before migration
```

### 4.5 Verification Checkpoint 1

**Criteria:**
- [ ] Current toolchain verified as v4.28.0-rc1
- [ ] Current dependency versions documented
- [ ] Backup branch created
- [ ] Build log saved
- [ ] Baseline document created

**Rollback Trigger:** If any verification fails, do not proceed to Phase 2.

---

## 5. Phase 2: Dependency Alignment

### 5.1 Phase Goals

- Research v4.28.0-compatible dependency versions
- Update dependency configuration files
- Regenerate Lake manifest
- Verify dependency resolution

### 5.2 Research Target Versions

```bash
# Check available tags for each dependency
git ls-remote --tags https://github.com/leanprover-community/batteries
git ls-remote --tags https://github.com/JLimperg/aesop
git ls-remote --tags https://github.com/leanprover-community/mathlib4
```

### 5.3 Version Selection Table

| Package | Current Version | Target Version | Rationale |
|---------|----------------|----------------|-----------|
| batteries | v4.10.0 | v4.28.0 | Latest stable release compatible with Lean 4.28.0-rc1 |
| aesop | v4.10.0 | v4.28.0 | Latest stable release compatible with Lean 4.28.0-rc1 |
| mathlib | v4.10.0 | v4.28.0 | Latest stable release compatible with Lean 4.28.0-rc1 |

### 5.4 Update Dependency Configuration

#### Step 5.4.1: Update lakefile.toml

```toml
[package]
name = "Morph"
version = "0.1.0"

[dependencies]
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.28.0" }
aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.28.0" }
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.28.0" }
```

#### Step 5.4.2: Update lakefile.lean

```lean
import Lake
open Lake DSL

package Morph {
  -- Add package configuration options if needed
}

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.28.0"

require aesop from git
  "https://github.com/JLimperg/aesop" @ "v4.28.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

target Morph.lean lib (pkg : Package) := do
  let leanArgs := #[`--quiet]
  buildLeanLib pkg leanArgs
```

### 5.5 Regenerate Lake Manifest

```bash
# Clean old dependencies
lake clean
rm -rf .lake/packages

# Update dependencies and regenerate manifest
lake update

# Verify manifest
cat lake-manifest.json
```

### 5.6 Verify Dependency Resolution

```bash
# Configure Lake workspace
lake configure

# Verify each dependency builds
lake build Batteries
lake build Aesop
lake build Mathlib
```

### 5.7 Verification Checkpoint 2

**Criteria:**
- [ ] Target versions researched and documented
- [ ] lakefile.toml updated
- [ ] lakefile.lean updated
- [ ] Lake manifest regenerated
- [ ] Lake configuration succeeds
- [ ] All dependencies build successfully

**Rollback Trigger:** If any verification fails, revert to backup branch.

**Rollback Procedure:**
```bash
git checkout backup/pre-migration -- lakefile.toml lakefile.lean lake-manifest.json
lake clean
rm -rf .lake/packages
lake update
```

---

## 6. Phase 3: Code Migration

### 6.1 Phase Goals

- Fix syntax errors
- Update imports
- Fix type errors
- Update proof scripts
- Update deprecated APIs

### 6.2 Step-by-Step Migration

#### Step 6.2.1: Fix Syntax Errors

```bash
# Identify syntax errors
lake build 2>&1 | grep "syntax error"

# Fix unterminated comment in Morph/Specs/ArcAffineIntegration/Examples.lean:237
# Add closing comment delimiter at end of file
```

#### Step 6.2.2: Update Imports

```bash
# Find all mathlib4 imports
grep -r "import.*Mathlib" Morph/ | cut -d: -f1 | sort -u

# Update import paths based on new module structure
# Example: Mathlib.Data.List → Std.Data.List
```

**Import Mapping Table:**

| Old Import | New Import | Status |
|------------|-------------|--------|
| `Mathlib.Data.List` | `Std.Data.List` | Updated |
| `Mathlib.Data.Nat` | `Std.Data.Nat` | Updated |
| `Mathlib.Tactic` | `Mathlib.Tactic` | No change |

#### Step 6.2.3: Fix Type Errors

```bash
# Identify type errors
lake build 2>&1 | grep "type mismatch"

# Fix type errors by:
# - Adding explicit type annotations
# - Updating function calls to match new signatures
# - Replacing deprecated functions
```

**Type Error Resolution Table:**

| File | Error | Resolution | Status |
|------|-------|-------------|--------|
| `Morph/Specs/MemoryModel/Spec.lean` | Type mismatch in `allocateBlock` | Add explicit type annotation | Pending |
| `Morph/Specs/Concurrency/Lemmas.lean` | Unknown identifier `List.map` | Update to `List.map` | Pending |

#### Step 6.2.4: Update Proof Scripts

```bash
# Find all aesop usage
grep -r "aesop\|aesop!" Morph/ | cut -d: -f1 | sort -u

# Update aesop configurations if needed
# Example: Update tactic syntax to current version
```

#### Step 6.2.5: Update Deprecated APIs

```bash
# Find deprecated API usage
lake build 2>&1 | grep "deprecated"

# Replace deprecated APIs:
# - Lake.Package.name → baseName, keyName, or prettyName
# - String.trim → String.trimAscii
```

**Deprecated API Replacement Table:**

| Deprecated API | Replacement | Files Affected | Status |
|---------------|-------------|----------------|--------|
| `Lake.Package.name` | `baseName` | `lakefile.lean` | Pending |
| `String.trim` | `String.trimAscii` | Multiple files | Pending |

### 6.3 Module-by-Module Migration

Migrate modules in dependency order:

| Order | Module | Dependencies | Status |
|-------|--------|--------------|--------|
| 1 | CommonTypes | None | Pending |
| 2 | GLOSSARY | CommonTypes | Pending |
| 3 | MorphLanguage | CommonTypes, GLOSSARY | Pending |
| 4 | MemoryModel | CommonTypes, GLOSSARY | Pending |
| 5 | ... | ... | Pending |

### 6.4 Verification Checkpoint 3

**Criteria:**
- [ ] All syntax errors fixed
- [ ] All imports updated
- [ ] All type errors fixed
- [ ] All proof scripts updated
- [ ] All deprecated APIs replaced
- [ ] All modules compile successfully

**Rollback Trigger:** If compilation fails with unresolvable errors, revert to backup branch.

**Rollback Procedure:**
```bash
git checkout backup/pre-migration -- .
lake clean
rm -rf .lake/packages
lake update
```

---

## 7. Phase 4: Verification

### 7.1 Phase Goals

- Verify full compilation
- Run all tests
- Execute all examples
- Verify all proofs complete (1 known sorry in Preservation.lean -- see ROADMAP.md)
- Document migration results

### 7.2 Full Compilation Verification

```bash
# Clean build
lake clean

# Full build
lake build 2>&1 | tee build-post-migration.log

# Verify zero errors
grep -i "error" build-post-migration.log
# Expected: No errors found
```

### 7.3 Test Execution

```bash
# Run all tests
lake build Morph.Tests.*

# Verify all tests pass
# Expected: All tests pass
```

### 7.4 Example Execution

```bash
# Execute all examples
for file in Morph/Specs/*/Examples.lean; do
  echo "Executing $file"
  lean --run "$file"
done

# Verify all examples execute successfully
# Expected: All examples execute without errors
```

### 7.5 Proof Verification

```bash
# Verify no sorry or admit placeholders (1 known exception in Preservation.lean)
grep -r "sorry\|admit" Morph/Specs/
# Expected: No results in Morph/Specs/

# Verify sorry count in Proofs/ (expected: 1 in Preservation.lean)
grep -r "sorry" Morph/Proofs/
```

### 7.6 Documentation Update

Update project documentation:

```markdown
# Migration Summary - YYYY-MM-DD

## Migration Completed

- Lean Toolchain: v4.28.0-rc1
- batteries: v4.28.0
- aesop: v4.28.0
- mathlib: v4.28.0

## Changes Made

- Updated dependency versions
- Fixed syntax errors
- Updated imports
- Fixed type errors
- Updated proof scripts
- Replaced deprecated APIs

## Verification Results

- Build Status: Passing
- Test Status: All tests pass
- Example Status: All examples execute
- Proof Status: All proofs complete

## Known Issues

- List any remaining issues
```

### 7.7 Verification Checkpoint 4

**Criteria:**
- [ ] Full compilation succeeds
- [ ] All tests pass
- [ ] All examples execute
- [ ] All proofs complete
- [ ] Documentation updated
- [ ] Migration summary created

**Rollback Trigger:** If any verification fails, investigate and resolve issues before proceeding.

---

## 8. Rollback Procedures

### 8.1 Rollback Triggers

Rollback should be triggered if:

| Trigger | Condition | Action |
|---------|-----------|--------|
| Critical Build Failure | Cannot compile after dependency update | Rollback to Phase 2 checkpoint |
| Unresolvable Type Errors | Type errors cannot be fixed | Rollback to Phase 3 checkpoint |
| Test Failures | Tests fail after code migration | Investigate and fix or rollback |
| Proof Failures | Proofs cannot be completed | Investigate and fix or rollback |

### 8.2 Rollback Procedures

#### Rollback to Phase 1 (Complete Rollback)

```bash
# Restore backup branch
git checkout backup/pre-migration

# Clean build artifacts
lake clean
rm -rf .lake/packages

# Restore dependencies
lake update

# Verify rollback
lake build
```

#### Rollback to Phase 2 (Dependency Rollback)

```bash
# Restore dependency configuration
git checkout backup/pre-migration -- lakefile.toml lakefile.lean lake-manifest.json

# Clean build artifacts
lake clean
rm -rf .lake/packages

# Restore dependencies
lake update

# Verify rollback
lake build
```

#### Rollback to Phase 3 (Code Rollback)

```bash
# Restore code changes
git checkout backup/pre-migration -- Morph/

# Clean build artifacts
lake clean

# Verify rollback
lake build
```

### 8.3 Rollback Documentation

Document each rollback:

```markdown
# Rollback Log - YYYY-MM-DD

## Rollback Reason

[Explain why rollback was necessary]

## Rollback Point

[Phase or checkpoint rolled back to]

## Rollback Actions

[List actions taken during rollback]

## Post-Rollback Status

[Current status after rollback]
```

---

## 9. Risk Mitigation

### 9.1 Risk Identification

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Dependency version incompatibility | Medium | High | Research versions thoroughly, test in isolation |
| Breaking changes in mathlib4 | High | High | Review release notes, create import mapping |
| Type signature changes | High | Medium | Update type annotations gradually |
| Proof script failures | Medium | Medium | Update proof automation gradually |
| Build time increase | Low | Low | Monitor build times, optimize if needed |

### 9.2 Mitigation Strategies

#### Strategy 1: Incremental Migration

Migrate modules incrementally:

1. Start with foundational modules (CommonTypes, GLOSSARY)
2. Migrate dependent modules next
3. Verify each module before proceeding

#### Strategy 2: Feature Flags

Use feature flags to enable/disable features:

```lean
-- Enable new feature when ready
set_option feature.newFeature true
```

#### Strategy 3: Parallel Development

Maintain parallel branches:

- `main` branch: Current state
- `migration` branch: Migration in progress
- `feature/*` branches: Feature development

### 9.3 Communication

Communicate migration progress:

- Daily status updates
- Weekly migration meetings
- Documentation of decisions
- Issue tracking for blockers

---

## 10. Post-Migration Activities

### 10.1 Cleanup

```bash
# Remove backup branch (after successful migration)
git branch -D backup/pre-migration

# Clean build artifacts
lake clean

# Remove temporary files
rm -f build.log build-post-migration.log
```

### 10.2 Documentation

Update project documentation:

- README.md: Update Lean version requirement
- CONTRIBUTING.md: Update build instructions
- CHANGELOG.md: Document migration changes

### 10.3 CI/CD Updates

Update CI/CD pipelines:

- Update Lean toolchain version
- Update dependency installation steps
- Update build commands

### 10.4 Team Training

Train team on new features:

- Lean 4.28.0-rc1 features
- Updated dependency APIs
- New coding patterns

---

## 11. Success Criteria

Migration is considered successful when:

| Criterion | Target | Measurement |
|-----------|--------|--------------|
| Compilation | 100% success | `lake build` exit code 0 |
| Tests | 100% pass | All tests pass |
| Examples | 100% execute | All examples execute |
| Proofs | 100% complete | No `sorry` or `admit` |
| Documentation | 100% updated | All docs updated |
| CI/CD | 100% passing | All CI/CD jobs pass |

---

## 12. Timeline

| Phase | Duration | Start Date | End Date | Status |
|-------|----------|------------|----------|--------|
| Phase 1: Preparation | 1-2 days | TBD | TBD | Pending |
| Phase 2: Dependency Alignment | 2-3 days | TBD | TBD | Pending |
| Phase 3: Code Migration | 5-10 days | TBD | TBD | Pending |
| Phase 4: Verification | 2-3 days | TBD | TBD | Pending |
| **Total** | **10-18 days** | TBD | TBD | Pending |

---

## 13. Related Documents

| Document | Type | Reference |
|----------|------|-----------|
| [`.specs/04_future_state/reqs/REQ-001-core-foundation.md`](../reqs/REQ-001-core-foundation.md) | Requirement | Core Foundation Requirements |
| [`.specs/04_future_state/reqs/REQ-002-dependency-version-alignment.md`](../reqs/REQ-002-dependency-version-alignment.md) | Requirement | Dependency Version Alignment |
| [`.specs/04_future_state/reqs/REQ-003-syntax-standards-compliance.md`](../reqs/REQ-003-syntax-standards-compliance.md) | Requirement | Syntax Standards Compliance |
| [ADR-001: Lean 4.28.0-rc1 Migration](../../02_adrs/ADR-001-lean-4.28.0-rc1-migration.md) | ADR | Migration to Lean 4.28.0-rc1 |
| [ADR-002: ProofWidgets Dependency Removal](../../02_adrs/ADR-002-proofwidgets-removal.md) | ADR | ProofWidgets Removal |
| [ADR-003: Dependency Version Alignment](../../02_adrs/ADR-003-dependency-version-alignment.md) | ADR | Dependency Version Alignment |

---

## 14. Change History

| Date | Version | Author | Description |
|------|---------|--------|-------------|
| 2026-01-31 | 1.0 | System | Initial design document |
