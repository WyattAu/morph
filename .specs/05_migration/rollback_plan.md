# Rollback Plan - Morph Lean 4.28.0-rc1 Migration

**Phase:** Phase 8 - Data & Rollback Strategy
**Status:** Draft
**Created:** 2026-01-31
**Purpose:** Define safety valve procedures for the Morph project migration to Lean 4.28.0-rc1

---

## Executive Summary

This rollback plan provides comprehensive procedures for reverting the Morph project migration from Lean 4.10.0 to Lean 4.28.0-rc1 in the event of critical failures. The plan addresses four rollback scenarios based on identified risks from the threat model ([`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md)) and incorporates checkpoints from the migration process design ([`.specs/04_future_state/design/DESIGN-003-migration-process.md`](../04_future_state/design/DESIGN-003-migration-process.md)).

### Rollback Philosophy

- **Safety First:** Rollback should be triggered at the first sign of critical failure
- **Quick Recovery:** Rollback procedures should complete within 15 minutes
- **State Preservation:** All rollback states are preserved via Git branches
- **Verification Required:** Every rollback must be verified before proceeding

---

## 1. Pre-Migration Backup Procedures

### 1.1 Backup Strategy Overview

Before initiating any migration activities, a complete backup of the project state must be created. This ensures that any rollback can restore the project to a known working state.

### 1.2 Pre-Migration Checklist

| Task | Command/Action | Verification |
|------|----------------|--------------|
| Verify current toolchain | `cat lean-toolchain` | Shows `leanprover/lean4:v4.28.0-rc1` |
| Verify current dependencies | `grep -A 10 "\[dependencies\]" lakefile.toml` | Shows current versions |
| Verify Lake configuration | `lake configure` | Succeeds without errors |
| Create backup branch | `git checkout -b backup/pre-migration` | Branch created |
| Document current state | `lake build 2>&1 | tee .specs/05_migration/pre-migration-build.log` | Build log saved |
| Tag backup commit | `git tag -a backup/pre-migration-$(date +%Y%m%d) -m "Pre-migration backup"` | Tag created |
| Backup .lake directory | `tar -czf .specs/05_migration/pre-migration-lake-backup.tar.gz .lake/` | Backup created |
| Verify backup integrity | `tar -tzf .specs/05_migration/pre-migration-lake-backup.tar.gz | head -20` | Files listed |

### 1.3 Phase-Specific Backup Checkpoints

#### Phase 1: Preparation Backup

```bash
# After completing Phase 1 preparation
git checkout -b backup/phase-1-preparation
git add -A
git commit -m "Backup: Phase 1 Preparation completed"
git tag backup/phase-1-$(date +%Y%m%d-%H%M%S)
```

**Contents Preserved:**
- Current toolchain state
- Current dependency configuration
- Baseline build log
- Environment configuration

#### Phase 2: Dependency Alignment Backup

```bash
# Before updating dependencies
git checkout -b backup/phase-2-pre-dependency-update
git add -A
git commit -m "Backup: Before dependency update"
git tag backup/phase-2-pre-$(date +%Y%m%d-%H%M%S)

# After dependency update (if successful)
git checkout -b backup/phase-2-post-dependency-update
git add lakefile.toml lakefile.lean lake-manifest.json
git commit -m "Backup: After dependency update"
git tag backup/phase-2-post-$(date +%Y%m%d-%H%M%S)
```

**Contents Preserved:**
- Original dependency configuration
- Updated dependency configuration
- Lake manifest state
- Package directory state

#### Phase 3: Code Migration Backup

```bash
# Before code migration
git checkout -b backup/phase-3-pre-code-migration
git add -A
git commit -m "Backup: Before code migration"
git tag backup/phase-3-pre-$(date +%Y%m%d-%H%M%S)

# After each module migration (optional incremental backups)
git checkout -b backup/phase-3-module-<ModuleName>
git add Morph/Specs/<ModuleName>/
git commit -m "Backup: After migrating <ModuleName> module"
```

**Contents Preserved:**
- Original code state
- Incremental migration states
- Module-by-module progress

#### Phase 4: Verification Backup

```bash
# Before final verification
git checkout -b backup/phase-4-pre-verification
git add -A
git commit -m "Backup: Before final verification"
git tag backup/phase-4-pre-$(date +%Y%m%d-%H%M%S)
```

**Contents Preserved:**
- Complete migrated state
- All code changes
- All configuration changes

### 1.4 Backup Verification Procedure

After creating any backup, verify its integrity:

```bash
# Verify Git backup
git log --oneline backup/pre-migration
git tag -l "backup/*"

# Verify .lake backup
tar -tzf .specs/05_migration/pre-migration-lake-backup.tar.gz | wc -l
# Expected: Non-zero count

# Verify build log
wc -l .specs/05_migration/pre-migration-build.log
# Expected: Non-zero count
```

### 1.5 Backup Restoration Test

Before proceeding with migration, test that the backup can be restored:

```bash
# Create test branch from backup
git checkout backup/pre-migration
git checkout -b test/backup-restoration

# Clean build artifacts
lake clean
rm -rf .lake/packages

# Restore .lake backup
tar -xzf .specs/05_migration/pre-migration-lake-backup.tar.gz

# Verify build works
lake build

# If successful, cleanup test branch
git checkout backup/pre-migration
git branch -D test/backup-restoration
```

---

## 2. Rollback Triggers and Conditions

### 2.1 Rollback Trigger Matrix

| Trigger Type | Condition | Severity | Action |
|--------------|-----------|----------|--------|
| **Critical Build Failure** | Lake workspace configuration fails | Critical | Immediate rollback to Phase 1 |
| **Critical Build Failure** | All modules fail to compile | Critical | Immediate rollback to Phase 1 |
| **Critical Build Failure** | Core modules fail to compile | Critical | Rollback to Phase 2 or Phase 3 |
| **Dependency Incompatibility** | Updated dependencies cause type errors | Critical | Rollback to Phase 2 |
| **Dependency Incompatibility** | Dependency resolution fails | Critical | Rollback to Phase 2 |
| **Syntax Errors After Migration** | New syntax errors introduced | High | Rollback to Phase 3 |
| **Syntax Errors After Migration** | Previously working files fail to parse | High | Rollback to Phase 3 |
| **Proof Regressions** | Previously working proofs fail | High | Rollback to Phase 3 |
| **Proof Regressions** | New sorry/admit placeholders introduced | High | Rollback to Phase 3 |
| **Test Failures** | Critical tests fail | Medium | Investigate or rollback |
| **Test Failures** | Regression tests fail | Medium | Investigate or rollback |

### 2.2 Rollback Decision Tree

```
START
  │
  ├─→ Critical Build Failure?
  │     ├─→ Yes → Rollback to Phase 1 (Complete Rollback)
  │     └─→ No → Continue
  │
  ├─→ Dependency Incompatibility?
  │     ├─→ Yes → Rollback to Phase 2 (Dependency Rollback)
  │     └─→ No → Continue
  │
  ├─→ Syntax Errors After Migration?
  │     ├─→ Yes → Rollback to Phase 3 (Code Rollback)
  │     └─→ No → Continue
  │
  ├─→ Proof Regressions?
  │     ├─→ Yes → Rollback to Phase 3 (Code Rollback)
  │     └─→ No → Continue
  │
  └─→ Test Failures?
        ├─→ Critical → Rollback to Phase 3 (Code Rollback)
        └─→ Non-Critical → Investigate and Fix
```

### 2.3 Rollback Escalation Procedure

1. **Level 1: Immediate Rollback (Critical)**
   - Trigger: Critical build failure, dependency incompatibility
   - Action: Execute rollback immediately without investigation
   - Timeframe: Within 5 minutes of trigger detection

2. **Level 2: Investigative Rollback (High)**
   - Trigger: Syntax errors, proof regressions
   - Action: Investigate for 15 minutes, then rollback if unresolved
   - Timeframe: Within 20 minutes of trigger detection

3. **Level 3: Deliberate Rollback (Medium)**
   - Trigger: Test failures, minor issues
   - Action: Investigate for up to 1 hour, then decide on rollback
   - Timeframe: Within 1 hour of trigger detection

---

## 3. Rollback Scenarios

### Scenario 1: Critical Build Failure

**Related Risks:** RISK-COMP-001, RISK-COMP-002, RISK-COMP-003

**Description:**
Lake workspace configuration fails or all modules fail to compile after migration. This is a critical failure that blocks all development work.

**Trigger Conditions:**
- `lake configure` fails with blocking errors
- `lake build` fails for all modules
- Core modules ([`Morph/Core.lean`](../../Morph/Core.lean), [`Morph/HIR.lean`](../../Morph/HIR.lean), [`Morph/MIR.lean`](../../Morph/MIR.lean)) fail to compile
- Lake workspace cannot be initialized

**Detection Commands:**
```bash
# Detect Lake configuration failure
lake configure 2>&1 | tee .specs/05_migration/rollback-detection.log
if [ $? -ne 0 ]; then
    echo "CRITICAL: Lake configuration failed"
fi

# Detect build failure
lake build 2>&1 | tee .specs/05_migration/rollback-detection.log
if [ $? -ne 0 ]; then
    echo "CRITICAL: Build failed"
fi

# Count compilation errors
ERROR_COUNT=$(lake build 2>&1 | grep -c "error:" || echo "0")
if [ "$ERROR_COUNT" -gt 100 ]; then
    echo "CRITICAL: Too many compilation errors ($ERROR_COUNT)"
fi
```

**Rollback Procedure:**

#### Step 1: Document Failure State

```bash
# Create failure documentation directory
mkdir -p .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)

# Capture error logs
lake build 2>&1 > .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/build-failure.log
lake configure 2>&1 > .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/configure-failure.log

# Document current state
git log --oneline -10 > .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/git-history.log
git diff > .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/git-diff.log
cat lakefile.toml > .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/lakefile.toml
cat lake-manifest.json > .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/lake-manifest.json
cat lean-toolchain > .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/lean-toolchain
```

#### Step 2: Stop All Build Processes

```bash
# Kill any running Lake processes
pkill -9 lake
pkill -9 lean

# Clean build artifacts
lake clean
rm -rf .lake/packages
rm -rf .lake/build
```

#### Step 3: Restore Pre-Migration State

```bash
# Checkout pre-migration backup
git checkout backup/pre-migration

# Restore .lake directory from backup
rm -rf .lake
tar -xzf .specs/05_migration/pre-migration-lake-backup.tar.gz

# Verify restoration
git status
ls -la .lake/packages/
```

#### Step 4: Verify Rollback Success

```bash
# Verify Lake configuration
lake configure 2>&1 | tee .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/post-rollback-configure.log
if [ $? -eq 0 ]; then
    echo "SUCCESS: Lake configuration restored"
else
    echo "FAILURE: Lake configuration still failing"
    exit 1
fi

# Verify build
lake build 2>&1 | tee .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/post-rollback-build.log
if [ $? -eq 0 ]; then
    echo "SUCCESS: Build restored"
else
    echo "WARNING: Build has issues but may be pre-existing"
fi

# Count errors
ERROR_COUNT=$(lake build 2>&1 | grep -c "error:" || echo "0")
echo "Post-rollback error count: $ERROR_COUNT"
```

#### Step 5: Document Rollback

```bash
# Create rollback report
cat > .specs/05_migration/rollback-scenario-1-$(date +%Y%m%d-%H%M%S)/rollback-report.md << 'EOF'
# Rollback Report - Scenario 1: Critical Build Failure

**Date:** $(date)
**Rollback Type:** Complete Rollback to Pre-Migration State
**Reason:** Critical build failure detected

## Failure Summary

- Lake Configuration: [FAILED/SUCCEEDED]
- Build Status: [FAILED/SUCCEEDED]
- Error Count: [N]

## Actions Taken

1. Documented failure state
2. Stopped all build processes
3. Restored pre-migration state
4. Verified rollback success

## Verification Results

- Lake Configuration: [PASSED/FAILED]
- Build Status: [PASSED/FAILED]
- Error Count: [N]

## Next Steps

[Describe next steps]
EOF
```

**Estimated Time:** 15 minutes

**Rollback Success Criteria:**
- [ ] Lake configuration succeeds
- [ ] Build completes (may have pre-existing errors)
- [ ] Error count is at or below pre-migration level
- [ ] All critical modules compile

---

### Scenario 2: Dependency Incompatibility

**Related Risks:** RISK-COMP-001, RISK-COMP-004, RISK-COMP-005, RISK-COMP-006

**Description:**
Updated dependencies cause type errors, import errors, or other compatibility issues. The build system works but code fails to compile due to dependency changes.

**Trigger Conditions:**
- Type errors after dependency update
- Import errors from updated dependencies
- Function signature mismatches
- Type class instance conflicts
- `lake build Batteries`, `lake build Aesop`, or `lake build Mathlib` fails

**Detection Commands:**
```bash
# Detect dependency build failures
lake build Batteries 2>&1 | tee .specs/05_migration/rollback-detection.log
if [ $? -ne 0 ]; then
    echo "CRITICAL: Batteries dependency build failed"
fi

lake build Aesop 2>&1 | tee .specs/05_migration/rollback-detection.log
if [ $? -ne 0 ]; then
    echo "CRITICAL: Aesop dependency build failed"
fi

lake build Mathlib 2>&1 | tee .specs/05_migration/rollback-detection.log
if [ $? -ne 0 ]; then
    echo "CRITICAL: Mathlib dependency build failed"
fi

# Detect type errors from dependencies
TYPE_ERRORS=$(lake build 2>&1 | grep "type mismatch" | wc -l)
if [ "$TYPE_ERRORS" -gt 50 ]; then
    echo "CRITICAL: Too many type errors from dependencies ($TYPE_ERRORS)"
fi

# Detect import errors
IMPORT_ERRORS=$(lake build 2>&1 | grep "unknown identifier" | wc -l)
if [ "$IMPORT_ERRORS" -gt 20 ]; then
    echo "CRITICAL: Too many import errors ($IMPORT_ERRORS)"
fi
```

**Rollback Procedure:**

#### Step 1: Document Failure State

```bash
# Create failure documentation directory
mkdir -p .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)

# Capture error logs
lake build Batteries 2>&1 > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/batteries-failure.log
lake build Aesop 2>&1 > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/aesop-failure.log
lake build Mathlib 2>&1 > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/mathlib-failure.log
lake build 2>&1 > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/build-failure.log

# Document current dependency state
cat lakefile.toml > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/lakefile.toml
cat lakefile.lean > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/lakefile.lean
cat lake-manifest.json > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/lake-manifest.json

# Count errors by type
lake build 2>&1 | grep "type mismatch" > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/type-errors.log
lake build 2>&1 | grep "unknown identifier" > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/import-errors.log
```

#### Step 2: Restore Dependency Configuration

```bash
# Stop all build processes
pkill -9 lake
pkill -9 lean

# Restore dependency files from Phase 2 backup
git checkout backup/phase-2-pre-dependency-update -- lakefile.toml lakefile.lean lake-manifest.json

# Clean build artifacts
lake clean
rm -rf .lake/packages
rm -rf .lake/build
```

#### Step 3: Restore Dependencies

```bash
# Restore original dependencies
lake update 2>&1 | tee .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/lake-update.log

# Verify dependency restoration
cat lake-manifest.json | grep -A 5 "batteries"
cat lake-manifest.json | grep -A 5 "aesop"
cat lake-manifest.json | grep -A 5 "mathlib"
```

#### Step 4: Verify Rollback Success

```bash
# Verify Lake configuration
lake configure 2>&1 | tee .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/post-rollback-configure.log
if [ $? -eq 0 ]; then
    echo "SUCCESS: Lake configuration restored"
else
    echo "FAILURE: Lake configuration still failing"
    exit 1
fi

# Verify dependency builds
lake build Batteries 2>&1 | tee .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/post-rollback-batteries.log
if [ $? -eq 0 ]; then
    echo "SUCCESS: Batteries builds"
else
    echo "WARNING: Batteries has issues"
fi

lake build Aesop 2>&1 | tee .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/post-rollback-aesop.log
if [ $? -eq 0 ]; then
    echo "SUCCESS: Aesop builds"
else
    echo "WARNING: Aesop has issues"
fi

lake build Mathlib 2>&1 | tee .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/post-rollback-mathlib.log
if [ $? -eq 0 ]; then
    echo "SUCCESS: Mathlib builds"
else
    echo "WARNING: Mathlib has issues"
fi

# Verify project build
lake build 2>&1 | tee .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/post-rollback-build.log
ERROR_COUNT=$(lake build 2>&1 | grep -c "error:" || echo "0")
echo "Post-rollback error count: $ERROR_COUNT"
```

#### Step 5: Document Rollback

```bash
# Create rollback report
cat > .specs/05_migration/rollback-scenario-2-$(date +%Y%m%d-%H%M%S)/rollback-report.md << 'EOF'
# Rollback Report - Scenario 2: Dependency Incompatibility

**Date:** $(date)
**Rollback Type:** Dependency Rollback to Phase 2
**Reason:** Dependency incompatibility detected

## Failure Summary

- Batteries Build: [FAILED/SUCCEEDED]
- Aesop Build: [FAILED/SUCCEEDED]
- Mathlib Build: [FAILED/SUCCEEDED]
- Type Errors: [N]
- Import Errors: [N]

## Actions Taken

1. Documented failure state
2. Stopped all build processes
3. Restored dependency configuration
4. Restored dependencies
5. Verified rollback success

## Verification Results

- Lake Configuration: [PASSED/FAILED]
- Batteries Build: [PASSED/FAILED]
- Aesop Build: [PASSED/FAILED]
- Mathlib Build: [PASSED/FAILED]
- Project Build: [PASSED/FAILED]
- Error Count: [N]

## Next Steps

[Describe next steps]
EOF
```

**Estimated Time:** 10 minutes

**Rollback Success Criteria:**
- [ ] Lake configuration succeeds
- [ ] All dependencies build successfully
- [ ] Type errors are at or below pre-migration level
- [ ] Import errors are at or below pre-migration level

---

### Scenario 3: Syntax Errors After Migration

**Related Risks:** RISK-COMP-007, RISK-COMP-008, RISK-QUAL-001

**Description:**
New syntax errors are introduced during code migration. Previously working files fail to parse or compile due to syntax changes.

**Trigger Conditions:**
- New syntax errors detected after code migration
- Previously working files fail to parse
- Unterminated comments, mismatched delimiters
- Deprecated syntax usage

**Detection Commands:**
```bash
# Detect syntax errors
SYNTAX_ERRORS=$(lake build 2>&1 | grep "syntax error" | wc -l)
if [ "$SYNTAX_ERRORS" -gt 0 ]; then
    echo "CRITICAL: Syntax errors detected ($SYNTAX_ERRORS)"
fi

# Detect unterminated comments
UNTERMINATED=$(lake build 2>&1 | grep "unterminated comment" | wc -l)
if [ "$UNTERMINATED" -gt 0 ]; then
    echo "CRITICAL: Unterminated comments detected ($UNTERMINATED)"
fi

# Detect parsing errors
PARSING_ERRORS=$(lake build 2>&1 | grep "parse error" | wc -l)
if [ "$PARSING_ERRORS" -gt 0 ]; then
    echo "CRITICAL: Parsing errors detected ($PARSING_ERRORS)"
fi

# Compare with pre-migration error count
if [ "$SYNTAX_ERRORS" -gt 5 ]; then
    echo "CRITICAL: Syntax errors exceed threshold"
fi
```

**Rollback Procedure:**

#### Step 1: Document Failure State

```bash
# Create failure documentation directory
mkdir -p .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)

# Capture error logs
lake build 2>&1 > .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)/build-failure.log

# Extract syntax errors
lake build 2>&1 | grep "syntax error" > .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)/syntax-errors.log
lake build 2>&1 | grep "unterminated comment" > .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)/unterminated-comments.log
lake build 2>&1 | grep "parse error" > .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)/parse-errors.log

# Document changed files
git diff --name-only > .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)/changed-files.log

# Create list of files with syntax errors
lake build 2>&1 | grep "syntax error" | cut -d: -f1 | sort -u > .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)/files-with-syntax-errors.log
```

#### Step 2: Identify Affected Files

```bash
# Get list of files with syntax errors
AFFECTED_FILES=$(lake build 2>&1 | grep "syntax error" | cut -d: -f1 | sort -u)

echo "Files with syntax errors:"
echo "$AFFECTED_FILES"

# Determine if rollback is needed
FILE_COUNT=$(echo "$AFFECTED_FILES" | wc -l)
if [ "$FILE_COUNT" -gt 10 ]; then
    echo "CRITICAL: Too many files with syntax errors ($FILE_COUNT), recommend full rollback"
fi
```

#### Step 3: Selective or Full Rollback

**Option A: Selective Rollback (if few files affected)**

```bash
# Rollback specific files
for file in $AFFECTED_FILES; do
    git checkout backup/phase-3-pre-code-migration -- "$file"
    echo "Rolled back: $file"
done
```

**Option B: Full Rollback (if many files affected)**

```bash
# Stop all build processes
pkill -9 lake
pkill -9 lean

# Restore all code from Phase 3 backup
git checkout backup/phase-3-pre-code-migration -- Morph/

# Clean build artifacts
lake clean
```

#### Step 4: Verify Rollback Success

```bash
# Verify syntax errors are resolved
SYNTAX_ERRORS=$(lake build 2>&1 | grep "syntax error" | wc -l)
if [ "$SYNTAX_ERRORS" -eq 0 ]; then
    echo "SUCCESS: All syntax errors resolved"
else
    echo "WARNING: Some syntax errors remain ($SYNTAX_ERRORS)"
fi

# Verify build
lake build 2>&1 | tee .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)/post-rollback-build.log
ERROR_COUNT=$(lake build 2>&1 | grep -c "error:" || echo "0")
echo "Post-rollback error count: $ERROR_COUNT"
```

#### Step 5: Document Rollback

```bash
# Create rollback report
cat > .specs/05_migration/rollback-scenario-3-$(date +%Y%m%d-%H%M%S)/rollback-report.md << 'EOF'
# Rollback Report - Scenario 3: Syntax Errors After Migration

**Date:** $(date)
**Rollback Type:** [Selective/Full] Rollback to Phase 3
**Reason:** Syntax errors detected after code migration

## Failure Summary

- Syntax Errors: [N]
- Unterminated Comments: [N]
- Parsing Errors: [N]
- Files Affected: [N]

## Actions Taken

1. Documented failure state
2. Identified affected files
3. Performed [selective/full] rollback
4. Verified rollback success

## Verification Results

- Syntax Errors Resolved: [YES/NO]
- Build Status: [PASSED/FAILED]
- Error Count: [N]

## Next Steps

[Describe next steps]
EOF
```

**Estimated Time:** 10 minutes (selective), 15 minutes (full)

**Rollback Success Criteria:**
- [ ] All syntax errors are resolved
- [ ] Build completes (may have pre-existing errors)
- [ ] Error count is at or below pre-migration level
- [ ] No new parsing errors

---

### Scenario 4: Proof Regressions

**Related Risks:** RISK-COMP-006, RISK-QUAL-001

**Description:**
Previously working proofs fail after migration. This may be due to changes in proof automation, tactic syntax, or type class resolution.

**Trigger Conditions:**
- Previously passing proofs fail
- New sorry/admit placeholders introduced
- Proof completion time increases significantly
- Aesop tactic failures

**Detection Commands:**
```bash
# Detect proof failures
PROOF_FAILURES=$(lake build 2>&1 | grep "proof failed" | wc -l)
if [ "$PROOF_FAILURES" -gt 0 ]; then
    echo "CRITICAL: Proof failures detected ($PROOF_FAILURES)"
fi

# Detect new sorry/admit placeholders
SORRY_COUNT=$(grep -r "sorry\|admit" Morph/Specs/ | wc -l)
if [ "$SORRY_COUNT" -gt 0 ]; then
    echo "CRITICAL: Sorry/admit placeholders detected ($SORRY_COUNT)"
fi

# Detect aesop failures
AESOP_FAILURES=$(lake build 2>&1 | grep "aesop.*failed" | wc -l)
if [ "$AESOP_FAILURES" -gt 10 ]; then
    echo "CRITICAL: Aesop failures detected ($AESOP_FAILURES)"
fi
```

**Rollback Procedure:**

#### Step 1: Document Failure State

```bash
# Create failure documentation directory
mkdir -p .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)

# Capture error logs
lake build 2>&1 > .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)/build-failure.log

# Extract proof failures
lake build 2>&1 | grep "proof failed" > .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)/proof-failures.log

# Extract sorry/admit placeholders
grep -rn "sorry\|admit" Morph/Specs/ > .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)/sorry-admit.log

# Extract aesop failures
lake build 2>&1 | grep "aesop.*failed" > .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)/aesop-failures.log

# Document changed files
git diff --name-only > .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)/changed-files.log

# Create list of files with proof failures
lake build 2>&1 | grep "proof failed" | cut -d: -f1 | sort -u > .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)/files-with-proof-failures.log
```

#### Step 2: Identify Affected Proofs

```bash
# Get list of files with proof failures
AFFECTED_FILES=$(lake build 2>&1 | grep "proof failed" | cut -d: -f1 | sort -u)

echo "Files with proof failures:"
echo "$AFFECTED_FILES"

# Count sorry/admit placeholders
SORRY_COUNT=$(grep -r "sorry\|admit" Morph/Specs/ | wc -l)
echo "Total sorry/admit placeholders: $SORRY_COUNT"

# Determine if rollback is needed
FILE_COUNT=$(echo "$AFFECTED_FILES" | wc -l)
if [ "$FILE_COUNT" -gt 5 ]; then
    echo "CRITICAL: Too many files with proof failures ($FILE_COUNT), recommend full rollback"
fi
```

#### Step 3: Selective or Full Rollback

**Option A: Selective Rollback (if few files affected)**

```bash
# Rollback specific files
for file in $AFFECTED_FILES; do
    git checkout backup/phase-3-pre-code-migration -- "$file"
    echo "Rolled back: $file"
done
```

**Option B: Full Rollback (if many files affected)**

```bash
# Stop all build processes
pkill -9 lake
pkill -9 lean

# Restore all code from Phase 3 backup
git checkout backup/phase-3-pre-code-migration -- Morph/

# Clean build artifacts
lake clean
```

#### Step 4: Verify Rollback Success

```bash
# Verify proof failures are resolved
PROOF_FAILURES=$(lake build 2>&1 | grep "proof failed" | wc -l)
if [ "$PROOF_FAILURES" -eq 0 ]; then
    echo "SUCCESS: All proof failures resolved"
else
    echo "WARNING: Some proof failures remain ($PROOF_FAILURES)"
fi

# Verify no new sorry/admit placeholders
SORRY_COUNT=$(grep -r "sorry\|admit" Morph/Specs/ | wc -l)
if [ "$SORRY_COUNT" -eq 0 ]; then
    echo "SUCCESS: No sorry/admit placeholders"
else
    echo "WARNING: Sorry/admit placeholders remain ($SORRY_COUNT)"
fi

# Verify build
lake build 2>&1 | tee .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)/post-rollback-build.log
ERROR_COUNT=$(lake build 2>&1 | grep -c "error:" || echo "0")
echo "Post-rollback error count: $ERROR_COUNT"
```

#### Step 5: Document Rollback

```bash
# Create rollback report
cat > .specs/05_migration/rollback-scenario-4-$(date +%Y%m%d-%H%M%S)/rollback-report.md << 'EOF'
# Rollback Report - Scenario 4: Proof Regressions

**Date:** $(date)
**Rollback Type:** [Selective/Full] Rollback to Phase 3
**Reason:** Proof regressions detected after code migration

## Failure Summary

- Proof Failures: [N]
- Sorry/Admit Placeholders: [N]
- Aesop Failures: [N]
- Files Affected: [N]

## Actions Taken

1. Documented failure state
2. Identified affected proofs
3. Performed [selective/full] rollback
4. Verified rollback success

## Verification Results

- Proof Failures Resolved: [YES/NO]
- Sorry/Admit Placeholders Removed: [YES/NO]
- Build Status: [PASSED/FAILED]
- Error Count: [N]

## Next Steps

[Describe next steps]
EOF
```

**Estimated Time:** 10 minutes (selective), 15 minutes (full)

**Rollback Success Criteria:**
- [ ] All proof failures are resolved
- [ ] No new sorry/admit placeholders
- [ ] Build completes (may have pre-existing errors)
- [ ] Error count is at or below pre-migration level

---

## 4. Verification After Rollback

### 4.1 Verification Checklist

After any rollback, the following verification steps must be completed:

| Verification Step | Command | Success Criteria |
|-------------------|---------|------------------|
| Lake Configuration | `lake configure` | Exit code 0, no errors |
| Dependency Build | `lake build Batteries Aesop Mathlib` | All dependencies build |
| Full Build | `lake build` | Exit code 0 or pre-migration error level |
| Error Count | `lake build 2>&1 \| grep -c "error:"` | At or below pre-migration level |
| Syntax Errors | `lake build 2>&1 \| grep "syntax error"` | No syntax errors |
| Proof Completeness | `grep -r "sorry\|admit" Morph/Specs/` | No sorry/admit placeholders |

### 4.2 Automated Verification Script

```bash
#!/bin/bash
# .specs/05_migration/verify-rollback.sh

set -e

echo "=== Rollback Verification ==="
echo ""

# Configuration
LOG_DIR=".specs/05_migration/rollback-verification-$(date +%Y%m%d-%H%M%S)"
mkdir -p "$LOG_DIR"

# Step 1: Verify Lake configuration
echo "Step 1: Verifying Lake configuration..."
lake configure 2>&1 | tee "$LOG_DIR/lake-configure.log"
if [ $? -eq 0 ]; then
    echo "✓ Lake configuration successful"
else
    echo "✗ Lake configuration failed"
    exit 1
fi
echo ""

# Step 2: Verify dependency builds
echo "Step 2: Verifying dependency builds..."
lake build Batteries 2>&1 | tee "$LOG_DIR/batteries-build.log"
if [ $? -eq 0 ]; then
    echo "✓ Batteries builds"
else
    echo "✗ Batteries build failed"
    exit 1
fi

lake build Aesop 2>&1 | tee "$LOG_DIR/aesop-build.log"
if [ $? -eq 0 ]; then
    echo "✓ Aesop builds"
else
    echo "✗ Aesop build failed"
    exit 1
fi

lake build Mathlib 2>&1 | tee "$LOG_DIR/mathlib-build.log"
if [ $? -eq 0 ]; then
    echo "✓ Mathlib builds"
else
    echo "✗ Mathlib build failed"
    exit 1
fi
echo ""

# Step 3: Verify full build
echo "Step 3: Verifying full build..."
lake build 2>&1 | tee "$LOG_DIR/full-build.log"
BUILD_EXIT_CODE=$?
echo ""

# Step 4: Count errors
echo "Step 4: Counting errors..."
ERROR_COUNT=$(grep -c "error:" "$LOG_DIR/full-build.log" || echo "0")
echo "Error count: $ERROR_COUNT"
echo ""

# Step 5: Check for syntax errors
echo "Step 5: Checking for syntax errors..."
SYNTAX_ERRORS=$(grep -c "syntax error" "$LOG_DIR/full-build.log" || echo "0")
if [ "$SYNTAX_ERRORS" -eq 0 ]; then
    echo "✓ No syntax errors"
else
    echo "✗ Syntax errors found: $SYNTAX_ERRORS"
    exit 1
fi
echo ""

# Step 6: Check for sorry/admit placeholders
echo "Step 6: Checking for sorry/admit placeholders..."
SORRY_COUNT=$(grep -r "sorry\|admit" Morph/Specs/ | wc -l)
if [ "$SORRY_COUNT" -eq 0 ]; then
    echo "✓ No sorry/admit placeholders"
else
    echo "✗ Sorry/admit placeholders found: $SORRY_COUNT"
    exit 1
fi
echo ""

# Step 7: Generate verification report
echo "Step 7: Generating verification report..."
cat > "$LOG_DIR/verification-report.md" << EOF
# Rollback Verification Report

**Date:** $(date)
**Log Directory:** $LOG_DIR

## Verification Results

| Step | Status | Details |
|------|--------|---------|
| Lake Configuration | ✓ | Successful |
| Batteries Build | ✓ | Successful |
| Aesop Build | ✓ | Successful |
| Mathlib Build | ✓ | Successful |
| Full Build | $(if [ $BUILD_EXIT_CODE -eq 0 ]; then echo "✓"; else echo "⚠"; fi) | Exit code: $BUILD_EXIT_CODE |
| Error Count | - | $ERROR_COUNT |
| Syntax Errors | ✓ | 0 |
| Sorry/Admit Placeholders | ✓ | 0 |

## Conclusion

Rollback verification $(if [ $BUILD_EXIT_CODE -eq 0 ] && [ $ERROR_COUNT -eq 0 ]; then echo "PASSED"; else echo "COMPLETED WITH WARNINGS"; fi).

EOF

echo "=== Rollback Verification Complete ==="
echo "Report saved to: $LOG_DIR/verification-report.md"
```

### 4.3 Post-Rollback Actions

After successful rollback verification:

1. **Notify Team:**
   ```bash
   # Create notification
   cat > .specs/05_migration/rollback-notification.md << EOF
   # Rollback Notification

   **Date:** $(date)
   **Scenario:** [Scenario Number]
   **Status:** Rollback completed and verified

   ## Summary

   [Brief summary of rollback]

   ## Next Steps

   [Describe next steps]
   EOF
   ```

2. **Create Post-Rollback Branch:**
   ```bash
   git checkout -b post-rollback-$(date +%Y%m%d-%H%M%S)
   git add .specs/05_migration/
   git commit -m "Documentation: Rollback completed and verified"
   ```

3. **Schedule Review:**
   - Schedule team meeting to review rollback
   - Discuss migration strategy adjustments
   - Plan next migration attempt

---

## 5. Rollback Decision Support

### 5.1 Rollback Decision Matrix

| Scenario | Severity | Rollback Type | Estimated Time | Success Probability |
|----------|----------|---------------|----------------|---------------------|
| Critical Build Failure | Critical | Complete | 15 minutes | 95% |
| Dependency Incompatibility | Critical | Dependency | 10 minutes | 90% |
| Syntax Errors After Migration | High | Selective/Full | 10-15 minutes | 85% |
| Proof Regressions | High | Selective/Full | 10-15 minutes | 80% |

### 5.2 Rollback Risk Assessment

| Rollback Type | Risk Level | Potential Issues | Mitigation |
|---------------|------------|------------------|------------|
| Complete Rollback | Low | Data loss | Git backup preserved |
| Dependency Rollback | Low | Dependency conflicts | Clean build artifacts |
| Selective Rollback | Medium | Incomplete rollback | Verify all affected files |
| Full Code Rollback | Low | Lost progress | Incremental backups |

### 5.3 Rollback Communication Template

```markdown
## Rollback Notification

**Date:** YYYY-MM-DD HH:MM:SS
**Scenario:** [Scenario 1/2/3/4]
**Severity:** [Critical/High/Medium]
**Rollback Type:** [Complete/Dependency/Selective/Full]

### Summary

[Brief description of what triggered the rollback]

### Actions Taken

1. [Action 1]
2. [Action 2]
3. [Action 3]

### Verification Results

- [ ] Rollback successful
- [ ] Build verified
- [ ] Error count acceptable
- [ ] No regressions introduced

### Next Steps

1. [Next step 1]
2. [Next step 2]
3. [Next step 3]

### Lessons Learned

[Lessons learned from this rollback]
```

---

## 6. Rollback Prevention Strategies

### 6.1 Pre-Migration Validation

Before attempting migration, validate the following:

```bash
# Validate toolchain version
if ! grep -q "v4.28.0-rc1" lean-toolchain; then
    echo "ERROR: Toolchain version mismatch"
    exit 1
fi

# Validate dependency versions
if ! grep -q "v4.28.0" lakefile.toml; then
    echo "WARNING: Dependency versions may not be aligned"
fi

# Validate Lake configuration
lake configure
if [ $? -ne 0 ]; then
    echo "ERROR: Lake configuration fails before migration"
    exit 1
fi
```

### 6.2 Incremental Migration

To minimize rollback risk, use incremental migration:

1. **Migrate one module at a time**
2. **Verify each module before proceeding**
3. **Create checkpoints after each module**
4. **Test proofs after each migration**

### 6.3 Automated Testing

Implement automated testing to catch issues early:

```bash
# Automated test script
#!/bin/bash
# .specs/05_migration/test-migration.sh

set -e

echo "Running migration tests..."

# Test 1: Syntax validation
lake build 2>&1 | grep "syntax error" && exit 1 || echo "✓ No syntax errors"

# Test 2: Type checking
lake build 2>&1 | grep "type mismatch" | wc -l | read ERROR_COUNT
if [ "$ERROR_COUNT" -gt 10 ]; then
    echo "✗ Too many type errors: $ERROR_COUNT"
    exit 1
fi
echo "✓ Type errors acceptable: $ERROR_COUNT"

# Test 3: Proof completeness
SORRY_COUNT=$(grep -r "sorry\|admit" Morph/Specs/ | wc -l)
if [ "$SORRY_COUNT" -gt 0 ]; then
    echo "✗ Sorry/admit placeholders found: $SORRY_COUNT"
    exit 1
fi
echo "✓ No sorry/admit placeholders"

echo "All migration tests passed!"
```

---

## 7. Rollback Log Template

```markdown
# Rollback Log Entry

**Date:** YYYY-MM-DD HH:MM:SS
**Scenario:** [Scenario 1/2/3/4]
**Trigger:** [Description of trigger]
**Severity:** [Critical/High/Medium]

## Pre-Rollback State

- Lake Configuration: [Status]
- Build Status: [Status]
- Error Count: [N]
- Files Affected: [N]

## Rollback Actions

1. [Action 1] - [Timestamp]
2. [Action 2] - [Timestamp]
3. [Action 3] - [Timestamp]

## Post-Rollback State

- Lake Configuration: [Status]
- Build Status: [Status]
- Error Count: [N]
- Files Affected: [N]

## Verification

- [ ] Lake configuration successful
- [ ] Build successful
- [ ] Error count acceptable
- [ ] No regressions

## Lessons Learned

[Lessons learned]

## Next Steps

[Next steps]
```

---

## 8. Appendix

### 8.1 Quick Reference Commands

```bash
# Create pre-migration backup
git checkout -b backup/pre-migration
git add -A
git commit -m "Backup: Pre-migration state"
git tag backup/pre-migration-$(date +%Y%m%d)

# Restore from backup
git checkout backup/pre-migration
lake clean
rm -rf .lake/packages
lake update

# Verify rollback
lake configure
lake build

# Count errors
lake build 2>&1 | grep -c "error:"

# Check for syntax errors
lake build 2>&1 | grep "syntax error"

# Check for sorry/admit placeholders
grep -r "sorry\|admit" Morph/Specs/
```

### 8.2 Related Documents

- [Threat Model Analysis](../03_threat_model/analysis.md)
- [Migration Process Design](../04_future_state/design/DESIGN-003-migration-process.md)
- [Dependency Configuration Design](../04_future_state/design/DESIGN-002-dependency-configuration.md)
- [Test Plan](../04_future_state/test_plan.md)

### 8.3 Rollback Contact Information

| Role | Name | Contact |
|------|------|---------|
| Migration Lead | [Name] | [Email] |
| DevOps Engineer | [Name] | [Email] |
| Project Lead | [Name] | [Email] |

---

## Definition of Done

This rollback plan is complete when:

- [x] All rollback scenarios documented
- [x] Rollback procedures defined for each scenario
- [x] Verification steps included for each scenario
- [x] Pre-migration backup procedures defined
- [x] Rollback triggers and conditions documented
- [x] Post-rollback verification procedures defined
- [x] Rollback prevention strategies included
- [x] Quick reference commands provided
