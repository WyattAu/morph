# DESIGN-002: Dependency Configuration Design

**Design ID:** DESIGN-002  
**Title:** Dependency Configuration Design for Lake Build System  
**Status:** Draft  
**Created:** 2026-01-31  
**Phase:** Phase 6 - Technical Design  
**Related Requirements:** REQ-002  
**Related ADRs:** ADR-001, ADR-003

---

## 1. Overview

This design document defines the dependency configuration structure for the Morph project using the Lake build system. It establishes conventions for [`lakefile.lean`](../../lakefile.lean), [`lakefile.toml`](../../lakefile.toml), and [`lake-manifest.json`](../../lake-manifest.json) to ensure consistent dependency management and compatibility with Lean 4.28.0-rc1.

---

## 2. Design Goals

1. **Version Alignment:** All dependencies aligned with Lean 4.28.0-rc1 toolchain
2. **Reproducibility:** Consistent builds across environments
3. **Maintainability:** Clear dependency structure and version management
4. **Compatibility:** Proper dependency resolution and Lake workspace configuration
5. **Documentation:** Clear documentation of dependency choices and rationale

---

## 3. Lakefile.lean Structure

### 3.1 File Header

Every [`lakefile.lean`](../../lakefile.lean) must begin with:

```lean
import Lake
open Lake DSL

package Morph {
  -- add package configuration options
}
```

### 3.2 Package Configuration

The package configuration section defines the Morph package:

```lean
package Morph {
  -- Add any package-specific configuration
  -- e.g., default targets, build options
}
```

### 3.3 Dependency Declarations

Dependencies are declared in the `require` section:

```lean
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.28.0"

require aesop from git
  "https://github.com/JLimperg/aesop" @ "v4.28.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"
```

### 3.4 Dependency Declaration Format

```lean
require <package_name> from git
  "<repository_url>" @ "<version_or_commit>"
```

| Component | Description | Example |
|-----------|-------------|---------|
| `require` | Keyword for dependency declaration | `require` |
| `<package_name>` | Local package name | `batteries`, `aesop`, `mathlib` |
| `from git` | Source type | `from git` |
| `"<repository_url>" | Git repository URL | `"https://github.com/leanprover-community/batteries"` |
| `@` | Version specifier separator | `@` |
| `"<version_or_commit>"` | Version tag or commit hash | `"v4.28.0"`, `"abc123def"` |

### 3.5 Target Configuration

Targets define what can be built:

```lean
target Morph.lean lib (pkg : Package) := do
  let leanArgs := #[`--quiet]
  buildLeanLib pkg leanArgs
```

### 3.6 Complete Lakefile.lean Template

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

---

## 4. Lakefile.toml Structure

### 4.1 File Format

[`lakefile.toml`](../../lakefile.toml) uses TOML format for dependency configuration:

```toml
[package]
name = "Morph"
version = "0.1.0"

[dependencies]
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.28.0" }
aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.28.0" }
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.28.0" }
```

### 4.2 Package Section

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `name` | String | Yes | Package name |
| `version` | String | Yes | Package version (semantic versioning) |

### 4.3 Dependencies Section

Each dependency is defined as a table:

```toml
[dependencies]
<package_name> = { git = "<url>", rev = "<version_or_commit>" }
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `git` | String | Yes | Git repository URL |
| `rev` | String | Yes | Git revision (tag, branch, or commit hash) |

### 4.4 Dependency Version Format

#### Version Tags (Preferred)

```toml
# Use official release tags when available
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.28.0" }
```

#### Commit Hashes (For Development)

```toml
# Use commit hashes for unreleased versions
aesop = { git = "https://github.com/JLimperg/aesop", rev = "abc123def456" }
```

#### Branch Names (For Development)

```toml
# Use branch names for tracking development versions
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.28.0-rc1" }
```

### 4.5 Version Selection Guidelines

| Scenario | Recommended Format | Example |
|----------|------------------|---------|
| Stable release | Tag with semantic version | `v4.28.0` |
| Release candidate | Tag with rc suffix | `v4.28.0-rc1` |
| Development version | Branch name | `master`, `v4.28.0-rc1` |
| Specific commit | Commit hash | `abc123def456` |

### 4.6 Complete Lakefile.toml Template

```toml
[package]
name = "Morph"
version = "0.1.0"

[dependencies]
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.28.0" }
aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.28.0" }
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.28.0" }
```

---

## 5. Lake Manifest Format

### 5.1 File Purpose

[`lake-manifest.json`](../../lake-manifest.json) is automatically generated by Lake and contains:

- Resolved dependency versions
- Transitive dependency information
- Build configuration
- Package metadata

### 5.2 Manifest Structure

```json
{
  "version": 1,
  "packages": {
    "Morph": {
      "name": "Morph",
      "version": "0.1.0",
      "dir": ".",
      "git": null,
      "rev": null
    },
    "batteries": {
      "name": "batteries",
      "version": "v4.28.0",
      "dir": ".lake/packages/batteries",
      "git": "https://github.com/leanprover-community/batteries",
      "rev": "v4.28.0"
    },
    "aesop": {
      "name": "aesop",
      "version": "v4.28.0",
      "dir": ".lake/packages/aesop",
      "git": "https://github.com/JLimperg/aesop",
      "rev": "v4.28.0"
    },
    "mathlib": {
      "name": "mathlib",
      "version": "v4.28.0",
      "dir": ".lake/packages/mathlib",
      "git": "https://github.com/leanprover-community/mathlib4",
      "rev": "v4.28.0"
    }
  }
}
```

### 5.3 Manifest Package Entry

Each package entry contains:

| Field | Type | Description |
|-------|------|-------------|
| `name` | String | Package name |
| `version` | String | Package version |
| `dir` | String | Local directory path |
| `git` | String or null | Git repository URL |
| `rev` | String or null | Git revision |

### 5.4 Manifest Generation

The manifest is generated using:

```bash
lake update
```

This command:
- Fetches all dependencies
- Resolves transitive dependencies
- Generates or updates [`lake-manifest.json`](../../lake-manifest.json)
- Creates `.lake/packages/` directory structure

### 5.5 Manifest Validation

Validate the manifest:

```bash
lake configure
```

This command:
- Verifies all dependencies are available
- Checks for version conflicts
- Validates Lake workspace configuration

---

## 6. Dependency Version Alignment

### 6.1 Target Dependency Versions

| Package | Current Version | Target Version | Repository |
|---------|----------------|----------------|------------|
| batteries | v4.10.0 | v4.28.0 | https://github.com/leanprover-community/batteries |
| aesop | v4.10.0 | v4.28.0 | https://github.com/JLimperg/aesop |
| mathlib | v4.10.0 | v4.28.0 | https://github.com/leanprover-community/mathlib4 |

### 6.2 Version Research Process

When researching target versions:

1. **Check Repository Tags**
   ```bash
   git ls-remote --tags https://github.com/leanprover-community/batteries
   ```

2. **Check Release Notes**
   - Review release notes for Lean 4.28.0-rc1 compatibility
   - Identify breaking changes

3. **Verify Compatibility**
   - Check if release notes mention Lean 4.28.0-rc1
   - Test with minimal example if uncertain

4. **Document Rationale**
   - Record why specific version was chosen
   - Note any compatibility concerns

### 6.3 Version Selection Criteria

| Criterion | Description |
|-----------|-------------|
| **Compatibility** | Must be compatible with Lean 4.28.0-rc1 |
| **Stability** | Prefer official releases over development branches |
| **Recency** | Choose most recent stable version |
| **Testing** | Prefer versions with community testing |
| **Documentation** | Prefer versions with good documentation |

---

## 7. Dependency Update Process

### 7.1 Update Procedure

1. **Research Target Versions**
   ```bash
   # Check available tags for each dependency
   git ls-remote --tags https://github.com/leanprover-community/batteries
   git ls-remote --tags https://github.com/JLimperg/aesop
   git ls-remote --tags https://github.com/leanprover-community/mathlib4
   ```

2. **Update lakefile.toml**
   ```toml
   [dependencies]
   batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.28.0" }
   aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.28.0" }
   mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.28.0" }
   ```

3. **Update lakefile.lean**
   ```lean
   require batteries from git
     "https://github.com/leanprover-community/batteries" @ "v4.28.0"

   require aesop from git
     "https://github.com/JLimperg/aesop" @ "v4.28.0"

   require mathlib from git
     "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"
   ```

4. **Regenerate Manifest**
   ```bash
   lake update
   ```

5. **Clean Build Artifacts**
   ```bash
   lake clean
   rm -rf .lake/packages
   ```

6. **Verify Configuration**
   ```bash
   lake configure
   ```

### 7.2 Verification Steps

After updating dependencies:

1. **Verify Manifest**
   ```bash
   cat lake-manifest.json | grep -A 5 "batteries"
   cat lake-manifest.json | grep -A 5 "aesop"
   cat lake-manifest.json | grep -A 5 "mathlib"
   ```

2. **Verify Dependency Compilation**
   ```bash
   lake build Batteries
   lake build Aesop
   lake build Mathlib
   ```

3. **Verify Project Compilation**
   ```bash
   lake build
   ```

---

## 8. Breaking Change Management

### 8.1 Identifying Breaking Changes

When updating dependencies, check for:

| Change Type | Example | Impact |
|-------------|----------|--------|
| Module reorganization | `Mathlib.Data.List` → `Std.Data.List` | Import statements |
| Theorem renaming | `list.map` → `List.map` | Theorem references |
| Type signature changes | Function parameter types | Type errors |
| Deprecated APIs | `String.trim` → `String.trimAscii` | Function calls |
| Type class hierarchy | New instance requirements | Instance declarations |

### 8.2 Breaking Change Documentation

Document breaking changes in a table:

| Dependency | Breaking Change | Migration Path |
|------------|----------------|----------------|
| mathlib4 | Module reorganization | Update import statements |
| batteries | `String.trim` deprecated | Use `String.trimAscii` |
| aesop | Tactic syntax changes | Update tactic syntax |

### 8.3 Migration Strategies

| Strategy | When to Use | Description |
|----------|--------------|-------------|
| **Direct Replacement** | Simple API changes | Replace old API with new API |
| **Adapter Pattern** | Complex API changes | Create adapter functions |
| **Gradual Migration** | Large codebases | Migrate module by module |
| **Complete Rewrite** | Fundamental changes | Rewrite affected code |

---

## 9. Dependency Locking

### 9.1 Purpose

Dependency locking ensures:

- Reproducible builds across environments
- Consistent dependency versions across team
- Prevents accidental dependency updates

### 9.2 Lock File

The [`lake-manifest.json`](../../lake-manifest.json) serves as the lock file:

- Contains exact versions of all dependencies
- Should be committed to version control
- Regenerated only when intentionally updating dependencies

### 9.3 Lock File Management

| Action | Command | Notes |
|--------|----------|-------|
| Update dependencies | `lake update` | Regenerates lock file |
| Check lock file | `cat lake-manifest.json` | Review versions |
| Verify lock file | `lake configure` | Validate configuration |

---

## 10. Transitive Dependencies

### 10.1 Handling Transitive Dependencies

Lake automatically resolves transitive dependencies:

- Direct dependencies are specified in [`lakefile.toml`](../../lakefile.toml)
- Transitive dependencies are resolved by Lake
- All dependencies are recorded in [`lake-manifest.json`](../../lake-manifest.json)

### 10.2 Transitive Dependency Conflicts

If transitive dependencies conflict:

1. **Review Conflict**
   ```bash
   lake configure
   # Lake will report version conflicts
   ```

2. **Resolve Conflict**
   - Update direct dependency to compatible version
   - Or specify exact version in [`lakefile.toml`](../../lakefile.toml)

3. **Verify Resolution**
   ```bash
   lake configure
   lake build
   ```

---

## 11. Implementation Guidelines

### 11.1 Adding a New Dependency

1. **Research Dependency**
   - Check if dependency is compatible with Lean 4.28.0-rc1
   - Review documentation and examples

2. **Add to lakefile.toml**
   ```toml
   [dependencies]
   new_package = { git = "https://github.com/example/new-package", rev = "v1.0.0" }
   ```

3. **Add to lakefile.lean**
   ```lean
   require new_package from git
     "https://github.com/example/new-package" @ "v1.0.0"
   ```

4. **Update Manifest**
   ```bash
   lake update
   ```

5. **Verify**
   ```bash
   lake configure
   lake build NewPackage
   ```

### 11.2 Removing a Dependency

1. **Remove from lakefile.toml**
   ```toml
   [dependencies]
   # Remove the dependency entry
   ```

2. **Remove from lakefile.lean**
   ```lean
   # Remove the require statement
   ```

3. **Clean Build Artifacts**
   ```bash
   lake clean
   rm -rf .lake/packages/new_package
   ```

4. **Update Manifest**
   ```bash
   lake update
   ```

5. **Verify**
   ```bash
   lake configure
   lake build
   ```

### 11.3 Updating a Dependency

1. **Research New Version**
   - Check release notes for breaking changes
   - Verify compatibility with Lean 4.28.0-rc1

2. **Update Version in lakefile.toml**
   ```toml
   [dependencies]
   package = { git = "...", rev = "v2.0.0" }
   ```

3. **Update Version in lakefile.lean**
   ```lean
   require package from git
     "..." @ "v2.0.0"
   ```

4. **Update Manifest**
   ```bash
   lake update
   ```

5. **Clean Build Artifacts**
   ```bash
   lake clean
   rm -rf .lake/packages/package
   ```

6. **Verify**
   ```bash
   lake configure
   lake build
   ```

---

## 12. Related Documents

| Document | Type | Reference |
|----------|------|-----------|
| [`.specs/04_future_state/reqs/REQ-002-dependency-version-alignment.md`](../reqs/REQ-002-dependency-version-alignment.md) | Requirement | Dependency Version Alignment |
| [ADR-001: Lean 4.28.0-rc1 Migration](../../02_adrs/ADR-001-lean-4.28.0-rc1-migration.md) | ADR | Migration to Lean 4.28.0-rc1 |
| [ADR-003: Dependency Version Alignment](../../02_adrs/ADR-003-dependency-version-alignment.md) | ADR | Dependency Version Alignment |
| [Lake Documentation](https://github.com/leanprover/lake) | External | Lake Build System |

---

## 13. Change History

| Date | Version | Author | Description |
|------|---------|--------|-------------|
| 2026-01-31 | 1.0 | System | Initial design document |
