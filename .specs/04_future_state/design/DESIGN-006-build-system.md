# DESIGN-006: Build System Design

**Design ID:** DESIGN-006  
**Title:** Build System Design  
**Status:** Draft  
**Created:** 2026-01-30  
**Related ADRs:** ADR-004, ADR-003, ADR-007  
**Related Requirements:** REQ-001 through REQ-007

---

## Purpose and Scope

This design document defines technical specifications for build system configuration in the Morph language Lean 4 formal verification project. It specifies Lake build configuration patterns, dependency management patterns, and test executable structure.

The scope includes:
- Lake build configuration patterns
- Dependency management patterns
- Test executable structure
- Build target definitions
- CI/CD integration patterns

---

## Technical Specifications

### Lake Configuration Files

#### lean-toolchain File

The `lean-toolchain` file pins the Lean 4 version:

```
leanprover/lean4:v4.10.0
```

**Purpose:** Ensures reproducible builds by pinning Lean 4 to v4.10.0.

#### lakefile.toml File

The `lakefile.toml` file defines package metadata and dependencies:

```toml
[package]
name = "Morph"
version = "0.1.0"
lean_version = "leanprover/lean4:v4.10.0"

[dependencies]
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.10.0" }
aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.10.0" }
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.10.0" }
```

**Purpose:** Defines package metadata and external dependencies.

#### lakefile.lean File

The `lakefile.lean` file defines custom build targets and tasks:

```lean
import Lake
open Lake DSL

package Morph {
  -- add package configuration options
}

-- Add library configuration
lean_lib Morph {
  -- add library configuration options
}

-- Add executable targets
lean_exe Morph.Executable {
  root := `Morph.Executable`
}

-- Add test targets
lean_test Morph.Specs.Tests {
  root := `Morph.Specs.Tests`
}
```

**Purpose:** Defines custom build targets and tasks.

#### lake-manifest.json File

The `lake-manifest.json` file is a lock file for dependency versions:

```json
{
  "name": "Morph",
  "version": "0.1.0",
  "lakeDir": ".lake",
  "packages": [
    {
      "name": "mathlib",
      "git": "https://github.com/leanprover-community/mathlib4",
      "rev": "v4.10.0",
      "inherited": false,
      "dir": ".lake/packages/mathlib"
    },
    {
      "name": "aesop",
      "git": "https://github.com/JLimperg/aesop",
      "rev": "v4.10.0",
      "inherited": false,
      "dir": ".lake/packages/aesop"
    },
    {
      "name": "batteries",
      "git": "https://github.com/leanprover-community/batteries",
      "rev": "v4.10.0",
      "inherited": false,
      "dir": ".lake/packages/batteries"
    }
  ]
}
```

**Purpose:** Lock file ensuring reproducible builds with exact dependency versions.

---

## Lake Build Configuration Patterns

### Library Configuration Pattern

Library configuration in `lakefile.lean`:

```lean
import Lake
open Lake DSL

package Morph {
  -- Package metadata
}

-- Library configuration
lean_lib Morph {
  -- Add library configuration options
  -- Sources: All .lean files in Morph/ directory
  -- Default target for `lake build`
}
```

### Executable Configuration Pattern

Executable configuration in `lakefile.lean`:

```lean
import Lake
open Lake DSL

package Morph {
  -- Package metadata
}

lean_lib Morph {
  -- Library configuration
}

-- Executable target
lean_exe Morph.Executable {
  root := `Morph.Executable`
  -- Support IO operations
  -- Can be run with `lake run Morph.Executable`
}
```

### Test Configuration Pattern

Test configuration in `lakefile.lean`:

```lean
import Lake
open Lake DSL

package Morph {
  -- Package metadata
}

lean_lib Morph {
  -- Library configuration
}

-- Test executable
lean_exe Morph.Specs.Tests {
  root := `Morph.Specs.Tests`
  -- Test executable
  -- Can be run with `lake test` or `lake run Morph.Specs.Tests`
}
```

### Custom Build Target Pattern

Custom build targets in `lakefile.lean`:

```lean
import Lake
open Lake DSL

package Morph {
  -- Package metadata
}

lean_lib Morph {
  -- Library configuration
}

-- Custom build target for specific domain
target buildDomain (domainName : String) : ScriptM Bool := do
  let modules ← findModulesInDomain domainName
  buildModules modules
```

---

## Dependency Management Patterns

### Standard Library Dependencies

Standard library imports in Lean files:

```lean
-- Standard library imports
import Std
import Lean
```

### Third-Party Library Dependencies

Third-party library imports in Lean files:

```lean
-- Mathlib imports
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

-- Aesop imports
import Aesop

-- Batteries imports
import Batteries.Data.List.Basic
import Batteries.Tactic.Aesop
```

### Project Core Dependencies

Project core imports in Lean files:

```lean
-- Project core imports
import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Memory
```

### Dependency Version Pinning

Dependency version pinning in `lakefile.toml`:

```toml
[dependencies]
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.10.0" }
aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.10.0" }
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.10.0" }
```

### Dependency Update Pattern

Updating dependencies:

```bash
# Update dependencies to latest compatible versions
lake update

# Update specific dependency
lake update mathlib
```

---

## Test Executable Structure

### Test File Structure

Test files follow the three-file pattern:

```
Morph/Specs/Tests/
├── Spec.lean      -- Test type definitions and specifications
├── Lemmas.lean    -- Test lemmas and proofs
└── Examples.lean  -- Test examples and test cases
```

### Test Executable Pattern

Test executable in `lakefile.lean`:

```lean
import Lake
open Lake DSL

package Morph {
  -- Package metadata
}

lean_lib Morph {
  -- Library configuration
}

-- Test executable
lean_exe Morph.Specs.Tests {
  root := `Morph.Specs.Tests`
}
```

### Test Case Pattern

Test cases in `Morph/Specs/Tests/Examples.lean`:

```lean
import Morph.Specs.Memory.MemoryModel.Spec
import Morph.Specs.Memory.MemoryModel.Lemmas

namespace Morph.Specs.Tests

/-! ## Memory Model Tests
-/

/-- Test: Allocation creates unique block. -/
#test allocationCreatesUniqueBlockTest : IO Unit := do
  let (state, address) := allocate 16 emptyMemoryState
  assert (allocationCreatesUniqueBlock 16 emptyMemoryState)

/-- Test: Deallocation frees block. -/
#test deallocationFreesBlockTest : IO Unit := do
  let state := deallocate 0x1000 oneBlockState
  assert (deallocationFreesBlock 0x1000 oneBlockState)

end Morph.Specs.Tests
```

### Running Tests

Running tests with Lake:

```bash
# Run all tests
lake test

# Run specific test executable
lake run Morph.Specs.Tests

# Run tests with verbose output
lake test --verbose
```

---

## Build Target Definitions

### Default Build Target

Default build target builds all libraries:

```bash
# Build all libraries
lake build

# Equivalent to
lake build Morph
```

### Specific Library Target

Build specific library:

```bash
# Build Morph library
lake build Morph

# Build specific module
lake build Morph.Specs.Memory.MemoryModel
```

### Executable Target

Build executable:

```bash
# Build executable
lake build Morph.Executable

# Run executable
lake run Morph.Executable
```

### Test Target

Build and run tests:

```bash
# Build and run tests
lake test

# Build test executable
lake build Morph.Specs.Tests

# Run test executable
lake run Morph.Specs.Tests
```

### Clean Target

Clean build artifacts:

```bash
# Clean all build artifacts
lake clean

# Clean specific target
lake clean Morph.Executable
```

---

## CI/CD Integration Patterns

### GitLab CI Pattern

GitLab CI configuration in `.gitlab-ci.yml`:

```yaml
stages:
  - lint
  - build
  - test

# Pre-commit validation
lint:
  stage: lint
  script:
    - pre-commit run --all-files
  rules:
    - if: '$CI_PIPELINE_SOURCE == "merge_request_event"'

# Lean compilation
build:
  stage: build
  script:
    - lake build
  rules:
    - if: '$CI_PIPELINE_SOURCE == "merge_request_event"'
    - if: '$CI_COMMIT_BRANCH == "main"'

# Test execution
test:
  stage: test
  script:
    - lake test
  rules:
    - if: '$CI_PIPELINE_SOURCE == "merge_request_event"'
    - if: '$CI_COMMIT_BRANCH == "main"'
```

### Jenkins Pattern

Jenkins configuration in `Jenkinsfile`:

```groovy
pipeline {
    agent any
    
    stages {
        stage('Lint') {
            steps {
                sh 'pre-commit run --all-files'
            }
        }
        
        stage('Build') {
            steps {
                sh 'lake build'
            }
        }
        
        stage('Test') {
            steps {
                sh 'lake test'
            }
        }
    }
    
    triggers {
        cron('H 0 * * *')  // Daily at midnight
    }
}
```

### Pre-commit Pattern

Pre-commit configuration in `.pre-commit-config.yaml`:

```yaml
repos:
  - repo: local
    hooks:
      - id: check-sorry
        name: Check for sorry placeholders
        entry: '! grep -r "sorry" Morph/Specs/'
        language: system
      - id: check-commented-code
        name: Check for commented-out code
        entry: './scripts/check_commented_code.sh'
        language: script
      - id: check-three-file-pattern
        name: Check three-file module pattern
        entry: './scripts/check_three_file_pattern.sh'
        language: script
```

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Unpinned Dependency Versions

**Incorrect:**
```toml
[dependencies]
mathlib = { git = "https://github.com/leanprover-community/mathlib4" }
```

**Correct:**
```toml
[dependencies]
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.10.0" }
```

### Anti-Pattern 2: Missing Test Executable

**Incorrect:**
```lean
import Lake
open Lake DSL

package Morph {
  -- Package metadata
}

lean_lib Morph {
  -- Library configuration
}
```

**Correct:**
```lean
import Lake
open Lake DSL

package Morph {
  -- Package metadata
}

lean_lib Morph {
  -- Library configuration
}

-- Test executable
lean_exe Morph.Specs.Tests {
  root := `Morph.Specs.Tests`
}
```

### Anti-Pattern 3: Using `sorry` in Tests

**Incorrect:**
```lean
#test allocationTest : IO Unit := do
  sorry
```

**Correct:**
```lean
#test allocationTest : IO Unit := do
  let (state, address) := allocate 16 emptyMemoryState
  assert (allocationCreatesUniqueBlock 16 emptyMemoryState)
```

### Anti-Pattern 4: Commented-Out Build Configuration

**Incorrect:**
```lean
-- Old build configuration
-- lean_exe Morph.OldExecutable {
--   root := `Morph.OldExecutable`
-- }

-- New build configuration
lean_exe Morph.Executable {
  root := `Morph.Executable`
}
```

**Correct:**
```lean
-- Build configuration
lean_exe Morph.Executable {
  root := `Morph.Executable`
}
```

---

## Verification Checklist

For build system configuration, verify:

- [ ] `lean-toolchain` file exists and pins Lean 4 to v4.10.0
- [ ] `lakefile.toml` file exists with package metadata
- [ ] `lakefile.lean` file exists with build targets
- [ ] `lake-manifest.json` file exists (generated by Lake)
- [ ] All dependencies are pinned to specific versions
- [ ] Test executable is configured
- [ ] CI/CD configuration includes build and test stages
- [ ] Pre-commit hooks check for `sorry` and commented-out code
- [ ] No commented-out build configuration
- [ ] Build succeeds with `lake build`
- [ ] Tests pass with `lake test`

---

## References

- [ADR-004: Lake Build System](../02_adrs/ADR-004-lake-build-system.md)
- [ADR-003: Lean 4 with mathlib4](../02_adrs/ADR-003-lean4-mathlib4.md)
- [ADR-007: CI/CD Integration](../02_adrs/ADR-007-ci-cd-integration.md)
- [Coding Standards](../01_standards/coding_standards.md)
- [REQ-005: Build System Domain Requirements](../04_future_state/reqs/REQ-005-build-system-domain.md)
- [Lake Documentation](https://github.com/leanprover/lean4/blob/master/doc/lake.md)
