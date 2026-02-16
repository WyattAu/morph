# DESIGN-001: File Structure Design

**Design ID:** DESIGN-001  
**Title:** File Structure Design for Morph Specification Modules  
**Status:** Draft  
**Created:** 2026-01-31  
**Phase:** Phase 6 - Technical Design  
**Related Requirements:** REQ-001, REQ-003  
**Related ADRs:** ADR-001, ADR-003

---

## 1. Overview

This design document defines the standard file structure for all Morph specification modules. It establishes conventions for file headers, module documentation, and the three-file module pattern (Spec.lean, Lemmas.lean, Examples.lean) to ensure consistency, maintainability, and proper separation of concerns across the codebase.

---

## 2. Design Goals

1. **Consistency:** All specification modules follow a uniform structure
2. **Separation of Concerns:** Clear separation between specifications, proofs, and examples
3. **Maintainability:** Easy to locate and understand module contents
4. **Documentation:** Comprehensive documentation at file and module level
5. **Compliance:** Alignment with Lean 4 coding standards

---

## 3. Standard File Header Format

### 3.1 Required Header Structure

Every Lean file in the Morph project must begin with the following header:

```lean
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
```

### 3.2 Header Components

| Component | Value | Purpose |
|-----------|-------|---------|
| Copyright Notice | `2024-2025 The Morph Project Authors` | Legal attribution |
| SPDX License | `Apache-2.0` | License identifier for automated tools |

### 3.3 Header Placement Rules

- **Position:** First lines of the file (before any other content)
- **Format:** Block comment using `/- ... -/` syntax
- **Spacing:** No blank lines before the header
- **Consistency:** All files must use identical header format

### 3.4 Implementation Guidelines

```lean
-- CORRECT: Standard header placement
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
import Morph.Specs.CommonTypes

-- INCORRECT: Header with blank line before
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.CommonTypes

-- INCORRECT: Header with additional content
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
Additional module description here
-/
import Morph.Specs.CommonTypes
```

---

## 4. Module Documentation Format

### 4.1 Module Docstring Structure

Each file must include a module-level documentation block using the `/-! ... -/` syntax:

```lean
/-!
# Specification: [Domain Name]

**Source:** `spec/path/to/spec.md`
**Status:** [Complete | In Progress | Pending]
**Last Updated:** YYYY-MM-DD
**Verified By:** [Name or "Pending"]

## Overview

[Brief description of what this module formalizes]

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| SPEC-001 | `spec_proposition_name` | ✓ |
| SPEC-002 | `spec_proposition_name` | ✓ |

## Known Issues

[List any known issues or limitations]

## TODO

[List pending work items]
-!/
```

### 4.2 Module Docstring Components

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| Title | Heading | Yes | Module name using `#` heading |
| Source | Link | Yes | Path to specification document |
| Status | Enum | Yes | One of: Complete, In Progress, Pending |
| Last Updated | Date | Yes | ISO 8601 format (YYYY-MM-DD) |
| Verified By | String | Yes | Name of verifier or "Pending" |
| Overview | Text | Yes | Brief description of module purpose |
| Mapping Summary | Table | Yes | Maps spec sections to Lean propositions |
| Known Issues | List | Optional | Known limitations or bugs |
| TODO | List | Optional | Pending work items |

### 4.3 Status Values

| Status | Meaning | When to Use |
|--------|---------|-------------|
| Complete | All specifications, lemmas, and examples are implemented and verified | When module is fully complete |
| In Progress | Implementation is ongoing, some components may be incomplete | During active development |
| Pending | Module exists but implementation has not started | When module is placeholder |

### 4.4 Mapping Summary Table

The mapping summary table provides traceability between specification documents and Lean 4 formalizations:

| Column | Description | Format |
|--------|-------------|--------|
| Spec Section | Reference to specification section | `SPEC-XXX` or section title |
| Lean 4 Proposition | Name of Lean 4 definition/theorem | `proposition_name` |
| Status | Implementation status | `✓` (complete), `~` (partial), `✗` (not started) |

### 4.5 Module Docstring Placement

```lean
-- CORRECT: Header followed by module docstring
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
/-!
# Specification: Memory Model

**Source:** `spec/memory/model.md`
**Status:** In Progress
**Last Updated:** 2026-01-31
**Verified By:** Pending

## Overview

This module formalizes the memory model for the Morph language,
including block allocation, deallocation, and memory safety properties.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| MEM-001 | `memory_safety` | ✓ |
| MEM-002 | `allocation_invariant` | ✓ |

## TODO

- Implement deallocation verification
- Add concurrency safety proofs
-!/
namespace Morph.Specs.MemoryModel
```

---

## 5. Three-File Module Pattern

### 5.1 Module Structure

Each specification domain in `Morph/Specs/` must follow the three-file pattern:

```
Morph/Specs/[DomainName]/
├── Spec.lean      -- Core types, definitions, and specification theorems
├── Lemmas.lean    -- Mathematical lemmas and proofs
└── Examples.lean  -- Concrete examples and test cases
```

### 5.2 File Responsibilities

| File | Purpose | Contents | Size Guidelines |
|------|---------|----------|-----------------|
| Spec.lean | Core specifications | Type definitions, inductive types, structures, specification theorems | 200-500 lines minimum |
| Lemmas.lean | Mathematical proofs | Lemmas, theorems, proofs, type class instances | 100-300 lines minimum |
| Examples.lean | Usage examples | Example programs, test cases, verification examples | 50-150 lines minimum |

### 5.3 Spec.lean File Structure

```lean
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
/-!
# Specification: [Domain Name]

[Module documentation as defined in Section 4]
-!
namespace Morph.Specs.DomainName

-- Imports
import Morph.Specs.CommonTypes
import Mathlib.Data.List.Basic

-- Type Definitions
/--
Description of the type.
-/
inductive MyType where
  | constructor1 : Type1 → MyType
  | constructor2 : Type2 → MyType
  deriving Repr, BEq

-- Structure Definitions
/--
Description of the structure.
-/
structure MyStructure where
  field1 : Type1
  field2 : Type2
  deriving Repr, BEq

-- Specification Theorems
/--
Main specification theorem describing the core property.
-/
theorem mainSpecification : Prop :=
  ∀ (x : MyType), property x

end Morph.Specs.DomainName
```

### 5.4 Lemmas.lean File Structure

```lean
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
/-!
# Specification: [Domain Name] - Lemmas

**Source:** `spec/path/to/spec.md`
**Status:** [Complete | In Progress | Pending]
**Last Updated:** YYYY-MM-DD
**Verified By:** [Name or "Pending"]

## Overview

This module contains lemmas and proofs for the [Domain Name] specification.

## Main Lemmas

- `lemma_name1`: Description
- `lemma_name2`: Description

## Main Theorems

- `theorem_name1`: Description
- `theorem_name2`: Description
-!/
namespace Morph.Specs.DomainName

-- Imports
import Morph.Specs.DomainName.Spec
import Mathlib.Tactic

-- Helper Lemmas
/--
Helper lemma for proving main properties.
-/
lemma helperLemma (x : MyType) : property x := by
  cases x
  all_goals simp

-- Main Lemmas
/--
Main lemma describing key property.
-/
lemma mainLemma (x : MyType) : strongerProperty x := by
  apply helperLemma
  -- proof continues

-- Type Class Instances
instance : BEq MyType where
  beq x y := match x, y with
    | constructor1 a, constructor1 b => a == b
    | constructor2 a, constructor2 b => a == b
    | _, _ => false

end Morph.Specs.DomainName
```

### 5.5 Examples.lean File Structure

```lean
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
/-!
# Specification: [Domain Name] - Examples

**Source:** `spec/path/to/spec.md`
**Status:** [Complete | In Progress | Pending]
**Last Updated:** YYYY-MM-DD
**Verified By:** [Name or "Pending"]

## Overview

This module contains examples and test cases for the [Domain Name] specification.

## Examples

- Example 1: Description
- Example 2: Description
-!/
namespace Morph.Specs.DomainName

-- Imports
import Morph.Specs.DomainName.Spec
import Morph.Specs.DomainName.Lemmas

-- Example 1: Basic Usage
/--
Example demonstrating basic usage of the type.
-/
example : MyType := constructor1 value

-- Example 2: Property Verification
/--
Example verifying a property holds for a specific value.
-/
example : property (constructor1 value) := by
  apply helperLemma

-- Example 3: Complex Scenario
/--
Example demonstrating a complex scenario.
-/
def complexExample : MyType :=
  let x := constructor1 value1
  let y := constructor2 value2
  -- combine x and y
  constructor1 (combine x y)

-- Verification Examples
/--
Example verifying the main specification.
-/
#eval mainSpecification  -- Should evaluate to true

end Morph.Specs.DomainName
```

### 5.6 Inter-File Dependencies

```lean
-- Spec.lean has no dependencies on Lemmas.lean or Examples.lean
-- Lemmas.lean depends on Spec.lean
-- Examples.lean depends on Spec.lean and Lemmas.lean

-- Import order in Lemmas.lean:
import Morph.Specs.DomainName.Spec

-- Import order in Examples.lean:
import Morph.Specs.DomainName.Spec
import Morph.Specs.DomainName.Lemmas
```

---

## 6. Namespace Declaration

### 6.1 Namespace Structure

All definitions must be within a namespace following the pattern:

```lean
namespace Morph.Specs.DomainName

-- Content here

end Morph.Specs.DomainName
```

### 6.2 Namespace Components

| Component | Value | Example |
|-----------|-------|---------|
| Root namespace | `Morph` | `Morph` |
| Sub-namespace | `Specs` | `Specs` |
| Domain name | PascalCase | `MemoryModel` |

### 6.3 Namespace Rules

- **Consistency:** All files in a module use the same namespace
- **Nesting:** No additional nesting within the namespace
- **Opening:** Namespace opened after imports and module docstring
- **Closing:** Namespace closed at the end of the file

---

## 7. File Organization Rules

### 7.1 File Ordering Within Module

Files within a module should be ordered as:

1. **Spec.lean** - Core definitions (no dependencies on other files)
2. **Lemmas.lean** - Proofs (depends on Spec.lean)
3. **Examples.lean** - Examples (depends on Spec.lean and Lemmas.lean)

### 7.2 Content Ordering Within File

Within each file, content should be ordered as:

1. Copyright header
2. Module docstring
3. Namespace declaration
4. Imports
5. Type definitions
6. Structure definitions
7. Function definitions
8. Theorem/lemma declarations
9. Type class instances
10. Namespace end

### 7.3 Import Organization

Imports should be organized as:

```lean
-- Standard library imports
import Std

-- Morph project imports
import Morph.Specs.CommonTypes
import Morph.Specs.GLOSSARY

-- External library imports
import Mathlib.Data.List.Basic
import Batteries.Data.HashMap
```

---

## 8. Size and Quality Guidelines

### 8.1 Minimum File Sizes

| File Type | Minimum Lines | Rationale |
|-----------|---------------|-----------|
| Spec.lean | 200 lines | Must contain substantial type definitions and specifications |
| Lemmas.lean | 100 lines | Must contain meaningful lemmas and proofs |
| Examples.lean | 50 lines | Must contain executable examples |

### 8.2 Stub File Detection

Files are considered stubs if they meet any of these criteria:

- **Less than 10 lines:** Clearly incomplete
- **Only placeholder content:** Contains only `sorry` or `admit`
- **No meaningful definitions:** Contains only imports and namespace

### 8.3 Quality Indicators

| Indicator | Target | Measurement |
|-----------|--------|--------------|
| Docstring coverage | 100% | All public definitions have docstrings |
| Proof completeness | 100% | No `sorry` or `admit` placeholders |
| Example executability | 100% | All examples compile and execute |
| Code quality | Zero violations | No commented-out code, no TODO markers |

---

## 9. Implementation Guidelines

### 9.1 Creating a New Module

When creating a new specification module:

1. Create directory: `Morph/Specs/[DomainName]/`
2. Create `Spec.lean` with header, docstring, and core definitions
3. Create `Lemmas.lean` with header, docstring, and proofs
4. Create `Examples.lean` with header, docstring, and examples
5. Verify all files compile: `lake build Morph.Specs.DomainName`

### 9.2 Restructuring Existing Modules

When restructuring an existing module to three-file pattern:

1. Analyze existing file content
2. Separate content into Spec/Lemmas/Examples
3. Add proper headers and docstrings
4. Update imports between files
5. Verify compilation
6. Run tests to ensure no regressions

### 9.3 Validation Checklist

For each module, verify:

- [ ] All three files exist (Spec.lean, Lemmas.lean, Examples.lean)
- [ ] All files have copyright header
- [ ] All files have module docstring
- [ ] All files use correct namespace
- [ ] All files meet minimum size requirements
- [ ] All imports are organized correctly
- [ ] All public definitions have docstrings
- [ ] All examples are executable
- [ ] Module compiles without errors

---

## 10. Related Documents

| Document | Type | Reference |
|----------|------|-----------|
| [`.specs/01_standards/coding_standards.md`](../01_standards/coding_standards.md) | Coding Standards | File header and documentation standards |
| [`.specs/04_future_state/reqs/REQ-001-core-foundation.md`](../reqs/REQ-001-core-foundation.md) | Requirement | Core Foundation Requirements |
| [`.specs/04_future_state/reqs/REQ-003-syntax-standards-compliance.md`](../reqs/REQ-003-syntax-standards-compliance.md) | Requirement | Syntax Standards Compliance |
| [ADR-001: Lean 4.28.0-rc1 Migration](../../02_adrs/ADR-001-lean-4.28.0-rc1-migration.md) | ADR | Migration to Lean 4.28.0-rc1 |

---

## 11. Change History

| Date | Version | Author | Description |
|------|---------|--------|-------------|
| 2026-01-31 | 1.0 | System | Initial design document |
