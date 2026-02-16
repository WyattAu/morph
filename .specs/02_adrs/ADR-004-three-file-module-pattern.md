# ADR-004: Three-File Module Pattern

**Status:** Accepted  
**Date:** 2026-01-31  
**Decision Type:** Architectural  
**Related ADRs:** None  
**Related Documents:** [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md), [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md), [`.specs/01_standards/coding_standards.md`](../01_standards/coding_standards.md)

---

## Context

The Morph project uses a consistent three-file pattern for organizing specifications across all 40+ specification domains. Each domain directory contains three files: `Spec.lean`, `Lemmas.lean`, and `Examples.lean`. This pattern provides clear separation of concerns and aligns with formal verification best practices.

### Current State

The project currently has 40+ specification directories, each following the three-file pattern:

```
Morph/Specs/[DomainName]/
├── Spec.lean      -- Core types, definitions, and specification theorems
├── Lemmas.lean    -- Mathematical lemmas and proofs
└── Examples.lean  -- Concrete examples and test cases
```

#### Example Directories

| Domain | Files |
|--------|-------|
| AbiAlignmentAlgebra | Spec.lean, Lemmas.lean, Examples.lean |
| AbiDataRefinement | Spec.lean, Lemmas.lean, Examples.lean |
| ASTGraph | Spec.lean, Lemmas.lean, Examples.lean |
| BackendTiling | Spec.lean, Lemmas.lean, Examples.lean |
| BuildLattice | Spec.lean, Lemmas.lean, Examples.lean |
| ConcurrencyProcessAlgebra | Spec.lean, Lemmas.lean, Examples.lean |
| ... | ... |

### File Purposes

#### Spec.lean

Contains the core specification for the domain:
- Type definitions (inductives, structures, classes)
- Core definitions and operations
- Specification theorems (statements without proofs)
- Fundamental properties and axioms
- Domain-specific terminology and conventions

#### Lemmas.lean

Contains mathematical lemmas and their proofs:
- Proofs of theorems stated in Spec.lean
- Supporting lemmas and auxiliary results
- Proof tactics and automation strategies
- Cross-references to relevant theorems in Spec.lean

#### Examples.lean

Contains concrete examples and test cases:
- Executable examples demonstrating specification concepts
- Test cases for lemmas and theorems
- Usage patterns and idioms
- Verification examples against lemmas

### Benefits of Current Pattern

1. **Clear Separation of Concerns:** Each file has a distinct, well-defined purpose.

2. **Improved Readability:** Large specifications are broken into manageable, focused files.

3. **Parallel Development:** Different team members can work on different files without conflicts.

4. **Incremental Compilation:** Changes to one file don't require recompiling the entire specification.

5. **Formal Verification Best Practices:** Aligns with how formal verification projects typically organize specifications.

6. **Documentation Structure:** The pattern naturally guides documentation and understanding of the domain.

### Alternatives Considered

#### Alternative 1: Single File Per Domain

**Structure:**
```
Morph/Specs/[DomainName]/
└── DomainName.lean
```

**Pros:**
- Simpler file structure
- Fewer files to manage
- Easier to navigate within a domain

**Cons:**
- Very large files (potentially thousands of lines)
- Difficult to read and maintain
- Changes to proofs require recompiling entire specification
- No clear separation between specification, proofs, and examples
- Harder for multiple developers to work on the same domain simultaneously
- Violates single responsibility principle

#### Alternative 2: Two-File Pattern (Spec + Proofs)

**Structure:**
```
Morph/Specs/[DomainName]/
├── Spec.lean      -- Specification and proofs
└── Examples.lean  -- Examples
```

**Pros:**
- Fewer files than three-file pattern
- Keeps examples separate for testing

**Cons:**
- Still mixes specification and proofs in one file
- Large files with mixed concerns
- Proofs obscure the specification structure
- Harder to find specific theorems or lemmas

#### Alternative 3: Five-File Pattern (Spec, Lemmas, Theorems, Proofs, Examples)

**Structure:**
```
Morph/Specs/[DomainName]/
├── Spec.lean      -- Types and definitions
├── Lemmas.lean    -- Lemma statements
├── Theorems.lean  -- Theorem statements
├── Proofs.lean    -- All proofs
└── Examples.lean  -- Examples
```

**Pros:**
- Maximum separation of concerns
- Each file has a very specific purpose

**Cons:**
- Too many files, increasing complexity
- Over-engineering for most domains
- Difficult to maintain relationships between lemmas and their proofs
- Increased cognitive load for developers
- More files to navigate and understand

#### Alternative 4: Maintain Three-File Pattern (Chosen)

**Pros:**
- Optimal balance of separation and simplicity
- Clear, well-defined boundaries between concerns
- Aligns with formal verification best practices
- Supports parallel development
- Enables incremental compilation
- Proven to work well in practice

**Cons:**
- More files than single-file approach
- Requires discipline to maintain separation

---

## Decision

**Maintain the three-file module pattern** for all specification domains in the Morph project.

### Pattern Definition

Each specification domain directory MUST contain exactly three files:

```
Morph/Specs/[DomainName]/
├── Spec.lean      -- Core types, definitions, and specification theorems
├── Lemmas.lean    -- Mathematical lemmas and proofs
└── Examples.lean  -- Concrete examples and test cases
```

### File Content Standards

#### Spec.lean Standards

**Purpose:** Define the specification for the domain without implementation details.

**Required Content:**
- Copyright and SPDX license header
- Module documentation with status and mapping summary
- Type definitions (inductives, structures, classes)
- Core definitions and operations
- Specification theorems (statements without proofs)
- Fundamental properties and axioms

**Prohibited Content:**
- Proofs of theorems (these go in Lemmas.lean)
- Executable examples (these go in Examples.lean)
- Test cases (these go in Examples.lean)

**Imports:** Minimal, well-organized imports only.

#### Lemmas.lean Standards

**Purpose:** Prove the theorems stated in Spec.lean and provide supporting lemmas.

**Required Content:**
- Copyright and SPDX license header
- Module documentation with status and mapping summary
- Proofs of theorems from Spec.lean
- Supporting lemmas and auxiliary results
- Clear, readable proof tactics
- Cross-references to relevant theorems in Spec.lean

**Prohibited Content:**
- New type definitions (these go in Spec.lean)
- Executable examples (these go in Examples.lean)

**Imports:** Must import the corresponding Spec.lean file.

#### Examples.lean Standards

**Purpose:** Provide concrete examples and test cases for the specification.

**Required Content:**
- Copyright and SPDX license header
- Module documentation with status and mapping summary
- Executable examples demonstrating specification concepts
- Test cases for lemmas and theorems
- Usage patterns and idioms
- Explanatory comments

**Prohibited Content:**
- New type definitions (these go in Spec.lean)
- New theorems (these go in Spec.lean)
- Proofs (these go in Lemmas.lean)

**Imports:** Must import the corresponding Spec.lean and Lemmas.lean files.

### Naming Conventions

- **Domain Names:** PascalCase, descriptive of the domain (e.g., `AbiAlignmentAlgebra`, `ConcurrencyProcessAlgebra`)
- **File Names:** Fixed pattern: `Spec.lean`, `Lemmas.lean`, `Examples.lean`
- **Module Names:** `Morph.Specs.[DomainName].Spec`, `Morph.Specs.[DomainName].Lemmas`, `Morph.Specs.[DomainName].Examples`

### Documentation Requirements

Each file MUST include:

1. **File Header:** Copyright notice and SPDX license identifier
2. **Module Documentation:** Complete docstring with:
   - Status (e.g., "Draft", "In Progress", "Complete")
   - Brief description of the domain
   - Mapping summary (what this domain represents)
   - Key types and theorems

### Enforcement

The three-file pattern MUST be enforced through:

1. **Code Review:** All new specification domains must follow the pattern.
2. **Linting:** Automated checks to verify correct file structure.
3. **Documentation:** The pattern is documented in this ADR and referenced in coding standards.
4. **Onboarding:** New developers are trained on the pattern as part of onboarding.

---

## Consequences

### Positive Consequences

1. **Clear Separation of Concerns:** Each file has a distinct, well-defined purpose, making the codebase easier to understand and navigate.

2. **Improved Maintainability:** Changes to proofs don't affect the specification structure, and examples can be modified independently.

3. **Parallel Development:** Multiple team members can work on different files of the same domain without conflicts.

4. **Incremental Compilation:** Changes to one file don't require recompiling the entire specification, improving build times.

5. **Formal Verification Best Practices:** Aligns with how formal verification projects typically organize specifications, making the project more accessible to the formal methods community.

6. **Documentation Structure:** The pattern naturally guides documentation and understanding of each domain.

7. **Consistency:** All 40+ specification domains follow the same pattern, reducing cognitive load for developers.

8. **Testability:** Examples are isolated in their own file, making it easy to run and verify them.

### Negative Consequences

1. **More Files:** The three-file pattern results in more files than a single-file approach, increasing file management overhead.

2. **Navigation Complexity:** Developers need to navigate between three files to understand a complete domain.

3. **Discipline Required:** Maintaining the separation requires discipline; developers may be tempted to put content in the wrong file.

4. **Import Management:** Lemmas.lean and Examples.lean must import Spec.lean, and Examples.lean must also import Lemmas.lean, creating a dependency chain.

5. **Learning Curve:** New developers need to learn the pattern and understand the purpose of each file.

### Neutral Consequences

1. **Build Structure:** The pattern aligns with Lake's module system, making builds straightforward.

2. **Tooling Support:** Most Lean 4 tooling works well with this pattern, as it's a common approach in the Lean ecosystem.

3. **File Size:** Individual files are smaller and more focused, but the total lines of code across all files is the same as a single-file approach.

---

## Status

**Accepted** - This decision has been approved and is the current standard for the project.

### Implementation Status

| Requirement | Status | Notes |
|-------------|--------|-------|
| Pattern Definition | Complete | All 40+ domains follow the pattern |
| Documentation | Complete | This ADR documents the pattern |
| Enforcement | Ongoing | Code reviews and linting enforce the pattern |

### Existing Domains

All existing specification domains already follow this pattern:

- AbiAlignmentAlgebra
- AbiDataRefinement
- ASTGraph
- BackendTiling
- BuildLattice
- ConcurrencyProcessAlgebra
- ExecutionModel
- LayeredConcurrency
- MonadicEffect
- SchedulingModes
- DialectProjection
- DualOptimization
- LexicalStructureSyntax
- ModuleSystem
- MorphLanguage
- OperatorNullCoalescing
- ScopingLambdaCalculus
- StrictStateUnidirectional
- SyntaxTranslation
- TypeSystem
- UnidirectionalDataFlow
- ArcAffineIntegration
- MemoryAcyclicity
- MemoryAffineLogic
- MemoryModel
- InfrastructureSafetyContracts
- LicenseDeonticLogic
- Licensing
- SecurityFlow
- SecurityOCap
- Financial
- GLOSSARY
- Maths
- ModuleExistential
- README
- RegistryConsensus
- SchedulerRandomizedStealing
- StorageDAWG
- TerminologyStandardization
- UnitGroupTheory
- VersionCompatibility

---

## References

- [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) - Current state analysis
- [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) - Target state definition
- [`.specs/01_standards/coding_standards.md`](../01_standards/coding_standards.md) - Coding standards (lines 230-268)
- [Formal Verification Best Practices](https://www.cl.cam.ac.uk/~jrh13/papers/dependable.pdf)
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)

---

## Appendix: File Template

### Spec.lean Template

```lean
/-!
# Module: Morph.Specs.[DomainName].Spec

Status: [Draft | In Progress | Complete]

## Mapping Summary

[Brief description of what this domain represents and its role in the Morph project]

## Key Types

- [TypeName]: [Description]
- [TypeName]: [Description]

## Key Theorems

- [TheoremName]: [Description]
- [TheoremName]: [Description]
-/

Copyright (c) [Year] [Copyright Holder]
SPDX-License-Identifier: [License-Identifier]

namespace Morph.Specs.[DomainName]

/-- [Description of the type] -/
inductive [TypeName] : Type where
  | [constructor] : [type]
  deriving [TypeClass]

/-- [Description of the definition] -/
def [DefinitionName] : [Type] := [definition]

/-- [Description of the theorem] -/
theorem [TheoremName] : [Proposition] := by
  sorry  -- Proof goes in Lemmas.lean

end Morph.Specs.[DomainName]
```

### Lemmas.lean Template

```lean
/-!
# Module: Morph.Specs.[DomainName].Lemmas

Status: [Draft | In Progress | Complete]

## Mapping Summary

[Proofs for theorems in Spec.lean and supporting lemmas]

## Key Lemmas

- [LemmaName]: [Description]
- [LemmaName]: [Description]
-/

Copyright (c) [Year] [Copyright Holder]
SPDX-License-Identifier: [License-Identifier]

namespace Morph.Specs.[DomainName]

open Spec

/-- [Description of the lemma] -/
lemma [LemmaName] : [Proposition] := by
  [proof tactics]

/-- Proof of [TheoremName] -/
theorem [TheoremName] : [Proposition] := by
  [proof tactics]

end Morph.Specs.[DomainName]
```

### Examples.lean Template

```lean
/-!
# Module: Morph.Specs.[DomainName].Examples

Status: [Draft | In Progress | Complete]

## Mapping Summary

[Examples demonstrating the specification and verifying lemmas]

## Examples

- [ExampleName]: [Description]
- [ExampleName]: [Description]
-/

Copyright (c) [Year] [Copyright Holder]
SPDX-License-Identifier: [License-Identifier]

namespace Morph.Specs.[DomainName]

open Spec Lemmas

/-- [Description of the example] -/
def [ExampleName] : [Type] := [example]

/-- [Explanation of what this example demonstrates] -/
example : [Proposition] := by
  [proof tactics]

end Morph.Specs.[DomainName]
```
