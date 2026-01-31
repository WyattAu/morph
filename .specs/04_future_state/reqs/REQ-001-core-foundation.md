# REQ-001: Core Foundation Requirements

**Requirement ID:** REQ-001  
**Title:** Core Foundation Modules - CommonTypes, GLOSSARY, MorphLanguage  
**Priority:** Critical  
**Domain:** Core Foundation  
**Status:** Pending Implementation

---

## Overview

The Core Foundation modules provide the fundamental type system, terminology, and language specification that all other Morph specification modules depend upon. These modules must be completed first as they form the foundation for the entire specification.

---

## Module Requirements

### 1. CommonTypes Module

**File:** [`Morph/Specs/CommonTypes.lean`](../Morph/Specs/CommonTypes.lean:1)  
**Current State:** 224 lines (single file)  
**Target State:** Complete three-file module (Spec.lean, Lemmas.lean, Examples.lean)

#### Description
The CommonTypes module defines shared type definitions, type aliases, and utility structures used across all specification modules. Currently exists as a single file but should follow the three-file pattern.

#### Acceptance Criteria

**REQ-001.1.1:** CommonTypes module must be restructured into three files:
- `Morph/Specs/CommonTypes/Spec.lean` - Type definitions and specifications
- `Morph/Specs/CommonTypes/Lemmas.lean` - Mathematical properties and proofs
- `Morph/Specs/CommonTypes/Examples.lean` - Usage examples

**REQ-001.1.2:** All type definitions must include:
- Complete docstrings explaining purpose and usage
- Type parameters clearly documented
- Invariant properties specified

**REQ-001.1.3:** Spec.lean must contain:
- Type aliases for frequently used types
- Basic structures (e.g., Option, Result, Either variants)
- Utility type constructors
- Type class definitions for common operations

**REQ-001.1.4:** Lemmas.lean must contain:
- Proofs of type equivalence where applicable
- Properties of type constructors
- Laws for type class instances
- No `sorry` placeholders

**REQ-001.1.5:** Examples.lean must contain:
- Executable examples for each type
- Demonstrations of type class usage
- Verified against lemmas

#### Dependencies
- None (this is a foundational module)

#### Current State Issues
- Currently single file instead of three-file pattern
- May lack comprehensive docstring coverage
- No separate lemmas or examples files

---

### 2. GLOSSARY Module

**Files:** 
- [`Morph/Specs/GLOSSARY/Spec.lean`](../Morph/Specs/GLOSSARY/Spec.lean:1) - 8 lines ⚠️ **STUB**
- [`Morph/Specs/GLOSSARY/Lemmas.lean`](../Morph/Specs/GLOSSARY/Lemmas.lean:1) - 8 lines ⚠️ **STUB**
- [`Morph/Specs/GLOSSARY/Examples.lean`](../Morph/Specs/GLOSSARY/Examples.lean:1) - 8 lines ⚠️ **STUB**
- [`Morph/Specs/GLOSSARY.lean`](../Morph/Specs/GLOSSARY.lean:1) - 18 lines

#### Description
The GLOSSARY module provides formal definitions of terminology used throughout the Morph specification. Currently exists as stub files with minimal content.

#### Acceptance Criteria

**REQ-001.2.1:** GLOSSARY module must contain formal definitions for all core terminology:
- Agent, capability, resource
- Memory, allocation, deallocation
- Concurrency, process, scheduling
- Security, flow, permission
- Module, dependency, build

**REQ-001.2.2:** Spec.lean must contain:
- Formal inductive definitions for each term
- Type signatures for term usage
- Relationships between terms (e.g., agent uses capability)
- No stub content (minimum 50 lines)

**REQ-001.2.3:** Lemmas.lean must contain:
- Properties of term relationships
- Equivalence proofs where applicable
- Consistency checks between related terms
- No stub content (minimum 50 lines)

**REQ-001.2.4:** Examples.lean must contain:
- Usage examples for each term
- Cross-references to modules where terms are used
- No stub content (minimum 50 lines)

**REQ-001.2.5:** Root GLOSSARY.lean must:
- Re-export all definitions from GLOSSARY module
- Provide a unified import point
- Maintain backward compatibility

#### Dependencies
- CommonTypes (for type definitions)

#### Current State Issues
- All three files are stubs (< 10 lines each)
- No formal term definitions
- No relationship specifications
- Root file may need consolidation with module structure

---

### 3. MorphLanguage Module

**Files:**
- [`Morph/Specs/MorphLanguage/Spec.lean`](../Morph/Specs/MorphLanguage/Spec.lean:1) - 265 lines
- [`Morph/Specs/MorphLanguage/Lemmas.lean`](../Morph/Specs/MorphLanguage/Lemmas.lean:1) - 321 lines
- [`Morph/Specs/MorphLanguage/Examples.lean`](../Morph/Specs/MorphLanguage/Examples.lean:1) - 376 lines
- **Total:** 962 lines

#### Description
The MorphLanguage module specifies the core syntax, typing rules, and operational semantics of the Morph language. This is the primary language specification module.

#### Acceptance Criteria

**REQ-001.3.1:** Spec.lean must contain:
- Complete syntax definition (inductive types for expressions, statements, programs)
- Type system definition (typing rules as inductive relations)
- Operational semantics (reduction rules)
- All syntax forms specified

**REQ-001.3.2:** Lemmas.lean must contain:
- Type soundness proofs (progress and preservation)
- Normalization proofs for terminating programs
- Confluence proofs where applicable
- No `sorry` placeholders

**REQ-001.3.3:** Examples.lean must contain:
- Complete programs demonstrating all language features
- Type derivation examples
- Execution traces
- All examples must compile and execute

**REQ-001.3.4:** All definitions must have:
- Complete docstrings
- Clear parameter descriptions
- Usage notes where appropriate

**REQ-001.3.5:** Examples must cover:
- Basic expressions and values
- Control flow constructs
- Function definitions and calls
- Type system features
- Memory operations
- Concurrency primitives

#### Dependencies
- CommonTypes (for shared types)
- GLOSSARY (for terminology)

#### Current State Issues
- May have incomplete type soundness proofs
- Examples may not cover all language features
- Potential TODO/FIXME markers

---

## Cross-Module Requirements

**REQ-001.4.1:** All three modules must compile without errors.

**REQ-001.4.2:** All modules must follow the three-file pattern (Spec.lean, Lemmas.lean, Examples.lean).

**REQ-001.4.3:** All docstrings must follow the project's documentation conventions.

**REQ-001.4.4:** No commented-out code blocks in any file.

**REQ-001.4.5:** No TODO/FIXME/WIP markers in any file.

---

## Verification Criteria

1. **Compilation:** All modules compile successfully with `lake build`
2. **Proof Completeness:** No `sorry` or `admit` placeholders in any lemma
3. **Example Execution:** All examples in Examples.lean files are executable
4. **Documentation:** 100% docstring coverage for all public definitions
5. **Code Quality:** Zero commented-out code blocks, zero TODO markers

---

## Notes

- These modules are **Critical Priority** as all other modules depend on them
- GLOSSARY stubs represent the most significant gap - requires substantial new content
- CommonTypes restructuring from single file to three-file pattern is a structural change
- MorphLanguage is the largest and most complex of the three modules

---

## Related Requirements

- REQ-002: Memory Domain Requirements (depends on CommonTypes, GLOSSARY)
- REQ-003: Concurrency Domain Requirements (depends on CommonTypes, GLOSSARY, MorphLanguage)
- REQ-004: Security Domain Requirements (depends on CommonTypes, GLOSSARY)
- All subsequent requirements depend on these core foundation modules
