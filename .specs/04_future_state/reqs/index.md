# Morph Language Specification - Requirements Index

**Phase 5 - Requirement Sharding**  
**Generated:** 2026-01-30  
**Purpose:** Index of all functional requirements for the Morph language Lean validation project

---

## Executive Summary

This index provides a comprehensive overview of all functional requirements organized by domain. The requirements specify the work needed to transform the current state of the Morph specification modules into a production-ready, fully validated formal specification.

### Key Metrics

- **Total Requirements:** 7
- **Total Modules:** 45 specification modules
- **Critical Priority:** 1 requirement (3 modules)
- **High Priority:** 3 requirements (10 modules)
- **Medium Priority:** 3 requirements (32 modules)

---

## Requirements by Priority

### Critical Priority

| Requirement ID | Title | Domain | Modules | Status |
|---------------|-------|--------|---------|--------|
| [REQ-001](REQ-001-core-foundation.md) | Core Foundation Requirements | Core Foundation | 3 | Pending |

**Rationale:** Core Foundation modules (CommonTypes, GLOSSARY, MorphLanguage) are the foundation for all other modules. They must be completed first as all other requirements depend on them.

---

### High Priority

| Requirement ID | Title | Domain | Modules | Status |
|---------------|-------|--------|---------|--------|
| [REQ-002](REQ-002-memory-domain.md) | Memory Domain Requirements | Memory | 3 | Pending |
| [REQ-003](REQ-003-concurrency-domain.md) | Concurrency Domain Requirements | Concurrency | 4 | Pending |
| [REQ-004](REQ-004-security-domain.md) | Security Domain Requirements | Security | 3 | Pending |

**Rationale:** Memory, Concurrency, and Security domains ensure core safety and correctness properties of the language. These are essential for production use.

---

### Medium Priority

| Requirement ID | Title | Domain | Modules | Status |
|---------------|-------|--------|---------|--------|
| [REQ-005](REQ-005-build-system-domain.md) | Build System Domain Requirements | Build System | 4 | Pending |
| [REQ-006](REQ-006-abi-domain.md) | ABI Domain Requirements | ABI | 2 | Pending |
| [REQ-007](REQ-007-language-features-domain.md) | Language Features Domain Requirements | Language Features | 21 | Pending |

**Rationale:** Build System, ABI, and Language Features domains support advanced functionality but are not critical for basic language execution.

---

## Requirements by Domain

### 1. Core Foundation Domain

**Requirement:** [REQ-001](REQ-001-core-foundation.md) - Core Foundation Requirements  
**Priority:** Critical  
**Modules:** 3

| Module | Current State | Key Issues |
|--------|---------------|-------------|
| CommonTypes | 224 lines (single file) | Needs restructuring to three-file pattern |
| GLOSSARY | 24 lines (all stubs) | All three files are stubs (< 10 lines) |
| MorphLanguage | 962 lines | May have incomplete type soundness proofs |

**Dependencies:** None (foundational)

---

### 2. Memory Domain

**Requirement:** [REQ-002](REQ-002-memory-domain.md) - Memory Domain Requirements  
**Priority:** High  
**Modules:** 3

| Module | Current State | Key Issues |
|--------|---------------|-------------|
| MemoryModel | 485 lines | Lemmas.lean small (81 lines) |
| MemoryAcyclicity | 367 lines | Lemmas.lean small (64 lines) |
| MemoryAffineLogic | 476 lines | Lemmas.lean small (62 lines) |

**Dependencies:** REQ-001

---

### 3. Concurrency Domain

**Requirement:** [REQ-003](REQ-003-concurrency-domain.md) - Concurrency Domain Requirements  
**Priority:** High  
**Modules:** 4

| Module | Current State | Key Issues |
|--------|---------------|-------------|
| LayeredConcurrency | 407 lines | Lemmas.lean stub (6 lines) |
| ConcurrencyProcessAlgebra | 1,605 lines | Spec.lean very large (1,076 lines) |
| SchedulingModes | 1,452 lines | Lemmas.lean large (744 lines) |
| SchedulerRandomizedStealing | 1,683 lines | Spec.lean stub (8 lines) |

**Dependencies:** REQ-001, REQ-002

---

### 4. Security Domain

**Requirement:** [REQ-004](REQ-004-security-domain.md) - Security Domain Requirements  
**Priority:** High  
**Modules:** 3

| Module | Current State | Key Issues |
|--------|---------------|-------------|
| SecurityFlow | 1,570 lines | Moderate coverage |
| SecurityOCap | 1,132 lines | Moderate coverage |
| LicenseDeonticLogic | 1,044 lines | Moderate coverage |

**Dependencies:** REQ-001, REQ-002

---

### 5. Build System Domain

**Requirement:** [REQ-005](REQ-005-build-system-domain.md) - Build System Domain Requirements  
**Priority:** Medium  
**Modules:** 4

| Module | Current State | Key Issues |
|--------|---------------|-------------|
| BuildLattice | 356 lines | Lemmas.lean very small (13 lines), Examples.lean very small (10 lines) |
| DependencySat | 97 lines | Spec.lean stub (9 lines), Examples.lean very small (10 lines) |
| ModuleSystem | 1,137 lines | Moderate coverage |
| ModuleExistential | 1,241 lines | Moderate coverage |

**Dependencies:** REQ-001

---

### 6. ABI Domain

**Requirement:** [REQ-006](REQ-006-abi-domain.md) - ABI Domain Requirements  
**Priority:** Medium  
**Modules:** 2

| Module | Current State | Key Issues |
|--------|---------------|-------------|
| AbiAlignmentAlgebra | 865 lines | Moderate coverage |
| AbiDataRefinement | 224 lines | Lemmas.lean EMPTY (0 lines) - CRITICAL |

**Dependencies:** REQ-001, REQ-002

---

### 7. Language Features Domain

**Requirement:** [REQ-007](REQ-007-language-features-domain.md) - Language Features Domain Requirements  
**Priority:** Medium  
**Modules:** 21

| Module | Current State | Key Issues |
|--------|---------------|-------------|
| ASTGraph | 881 lines | Moderate coverage |
| BackendTiling | 133 lines | Examples.lean very small (10 lines) |
| DialectProjection | 1,266 lines | Large coverage |
| DualOptimization | 1,574 lines | Large coverage |
| ExecutionModel | 1,948 lines | Large coverage |
| Financial | 981 lines | Moderate coverage |
| InfrastructureSafetyContracts | 1,542 lines | Large coverage |
| LexicalStructureSyntax | 1,219 lines | Large coverage |
| Licensing | 784 lines | Moderate coverage |
| LinkerLogic | 523 lines | Moderate coverage |
| Maths | 750 lines | Moderate coverage |
| MonadicEffect | 1,376 lines | Large coverage |
| OperatorNullCoalescing | 671 lines | Moderate coverage |
| README | 38 lines | Lemmas.lean stub (8 lines), Examples.lean stub (8 lines) |
| RegistryConsensus | 640 lines | Spec.lean stub (8 lines) |
| ScopingLambdaCalculus | 913 lines | Lemmas.lean small (65 lines) |
| StorageDAWG | 1,613 lines | Large coverage |
| StrictStateUnidirectional | 147 lines | Small coverage |
| SyntaxTranslation | 261 lines | Small coverage |
| TerminologyStandardization | 304 lines | Lemmas.lean stub (6 lines), Examples.lean stub (6 lines) |
| TypeSystem | 1,799 lines | Largest module - critical |
| UnidirectionalDataFlow | 100 lines | Spec.lean stub (9 lines) |
| UnitGroupTheory | 759 lines | Moderate coverage |
| VersionCompatibility | 810 lines | Moderate coverage |

**Dependencies:** REQ-001, REQ-002, REQ-003, REQ-004, REQ-005, REQ-006

---

## Critical Issues Summary

### Empty Files (0 lines)

| Module | File | Domain | Priority |
|--------|------|--------|----------|
| AbiDataRefinement | Lemmas.lean | ABI | Critical |

This is the most critical empty file issue in the entire codebase and must be addressed immediately.

### Stub Files (< 10 lines)

| Module | File | Domain | Priority |
|--------|------|--------|----------|
| GLOSSARY | Spec.lean | Core Foundation | Critical |
| GLOSSARY | Lemmas.lean | Core Foundation | Critical |
| GLOSSARY | Examples.lean | Core Foundation | Critical |
| LayeredConcurrency | Lemmas.lean | Concurrency | High |
| SchedulerRandomizedStealing | Spec.lean | Concurrency | High |
| DependencySat | Spec.lean | Build System | Medium |
| README | Lemmas.lean | Language Features | Medium |
| README | Examples.lean | Language Features | Medium |
| RegistryConsensus | Spec.lean | Language Features | Medium |
| TerminologyStandardization | Lemmas.lean | Language Features | Medium |
| TerminologyStandardization | Examples.lean | Language Features | Medium |
| UnidirectionalDataFlow | Spec.lean | Language Features | Medium |

**Total Stub Files:** 12

### Very Small Lemmas.lean Files (< 100 lines)

| Module | Lines | Domain | Priority |
|--------|-------|--------|----------|
| MemoryModel | 81 | Memory | High |
| MemoryAcyclicity | 64 | Memory | High |
| MemoryAffineLogic | 62 | Memory | High |
| BuildLattice | 13 | Build System | Medium |
| ScopingLambdaCalculus | 65 | Language Features | Medium |
| UnidirectionalDataFlow | 34 | Language Features | Medium |

### Very Small Examples.lean Files (< 100 lines)

| Module | Lines | Domain | Priority |
|--------|-------|--------|----------|
| MemoryModel | 58 | Memory | High |
| MemoryAcyclicity | 58 | Memory | High |
| MemoryAffineLogic | 55 | Memory | High |
| BuildLattice | 10 | Build System | Medium |
| DependencySat | 10 | Build System | Medium |
| BackendTiling | 10 | Language Features | Medium |
| README | 8 | Language Features | Medium |
| TerminologyStandardization | 6 | Language Features | Medium |

---

## Implementation Order

Based on dependencies and priorities, the recommended implementation order is:

1. **Phase 1: Core Foundation** (REQ-001) - Must be completed first
2. **Phase 2: Memory Domain** (REQ-002) - Depends on Core Foundation
3. **Phase 3: Concurrency Domain** (REQ-003) - Depends on Core Foundation and Memory
4. **Phase 4: Security Domain** (REQ-004) - Depends on Core Foundation and Memory
5. **Phase 5: Build System Domain** (REQ-005) - Depends on Core Foundation
6. **Phase 6: ABI Domain** (REQ-006) - Depends on Core Foundation and Memory
7. **Phase 7: Language Features Domain** (REQ-007) - Depends on all previous phases

---

## Verification Criteria

All requirements must meet the following criteria:

1. **Compilation:** All modules compile successfully with `lake build`
2. **Proof Completeness:** No `sorry` or `admit` placeholders in any lemma
3. **Example Execution:** All examples in Examples.lean files are executable
4. **Documentation:** 100% docstring coverage for all public definitions
5. **Code Quality:** Zero commented-out code blocks, zero TODO markers
6. **Stub Elimination:** All stub files expanded to full implementations
7. **Empty File Elimination:** All empty files populated with content

---

## Related Documentation

- [Current State Manifest](../00_current_state/manifest.md) - Detailed analysis of current module state
- [Future State Manifest](../manifest.md) - Target specifications for all modules
- [Architecture Documentation](../../docs/architecture/) - System architecture details
- [Coding Standards](../01_standards/coding_standards.md) - Development guidelines

---

## Change Log

| Date | Version | Changes |
|------|---------|---------|
| 2026-01-30 | 1.0 | Initial requirements index created |
