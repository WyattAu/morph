# Morph Spec Module Status

> Auto-generated. Last updated: 2026-05-11

## Summary

| Metric | Count |
|--------|-------|
| Total modules | 43 |
| Total real lemmas | 83 |
| Total real examples | 73 |
| Modules with lemmas stub | 17 |
| Modules with examples stub | 19 |
| Total sorries | 0 |

### Modules per Tier

| Tier | Description | Count |
|------|-------------|-------|
| **1** | Real lemmas or core module | 8 |
| **2** | Real Spec.lean (>50 lines), stub lemmas | 19 |
| **3** | Minimal Spec.lean, stub lemmas | 0 |
| **4** | Empty (no Spec.lean content) | 16 |

## Module Status Table

| Module | Spec Lines | Real Lemmas | Real Examples | Lemmas Stub | Examples Stub | Sorries | Tier |
|--------|-----------|-------------|---------------|-------------|---------------|---------|------|
| AbiAlignmentAlgebra | 147 | 0 | 0 | Yes | Yes | 0 | 2 |
| AbiDataRefinement | 111 | 0 | 0 | Yes | Yes | 0 | 2 |
| ArcAffineIntegration | 124 | 0 | 0 | Yes | Yes | 0 | 2 |
| ASTGraph | 147 | 0 | 0 | Yes | Yes | 0 | 2 |
| BackendTiling | 188 | 0 | 0 | No | No | 0 | 2 |
| BuildLattice | 175 | 0 | 0 | No | No | 0 | 2 |
| **ConcurrencyProcessAlgebra** | 201 | 31 | 36 | No | Yes | 0 | **1** |
| DependencySat | 108 | 0 | 0 | No | No | 0 | 2 |
| DialectProjection | 0 | 0 | 0 | No | No | 0 | 4 |
| DualOptimization | 0 | 0 | 0 | No | No | 0 | 4 |
| ExecutionModel | 0 | 0 | 0 | No | No | 0 | 4 |
| Financial | 0 | 0 | 0 | No | No | 0 | 4 |
| **GLOSSARY** | 289 | 0 | 0 | Yes | Yes | 0 | **1** |
| InfrastructureSafetyContracts | 0 | 0 | 0 | No | No | 0 | 4 |
| LayeredConcurrency | 152 | 0 | 0 | Yes | Yes | 0 | 2 |
| LexicalStructureSyntax | 0 | 0 | 0 | No | No | 0 | 4 |
| LicenseDeonticLogic | 160 | 0 | 0 | Yes | Yes | 0 | 2 |
| Licensing | 0 | 0 | 0 | No | No | 0 | 4 |
| LinkerLogic | 0 | 0 | 0 | No | No | 0 | 4 |
| Maths | 0 | 0 | 0 | No | No | 0 | 4 |
| MemoryAcyclicity | 110 | 0 | 0 | Yes | Yes | 0 | 2 |
| MemoryAffineLogic | 126 | 0 | 0 | Yes | Yes | 0 | 2 |
| **MemoryModel** | 142 | 7 | 5 | No | No | 0 | **1** |
| ModuleExistential | 170 | 0 | 0 | Yes | Yes | 0 | 2 |
| **ModuleSystem** | 210 | 0 | 0 | Yes | Yes | 0 | **1** |
| MonadicEffect | 0 | 0 | 0 | No | No | 0 | 4 |
| **MorphLanguage** | 183 | 19 | 32 | No | No | 0 | **1** |
| OperatorNullCoalescing | 0 | 0 | 0 | No | No | 0 | 4 |
| README | 0 | 0 | 0 | No | No | 0 | 4 |
| RegistryConsensus | 0 | 0 | 0 | No | No | 0 | 4 |
| SchedulerRandomizedStealing | 99 | 0 | 0 | Yes | Yes | 0 | 2 |
| SchedulingModes | 81 | 0 | 0 | Yes | Yes | 0 | 2 |
| ScopingLambdaCalculus | 0 | 0 | 0 | No | No | 0 | 4 |
| **SecurityFlow** | 146 | 14 | 0 | No | Yes | 0 | **1** |
| SecurityOCap | 156 | 0 | 0 | Yes | Yes | 0 | 2 |
| StorageDAWG | 0 | 0 | 0 | No | No | 0 | 4 |
| StrictStateUnidirectional | 0 | 0 | 0 | No | No | 0 | 4 |
| SyntaxTranslation | 100 | 0 | 0 | Yes | Yes | 0 | 2 |
| TerminologyStandardization | 129 | 0 | 0 | No | No | 0 | 2 |
| **TypeSystem** | 174 | 11 | 0 | No | No | 0 | **1** |
| **UnidirectionalDataFlow** | 16 | 1 | 0 | No | No | 0 | **1** |
| UnitGroupTheory | 165 | 0 | 0 | Yes | Yes | 0 | 2 |
| VersionCompatibility | 177 | 0 | 0 | Yes | Yes | 0 | 2 |

## Tier Definitions

- **Tier 1**: Has real lemmas (`theorem`/`lemma` declarations with no `example : True := trivial` stub) or is a designated core module (MemoryModel, SecurityFlow, MorphLanguage, TypeSystem, ConcurrencyProcessAlgebra, ModuleSystem, GLOSSARY)
- **Tier 2**: Has real Spec.lean content (>50 lines) but no real lemmas
- **Tier 3**: Minimal Spec.lean content with stub lemmas
- **Tier 4**: Empty (no Spec.lean content)
