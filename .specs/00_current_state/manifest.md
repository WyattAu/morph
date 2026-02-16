# Morph Project - Current State Manifest

**Generated:** 2026-01-31T21:01:57Z  
**Phase:** Phase 1 - Archaeology  
**Purpose:** Map current codebase structure, errors, and dependencies

---

## 1. File Structure

### 1.1 Root Level `.lean` Files

| File | Purpose |
|-------|----------|
| [`Morph.lean`](Morph.lean) | Main entry point |
| [`lakefile.lean`](lakefile.lean) | Lake build configuration |

### 1.2 Core Morph Library Files

| File | Purpose |
|-------|----------|
| [`Morph/Core.lean`](Morph/Core.lean) | Core definitions and types |
| [`Morph/Executable.lean`](Morph/Executable.lean) | Executable definitions |
| [`Morph/HIR.lean`](Morph/HIR.lean) | High-level Intermediate Representation |
| [`Morph/Memory.lean`](Morph/Memory.lean) | Memory model definitions |
| [`Morph/MIR.lean`](Morph/MIR.lean) | Mid-level Intermediate Representation |
| [`Morph/Semantics.lean`](Morph/Semantics.lean) | Semantic definitions |
| [`Morph/Syntax.lean`](Morph/Syntax.lean) | Syntax definitions |

### 1.3 Specs Library Files

#### Common Types
- [`Morph/Specs/CommonTypes.lean`](Morph/Specs/CommonTypes.lean)
- [`Morph/Specs/GLOSSARY.lean`](Morph/Specs/GLOSSARY.lean)

#### ABI and Build Specifications
| Directory | Files |
|-----------|-------|
| [`Morph/Specs/AbiAlignmentAlgebra/`](Morph/Specs/AbiAlignmentAlgebra/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/AbiDataRefinement/`](Morph/Specs/AbiDataRefinement/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/BackendTiling/`](Morph/Specs/BackendTiling/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/BuildLattice/`](Morph/Specs/BuildLattice/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/DependencySat/`](Morph/Specs/DependencySat/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/LinkerLogic/`](Morph/Specs/LinkerLogic/) | Spec.lean, Lemmas.lean, Examples.lean |

#### Concurrency Specifications
| Directory | Files |
|-----------|-------|
| [`Morph/Specs/ConcurrencyProcessAlgebra/`](Morph/Specs/ConcurrencyProcessAlgebra/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/ExecutionModel/`](Morph/Specs/ExecutionModel/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/LayeredConcurrency/`](Morph/Specs/LayeredConcurrency/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/MonadicEffect/`](Morph/Specs/MonadicEffect/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/SchedulingModes/`](Morph/Specs/SchedulingModes/) | Spec.lean, Lemmas.lean, Examples.lean |

#### Language Specifications
| Directory | Files |
|-----------|-------|
| [`Morph/Specs/ASTGraph/`](Morph/Specs/ASTGraph/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/DialectProjection/`](Morph/Specs/DialectProjection/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/DualOptimization/`](Morph/Specs/DualOptimization/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/LexicalStructureSyntax/`](Morph/Specs/LexicalStructureSyntax/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/ModuleSystem/`](Morph/Specs/ModuleSystem/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/MorphLanguage/`](Morph/Specs/MorphLanguage/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/OperatorNullCoalescing/`](Morph/Specs/OperatorNullCoalescing/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/ScopingLambdaCalculus/`](Morph/Specs/ScopingLambdaCalculus/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/StrictStateUnidirectional/`](Morph/Specs/StrictStateUnidirectional/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/SyntaxTranslation/`](Morph/Specs/SyntaxTranslation/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/TypeSystem/`](Morph/Specs/TypeSystem/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/UnidirectionalDataFlow/`](Morph/Specs/UnidirectionalDataFlow/) | Spec.lean, Lemmas.lean, Examples.lean |

#### Memory Specifications
| Directory | Files |
|-----------|-------|
| [`Morph/Specs/ArcAffineIntegration/`](Morph/Specs/ArcAffineIntegration/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/MemoryAcyclicity/`](Morph/Specs/MemoryAcyclicity/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/MemoryAffineLogic/`](Morph/Specs/MemoryAffineLogic/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/MemoryModel/`](Morph/Specs/MemoryModel/) | Spec.lean, Lemmas.lean, Examples.lean |

#### Security and Licensing Specifications
| Directory | Files |
|-----------|-------|
| [`Morph/Specs/InfrastructureSafetyContracts/`](Morph/Specs/InfrastructureSafetyContracts/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/LicenseDeonticLogic/`](Morph/Specs/LicenseDeonticLogic/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/Licensing/`](Morph/Specs/Licensing/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/SecurityFlow/`](Morph/Specs/SecurityFlow/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/SecurityOCap/`](Morph/Specs/SecurityOCap/) | Spec.lean, Lemmas.lean, Examples.lean |

#### Tooling and Other Specifications
| Directory | Files |
|-----------|-------|
| [`Morph/Specs/Financial/`](Morph/Specs/Financial/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/GLOSSARY/`](Morph/Specs/GLOSSARY/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/Maths/`](Morph/Specs/Maths/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/ModuleExistential/`](Morph/Specs/ModuleExistential/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/README/`](Morph/Specs/README/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/RegistryConsensus/`](Morph/Specs/RegistryConsensus/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/SchedulerRandomizedStealing/`](Morph/Specs/SchedulerRandomizedStealing/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/StorageDAWG/`](Morph/Specs/StorageDAWG/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/TerminologyStandardization/`](Morph/Specs/TerminologyStandardization/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/UnitGroupTheory/`](Morph/Specs/UnitGroupTheory/) | Spec.lean, Lemmas.lean, Examples.lean |
| [`Morph/Specs/VersionCompatibility/`](Morph/Specs/VersionCompatibility/) | Spec.lean, Lemmas.lean, Examples.lean |

### 1.4 Test Files

| File | Purpose |
|-------|----------|
| [`Morph/Tests/AST.lean`](Morph/Tests/AST.lean) | AST tests |
| [`Morph/Tests/Core.lean`](Morph/Tests/Core.lean) | Core tests |
| [`Morph/Tests/Executable.lean`](Morph/Tests/Executable.lean) | Executable tests |
| [`Morph/Tests/Memory.lean`](Morph/Tests/Memory.lean) | Memory tests |
| [`Morph/Tests/Semantics.lean`](Morph/Tests/Semantics.lean) | Semantics tests |
| [`Morph/Tests/Typing.lean`](Morph/Tests/Typing.lean) | Typing tests |

### 1.5 Directory Organization

```
morph/
├── Morph.lean                          # Main entry point
├── lakefile.lean                       # Lake build config
├── Morph/
│   ├── Core.lean                        # Core definitions
│   ├── Executable.lean                  # Executable definitions
│   ├── HIR.lean                         # High-level IR
│   ├── Memory.lean                      # Memory model
│   ├── MIR.lean                         # Mid-level IR
│   ├── Semantics.lean                   # Semantics
│   ├── Syntax.lean                      # Syntax
│   ├── Specs/                           # Specifications directory
│   │   ├── CommonTypes.lean
│   │   ├── GLOSSARY.lean
│   │   └── [40+ specification subdirectories]/
│   │       ├── Spec.lean
│   │       ├── Lemmas.lean
│   │       └── Examples.lean
│   └── Tests/                           # Test files
│       ├── AST.lean
│       ├── Core.lean
│       ├── Executable.lean
│       ├── Memory.lean
│       ├── Semantics.lean
│       └── Typing.lean
```

### 1.6 Module Hierarchy

```
Morph (root library)
├── Morph.Core
├── Morph.Executable
├── Morph.HIR
├── Morph.Memory
├── Morph.MIR
├── Morph.Semantics
├── Morph.Syntax
├── Morph.Specs.*
│   ├── Morph.Specs.CommonTypes
│   ├── Morph.Specs.GLOSSARY
│   ├── Morph.Specs.Abis.*
│   ├── Morph.Specs.Build.*
│   ├── Morph.Specs.Concurrency.*
│   ├── Morph.Specs.Language.*
│   ├── Morph.Specs.Memory.*
│   ├── Morph.Specs.Security.*
│   └── Morph.Specs.Tooling.*
└── Morph.Tests.*
```

---

## 2. Error Analysis

### 2.1 Error Summary

| Error Type | Count | Root Cause |
|------------|-------|-------------|
| Dependency Configuration | 1 | ProofWidgets package incompatibility |
| Syntax Error | 1 | Unterminated comment |

### 2.2 Error Details

#### 2.2.1 Dependency Configuration Error (BLOCKING)

**Affected Files (7 total):**
- [`Morph/Executable.lean`](Morph/Executable.lean)
- [`Morph/Specs/AbiAlignmentAlgebra/Lemmas.lean`](Morph/Specs/AbiAlignmentAlgebra/Lemmas.lean)
- [`Morph/Specs/AbiDataRefinement/Examples.lean`](Morph/Specs/AbiDataRefinement/Examples.lean)
- [`Morph/Specs/AbiDataRefinement/Lemmas.lean`](Morph/Specs/AbiDataRefinement/Lemmas.lean)
- [`Morph/Specs/ConcurrencyProcessAlgebra/Examples.lean`](Morph/Specs/ConcurrencyProcessAlgebra/Examples.lean)
- [`Morph/Specs/ConcurrencyProcessAlgebra/Lemmas.lean`](Morph/Specs/ConcurrencyProcessAlgebra/Lemmas.lean)
- [`Morph/Specs/ConcurrencyProcessAlgebra/Spec.lean`](Morph/Specs/ConcurrencyProcessAlgebra/Spec.lean)

**Root Cause:** The ProofWidgets4 dependency package (version v0.0.84) has configuration errors in its lakefile.lean that are incompatible with Lean 4.28.0-rc1.

**Specific Errors in ProofWidgets:**
- Line 17: `BuildJob` type unknown - missing import or open statement
- Line 31: Application type mismatch - `Hash` vs `String` expected for `BuildTrace.mk`
- Line 45, 47: `BuildJob` type unknown
- Line 55: Cannot synthesize implicit argument `BuildJob`
- Line 65: `BuildJob` type unknown
- Line 77: Invalid field notation on `BuildJob`
- Line 83: Invalid field `afterReleaseAsync` - field does not exist in `Lake.Package`
- Lines 114, 117: Declarations use 'sorry' (incomplete proofs)

**Impact:** This is a blocking error that prevents the Lake workspace from configuring, which affects all files that depend on Lake setup.

#### 2.2.2 Syntax Error

**File:** [`Morph/Specs/ArcAffineIntegration/Examples.lean`](Morph/Specs/ArcAffineIntegration/Examples.lean:237)

**Error:** `unterminated comment`

**Line:** 237

**Impact:** Prevents parsing of this specific file.

### 2.3 Warnings (Non-Blocking)

#### 2.3.1 Mathlib Deprecation Warnings

**File:** `.lake/packages/mathlib/lakefile.lean`

| Line | Warning | Suggested Fix |
|------|----------|----------------|
| 104:13, 104:24 | `Lake.Package.name` deprecated | Use `baseName`, `keyName`, or `prettyName` instead |
| 121:53 | `String.trim` deprecated | Use `String.trimAscii` instead |
| 124:23 | `Lake.Package.name` deprecated | Use `baseName`, `keyName`, or `prettyName` instead |

**Note:** Type signature change: `String → String.Slice` instead of `String → String`

#### 2.3.2 ProofWidgets Warnings

**File:** `.lake/packages/proofwidgets/lakefile.lean`

| Line | Warning |
|------|----------|
| 114:7 | declaration uses 'sorry' |
| 117:7 | declaration uses 'sorry' |

---

## 3. Syntax Issues

### 3.1 Files with Syntax Issues

| File | Issue | Line |
|------|--------|------|
| [`Morph/Specs/ArcAffineIntegration/Examples.lean`](Morph/Specs/ArcAffineIntegration/Examples.lean:237) | Unterminated comment | 237 |

### 3.2 Deprecated Lean 4 Syntax

No deprecated syntax detected in the project's own files. The deprecation warnings are in external dependencies (mathlib).

### 3.3 Comment Syntax Issues

| File | Issue | Details |
|------|--------|---------|
| [`Morph/Specs/ArcAffineIntegration/Examples.lean`](Morph/Specs/ArcAffineIntegration/Examples.lean:237) | Unterminated comment | File ends without closing `-/` or `--` |

---

## 4. Dependencies

### 4.1 Lean Toolchain

| Property | Value |
|-----------|-------|
| Toolchain | `leanprover/lean4:v4.28.0-rc1` |
| File | [`lean-toolchain`](lean-toolchain) |

### 4.2 External Dependencies

#### 4.2.1 Direct Dependencies (from [`lakefile.toml`](lakefile.toml))

| Package | URL | Version | Purpose |
|---------|-----|---------|---------|
| batteries | https://github.com/leanprover-community/batteries | v4.10.0 | Standard library extensions |
| aesop | https://github.com/JLimperg/aesop | v4.10.0 | Automation for Lean proofs |
| mathlib | https://github.com/leanprover-community/mathlib4 | v4.10.0 | Mathematical library |

#### 4.2.2 All Dependencies (from [`lake-manifest.json`](lake-manifest.json))

| Package | URL | Version | Type | Scope |
|---------|-----|---------|------|-------|
| importGraph | https://github.com/leanprover-community/import-graph | 875ad9d88ed684e39c16bdea260e6ecfa15afd60 | git | direct |
| aesop | https://github.com/JLimperg/aesop | fb12f5535c80e40119286d9575c9393562252d21 | git | direct |
| batteries | https://github.com/leanprover-community/batteries | 1f22a4f44c1726b61fab3c2c75e0651f35c795dc | git | direct |
| mathlib4 | https://github.com/leanprover-community/mathlib4 | 32d24245c7a12ded17325299fd41d412022cd3fe | git | direct |
| Cli | https://github.com/leanprover/lean4-cli | 28e0856d4424863a85b18f38868c5420c55f9bae | git | inherited (leanprover) |
| plausible | https://github.com/leanprover-community/plausible | 8d3713f36dda48467eb61f8c1c4db89c49a6251a | git | inherited (leanprover-community) |
| LeanSearchClient | https://github.com/leanprover-community/LeanSearchClient | 19e5f5cc9c21199be466ef99489e3acab370f079 | git | inherited (leanprover-community) |
| **proofwidgets** | https://github.com/leanprover-community/ProofWidgets4 | **ef8377f31b5535430b6753a974d685b0019d0681** | git | inherited (leanprover-community) |
| Qq | https://github.com/leanprover-community/quote4 | 523ec6fc8062d2f470fdc8de6f822fe89552b5e6 | git | inherited (leanprover-community) |

### 4.3 Dependency Version Mismatch

**Critical Issue:** The project specifies dependency versions as `v4.10.0` in [`lakefile.toml`](lakefile.toml) but the Lean toolchain is `v4.28.0-rc1`. This significant version gap (18 minor versions) likely causes the ProofWidgets compatibility issues.

| Component | Version | Notes |
|-----------|---------|-------|
| Lean Toolchain | v4.28.0-rc1 | Very recent (release candidate) |
| Direct Dependencies | v4.10.0 | Significantly older |
| ProofWidgets | v0.0.84 | Not compatible with Lean 4.28 |

---

## 5. Build System

### 5.1 Lake Configuration

| Property | Value |
|-----------|-------|
| Package Name | morph |
| Package Version | 0.1.0 |
| Lake Manifest Version | 1.1.0 |
| Packages Directory | .lake/packages |

### 5.2 Lean Libraries

| Library | Glob Pattern |
|----------|--------------|
| Morph | `Morph.+` |
| Morph.Tests | `Morph.Tests.+` |

---

## 6. Summary Statistics

| Metric | Count |
|--------|--------|
| Total `.lean` files | ~160 |
| Root `.lean` files | 2 |
| Core library files | 7 |
| Spec directories | 40+ |
| Spec files per directory | 3 (Spec, Lemmas, Examples) |
| Test files | 6 |
| Direct dependencies | 3 |
| Total dependencies | 9 |
| Files with errors | 8 |
| Files with warnings | 1 (mathlib) |

---

## 7. Action Items

### 7.1 Critical (Blocking)

1. **Fix ProofWidgets dependency incompatibility**
   - Update ProofWidgets to a version compatible with Lean 4.28.0-rc1
   - Or downgrade Lean toolchain to match dependency versions (v4.10.0)

2. **Fix unterminated comment**
   - File: [`Morph/Specs/ArcAffineIntegration/Examples.lean`](Morph/Specs/ArcAffineIntegration/Examples.lean:237)
   - Add closing comment delimiter

### 7.2 High Priority

3. **Resolve dependency version mismatch**
   - Align dependency versions with Lean toolchain version
   - Update all dependencies to versions compatible with Lean 4.28.0-rc1

### 7.3 Medium Priority

4. **Address mathlib deprecation warnings**
   - Update mathlib to latest version
   - Replace deprecated API calls

---

## 8. Notes

- The project uses Lake as its build system
- The codebase follows a specification-driven approach with Spec/Lemmas/Examples structure
- The project is in early development (version 0.1.0)
- There is a significant version mismatch between the Lean toolchain and dependencies
- The ProofWidgets dependency is the primary blocking issue
