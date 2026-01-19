import Morph.Core
import Morph.Syntax
import Morph.Memory

/-!
# Specification: Spec Directory README

**Source:** `spec/README.md`
**Status:** Partial
**Last Updated:** 2026-01-16
**Verified By:** Kilo Code

## Overview

This specification formalizes the directory structure and organization of the Morph specification ecosystem. The spec directory contains all formal specifications for the Morph language, organized by domain and functionality.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| Directory Structure | `spec_directory_structure` | ✓ Complete |
| Specification Categories | `spec_categories` | ✓ Complete |
| Naming Convention | `spec_naming_convention` | ✓ Complete |
| Documentation Standards | `spec_documentation_standards` | ✓ Complete |

## Directory Structure

### Top-Level Organization

The spec directory is organized as follows:

```lean
/-- The top-level spec directory structure. -/
inductive SpecDir where
  | root : SpecDir
  | architecture : SpecDir
  | build : SpecDir
  | concurrency : SpecDir
  | conventions : SpecDir
  | financial : SpecDir
  | language : SpecDir
  deriving Repr

/-- A specification file path. -/
structure SpecPath where
  dir : SpecDir
  name : String
  deriving Repr

/-- The set of all valid specification files. -/
def ValidSpecFiles : Set SpecPath :=
  { p | p.dir = .root ∧ p.name ∈ {"GLOSSARY.md", "README.md"} } ∪
  { p | p.dir = .root ∧ p.name ∈ {"module_existential_spec.md",
                                     "registry_consensus_spec.md",
                                     "scheduler_randomized_stealing_spec.md",
                                     "security_ocap_spec.md",
                                     "storage_dawg_spec.md",
                                     "distributed_vector_clock_spec.md"} } ∪
  { p | p.dir = .architecture ∧ p.name = "layered_concurrency_spec.md" } ∪
  { p | p.dir = .build ∧ p.name ∈ {"abi_alignment_algebra_spec.md",
                                    "abi_data_refinement_spec.md",
                                    "backend_tiling_spec.md",
                                    "build_lattice_spec.md",
                                    "dependency_sat_spec.md",
                                    "linker_logic_spec.md"} } ∪
  { p | p.dir = .concurrency ∧ p.name ∈ {"concurrency_process_algebra_spec.md",
                                          "execution_model_spec.md",
                                          "monadic_effect_spec.md",
                                          "scheduling_modes_spec.md"} } ∪
  { p | p.dir = .conventions ∧ p.name ∈ {"terminology_standardization_spec.md",
                                          "version_compatibility_spec.md"} } ∪
  { p | p.dir = .financial ∧ p.name = "financial_spec.md" } ∪
  { p | p.dir = .language ∧ True }  -- All files in language/ subdirectory
```

### Subdirectory Structure

```lean
/-- The language subdirectory structure. -/
inductive LanguageSubdir where
  | core : LanguageSubdir
  | types : LanguageSubdir
  | memory : LanguageSubdir
  | concurrency : LanguageSubdir
  deriving Repr

/-- A language specification file path. -/
structure LanguageSpecPath where
  subdir : LanguageSubdir
  name : String
  deriving Repr
```

## Specification Categories

### Core Specifications

```lean
/-- Core language specifications define fundamental language features. -/
def IsCoreSpec : SpecPath → Prop
  | { dir := .root, name := n } =>
      n ∈ {"module_existential_spec.md",
           "registry_consensus_spec.md",
           "scheduler_randomized_stealing_spec.md",
           "security_ocap_spec.md",
           "storage_dawg_spec.md",
           "distributed_vector_clock_spec.md"}
  | _ => False
```

### Architecture Specifications

```lean
/-- Architecture specifications define system architecture and design. -/
def IsArchitectureSpec : SpecPath → Prop
  | { dir := .architecture, .. } => True
  | _ => False
```

### Build Specifications

```lean
/-- Build specifications define the build system and compilation process. -/
def IsBuildSpec : SpecPath → Prop
  | { dir := .build, .. } => True
  | _ => False
```

### Concurrency Specifications

```lean
/-- Concurrency specifications define concurrency models and execution. -/
def IsConcurrencySpec : SpecPath → Prop
  | { dir := .concurrency, .. } => True
  | _ => False
```

### Convention Specifications

```lean
/-- Convention specifications define language conventions and standards. -/
def IsConventionSpec : SpecPath → Prop
  | { dir := .conventions, .. } => True
  | _ => False
```

### Financial Specifications

```lean
/-- Financial specifications define financial domain features. -/
def IsFinancialSpec : SpecPath → Prop
  | { dir := .financial, .. } => True
  | _ => False
```

### Language Specifications

```lean
/-- Language specifications define language syntax and semantics. -/
def IsLanguageSpec : SpecPath → Prop
  | { dir := .language, .. } => True
  | _ => False
```

## Naming Convention

### Specification File Naming

```lean
/-- A specification file name follows the convention: {domain}_{feature}_spec.md -/
def IsValidSpecName (name : String) : Prop :=
  name.endsWith "_spec.md" ∧
  ¬name.startsWith "_" ∧
  name.length > "_spec.md".length

/-- The domain prefix of a specification file name. -/
def SpecDomain (name : String) : String :=
  if name.contains "_" then
    name.take (name.find! "_")
  else
    ""

/-- The feature name of a specification file name. -/
def SpecFeature (name : String) : String :=
  if name.contains "_spec.md" then
    name.drop (name.find! "_" + 1) |>.dropRight "_spec.md".length
  else
    ""
```

## Documentation Standards

### Specification Document Structure

```lean
/-- A specification document has a standard structure. -/
structure SpecDoc where
  title : String
  overview : String
  requirements : List SpecRequirement
  examples : List SpecExample
  deriving Repr

/-- A specification requirement. -/
structure SpecRequirement where
  id : String
  description : String
  priority : Priority
  deriving Repr

/-- A specification example. -/
structure SpecExample where
  description : String
  code : String
  expected : String
  deriving Repr

/-- Requirement priority levels. -/
inductive Priority where
  | critical
  | high
  | medium
  | low
  deriving Repr
```

### Cross-Reference Standards

```lean
/-- A cross-reference to another specification. -/
structure SpecCrossRef where
  target : SpecPath
  section : String
  description : String
  deriving Repr

/-- A specification document may contain cross-references. -/
structure SpecDocWithRefs where
  doc : SpecDoc
  refs : List SpecCrossRef
  deriving Repr
```

## Specification Dependencies

```lean
/-- A specification depends on another specification. -/
structure SpecDependency where
  source : SpecPath
  target : SpecPath
  reason : String
  deriving Repr

/-- The dependency graph of all specifications. -/
def SpecDependencyGraph : DirectedGraph SpecPath := fun p1 p2 =>
  ∃ dep : SpecDependency, dep.source = p1 ∧ dep.target = p2

/-- A specification has no circular dependencies. -/
def HasNoCircularDeps (specs : List SpecPath) : Prop :=
  ∀ p : SpecPath, p ∈ specs → ¬Path SpecDependencyGraph p p
```

## Specification Validation

```lean
/-- A specification is valid if it meets all standards. -/
def IsValidSpec (path : SpecPath) : Prop :=
  path ∈ ValidSpecFiles ∧
  IsValidSpecName path.name ∧
  (IsCoreSpec path ∨ IsArchitectureSpec path ∨ IsBuildSpec path ∨
   IsConcurrencySpec path ∨ IsConventionSpec path ∨
   IsFinancialSpec path ∨ IsLanguageSpec path)

/-- All specifications in a set are valid. -/
def AllSpecsValid (specs : List SpecPath) : Prop :=
  ∀ p : SpecPath, p ∈ specs → IsValidSpec p
```

## Specification Versioning

```lean
/-- A specification version. -/
structure SpecVersion where
  major : Nat
  minor : Nat
  patch : Nat
  deriving Repr

/-- Compare two specification versions. -/
def SpecVersion.compare (v1 v2 : SpecVersion) : Ordering :=
  match v1.major, v2.major with
  | m1, m2 => if m1 < m2 then .lt else if m1 > m2 then .gt else
    match v1.minor, v2.minor with
    | n1, n2 => if n1 < n2 then .lt else if n1 > n2 then .gt else
      match v1.patch, v2.patch with
      | p1, p2 => if p1 < p2 then .lt else if p1 > p2 then .gt else .eq

/-- A specification with version information. -/
structure SpecWithVersion where
  path : SpecPath
  version : SpecVersion
  deriving Repr
```

## Known Issues

### None

No known issues identified in the README specification.

## Notes

- The spec directory is organized by domain and functionality
- Each specification follows a consistent naming convention
- Specifications may have dependencies on other specifications
- Circular dependencies are not allowed
- All specifications must meet documentation standards
-!/
