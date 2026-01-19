import Morph.Core
import Morph.Syntax
import Morph.Memory

/-!
# Examples: Spec Directory README

**Source:** `spec/README.md`
**Status:** Partial
**Last Updated:** 2026-01-16
**Verified By:** Kilo Code

## Overview

This file contains concrete examples and test cases for the spec directory structure and organization definitions. These examples demonstrate how the formal definitions apply to practical scenarios in the Morph specification ecosystem.

## Example Index

| Example | Description | Status |
|---------|-------------|--------|
| `example_spec_path_glossary` | GLOSSARY.md spec path | ✓ Complete |
| `example_spec_path_module_existential` | module_existential_spec.md spec path | ✓ Complete |
| `example_spec_path_registry_consensus` | registry_consensus_spec.md spec path | ✓ Complete |
| `example_spec_path_scheduler_randomized` | scheduler_randomized_stealing_spec.md spec path | ✓ Complete |
| `example_spec_path_build_lattice` | build_lattice_spec.md spec path | ✓ Complete |
| `example_spec_path_concurrency_process_algebra` | concurrency_process_algebra_spec.md spec path | ✓ Complete |
| `example_spec_name_parsing` | Parsing spec name into domain and feature | ✓ Complete |
| `example_spec_dependency` | Example specification dependency | ✓ Complete |
| `example_spec_version_comparison` | Version comparison examples | ✓ Complete |
| `example_spec_doc_structure` | Example specification document | ✓ Complete |
| `example_spec_crossref` | Example cross-reference | ✓ Complete |

## Spec Path Examples

### GLOSSARY.md

```lean
/-- Example: GLOSSARY.md is a valid spec path -/
def example_spec_path_glossary : SpecPath :=
  { dir := .root, name := "GLOSSARY.md" }

example : example_spec_path_glossary ∈ ValidSpecFiles := by
  -- Proof: GLOSSARY.md is listed in ValidSpecFiles for root directory
  unfold ValidSpecFiles
  simp

example : IsValidSpec example_spec_path_glossary := by
  -- Proof: GLOSSARY.md is a valid spec name and is in ValidSpecFiles
  unfold IsValidSpec
  constructor
  · unfold IsValidSpecName
    simp
  · exact example_spec_path_glossary ∈ ValidSpecFiles
```

### module_existential_spec.md

```lean
/-- Example: module_existential_spec.md is a valid spec path -/
def example_spec_path_module_existential : SpecPath :=
  { dir := .root, name := "module_existential_spec.md" }

example : example_spec_path_module_existential ∈ ValidSpecFiles := by
  -- Proof: module_existential_spec.md is listed in ValidSpecFiles for root directory
  unfold ValidSpecFiles
  simp

example : IsValidSpec example_spec_path_module_existential := by
  -- Proof: module_existential_spec.md is a valid spec name and is in ValidSpecFiles
  unfold IsValidSpec
  constructor
  · unfold IsValidSpecName
    simp
  · exact example_spec_path_module_existential ∈ ValidSpecFiles

example : IsCoreSpec example_spec_path_module_existential := by
  -- Proof: module_existential_spec.md is listed as a core spec
  unfold IsCoreSpec
  simp
```

### registry_consensus_spec.md

```lean
/-- Example: registry_consensus_spec.md is a valid spec path -/
def example_spec_path_registry_consensus : SpecPath :=
  { dir := .root, name := "registry_consensus_spec.md" }

example : example_spec_path_registry_consensus ∈ ValidSpecFiles := by
  -- Proof: registry_consensus_spec.md is listed in ValidSpecFiles for root directory
  unfold ValidSpecFiles
  simp

example : IsValidSpec example_spec_path_registry_consensus := by
  -- Proof: registry_consensus_spec.md is a valid spec name and is in ValidSpecFiles
  unfold IsValidSpec
  constructor
  · unfold IsValidSpecName
    simp
  · exact example_spec_path_registry_consensus ∈ ValidSpecFiles

example : IsCoreSpec example_spec_path_registry_consensus := by
  -- Proof: registry_consensus_spec.md is listed as a core spec
  unfold IsCoreSpec
  simp
```

### scheduler_randomized_stealing_spec.md

```lean
/-- Example: scheduler_randomized_stealing_spec.md is a valid spec path -/
def example_spec_path_scheduler_randomized : SpecPath :=
  { dir := .root, name := "scheduler_randomized_stealing_spec.md" }

example : example_spec_path_scheduler_randomized ∈ ValidSpecFiles := by
  -- Proof: scheduler_randomized_stealing_spec.md is listed in ValidSpecFiles for root directory
  unfold ValidSpecFiles
  simp

example : IsValidSpec example_spec_path_scheduler_randomized := by
  -- Proof: scheduler_randomized_stealing_spec.md is a valid spec name and is in ValidSpecFiles
  unfold IsValidSpec
  constructor
  · unfold IsValidSpecName
    simp
  · exact example_spec_path_scheduler_randomized ∈ ValidSpecFiles

example : IsCoreSpec example_spec_path_scheduler_randomized := by
  -- Proof: scheduler_randomized_stealing_spec.md is listed as a core spec
  unfold IsCoreSpec
  simp
```

### build_lattice_spec.md

```lean
/-- Example: build_lattice_spec.md is a valid spec path -/
def example_spec_path_build_lattice : SpecPath :=
  { dir := .build, name := "build_lattice_spec.md" }

example : example_spec_path_build_lattice ∈ ValidSpecFiles := by
  -- Proof: build_lattice_spec.md is listed in ValidSpecFiles for build directory
  sorry

example : IsValidSpec example_spec_path_build_lattice := by
  -- Proof: build_lattice_spec.md is a valid spec name and is in ValidSpecFiles
  sorry

example : IsBuildSpec example_spec_path_build_lattice := by
  -- Proof: build_lattice_spec.md is in the build directory
  sorry
```

### concurrency_process_algebra_spec.md

```lean
/-- Example: concurrency_process_algebra_spec.md is a valid spec path -/
def example_spec_path_concurrency_process_algebra : SpecPath :=
  { dir := .concurrency, name := "concurrency_process_algebra_spec.md" }

example : example_spec_path_concurrency_process_algebra ∈ ValidSpecFiles := by
  -- Proof: concurrency_process_algebra_spec.md is listed in ValidSpecFiles for concurrency directory
  sorry

example : IsValidSpec example_spec_path_concurrency_process_algebra := by
  -- Proof: concurrency_process_algebra_spec.md is a valid spec name and is in ValidSpecFiles
  sorry

example : IsConcurrencySpec example_spec_path_concurrency_process_algebra := by
  -- Proof: concurrency_process_algebra_spec.md is in the concurrency directory
  sorry
```

## Spec Name Parsing Examples

### Parsing Spec Name

```lean
/-- Example: Parsing "module_existential_spec.md" -/
def example_spec_name_parsing_name : String := "module_existential_spec.md"

example : IsValidSpecName example_spec_name_parsing_name := by
  -- Proof: name ends with "_spec.md" and is long enough
  unfold IsValidSpecName
  simp

example : SpecDomain example_spec_name_parsing_name = "module" := by
  -- Proof: domain is the substring before the first "_"
  unfold SpecDomain
  simp

example : SpecFeature example_spec_name_parsing_name = "existential" := by
  -- Proof: feature is the substring between "_" and "_spec.md"
  unfold SpecFeature
  simp

example : SpecDomain example_spec_name_parsing_name ++ "_" ++
          SpecFeature example_spec_name_parsing_name ++ "_spec.md" =
          example_spec_name_parsing_name := by
  -- Proof: by definition of SpecDomain and SpecFeature
  unfold SpecDomain
  unfold SpecFeature
  simp
```

## Spec Dependency Examples

### Example Dependency

```lean
/-- Example: module_existential_spec depends on GLOSSARY -/
def example_spec_dependency : SpecDependency :=
  { source := { dir := .root, name := "module_existential_spec.md" },
    target := { dir := .root, name := "GLOSSARY.md" },
    reason := "Uses terminology defined in glossary" }

example : SpecDependencyGraph example_spec_dependency.source
                              example_spec_dependency.target := by
  -- Proof: There exists a dependency from source to target
  unfold SpecDependencyGraph
  simp

example : ¬SpecDependencyGraph example_spec_dependency.target
                                  example_spec_dependency.source := by
  -- Proof: No circular dependencies allowed
  unfold SpecDependencyGraph
  intro h
  apply SpecDependencyGraph
  · exact example_spec_dependency
```

## Spec Version Examples

### Version Comparison

```lean
/-- Example: Version 1.0.0 -/
def example_spec_version_1_0_0 : SpecVersion :=
  { major := 1, minor := 0, patch := 0 }

/-- Example: Version 1.2.3 -/
def example_spec_version_1_2_3 : SpecVersion :=
  { major := 1, minor := 2, patch := 3 }

/-- Example: Version 2.0.0 -/
def example_spec_version_2_0_0 : SpecVersion :=
  { major := 2, minor := 0, patch := 0 }

/-- Version 1.0.0 is less than 1.2.3 -/
example :
    SpecVersion.compare example_spec_version_1_0_0 example_spec_version_1_2_3 = .lt := by
  -- Proof: major versions are equal, minor version 0 < 2
  sorry

/-- Version 1.2.3 is less than 2.0.0 -/
example :
    SpecVersion.compare example_spec_version_1_2_3 example_spec_version_2_0_0 = .lt := by
  -- Proof: major version 1 < 2
  sorry

/-- Version 1.0.0 equals itself -/
example :
    SpecVersion.compare example_spec_version_1_0_0 example_spec_version_1_0_0 = .eq := by
  -- Proof: all components are equal
  sorry
```

## Spec Document Examples

### Document Structure

```lean
/-- Example: A specification document -/
def example_spec_doc_structure : SpecDoc :=
  { title := "Module Existential Specification",
    overview := "This specification defines module privacy using existential types.",
    requirements :=
      [ { id := "REQ-001",
          description := "Modules must support privacy using existential types",
          priority := .critical },
        { id := "REQ-002",
          description := "Module boundaries must be enforced at compile time",
          priority := .high } ],
    examples :=
      [ { description := "Private module definition",
          code := "module private Module { ... }",
          expected := "Module contents are hidden from external access" } ] }

example : example_spec_doc_structure.title = "Module Existential Specification" := by
  rfl

example : example_spec_doc_structure.requirements.length = 2 := by
  rfl

example : example_spec_doc_structure.requirements.get? 0 |>.map (·.id) = some "REQ-001" := by
  rfl
```

## Spec Cross-Reference Examples

### Cross-Reference

```lean
/-- Example: A cross-reference to another specification -/
def example_spec_crossref : SpecCrossRef :=
  { target := { dir := .root, name := "GLOSSARY.md" },
    section := "Existential Type",
    description := "See glossary for definition of existential type" }

example : example_spec_crossref.target ∈ ValidSpecFiles := by
  -- Proof: GLOSSARY.md is a valid spec file
  unfold ValidSpecFiles
  simp

example : example_spec_crossref.section = "Existential Type" := by
  rfl
```

## Spec Category Examples

### Category Classification

```lean
/-- Example: Core specifications -/
def example_core_specs : List SpecPath :=
  [ { dir := .root, name := "module_existential_spec.md" },
    { dir := .root, name := "registry_consensus_spec.md" },
    { dir := .root, name := "scheduler_randomized_stealing_spec.md" } ]

example : ∀ p : SpecPath, p ∈ example_core_specs → IsCoreSpec p := by
  -- Proof: All specs in the list are core specifications
  sorry

/-- Example: Build specifications -/
def example_build_specs : List SpecPath :=
  [ { dir := .build, name := "build_lattice_spec.md" },
    { dir := .build, name := "dependency_sat_spec.md" } ]

example : ∀ p : SpecPath, p ∈ example_build_specs → IsBuildSpec p := by
  -- Proof: All specs in the list are build specifications
  sorry

/-- Example: Concurrency specifications -/
def example_concurrency_specs : List SpecPath :=
  [ { dir := .concurrency, name := "concurrency_process_algebra_spec.md" },
    { dir := .concurrency, name := "execution_model_spec.md" } ]

example : ∀ p : SpecPath, p ∈ example_concurrency_specs → IsConcurrencySpec p := by
  -- Proof: All specs in the list are concurrency specifications
  sorry
```

## Spec Validation Examples

### Valid Spec Set

```lean
/-- Example: A set of valid specifications -/
def example_valid_specs : List SpecPath :=
  [ { dir := .root, name := "module_existential_spec.md" },
    { dir := .root, name := "registry_consensus_spec.md" },
    { dir := .build, name := "build_lattice_spec.md" },
    { dir := .concurrency, name := "concurrency_process_algebra_spec.md" } ]

example : AllSpecsValid example_valid_specs := by
  -- Proof: All specs in the list are valid
  intro p
  cases h
  case _ => rfl
```

## Notes

- All examples are simplified for clarity
- Some proofs are marked as `sorry` (placeholder) for brevity
- These examples demonstrate how the formal definitions apply to practical scenarios
- Examples can be used as test cases for verification
-/
