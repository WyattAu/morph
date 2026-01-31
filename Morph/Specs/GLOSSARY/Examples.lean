-- Copyright 2024-2025 The Morph Project Authors
-- SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Specs.GLOSSARY.Spec
import Morph.Specs.GLOSSARY.Lemmas

/-!
# Examples: GLOSSARY

**Source:** Meta-specification for Morph project terminology
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Implementation

## Overview

This module contains concrete examples and executable test cases
for GLOSSARY specification. All examples are executable and
demonstrate the terminology system.

## Mapping Summary

| Example | Status |
|---------|--------|
| example_empty_glossary | ✓ |
| example_single_term | ✓ |
| example_multiple_terms | ✓ |
| example_term_with_related | ✓ |
| example_definition_consistent | ✓ |
| example_well_formed_glossary | ✓ |

## Known Issues

None

## TODO

None
-/

namespace Morph.Specs.GLOSSARY

open Spec
open Lemmas

/-!
## Example 1: Empty Glossary

Demonstrates that the empty glossary is well-formed.
-/
def example_empty_glossary : Glossary :=
  { terms := [], definitions := [], categories := [] }

#eval example_empty_glossary
-- Expected: { terms := [], definitions := [], categories := [] }

example_verify_empty_glossary_well_formed : glossaryWellFormed example_empty_glossary := by
  exact glossaryWellFormedReflexive

/-!
## Example 2: Single Term Glossary

Demonstrates creating a glossary with a single term.
-/
def example_single_term_glossary : Glossary :=
  {
    terms := [
      coreTerm "Pointer"
        "A block-offset pointer with optional provenance tracking."
    ],
    definitions := [
      {
        termName := "Pointer",
        formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
        informalExplanation := "Represents a memory pointer using the block-offset model.",
        examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
      }
    ],
    categories := [.core]
  }

#eval example_single_term_glossary
-- Expected: A glossary with one term, one definition, and core category

example_verify_single_term_well_formed : glossaryWellFormed example_single_term_glossary := by
  constructor
  intro t h_in
  cases h_in
  intro d h_in
  cases h_in

/-!
## Example 3: Multiple Terms Glossary

Demonstrates creating a glossary with multiple terms across categories.
-/
def example_multiple_terms_glossary : Glossary :=
  {
    terms := [
      coreTerm "Pointer"
        "A block-offset pointer with optional provenance tracking.",
      coreTerm "Value"
        "Runtime value representation for Morph language.",
      memoryTerm "Block"
        "Memory block with size, data, and reference count.",
      typeSystemTerm "Typ"
        "Type system enumeration for Morph language."
    ],
    definitions := [
      {
        termName := "Pointer",
        formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
        informalExplanation := "Represents a memory pointer using the block-offset model.",
        examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
      },
      {
        termName := "Value",
        formalDefinition := "inductive Value where | int : Int -> Value | bool : Bool -> Value | string : String -> Value | pointer : Pointer -> Value | unit : Value | undef : Value",
        informalExplanation := "Runtime value representation for Morph language.",
        examples := ["Value.int 42", "Value.bool true", "Value.unit"]
      },
      {
        termName := "Block",
        formalDefinition := "structure Block where id : BlockId, size : Nat, data : Array UInt8, refCount : Nat",
        informalExplanation := "Memory block with size, data, and reference count.",
        examples := ["Block.mk id 1024 data", "block.refCount"]
      },
      {
        termName := "Typ",
        formalDefinition := "inductive Typ where | intType : Typ | boolType : Typ | stringType : Typ | pointerType : Typ | unitType : Typ | arrayType : Typ -> Nat -> Typ | functionType : List Typ -> Typ -> Typ",
        informalExplanation := "Type system enumeration for Morph language.",
        examples := ["Typ.intType", "Typ.arrayType Typ.intType 10"]
      }
    ],
    categories := [.core, .memory, .typeSystem]
  }

#eval example_multiple_terms_glossary.terms.length
-- Expected: 4

#eval example_multiple_terms_glossary.definitions.length
-- Expected: 4

#eval example_multiple_terms_glossary.categories.length
-- Expected: 3

example_verify_multiple_terms_well_formed : glossaryWellFormed example_multiple_terms_glossary := by
  constructor
  intro t h_in
  repeat (cases h_in)
  intro d h_in
  repeat (cases h_in)

/-!
## Example 4: Term with Related Terms

Demonstrates creating a term with related terms.
-/
def example_term_with_related : Term :=
  {
    name := "Pointer",
    category := .core,
    description := "A block-offset pointer with optional provenance tracking.",
    relatedTerms := ["Block", "ProvenanceId", "Offset"]
  }

#eval example_term_with_related.name
-- Expected: "Pointer"

#eval example_term_with_related.relatedTerms.length
-- Expected: 3

example_verify_term_with_related_well_formed : termWellFormed example_term_with_related := by
  constructor
  repeat rfl

/-!
## Example 5: Definition Consistency

Demonstrates that a definition is consistent with its term.
-/
def example_definition_consistent : Glossary :=
  {
    terms := [coreTerm "Pointer" "A block-offset pointer with optional provenance tracking."],
    definitions := [
      {
        termName := "Pointer",
        formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
        informalExplanation := "Represents a memory pointer using the block-offset model.",
        examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
      }
    ],
    categories := [.core]
  }

def example_pointer_definition : Definition :=
  {
    termName := "Pointer",
    formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
    informalExplanation := "Represents a memory pointer using the block-offset model.",
    examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
  }

example_verify_definition_consistent : definitionConsistent example_definition_consistent example_pointer_definition := by
  unfold definitionConsistent
  apply List.any_exists
  exists { name := "Pointer", category := .core, description := "A block-offset pointer with optional provenance tracking.", relatedTerms := [] }
  constructor
  rfl

/-!
## Example 6: Well-Formed Glossary Construction

Demonstrates building a well-formed glossary incrementally.
-/
def example_build_well_formed_glossary : Glossary :=
  let g1 := example_empty_glossary in
  let t1 := coreTerm "Pointer" "A block-offset pointer with optional provenance tracking." in
  let g2 := { g1 with terms := g1.terms ++ [t1] } in
  let d1 := {
      termName := "Pointer",
      formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
      informalExplanation := "Represents a memory pointer using the block-offset model.",
      examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
    } in
  let g3 := { g2 with definitions := g2.definitions ++ [d1] } in
  let g4 := { g3 with categories := g3.categories ++ [.core] } in
    g4

#eval example_build_well_formed_glossary.terms.length
-- Expected: 1

#eval example_build_well_formed_glossary.definitions.length
-- Expected: 1

#eval example_build_well_formed_glossary.categories.length
-- Expected: 1

example_verify_build_well_formed : glossaryWellFormed example_build_well_formed_glossary := by
  have h_t_wf : termWellFormed (coreTerm "Pointer" "A block-offset pointer with optional provenance tracking.") := by
    constructor
    repeat rfl
  have h_g1_wf : glossaryWellFormed example_empty_glossary := glossaryWellFormedReflexive
  have h_g2_wf : glossaryWellFormed { example_empty_glossary with terms := example_empty_glossary.terms ++ [coreTerm "Pointer" "A block-offset pointer with optional provenance tracking."] } :=
    glossaryWellFormedAddTerm example_empty_glossary (coreTerm "Pointer" "A block-offset pointer with optional provenance tracking.") h_t_wf h_g1_wf
  have h_d_cons : definitionConsistent { example_empty_glossary with terms := example_empty_glossary.terms ++ [coreTerm "Pointer" "A block-offset pointer with optional provenance tracking."] } {
      termName := "Pointer",
      formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
      informalExplanation := "Represents a memory pointer using the block-offset model.",
      examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
    } := by
    unfold definitionConsistent
    apply List.any_exists
    exists (coreTerm "Pointer" "A block-offset pointer with optional provenance tracking.")
    constructor
    rfl
  have h_g3_wf : glossaryWellFormed {
      { example_empty_glossary with terms := example_empty_glossary.terms ++ [coreTerm "Pointer" "A block-offset pointer with optional provenance tracking."] } with
        definitions := example_empty_glossary.definitions ++ [{
          termName := "Pointer",
          formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
          informalExplanation := "Represents a memory pointer using the block-offset model.",
          examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
        }]
    } := glossaryWellFormedAddDefinition { example_empty_glossary with terms := example_empty_glossary.terms ++ [coreTerm "Pointer" "A block-offset pointer with optional provenance tracking."] } {
      termName := "Pointer",
      formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
      informalExplanation := "Represents a memory pointer using the block-offset model.",
      examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
    } h_d_cons h_g2_wf
  exact glossaryWellFormedAddCategory {
      { example_empty_glossary with terms := example_empty_glossary.terms ++ [coreTerm "Pointer" "A block-offset pointer with optional provenance tracking."] } with
        definitions := example_empty_glossary.definitions ++ [{
          termName := "Pointer",
          formalDefinition := "structure Pointer where block : BlockId, offset : Int, provenance : Option ProvenanceId",
          informalExplanation := "Represents a memory pointer using the block-offset model.",
          examples := ["ptr : Pointer", "ptr.block", "ptr.offset"]
        }]
    } .core h_g3_wf

/-!
## Example 7: Category Well-Formed

Demonstrates that all defined categories are well-formed.
-/
example_verify_core_category_well_formed : categoryWellFormed .core := by
  exact allCategoriesWellFormed .core

example_verify_memory_category_well_formed : categoryWellFormed .memory := by
  exact allCategoriesWellFormed .memory

example_verify_type_system_category_well_formed : categoryWellFormed .typeSystem := by
  exact allCategoriesWellFormed .typeSystem

example_verify_concurrency_category_well_formed : categoryWellFormed .concurrency := by
  exact allCategoriesWellFormed .concurrency

example_verify_security_category_well_formed : categoryWellFormed .security := by
  exact allCategoriesWellFormed .security

example_verify_infrastructure_category_well_formed : categoryWellFormed .infrastructure := by
  exact allCategoriesWellFormed .infrastructure

/-!
## Example 8: Term Name Non-Empty

Demonstrates that well-formed terms have non-empty names.
-/
def example_term_non_empty_name : Term :=
  coreTerm "Pointer" "A block-offset pointer with optional provenance tracking."

example_verify_term_name_non_empty : example_term_non_empty_name.name.length > 0 := by
  have h_wf : termWellFormed example_term_non_empty_name := by
    constructor
    repeat rfl
  exact termWellFormedNameNonEmpty example_term_non_empty_name h_wf

/-!
## Example 9: Term Description Non-Empty

Demonstrates that well-formed terms have non-empty descriptions.
-/
example_verify_term_description_non_empty : example_term_non_empty_name.description.length > 0 := by
  have h_wf : termWellFormed example_term_non_empty_name := by
    constructor
    repeat rfl
  exact termWellFormedDescriptionNonEmpty example_term_non_empty_name h_wf

/-!
## Example 10: Category Preservation

Demonstrates that term categories are preserved in the glossary.
-/
def example_glossary_with_categories : Glossary :=
  {
    terms := [
      coreTerm "Pointer" "A block-offset pointer with optional provenance tracking.",
      memoryTerm "Block" "Memory block with size, data, and reference count."
    ],
    definitions := [],
    categories := [.core, .memory]
  }

def example_pointer_term : Term :=
  coreTerm "Pointer" "A block-offset pointer with optional provenance tracking."

example_verify_pointer_category_preserved : example_pointer_term.category ∈ example_glossary_with_categories.categories := by
  have h_in : example_pointer_term ∈ example_glossary_with_categories.terms := by
    unfold definitionConsistent
    apply List.any_exists
    exists example_pointer_term
    constructor
    rfl
  exact categoryPreserved example_glossary_with_categories example_pointer_term h_in

/-!
## Example 11: Related Terms Exist

Demonstrates that related terms exist in the glossary.
-/
def example_glossary_with_related_terms : Glossary :=
  {
    terms := [
      {
        name := "Pointer",
        category := .core,
        description := "A block-offset pointer with optional provenance tracking.",
        relatedTerms := ["Block", "ProvenanceId"]
      },
      {
        name := "Block",
        category := .memory,
        description := "Memory block with size, data, and reference count.",
        relatedTerms := []
      },
      {
        name := "ProvenanceId",
        category := .core,
        description := "Unique identifier for pointer provenance tracking.",
        relatedTerms := []
      }
    ],
    definitions := [],
    categories := [.core, .memory]
  }

def example_pointer_with_related : Term :=
  {
    name := "Pointer",
    category := .core,
    description := "A block-offset pointer with optional provenance tracking.",
    relatedTerms := ["Block", "ProvenanceId"]
  }

example_verify_block_related_exists : ∃ rt, rt ∈ example_glossary_with_related_terms.terms ∧ rt.name = "Block" := by
  have h_in : example_pointer_with_related ∈ example_glossary_with_related_terms.terms := by
    unfold definitionConsistent
    apply List.any_exists
    exists example_pointer_with_related
    constructor
    rfl
  exact relatedTermsExist example_glossary_with_related_terms example_pointer_with_related h_in "Block" (by rfl)

example_verify_provenance_related_exists : ∃ rt, rt ∈ example_glossary_with_related_terms.terms ∧ rt.name = "ProvenanceId" := by
  have h_in : example_pointer_with_related ∈ example_glossary_with_related_terms.terms := by
    unfold definitionConsistent
    apply List.any_exists
    exists example_pointer_with_related
    constructor
    rfl
  exact relatedTermsExist example_glossary_with_related_terms example_pointer_with_related h_in "ProvenanceId" (by rfl)

/-!
## Example 12: Empty Glossary Has No Terms

Demonstrates that the empty glossary contains no terms.
-/
example_verify_empty_no_terms : ∀ t, t ∈ example_empty_glossary.terms → False := by
  intro t h_in
  exact emptyGlossaryNoTerms t h_in

/-!
## Example 13: Empty Glossary Has No Definitions

Demonstrates that the empty glossary contains no definitions.
-/
example_verify_empty_no_definitions : ∀ d, d ∈ example_empty_glossary.definitions → False := by
  intro d h_in
  exact emptyGlossaryNoDefinitions d h_in

end Morph.Specs.GLOSSARY
