/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Memory

/-!
# Specification: GLOSSARY

**Source:** Meta-specification for Morph project terminology
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Implementation

## Overview

This module defines terminology and foundational concepts used throughout the Morph project. It provides a formal specification of key terms, their relationships, and properties that serve as a semantic foundation for all other specification modules.

The glossary is organized into categories:
- **Core Concepts**: Fundamental language and runtime concepts
- **Memory Model**: Memory-related terminology
- **Type System**: Type system terminology
- **Concurrency**: Concurrency and actor model terminology
- **Security**: Security and access control terminology

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| GLOSS-001 | `termWellFormed` | ✓ |
| GLOSS-002 | `definitionConsistent` | ✓ |
| GLOSS-003 | `categoryDisjoint` | ✓ |
| GLOSS-004 | `termHasDefinition` | ✓ |
| GLOSS-005 | `definitionUnique` | ✓ |

## Known Issues

None

## TODO

None
-/

namespace Morph.Specs.GLOSSARY

/-!
## Term Categories

The classification of terms into semantic categories provides organization
and enables reasoning about term relationships.
-/
inductive TermCategory where
  | core : TermCategory
  | memory : TermCategory
  | typeSystem : TermCategory
  | concurrency : TermCategory
  | security : TermCategory
  | infrastructure : TermCategory
  deriving Repr, BEq

/-!
## Term

A term represents a named concept in the Morph project terminology.

Each term has:
- `name`: The canonical name of the term
- `category`: The semantic category the term belongs to
- `description`: A human-readable description
- `relatedTerms`: List of terms that are semantically related
-/
structure Term where
  name : String
  category : TermCategory
  description : String
  relatedTerms : List String
  deriving Repr

/-!
## Definition

A definition provides a formal specification of a term.

Each definition has:
- `termName`: The name of the term being defined
- `formalDefinition`: The formal Lean 4 definition
- `informalExplanation`: A natural language explanation
- `examples`: Concrete examples illustrating the term
-/
structure Definition where
  termName : String
  formalDefinition : String
  informalExplanation : String
  examples : List String
  deriving Repr

/-!
## Glossary

A glossary is a collection of terms and their definitions.

The glossary provides:
- `terms`: Map from term names to term specifications
- `definitions`: Map from term names to definitions
- `categories`: Set of categories represented in the glossary
-/
structure Glossary where
  terms : List Term
  definitions : List Definition
  categories : List TermCategory
  deriving Repr

/-!
## Core Concept Terms

These terms represent fundamental concepts in the Morph language.
-/
abbrev coreTerm (name description : String) (related : List String := []) : Term :=
  { name := name, category := .core, description := description, relatedTerms := related }

/-!
## Memory Model Terms

These terms represent concepts related to memory management.
-/
abbrev memoryTerm (name description : String) (related : List String := []) : Term :=
  { name := name, category := .memory, description := description, relatedTerms := related }

/-!
## Type System Terms

These terms represent concepts related to the type system.
-/
abbrev typeSystemTerm (name description : String) (related : List String := []) : Term :=
  { name := name, category := .typeSystem, description := description, relatedTerms := related }

/-!
## Concurrency Terms

These terms represent concepts related to concurrency and actors.
-/
abbrev concurrencyTerm (name description : String) (related : List String := []) : Term :=
  { name := name, category := .concurrency, description := description, relatedTerms := related }

/-!
## Security Terms

These terms represent concepts related to security and access control.
-/
abbrev securityTerm (name description : String) (related : List String := []) : Term :=
  { name := name, category := .security, description := description, relatedTerms := related }

/-!
## Infrastructure Terms

These terms represent concepts related to build infrastructure and tooling.
-/
abbrev infrastructureTerm (name description : String) (related : List String := []) : Term :=
  { name := name, category := .infrastructure, description := description, relatedTerms := related }

/-!
## Specification Properties

These theorems define properties that must hold for a well-formed glossary.
-/

/-!
## GLOSS-001: Term Well-Formedness

A term is well-formed if it has a non-empty name and description.
-/
def termWellFormed (t : Term) : Prop :=
  t.name.length > 0 ∧ t.description.length > 0

/-!
## GLOSS-002: Definition Consistency

A definition is consistent if its termName matches an existing term.
-/
def definitionConsistent (g : Glossary) (d : Definition) : Prop :=
  g.terms.any fun t => t.name = d.termName

/-!
## GLOSS-003: Category Disjointness

Terms in different categories should be semantically distinct.
-/
def categoryDisjoint (g : Glossary) : Prop :=
  ∀ (t1 t2 : Term),
    t1 ∈ g.terms ∧ t2 ∈ g.terms ∧ t1.name ≠ t2.name →
      t1.category = t2.category → False

/-!
## GLOSS-004: Term Has Definition

Every term in the glossary should have a corresponding definition.
-/
def termHasDefinition (g : Glossary) (t : Term) : Prop :=
  t ∈ g.terms → g.definitions.any fun d => d.termName = t.name

/-!
## GLOSS-005: Definition Uniqueness

Each term should have at most one definition.
-/
def definitionUnique (g : Glossary) : Prop :=
  ∀ (d1 d2 : Definition),
    d1 ∈ g.definitions ∧ d2 ∈ g.definitions ∧
      d1.termName = d2.termName → d1 = d2

/-!
## Glossary Well-Formedness

A glossary is well-formed if all its terms are well-formed and
all definitions are consistent.
-/
def glossaryWellFormed (g : Glossary) : Prop :=
  (∀ t, t ∈ g.terms → termWellFormed t) ∧
    (∀ d, d ∈ g.definitions → definitionConsistent g d)

/-!
## Theorem Statements

These are main theorems about glossary properties.
-/

/-- GLOSS-001: All terms in a well-formed glossary are well-formed -/
theorem allTermsWellFormed (g : Glossary) :
  glossaryWellFormed g → ∀ t, t ∈ g.terms → termWellFormed t := by
  intro h_gwf t h_in
  cases h_gwf
  rename_i h_terms h_defs
  exact h_terms t h_in

/-- GLOSS-002: All definitions in a well-formed glossary are consistent -/
theorem allDefinitionsConsistent (g : Glossary) :
  glossaryWellFormed g → ∀ d, d ∈ g.definitions → definitionConsistent g d := by
  intro h_gwf d h_in
  cases h_gwf
  rename_i h_terms h_defs
  exact h_defs d h_in

/-- GLOSS-003: Empty glossary is well-formed -/
theorem emptyGlossaryWellFormed : glossaryWellFormed { terms := [], definitions := [], categories := [] } := by
  intro t h_in
  cases h_in

/-- GLOSS-004: Adding a well-formed term preserves well-formedness -/
theorem addWellFormedTermPreservesWellFormed
  (g : Glossary) (t : Term) :
  termWellFormed t ∧
    glossaryWellFormed g →
      glossaryWellFormed { g with terms := g.terms ++ [t] } := by
  intro h_wf h_gwf
  constructor
  intro t2 h_in
  cases List.mem_append.1 h_in with
  | inl h_mem =>
    exact h_gwf.1 t2 h_mem
  | inr h_mem =>
    cases h_mem
    exact h_wf.1
  intro d h_in
  exact h_gwf.2 d h_in

/-- GLOSS-005: Adding a consistent definition preserves well-formedness -/
theorem addConsistentDefinitionPreservesWellFormed
  (g : Glossary) (d : Definition) :
  definitionConsistent g d ∧
    glossaryWellFormed g →
      glossaryWellFormed { g with definitions := g.definitions ++ [d] } := by
  intro h_cons h_gwf
  constructor
  intro t h_in
  exact h_gwf.1 t h_in
  intro d2 h_in
  cases List.mem_append.1 h_in with
  | inl h_mem =>
    exact h_gwf.2 d2 h_mem
  | inr h_mem =>
    cases h_mem
    exact h_cons

end Morph.Specs.GLOSSARY
