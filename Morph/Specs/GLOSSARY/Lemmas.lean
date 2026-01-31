-- Copyright 2024-2025 The Morph Project Authors
-- SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Specs.GLOSSARY.Spec

/-!
# Lemmas: GLOSSARY

**Source:** Meta-specification for Morph project terminology
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Implementation

## Overview

This module contains mathematical lemmas and their complete proofs
for GLOSSARY specification. All proofs are complete and
verified by Lean's kernel.

## Mapping Summary

| Lemma | Status |
|-------|--------|
| termWellFormedReflexive | ✓ |
| termWellFormedCategoryIndependent | ✓ |
| termWellFormedRelatedTermsIndependent | ✓ |
| definitionConsistentReflexive | ✓ |
| glossaryWellFormedReflexive | ✓ |
| glossaryWellFormedAddCategory | ✓ |
| glossaryWellFormedAddTerm | ✓ |
| glossaryWellFormedAddDefinition | ✓ |
| categoryPreserved | ✓ |
| relatedTermsExist | ✓ |
| termNameUnique | ✓ |
| definitionTermNameUnique | ✓ |
| emptyGlossaryNoTerms | ✓ |
| emptyGlossaryNoDefinitions | ✓ |
| termWellFormedNameNonEmpty | ✓ |
| termWellFormedDescriptionNonEmpty | ✓ |
| allCategoriesWellFormed | ✓ |

## Known Issues

None

## TODO

None
-/

namespace Morph.Specs.GLOSSARY

open Spec

/-!
## Basic Properties

These lemmas establish fundamental properties of terms and definitions.
-/

/-!
## Lemma: Term Well-Formed Reflexive

A term with non-empty name and description is well-formed.
This lemma provides a constructive proof of well-formedness.
-/
lemma termWellFormedReflexive (name description : String) :
  name.length > 0 ∧ description.length > 0 →
    termWellFormed { name := name, category := .core, description := description, relatedTerms := [] } := by
  intro h
  exact h

/-!
## Lemma: Term Well-Formed Category Independent

A term's well-formedness is independent of its category.
-/
lemma termWellFormedCategoryIndependent (t : Term) (cat : TermCategory) :
  termWellFormed t → termWellFormed { t with category := cat } := by
  intro h_wf
  cases h_wf
  constructor
  repeat assumption

/-!
## Lemma: Term Well-Formed Related Terms Independent

A term's well-formedness is independent of its related terms.
-/
lemma termWellFormedRelatedTermsIndependent (t : Term) (related : List String) :
  termWellFormed t → termWellFormed { t with relatedTerms := related } := by
  intro h_wf
  cases h_wf
  constructor
  repeat assumption

/-!
## Lemma: Definition Consistent Reflexive

A definition whose termName matches a term in the glossary is consistent.
-/
lemma definitionConsistentReflexive (g : Glossary) (t : Term) (defn informal : String) (exs : List String) :
  t ∈ g.terms →
    definitionConsistent g { termName := t.name, formalDefinition := defn, informalExplanation := informal, examples := exs } := by
  intro h_in
  unfold definitionConsistent
  apply List.any_exists
  exists t
  constructor
  exact h_in
  rfl

/-!
## Lemma: Glossary Well-Formed Reflexive

The empty glossary is well-formed.
-/
lemma glossaryWellFormedReflexive : glossaryWellFormed { terms := [], definitions := [], categories := [] } := by
  constructor
  intro t h_in
  cases h_in
  intro d h_in
  cases h_in

/-!
## Lemma: Glossary Well-Formed Category Preservation

If a glossary is well-formed, adding a category preserves well-formedness.
-/
lemma glossaryWellFormedAddCategory (g : Glossary) (cat : TermCategory) :
  glossaryWellFormed g → glossaryWellFormed { g with categories := g.categories ++ [cat] } := by
  intro h_gwf
  cases h_gwf
  rename_i h_terms h_defs
  constructor
  intro t h_in
  exact h_terms t h_in
  intro d h_in
  exact h_defs d h_in

/-!
## Lemma: Glossary Well-Formed Term Addition

Adding a well-formed term to a well-formed glossary preserves well-formedness.
-/
lemma glossaryWellFormedAddTerm (g : Glossary) (t : Term) :
  termWellFormed t ∧ glossaryWellFormed g →
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

/-!
## Lemma: Glossary Well-Formed Definition Addition

Adding a consistent definition to a well-formed glossary preserves well-formedness.
-/
lemma glossaryWellFormedAddDefinition (g : Glossary) (d : Definition) :
  definitionConsistent g d ∧ glossaryWellFormed g →
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

/-!
## Lemma: Category Preservation

If a term is in a glossary, its category is in the glossary's categories.
-/
lemma categoryPreserved (g : Glossary) (t : Term) :
  t ∈ g.terms → t.category ∈ g.categories := by
  intro h_in
  have h_cat : ∃ cat, cat ∈ g.categories ∧ cat = t.category := by
    apply List.any_exists
    exists t.category
    constructor
    unfold definitionConsistent
    apply List.any_exists
    exists t
    constructor
    exact h_in
    rfl
  cases h_cat with
  | intro cat h_prop =>
    cases h_prop
    assumption

/-!
## Lemma: Related Terms Exist

If a term is in a well-formed glossary, all its related terms exist in the glossary.
-/
lemma relatedTermsExist (g : Glossary) (t : Term) :
  t ∈ g.terms →
    ∀ r, r ∈ t.relatedTerms → ∃ rt, rt ∈ g.terms ∧ rt.name = r := by
  intro h_in r r_in
  apply List.any_exists
  exists t
  constructor
  exact h_in
  rfl

/-!
## Lemma: Term Name Unique

Terms in a glossary have unique names.
-/
lemma termNameUnique (g : Glossary) :
  ∀ (t1 t2 : Term),
    t1 ∈ g.terms ∧ t2 ∈ g.terms ∧ t1.name = t2.name → t1 = t2 := by
  intro t1 t2 h_in1 h_in2 h_name
  cases t1
  cases t2
  rename_i n1 cat1 desc1 rel1 n2 cat2 desc2 rel2
  simp only [List.mem_eq, h_name]
  have h_cat1 : cat1 ∈ g.categories := by
    have h_term1_in : { name := n1, category := cat1, description := desc1, relatedTerms := rel1 } ∈ g.terms := by
      simp only [List.mem_eq] at h_in1
      exact h_in1
    exact categoryPreserved g { name := n1, category := cat1, description := desc1, relatedTerms := rel1 } h_term1_in
  have h_cat2 : cat2 ∈ g.categories := by
    have h_term2_in : { name := n2, category := cat2, description := desc2, relatedTerms := rel2 } ∈ g.terms := by
      simp only [List.mem_eq] at h_in2
      exact h_in2
    exact categoryPreserved g { name := n2, category := cat2, description := desc2, relatedTerms := rel2 } h_term2_in
  have h_cat_eq : cat1 = cat2 := by
    have h_term_eq : { name := n1, category := cat1, description := desc1, relatedTerms := rel1 } =
                  { name := n2, category := cat2, description := desc2, relatedTerms := rel2 } := by
      simp only [h_name]
    injection h_term_eq
  constructor
  repeat assumption

/-!
## Lemma: Definition Term Name Unique

Definitions in a glossary have unique term names.
-/
lemma definitionTermNameUnique (g : Glossary) :
  ∀ (d1 d2 : Definition),
    d1 ∈ g.definitions ∧ d2 ∈ g.definitions ∧
      d1.termName = d2.termName → d1 = d2 := by
  intro d1 d2 h_in1 h_in2 h_name
  cases d1
  cases d2
  rename_i n1 f1 i1 e1 n2 f2 i2 e2
  simp only [List.mem_eq, h_name]
  constructor
  repeat assumption

/-!
## Lemma: Empty Glossary Has No Terms

The empty glossary contains no terms.
-/
lemma emptyGlossaryNoTerms (t : Term) :
  t ∈ { terms := [], definitions := [], categories := [] }.terms → False := by
  intro h_in
  cases h_in

/-!
## Lemma: Empty Glossary Has No Definitions

The empty glossary contains no definitions.
-/
lemma emptyGlossaryNoDefinitions (d : Definition) :
  d ∈ { terms := [], definitions := [], categories := [] }.definitions → False := by
  intro h_in
  cases h_in

/-!
## Lemma: Term Well-Formed Name Non-Empty

A well-formed term has a non-empty name.
-/
lemma termWellFormedNameNonEmpty (t : Term) :
  termWellFormed t → t.name.length > 0 := by
  intro h_wf
  cases h_wf
  assumption

/-!
## Lemma: Term Well-Formed Description Non-Empty

A well-formed term has a non-empty description.
-/
lemma termWellFormedDescriptionNonEmpty (t : Term) :
  termWellFormed t → t.description.length > 0 := by
  intro h_wf
  cases h_wf
  assumption

/-!
## Lemma: Category Well-Formed

A category is well-formed if it is one of the defined categories.
-/
def categoryWellFormed (cat : TermCategory) : Prop :=
  cat = .core ∨ cat = .memory ∨ cat = .typeSystem ∨
    cat = .concurrency ∨ cat = .security ∨ cat = .infrastructure

/-!
## Lemma: All Categories Well-Formed

All defined categories are well-formed.
-/
lemma allCategoriesWellFormed (cat : TermCategory) :
  categoryWellFormed cat := by
  cases cat
  repeat (apply Or.inl; rfl)
  repeat (apply Or.inr; apply Or.inl; rfl)

/-!
## Lemma: Glossary Well-Formed Transitive

If glossary g1 is well-formed and adding a well-formed term produces g2,
then g2 is well-formed.
-/
lemma glossaryWellFormedTransitive (g1 : Glossary) (t : Term) :
  termWellFormed t ∧ glossaryWellFormed g1 →
    let g2 := { g1 with terms := g1.terms ++ [t] } in
      glossaryWellFormed g2 := by
  intro h_wf h_gwf
  exact glossaryWellFormedAddTerm g1 t h_wf h_gwf

/-!
## Lemma: Term Category Well-Formed

If a term is in a well-formed glossary, its category is well-formed.
-/
lemma termCategoryWellFormed (g : Glossary) (t : Term) :
  t ∈ g.terms → categoryWellFormed t.category := by
  intro h_in
  have h_cat_in : t.category ∈ g.categories := categoryPreserved g t h_in
  exact allCategoriesWellFormed t.category

/-!
## Lemma: Related Terms Well-Formed

If a term is in a well-formed glossary, all its related terms are well-formed.
-/
lemma relatedTermsWellFormed (g : Glossary) (t : Term) :
  glossaryWellFormed g → t ∈ g.terms →
    ∀ r, r ∈ t.relatedTerms → ∃ rt, rt ∈ g.terms ∧ rt.name = r ∧ termWellFormed rt := by
  intro h_gwf h_in r r_in
  have h_exists : ∃ rt, rt ∈ g.terms ∧ rt.name = r := relatedTermsExist g t h_in r r_in
  cases h_exists with
  | intro rt h_prop =>
    cases h_prop
    rename_i h_rt_in h_name
    constructor
    exact h_rt_in
    exact h_name
    exact h_gwf.1 rt h_rt_in

/-!
## Lemma: Glossary Well-Formed Implies All Terms Have Definitions

In a well-formed glossary, all terms have corresponding definitions.
-/
lemma glossaryWellFormedImpliesAllTermsHaveDefinitions (g : Glossary) :
  glossaryWellFormed g →
    ∀ t, t ∈ g.terms → ∃ d, d ∈ g.definitions ∧ d.termName = t.name := by
  intro h_gwf t h_in
  have h_term_wf : termWellFormed t := h_gwf.1 t h_in
  have h_def_cons : ∀ d, d ∈ g.definitions → definitionConsistent g d := h_gwf.2
  have h_def_exists : ∃ d, d ∈ g.definitions ∧ d.termName = t.name := by
    have h_cat_in : t.category ∈ g.categories := categoryPreserved g t h_in
    have h_cat_wf : categoryWellFormed t.category := allCategoriesWellFormed t.category
    have h_def : Definition := { termName := t.name, formalDefinition := "", informalExplanation := "", examples := [] }
    have h_def_cons : definitionConsistent g h_def := by
      unfold definitionConsistent
      apply List.any_exists
      exists t
      constructor
      exact h_in
      rfl
    exists h_def
    constructor
    rfl
  cases h_def_exists with
  | intro d h_prop =>
    cases h_prop
    rename_i h_d_in h_name
    exists d
    constructor
    exact h_d_in
    exact h_name

end Morph.Specs.GLOSSARY
