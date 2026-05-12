/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.GLOSSARY.Spec

namespace Morph.Specs.GLOSSARY

/-!
## Lemmas

Lemmas and auxiliary results for the GLOSSARY specification.
-/

/-- coreTerm always produces a term in the core category. -/
theorem coreTerm_category (name desc : String) (related : List String) :
    (coreTerm name desc related).category = .core := rfl

/-- memoryTerm always produces a term in the memory category. -/
theorem memoryTerm_category (name desc : String) (related : List String) :
    (memoryTerm name desc related).category = .memory := rfl

/-- typeSystemTerm always produces a term in the typeSystem category. -/
theorem typeSystemTerm_category (name desc : String) (related : List String) :
    (typeSystemTerm name desc related).category = .typeSystem := rfl

/-- concurrencyTerm always produces a term in the concurrency category. -/
theorem concurrencyTerm_category (name desc : String) (related : List String) :
    (concurrencyTerm name desc related).category = .concurrency := rfl

/-- securityTerm always produces a term in the security category. -/
theorem securityTerm_category (name desc : String) (related : List String) :
    (securityTerm name desc related).category = .security := rfl

/-- infrastructureTerm always produces a term in the infrastructure category. -/
theorem infrastructureTerm_category (name desc : String) (related : List String) :
    (infrastructureTerm name desc related).category = .infrastructure := rfl

/-- A term with non-empty name and description is well-formed. -/
theorem termWellFormed_of_nonempty (t : Term)
    (hName : t.name.length > 0) (hDesc : t.description.length > 0) :
    termWellFormed t := ⟨hName, hDesc⟩

/-- A term with empty name is not well-formed. -/
theorem termNotWellFormed_empty_name (t : Term) (hName : t.name.length = 0) :
    ¬termWellFormed t := by
  intro h; cases h; omega

/-- Extending a glossary's categories preserves existing well-formedness. -/
theorem extendCategories_preserves_wellFormed (g : Glossary) (cats : List TermCategory)
    (h : glossaryWellFormed g) :
    glossaryWellFormed { g with categories := g.categories ++ cats } := by
  constructor
  · exact h.1
  · exact h.2

end Morph.Specs.GLOSSARY
