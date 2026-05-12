/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.GLOSSARY.Spec

namespace Morph.Specs.GLOSSARY

/-!
## Examples

Concrete examples demonstrating the GLOSSARY specification.
-/

def t_alloc : Term :=
  coreTerm "allocation" "Reserving memory for a variable or data structure" ["block", "memory"]

def t_refcount : Term :=
  memoryTerm "reference_count" "Count of active references to a memory block" ["allocation", "deallocation"]

def d_alloc : Definition := {
  termName := "allocation",
  formalDefinition := "allocate : Memory → Nat → Memory × BlockId",
  informalExplanation := "Reserves a contiguous block of memory of the given size",
  examples := ["allocate mem 16"]
}

def d_refcount : Definition := {
  termName := "reference_count",
  formalDefinition := "refCount : Block → Nat",
  informalExplanation := "Number of active references to a memory block",
  examples := ["block.refCount"]
}

def g_simple : Glossary := {
  terms := [t_alloc, t_refcount],
  definitions := [d_alloc, d_refcount],
  categories := [.core, .memory]
}

/-- The allocation term is well-formed (non-empty name and description). -/
example : termWellFormed t_alloc := by
  simp [termWellFormed, t_alloc]; decide

/-- The reference_count term is well-formed. -/
example : termWellFormed t_refcount := by
  simp [termWellFormed, t_refcount]; decide

/-- coreTerm produces a term in the core category. -/
example : (coreTerm "test" "desc" []).category = .core := rfl

/-- memoryTerm produces a term in the memory category. -/
example : (memoryTerm "test" "desc" []).category = .memory := rfl

/-- An empty glossary is well-formed. -/
example : glossaryWellFormed { terms := [], definitions := [], categories := [] } :=
  emptyGlossaryWellFormed

end Morph.Specs.GLOSSARY
