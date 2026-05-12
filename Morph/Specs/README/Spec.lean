/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core

namespace Morph.Specs.README

open Morph.Core

/-!
# README Specification

This module serves as the specification entry point for the Morph project.
It defines the top-level structure, invariants, and architectural principles
that all other spec modules must conform to.

## Project Architecture

Morph is organized into three layers:

1. **Spec Layer** (`Morph/Specs/`): Formal specifications of language features,
   type systems, memory models, and verification targets.

2. **Proof Layer** (`Morph/Proofs/`): Formal proofs that implementations
   satisfy their specifications.

3. **Implementation Layer** (`Morph/`): Executable implementations of
   compilers, runtimes, and standard libraries.

## Specification Conventions

Every `Spec.lean` module must:
- Define its namespace as `Morph.Specs.<ModuleName>`
- Include a module-level doc comment describing its purpose
- Define at least one structure or inductive type
- Provide at least one theorem or lemma proving a property
- Reference any ADRs that motivated the design
-/

/-- Top-level Morph specification version, following semantic versioning. -/
structure SpecVersion where
  major : Nat
  minor : Nat
  patch : Nat
deriving BEq

/-- The current specification version. -/
def currentVersion : SpecVersion :=
  { major := 0, minor := 4, patch := 0 }

/-- Specification module status in the development lifecycle. -/
inductive ModuleStatus where
  | draft
  | review
  | stable
  | deprecated
deriving BEq

/-- A specification module descriptor for the module registry. -/
structure SpecModule where
  modNamespace : String
  description : String
  version : SpecVersion
  status : ModuleStatus
deriving BEq

/-- The core module listing for the specification registry. -/
def coreModules : List SpecModule :=
  [ { modNamespace := "Morph.Specs.TypeSystem"
    , description := "Type system formalization"
    , version := currentVersion
    , status := ModuleStatus.review }
  , { modNamespace := "Morph.Specs.MemoryModel"
    , description := "Block-offset memory model"
    , version := currentVersion
    , status := ModuleStatus.draft }
  ]

/-- All Morph specifications must have unique namespaces. -/
def namespaceUnique (mods : List SpecModule) : Prop :=
  mods.length = (mods.map SpecModule.modNamespace).eraseDups.length

theorem coreModules_unique : namespaceUnique coreModules := by
  unfold namespaceUnique coreModules
  native_decide

end Morph.Specs.README
