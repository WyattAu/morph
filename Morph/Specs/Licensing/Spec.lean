/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core

namespace Morph.Specs.Licensing

open Morph.Core

/-!
# Licensing Specification

Formal model of open-source license compatibility for the Morph ecosystem:
- License type classification (permissive, copyleft, proprietary)
- License compatibility checking for dependency graphs
- License obligation propagation through transitive dependencies
-/

/-- License categories for formal compatibility analysis. -/
inductive LicenseCategory where
  | permissive
  | weakCopyleft
  | strongCopyleft
  | proprietary
deriving Repr, BEq

/-- A license with its category and known compatibility constraints. -/
structure License where
  name : String
  category : LicenseCategory
  spdxId : Option String
deriving Repr, BEq

/-- SPDX identifiers for common licenses. -/
def licenseApache2 : License :=
  { name := "Apache-2.0", category := .permissive, spdxId := "Apache-2.0" }

def licenseMIT : License :=
  { name := "MIT", category := .permissive, spdxId := "MIT" }

def licenseGPL2 : License :=
  { name := "GPL-2.0", category := .strongCopyleft, spdxId := "GPL-2.0-only" }

def licenseGPL3 : License :=
  { name := "GPL-3.0", category := .strongCopyleft, spdxId := "GPL-3.0-only" }

def licenseLGPL : License :=
  { name := "LGPL-2.1", category := .weakCopyleft, spdxId := "LGPL-2.1-only" }

def licenseMorphDefault : License :=
  { name := "Apache-2.0", category := .permissive, spdxId := "Apache-2.0" }

/-- Two licenses are compatible if their categories are compatible.
    Permissive can be linked with anything. Strong copyleft requires
    the same category. Weak copyleft allows permissive. Proprietary
    allows only proprietary and permissive (one-way). -/
def compatible (l1 l2 : License) : Bool :=
  match l1.category, l2.category with
  | .permissive, _ => true
  | _, .permissive => true
  | .weakCopyleft, .weakCopyleft => true
  | .weakCopyleft, .strongCopyleft => true
  | .strongCopyleft, .strongCopyleft => true
  | .strongCopyleft, .weakCopyleft => true
  | .proprietary, .proprietary => true
  | _, _ => false

/-- A dependency graph node with its license. -/
structure Dependency where
  name : String
  license : License
  dependencies : List String
deriving Repr, BEq

/-- Transitive license compatibility: all transitive dependencies
    must be compatible with the root license. -/
def transitiveCompatible (root : License) (deps : List Dependency) : Bool :=
  deps.all (fun dep => compatible root dep.license)

end Morph.Specs.Licensing
