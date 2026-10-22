/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax

namespace Morph.Specs.ModuleExistential

/-!
# Specification: Module Existential

This module formalizes module existential types, privacy, encapsulation,
and access control for Morph language.
-/

/- ## Module Identifiers -/

structure ModuleId where
  name : String
  deriving Repr, BEq, DecidableEq

/- ## Module Visibility -/

inductive Visibility where
  | visPrivate : Visibility
  | visPublic : Visibility
  | visInternal : Visibility
  deriving Repr, BEq, DecidableEq

/- ## Module Declarations -/

structure ModuleDecl where
  id : ModuleId
  visibility : Visibility
  exports : List String
  deriving Repr

def IsPrivateModule (mod : ModuleDecl) : Prop :=
  mod.visibility = .visPrivate

def IsPublicModule (mod : ModuleDecl) : Prop :=
  mod.visibility = .visPublic

def IsInternalModule (mod : ModuleDecl) : Prop :=
  mod.visibility = .visInternal

/- ## Environment Extensions -/

structure TypeWithVisibility where
  typ : Morph.Core.Typ
  visibility : Visibility

def TypeWithVisibility.isPublic (t : TypeWithVisibility) : Prop :=
  t.visibility = .visPublic

def TypeWithVisibility.isPrivate (t : TypeWithVisibility) : Prop :=
  t.visibility = .visPrivate

abbrev ModuleEnv := List (String × TypeWithVisibility)

def ModuleEnv.contains (env : ModuleEnv) (sym : String) : Bool :=
  env.any fun (s, _) => s = sym

def ModuleEnv.getType (env : ModuleEnv) (sym : String) : Option TypeWithVisibility :=
  (env.find? fun (s, _) => s = sym).map fun (_, t) => t

def defaultEnv : ModuleEnv := []

/- ## Existential Types -/

structure ExistentialType where
  interface : Morph.Core.Typ

structure ExistentialValue where
  type : ExistentialType

/- ## Module Interface -/

structure ModuleInterface where
  module : ModuleId
  types : List (String × Morph.Core.Typ)
  functions : List (String × Morph.Core.Typ)

def ModuleDecl.implements (mod : ModuleDecl) (iface : ModuleInterface) : Prop :=
  mod.id = iface.module ∧
  ∀ (sym : String), sym ∈ mod.exports →
    (∃ (τ : Morph.Core.Typ), (sym, τ) ∈ iface.types ∨ (sym, τ) ∈ iface.functions)

/- ## Module Implementation -/

structure ModuleImplementation where
  module : ModuleId
  privateTypes : List (String × Morph.Core.Typ)
  privateFunctions : List (String × Morph.Core.Typ)

def ModuleDecl.hasImplementation (mod : ModuleDecl) (impl : ModuleImplementation) : Prop :=
  mod.id = impl.module ∧
  ∀ (sym : String), sym ∈ mod.exports →
    ∀ (τ : Morph.Core.Typ),
      (sym, τ) ∈ impl.privateTypes → False

/- ## Access Control -/

inductive AccessRule where
  | allow : AccessRule
  | deny : AccessRule
  deriving Repr, BEq, DecidableEq

structure AccessEntry where
  module : ModuleId
  symbol : String
  rule : AccessRule

structure AccessControl where
  entries : List AccessEntry

def AccessControl.isAllowed (acl : AccessControl) (mod : ModuleId) (sym : String) : Bool :=
  match acl.entries.find?
      (fun e => decide (e.module = mod) && decide (e.symbol = sym)) with
  | some entry => decide (entry.rule = AccessRule.allow)
  | none => false

/- ## Module Composition -/

structure ModuleComposition where
  modules : List ModuleDecl
  imports : List (ModuleId × ModuleId)

def ModuleComposition.importsOf (comp : ModuleComposition) (importer imported : ModuleId) : Bool :=
  comp.imports.any (fun p => decide (p = (importer, imported))) &&
    (comp.modules.any fun m => decide (m.id = importer)) &&
    (comp.modules.any fun m => decide (m.id = imported))

/- ## Correctness Specifications -/

/-- **Module privacy**: every environment entry for this module carries the
module's own visibility. (This was `True`.) -/
def spec_module_privacy (mod : ModuleDecl) (env : ModuleEnv) : Prop :=
  ∀ (twv : TypeWithVisibility), (mod.id.name, twv) ∈ env →
    twv.visibility = mod.visibility

def spec_module_interface (mod : ModuleDecl) (iface : ModuleInterface) (_env : ModuleEnv) : Prop :=
  mod.implements iface

def spec_module_implementation (mod : ModuleDecl) (impl : ModuleImplementation) : Prop :=
  mod.hasImplementation impl

/-- **Encapsulation**: every exported name is public in the environment. (This
was `True`.) -/
def ModuleDecl.isEncapsulated (mod : ModuleDecl) (env : ModuleEnv) : Prop :=
  ∀ (sym : String) (twv : TypeWithVisibility),
    (sym, twv) ∈ env → sym ∈ mod.exports → twv.isPublic

def spec_module_encapsulation (mod : ModuleDecl) (impl : ModuleImplementation) (_env : ModuleEnv) : Prop :=
  mod.hasImplementation impl

/-- **Access control is sound**: an allowed name corresponds to an `allow` entry
for that module. (This was `True`.) -/
def spec_module_access_control (mod : ModuleDecl) (acl : AccessControl)
    (_env : ModuleEnv) : Prop :=
  ∀ (sym : String), AccessControl.isAllowed acl mod.id sym = true →
    ∃ e, e ∈ acl.entries ∧ e.module = mod.id ∧ e.symbol = sym ∧
      e.rule = AccessRule.allow

/-- **Composition**: a successful import relates two declared modules. (This was
`True`.) -/
def spec_module_composition (comp : ModuleComposition) (_env : ModuleEnv) : Prop :=
  ∀ (A B : ModuleId), comp.importsOf A B = true →
    (comp.modules.any (fun m => decide (m.id = A))) = true ∧
    (comp.modules.any (fun m => decide (m.id = B))) = true

/-- A value conforms to an existential when their interfaces agree. -/
def ExistentialValue.conforms (v : ExistentialValue) (t : ExistentialType) : Prop :=
  v.type.interface = t.interface

/-- **Existential types**: a conforming value's interface is the bound interface.
(This was `True`.) -/
def spec_existential_types (t : ExistentialType) : Prop :=
  ∀ (v : ExistentialValue), v.conforms t → v.type.interface = t.interface

/- ## Correctness Invariants -/

/-- **Private implementation types are not exported** by a private module. (This
was `True`.) -/
def inv_private_no_public_impl (mod : ModuleDecl) (impl : ModuleImplementation) : Prop :=
  IsPrivateModule mod → ∀ (sym : String) (τ : Morph.Core.Typ),
    (sym, τ) ∈ impl.privateTypes → sym ∉ mod.exports

def inv_interface_complete (mod : ModuleDecl) (iface : ModuleInterface) : Prop :=
  mod.implements iface →
  ∀ (sym : String), sym ∈ mod.exports →
    ∃ (τ : Morph.Core.Typ), (sym, τ) ∈ iface.types ∨ (sym, τ) ∈ iface.functions

/-- **Access control soundness**: the same statement as
`spec_module_access_control`, without the environment. (This was `True`.) -/
def inv_access_control_sound (mod : ModuleDecl) (acl : AccessControl) : Prop :=
  ∀ (sym : String), AccessControl.isAllowed acl mod.id sym = true →
    ∃ e, e ∈ acl.entries ∧ e.module = mod.id ∧ e.symbol = sym ∧
      e.rule = AccessRule.allow

def inv_composition_transitive (comp : ModuleComposition) : Prop :=
  ∀ (A B C : ModuleId),
    comp.importsOf A B ∧ comp.importsOf B C → comp.importsOf A C

end Morph.Specs.ModuleExistential
