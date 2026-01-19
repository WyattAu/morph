/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Specs.GLOSSARY
import Morph.Specs.GLOSSARY.Spec
import Morph.Specs.ModuleExistential.Spec

/-!
# Examples: Module Existential

This module contains concrete examples and test cases for module
existential specification. These examples demonstrate how to formal
definitions apply to practical scenarios in the Morph language.

## Overview

The Module Existential Examples module provides:
- Module privacy examples
- Existential type examples
- Module interface examples
- Module implementation examples
- Module encapsulation examples
- Access control examples
- Module composition examples

## Key Concepts

- **Module Privacy:** Demonstrating private, public, and internal module declarations
- **Existential Types:** Demonstrating hiding of implementation details
- **Module Interface:** Demonstrating public API definitions
- **Module Implementation:** Demonstrating private type and function declarations
- **Encapsulation:** Demonstrating hiding of implementation details
- **Access Control:** Demonstrating fine-grained access control
- **Module Composition:** Demonstrating combining multiple modules

-!
namespace Morph.Specs.ModuleExistential

/-!
## Module Privacy Examples

These examples demonstrate module privacy declarations.
-/

/-- Example: A private module declaration -/
def example_private_module : ModuleDecl :=
  { id := { name := "PrivateModule" },
    visibility := .private,
    exports := ["publicFunction"] }

example : IsPrivateModule example_private_module := by
  rfl

example : spec_module_privacy example_private_module defaultEnv := by
  -- Proof: All exported symbols are public in environment
  intro sym h_in_exports
  -- From h_in_exports, sym is in exports
  -- From spec_module_privacy definition, need to show sym is in env and type is public
  have h_contains : defaultEnv.contains sym := by
    sorry  -- Environment contains symbol
  have h_type : ∃ (τ : Type), defaultEnv.getType sym = τ ∧ τ.isPublic := by
    sorry  -- Symbol has public type in environment
  exact ⟨h_contains, h_type⟩

/-- Example: A public module declaration -/
def example_public_module : ModuleDecl :=
  { id := { name := "PublicModule" },
    visibility := .public,
    exports := ["publicFunction", "publicType"] }

example : IsPublicModule example_public_module := by
  rfl

example : ¬IsPrivateModule example_public_module := by
  -- Proof: visibility is .public, not .private
  intro h_public
  -- From h_public, visibility is .public
  -- IsPrivateModule is defined as visibility = .private
  -- Since .public ≠ .private, the statement follows
  sorry  -- Requires constructor inequality

/-!
## Existential Type Examples

These examples demonstrate existential types for hiding implementation details.
-/

/-- Example: An existential type for a private implementation -/
def example_existential_type : ExistentialType :=
  { interface := Unit,  -- Public interface is Unit
    implementation := Nat,  -- Private implementation is Nat
    witness := fun (_ : Nat) => ()  -- Witness converts Nat to Unit }

/-- Example: An existential value -/
def example_existential_value : ExistentialValue :=
  { type := example_existential_type,
    value := 42 }  -- Concrete value of type Nat

example : example_existential_value.type = example_existential_type := by
  rfl

example : spec_existential_types example_existential_type example_existential_value := by
  -- Proof: The existential type hides implementation
  intro h_eq f h_forall
  -- Since v.type = t, v.value : t.implementation
  -- Need to show: ∀ (f : t.interface → Prop),
  --   (∀ (x : t.implementation), f (t.witness x)) → f (t.witness v.value)
  -- Let f be an arbitrary function from t.interface → Prop
  -- For any x : t.implementation, assume f (t.witness x)
  -- Then f (t.witness v.value) must hold since v.value : t.implementation
  -- This follows from the definition of spec_existential_types
  -- The key insight is that the witness function provides the only way
  -- to access the implementation value from the interface
  exact h_forall v.value (h_eq ▸ rfl)

/-!
## Module Interface Examples

These examples demonstrate module interfaces.
-/

/-- Example: A module interface -/
def example_module_interface : ModuleInterface :=
  { module := { name := "MyModule" },
    types := [("MyType", .int)],
    functions := [("myFunction", .int → .int)] }

/-- Example: A module that implements an interface -/
def example_module_implements_interface : ModuleDecl :=
  { id := { name := "MyModule" },
    visibility := .public,
    exports := ["MyType", "myFunction"] }

example : example_module_implements_interface.implements example_module_interface := by
  -- Proof: All exported symbols are in interface
  intro sym h_in_exports
  -- From h_in_exports, sym is in exports
  -- From implements definition, need to show:
  -- ∃ (τ : Type), (sym, τ) ∈ iface.types ∨ (sym, τ) ∈ iface.functions
  -- Check each exported symbol
  cases sym with
  | "MyType" =>
    have h_in_types : ("MyType", .int) ∈ example_module_interface.types := by
      -- "MyType" is in types
      exact Or.inl h_in_types
  | "myFunction" =>
    have h_in_functions : ("myFunction", .int → .int) ∈ example_module_interface.functions := by
      -- "myFunction" is in functions
      exact Or.inr h_in_functions

example : spec_module_interface example_module_implements_interface
                                  example_module_interface
                                  defaultEnv := by
  -- Proof: All exported symbols are public in environment
  intro sym h_in_exports
  -- From h_in_exports, sym is in exports
  -- From spec_module_interface definition, need to show:
  -- ∃ (τ : Type), (sym, τ) ∈ iface.types ∨ (sym, τ) ∈ iface.functions) ∧
  --   env.getType sym = τ ∧ τ.isPublic
  -- We already proved the first part in previous example
  -- Now need to show the environment part
  cases sym with
  | "MyType" =>
    have h_env : defaultEnv.getType "MyType" = .int := by
      sorry  -- Environment lookup returns .int
    have h_public : .int.isPublic := by
      sorry  -- .int type is public
    exact ⟨Or.inl h_in_types, ⟨h_env, h_public⟩⟩
  | "myFunction" =>
    have h_env : defaultEnv.getType "myFunction" = .int → .int := by
      sorry  -- Environment lookup returns function type
    have h_public : (.int → .int).isPublic := by
      sorry  -- Function type is public
    exact ⟨Or.inr h_in_functions, ⟨h_env, h_public⟩⟩

/-!
## Module Implementation Examples

These examples demonstrate module implementations with private types and functions.
-/

/-- Example: A module implementation with private types and functions -/
def example_module_implementation : ModuleImplementation :=
  { module := { name := "MyModule" },
    privateTypes := [("PrivateType", .bool)],
    privateFunctions := [("privateFunction", .bool → .bool)] }

/-- Example: A module with implementation -/
def example_module_with_implementation : ModuleDecl :=
  { id := { name := "MyModule" },
    visibility := .private,
    exports := ["publicFunction"] }

example : example_module_with_implementation.hasImplementation
           example_module_implementation := by
  -- Proof: The module has the given implementation
  constructor
  · rfl
  · rfl

example : spec_module_implementation example_module_with_implementation
                                     example_module_implementation := by
  -- Proof: Private symbols are not exported
  intro sym h_in_private
  -- From h_in_private, sym is in private types
  -- From spec_module_implementation definition, need to show:
  -- sym ∉ mod.exports ∧
  --   ((∃ (τ : Type), (sym, τ) ∈ impl.privateTypes) ∨
  --    (∃ (τ : Type), (sym, τ) ∈ impl.privateFunctions))
  -- Check each non-exported symbol
  cases sym with
  | "publicFunction" =>
    have h_not_in_private : ("publicFunction", ·) ∉ example_module_implementation.privateTypes ∧
      ("publicFunction", ·) ∉ example_module_implementation.privateFunctions := by
      -- "publicFunction" is not in private types or functions
      exact And h_not_in_private
  | "PrivateType" =>
    have h_in_private_types : ("PrivateType", .bool) ∈ example_module_implementation.privateTypes := by
      -- "PrivateType" is in private types
      exact Or.inl h_in_private_types
  | "privateFunction" =>
    have h_in_private_functions : ("privateFunction", .bool → .bool) ∈ example_module_implementation.privateFunctions := by
      -- "privateFunction" is in private functions
      exact Or.inr h_in_private_functions
  exact ⟨And h_not_in_private, Or.inl h_in_private_types ∨ Or.inr h_in_private_functions⟩

/-!
## Module Encapsulation Examples

These examples demonstrate module encapsulation.
-/

/-- Example: A module with encapsulation -/
def example_module_encapsulation_mod : ModuleDecl :=
  { id := { name := "EncapsulatedModule" },
    visibility := .private,
    exports := ["publicFunction"] }

def example_module_encapsulation_impl : ModuleImplementation :=
  { module := { name := "EncapsulatedModule" },
    privateTypes := [("PrivateType", .bool)],
    privateFunctions := [("privateFunction", .bool → .bool)] }

example : spec_module_encapsulation example_module_encapsulation_mod
                                    example_module_encapsulation_impl
                                    defaultEnv := by
  -- Proof: Private symbols are hidden from external code
  intro sym h_in_private h_encap
  -- From h_in_private, sym is in private types
  -- From h_encap, mod has encapsulation
  -- From spec_module_encapsulation definition, need to show:
  -- sym ∉ mod.exports ∧
  --   (¬env.contains sym ∨
  --    (∃ (τ' : Type), env.getType sym = τ' ∧ τ'.isPrivate))
  -- Check each non-exported symbol
  cases sym with
  | "publicFunction" =>
    have h_not_exported : sym ∉ example_module_encapsulation_mod.exports := by
      -- "publicFunction" is exported
    have h_hidden : ¬defaultEnv.contains sym ∨
      (∃ (τ' : Type), defaultEnv.getType sym = τ' ∧ τ'.isPrivate) := by
      -- Symbol is not in env or is private
      sorry  -- From encapsulation property
    exact ⟨h_not_exported, h_hidden⟩
  | "PrivateType" =>
    have h_not_exported : sym ∉ example_module_encapsulation_mod.exports := by
      -- "PrivateType" is not exported
    have h_hidden : ¬defaultEnv.contains sym ∨
      (∃ (τ' : Type), defaultEnv.getType sym = τ' ∧ τ'.isPrivate) := by
      -- Symbol is not in env or is private
      sorry  -- From encapsulation property
    exact ⟨h_not_exported, h_hidden⟩
  | "privateFunction" =>
    have h_not_exported : sym ∉ example_module_encapsulation_mod.exports := by
      -- "privateFunction" is not exported
    have h_hidden : ¬defaultEnv.contains sym ∨
      (∃ (τ' : Type), defaultEnv.getType sym = τ' ∧ τ'.isPrivate) := by
      -- Symbol is not in env or is private
      sorry  -- From encapsulation property
    exact ⟨h_not_exported, h_hidden⟩

/-!
## Module Access Control Examples

These examples demonstrate access control.
-/

/-- Example: An access control list -/
def example_module_access_control : AccessControl :=
  { entries :=
      [ { module := { name := "MyModule" },
          symbol := "publicFunction",
          rule := .allow },
        { module := { name := "MyModule" },
          symbol := "privateFunction",
          rule := .deny } ] }

/-- Example: A private module with access control -/
def example_module_with_acl : ModuleDecl :=
  { id := { name := "MyModule" },
    visibility := .private,
    exports := ["publicFunction"] }

example : example_module_access_control.isAllowed
           { name := "MyModule" } "publicFunction" = true := by
  rfl

example : example_module_access_control.isAllowed
           { name := "MyModule" } "privateFunction" = false := by
  rfl

example : spec_module_access_control example_module_with_acl
                                   example_module_access_control
                                   defaultEnv := by
  -- Proof: Only allowed symbols can be accessed
  intro sym h_allowed
  -- From h_allowed, access is granted
  -- From spec_module_access_control definition, need to show:
  -- sym ∈ mod.exports ∧
  --   ∃ (τ : Type), env.getType sym = τ ∧ τ.isPublic
  -- From isAllowed definition, symbol must be in exports
  have h_in_exports : sym ∈ example_module_with_acl.exports := by
    -- Symbol is in exports
  have h_type : ∃ (τ : Type), defaultEnv.getType sym = τ ∧ τ.isPublic := by
    sorry  -- Symbol has public type in environment
  exact ⟨h_in_exports, h_type⟩

/-!
## Module Composition Examples

These examples demonstrate module composition.
-/

/-- Example: A module composition -/
def example_module_composition : ModuleComposition :=
  { modules :=
      [ { id := { name := "ModuleA" },
          visibility := .public,
          exports := ["functionA"] },
        { id := { name := "ModuleB" },
          visibility := .public,
          exports := ["functionB"] } ],
    imports :=
      [ ({ name := "ModuleA" }, { name := "ModuleB" }) ] }

example : example_module_composition.imports
           { name := "ModuleA" } { name := "ModuleB" } := by
  -- Proof: ModuleA imports ModuleB
  -- From imports definition, need to show:
  -- (importer, imported) ∈ comp.imports ∧
  --   ∃ (mod : ModuleDecl), mod ∈ comp.modules ∧ mod.id = importer ∧
  --   ∃ (mod' : ModuleDecl), mod' ∈ comp.modules ∧ mod'.id = imported
  -- From modules list, ModuleA and ModuleB are present
  have h_importer : ∃ (mod : ModuleDecl),
    mod ∈ example_module_composition.modules ∧ mod.id = { name := "ModuleA" } := by
      constructor
      · rfl
    have h_imported : ∃ (mod' : ModuleDecl),
    mod' ∈ example_module_composition.modules ∧ mod'.id = { name := "ModuleB" } := by
      constructor
      · rfl
    exact ⟨h_importer, h_imported⟩

example : spec_module_composition example_module_composition defaultEnv := by
  -- Proof: Imported symbols are available in importer
  intro importer imported h_imports sym h_in_exports
  -- From h_imports, importer imports imported
  -- From h_in_exports, sym is in imported module's exports
  -- From spec_module_composition definition, need to show:
  -- env.contains sym ∧ ∃ (τ : Type), env.getType sym = τ
  -- From h_in_exports, sym is in exports of imported module
  -- Need to show symbol is available in environment
  have h_module : ∃ (mod : ModuleDecl),
    mod ∈ example_module_composition.modules ∧ mod.id = imported := by
    -- From h_imports, imported module is in composition
      sorry  -- Requires list membership property
  have h_exports : sym ∈ mod.exports := by
    sorry  -- From h_module, symbol is in exports
    have h_contains : defaultEnv.contains sym := by
    sorry  -- Imported symbols are available in environment
    have h_type : ∃ (τ : Type), defaultEnv.getType sym = τ := by
    sorry  -- Symbol has a type in environment
    exact ⟨h_contains, h_type⟩

end Morph.Specs.ModuleExistential
