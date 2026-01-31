/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Specs.ModuleExistential.Spec

/-!
# Examples: Module Existential

**Source:** spec/language/module_existential_spec.md
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Kilo Code

## Overview

This module contains executable examples for the Module Existential specification.
All examples are concrete and can be evaluated.

## Example Summary

| Example ID | Description | Status |
|------------|-------------|--------|
| ME-EX-001 | Simple module interface | ✓ |
| ME-EX-002 | Module interface with constraints | ✓ |
| ME-EX-003 | Simple module implementation | ✓ |
| ME-EX-004 | Module implementation with body | ✓ |
| ME-EX-005 | Simple existential module | ✓ |
| ME-EX-006 | Existential with constraints | ✓ |
| ME-EX-007 | Simple module binding | ✓ |
| ME-EX-008 | Binding with implementation | ✓ |
| ME-EX-009 | Empty module environment | ✓ |
| ME-EX-010 | Environment with bindings | ✓ |
| ME-EX-011 | Type constraint | ✓ |
| ME-EX-012 | Value constraint | ✓ |
| ME-EX-013 | Dependency constraint | ✓ |
| ME-EX-014 | Eliminate existential | ✓ |
| ME-EX-015 | Introduce existential | ✓ |
| ME-EX-016 | Resolve existential | ✓ |
| ME-EX-017 | Add signature | ✓ |
| ME-EX-018 | Remove signature | ✓ |
| ME-EX-019 | Add constraint | ✓ |
| ME-EX-020 | Remove constraint | ✓ |

-/
namespace Morph.Specs.ModuleExistential

/-!
## Module Interface Examples

Examples of module interfaces.
-/

/-- ME-EX-001: Simple module interface. -/
def exampleSimpleInterface : ModuleInterface :=
  {
    name := "SimpleInterface",
    signature := [("foo", Morph.Core.Typ.intType)],
    constraints := []
  }

/-- ME-EX-002: Module interface with multiple signatures. -/
def exampleInterfaceMultipleSigs : ModuleInterface :=
  {
    name := "MultiSigInterface",
    signature := [
      ("foo", Morph.Core.Typ.intType),
      ("bar", Morph.Core.Typ.stringType)
    ],
    constraints := []
  }

/-- ME-EX-003: Module interface with constraints. -/
def exampleInterfaceWithConstraints : ModuleInterface :=
  {
    name := "ConstrainedInterface",
    signature := [("foo", Morph.Core.Typ.intType)],
    constraints := [
      ModuleConstraint.typeConstraint "foo" Morph.Core.Typ.intType,
      ModuleConstraint.valueConstraint "foo" "42"
    ]
  }

/-- ME-EX-004: Check if interface is well-formed. -/
def exampleInterfaceWellFormed : Bool :=
  isInterfaceWellFormed exampleSimpleInterface

/-- ME-EX-005: Get signature by name. -/
def exampleGetSignature : Option Morph.Core.Typ :=
  getSignatureByName exampleSimpleInterface "foo"

/-!
## Module Implementation Examples

Examples of module implementations.
-/

/-- ME-EX-006: Simple module implementation. -/
def exampleSimpleImplementation : ModuleImplementation :=
  {
    interface := exampleSimpleInterface,
    name := "SimpleInterface",
    body := "def foo : Int := 42"
  }

/-- ME-EX-007: Module implementation with body. -/
def exampleImplementationWithBody : ModuleImplementation :=
  {
    interface := exampleInterfaceWithConstraints,
    name := "ConstrainedInterface",
    body := "def foo : Int := 42"
  }

/-- ME-EX-008: Check if implementation satisfies interface. -/
def exampleImplementationSatisfies : Bool :=
  implementationSatisfiesInterface exampleSimpleImplementation

/-!
## Existential Module Examples

Examples of existential modules.
-/

/-- ME-EX-009: Simple existential module. -/
def exampleSimpleExistential : ModuleExistential :=
  {
    interface := exampleSimpleInterface,
    binder := "impl"
  }

/-- ME-EX-010: Existential with constraints. -/
def exampleExistentialWithConstraints : ModuleExistential :=
  {
    interface := exampleInterfaceWithConstraints,
    binder := "impl"
  }

/-- ME-EX-011: Eliminate existential. -/
def exampleEliminateExistential : Bool :=
  eliminateExistential exampleSimpleExistential exampleSimpleImplementation

/-- ME-EX-012: Introduce existential. -/
def exampleIntroduceExistential : ModuleExistential :=
  introduceExistential exampleSimpleInterface "impl"

/-!
## Module Binding Examples

Examples of module bindings.
-/

/-- ME-EX-013: Simple module binding. -/
def exampleSimpleBinding : ModuleBinding :=
  {
    existential := exampleSimpleExistential,
    implementation := exampleSimpleImplementation
  }

/-- ME-EX-014: Check if binding is valid. -/
def exampleBindingValid : Bool :=
  isBindingValid exampleSimpleBinding

/-!
## Module Environment Examples

Examples of module environments.
-/

/-- ME-EX-015: Empty module environment. -/
def exampleEmptyEnvironment : ModuleEnvironment :=
  {
    bindings := []
  }

/-- ME-EX-016: Environment with bindings. -/
def exampleEnvironmentWithBindings : ModuleEnvironment :=
  {
    bindings := [exampleSimpleBinding]
  }

/-- ME-EX-017: Resolve existential in environment. -/
def exampleResolveExistential : Option ModuleImplementation :=
  resolveExistential exampleEnvironmentWithBindings exampleSimpleExistential

/-- ME-EX-018: Add binding to environment. -/
def exampleAddBinding : ModuleEnvironment :=
  addBinding exampleEmptyEnvironment exampleSimpleBinding

/-- ME-EX-019: Check if environment is consistent. -/
def exampleEnvironmentConsistent : Bool :=
  isEnvironmentConsistent exampleEnvironmentWithBindings

/-!
## Constraint Examples

Examples of module constraints.
-/

/-- ME-EX-020: Type constraint. -/
def exampleTypeConstraint : ModuleConstraint :=
  ModuleConstraint.typeConstraint "foo" Morph.Core.Typ.intType

/-- ME-EX-021: Value constraint. -/
def exampleValueConstraint : ModuleConstraint :=
  ModuleConstraint.valueConstraint "foo" "42"

/-- ME-EX-022: Dependency constraint. -/
def exampleDependencyConstraint : ModuleConstraint :=
  ModuleConstraint.dependencyConstraint "dep"

/-- ME-EX-023: Check if implementation satisfies constraint. -/
def exampleSatisfiesConstraint : Bool :=
  satisfiesConstraint exampleSimpleImplementation exampleTypeConstraint

/-- ME-EX-024: Check if implementation satisfies all constraints. -/
def exampleSatisfiesAllConstraints : Bool :=
  satisfiesAllConstraints exampleSimpleImplementation

/-!
## Signature Operation Examples

Examples of signature operations.
-/

/-- ME-EX-025: Add signature to interface. -/
def exampleAddSignature : ModuleInterface :=
  addSignature exampleSimpleInterface "bar" Morph.Core.Typ.stringType

/-- ME-EX-026: Remove signature from interface. -/
def exampleRemoveSignature : ModuleInterface :=
  removeSignature exampleInterfaceMultipleSigs "foo"

/-- ME-EX-027: Check if interface has signature. -/
def exampleHasSignature : Bool :=
  hasSignature exampleSimpleInterface "foo"

/-- ME-EX-028: Check if interface does not have signature. -/
def exampleNotHasSignature : Bool :=
  hasSignature exampleSimpleInterface "nonexistent"

/-!
## Constraint Operation Examples

Examples of constraint operations.
-/

/-- ME-EX-029: Add constraint to interface. -/
def exampleAddConstraint : ModuleInterface :=
  addConstraint exampleSimpleInterface exampleTypeConstraint

/-- ME-EX-030: Remove constraint from interface. -/
def exampleRemoveConstraint : ModuleInterface :=
  removeConstraint exampleInterfaceWithConstraints exampleTypeConstraint

/-- ME-EX-031: Check if interface has constraint. -/
def exampleHasConstraint : Bool :=
  hasConstraint exampleInterfaceWithConstraints exampleTypeConstraint

/-- ME-EX-032: Check if interface does not have constraint. -/
def exampleNotHasConstraint : Bool :=
  hasConstraint exampleSimpleInterface exampleTypeConstraint

/-!
## Environment Operation Examples

Examples of environment operations.
-/

/-- ME-EX-033: Remove binding from environment. -/
def exampleRemoveBinding : ModuleEnvironment :=
  removeBinding exampleEnvironmentWithBindings exampleSimpleExistential

/-- ME-EX-034: Check if environment has binding. -/
def exampleHasBinding : Bool :=
  hasBinding exampleEnvironmentWithBindings exampleSimpleExistential

/-- ME-EX-035: Merge two environments. -/
def exampleMergeEnvironments : ModuleEnvironment :=
  mergeEnvironments exampleEmptyEnvironment exampleEnvironmentWithBindings

/-!
## Complex Examples

More complex examples combining multiple concepts.
-/

/-- ME-EX-036: Interface with multiple constraints. -/
def exampleInterfaceMultipleConstraints : ModuleInterface :=
  {
    name := "MultiConstraintInterface",
    signature := [
      ("foo", Morph.Core.Typ.intType),
      ("bar", Morph.Core.Typ.stringType)
    ],
    constraints := [
      ModuleConstraint.typeConstraint "foo" Morph.Core.Typ.intType,
      ModuleConstraint.valueConstraint "foo" "42",
      ModuleConstraint.dependencyConstraint "dep"
    ]
  }

/-- ME-EX-037: Implementation for multi-constraint interface. -/
def exampleMultiConstraintImplementation : ModuleImplementation :=
  {
    interface := exampleInterfaceMultipleConstraints,
    name := "MultiConstraintInterface",
    body := "def foo : Int := 42\ndef bar : String := \"hello\""
  }

/-- ME-EX-038: Existential for multi-constraint interface. -/
def exampleMultiConstraintExistential : ModuleExistential :=
  {
    interface := exampleInterfaceMultipleConstraints,
    binder := "impl"
  }

/-- ME-EX-039: Binding for multi-constraint existential. -/
def exampleMultiConstraintBinding : ModuleBinding :=
  {
    existential := exampleMultiConstraintExistential,
    implementation := exampleMultiConstraintImplementation
  }

/-- ME-EX-040: Environment with multiple bindings. -/
def exampleEnvironmentMultipleBindings : ModuleEnvironment :=
  {
    bindings := [
      exampleSimpleBinding,
      exampleMultiConstraintBinding
    ]
  }

/-- ME-EX-041: Resolve multi-constraint existential. -/
def exampleResolveMultiConstraintExistential : Option ModuleImplementation :=
  resolveExistential exampleEnvironmentMultipleBindings exampleMultiConstraintExistential

/-- ME-EX-042: Check if multi-constraint implementation satisfies all constraints. -/
def exampleMultiConstraintSatisfiesAll : Bool :=
  satisfiesAllConstraints exampleMultiConstraintImplementation

/-!
## Interface Chain Examples

Examples of chaining interface operations.
-/

/-- ME-EX-043: Chain of add signature operations. -/
def exampleChainAddSignatures : ModuleInterface :=
  let iface1 := addSignature exampleSimpleInterface "bar" Morph.Core.Typ.stringType
  let iface2 := addSignature iface1 "baz" Morph.Core.Typ.boolType
  iface2

/-- ME-EX-044: Chain of add constraint operations. -/
def exampleChainAddConstraints : ModuleInterface :=
  let iface1 := addConstraint exampleSimpleInterface exampleTypeConstraint
  let iface2 := addConstraint iface1 exampleValueConstraint
  iface2

/-- ME-EX-045: Chain of environment operations. -/
def exampleChainEnvironmentOps : ModuleEnvironment :=
  let env1 := addBinding exampleEmptyEnvironment exampleSimpleBinding
  let env2 := addBinding env1 exampleMultiConstraintBinding
  env2

/-!
## Edge Case Examples

Examples of edge cases and boundary conditions.
-/

/-- ME-EX-046: Interface with empty signature. -/
def exampleInterfaceEmptySignature : ModuleInterface :=
  {
    name := "EmptySigInterface",
    signature := [],
    constraints := []
  }

/-- ME-EX-047: Interface with empty constraints. -/
def exampleInterfaceEmptyConstraints : ModuleInterface :=
  {
    name := "EmptyConstraintInterface",
    signature := [("foo", Morph.Core.Typ.intType)],
    constraints := []
  }

/-- ME-EX-048: Implementation with empty body. -/
def exampleImplementationEmptyBody : ModuleImplementation :=
  {
    interface := exampleSimpleInterface,
    name := "SimpleInterface",
    body := ""
  }

/-- ME-EX-049: Existential with empty binder. -/
def exampleExistentialEmptyBinder : ModuleExistential :=
  {
    interface := exampleSimpleInterface,
    binder := ""
  }

/-- ME-EX-050: Environment with empty bindings. -/
def exampleEnvironmentEmptyBindings : ModuleEnvironment :=
  {
    bindings := []
  }

end Morph.Specs.ModuleExistential
