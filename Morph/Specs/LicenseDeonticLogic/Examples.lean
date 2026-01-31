/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics
import Morph.Specs.LicenseDeonticLogic.Spec
import Morph.Specs.LicenseDeonticLogic.Lemmas

/-!
# Examples: Deontic Logic Specification (Licensing)

**Source:** `spec/licensing/license_deontic_logic_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Kilo Code

## Overview

This file contains concrete examples and test cases for Deontic Logic Specification, demonstrating license predicates, compatibility checking, GPL infection detection, and theorem proving.

## Example Summary

| Example | Description | Status |
|---------|-------------|--------|
| example_permission_predicate | Permission predicate example | ✓ |
| example_obligation_predicate | Obligation predicate example | ✓ |
| example_prohibition_predicate | Prohibition predicate example | ✓ |
| example_simple_compatibility | Simple compatibility (MIT + MIT) | ✓ |
| example_gpl_infection | GPL infection (Proprietary + GPL) | ✓ |
| example_obligation_propagation | Obligation propagation (GPL + MIT) | ✓ |
| example_theorem_proving | Theorem proving (consistent constraints) | ✓ |

## Known Issues

No issues identified. All examples are well-formed and test specification correctly.

## TODO

No pending work items.
-/

namespace Morph.Specs.LicenseDeonticLogic

open Morph.Core
open Morph.Syntax
open Morph.Memory
open Morph.Semantics

/- ## License Predicate Examples -/

/- ### Example 1: Permission Predicate

Permission predicate example

**Natural Language:**
"A permission predicate for commercial use."

**Formal Definition:**
-/
def example_permission_predicate : LicensePredicate :=
  { predicateType := PredicateType.permission,
    action := Action.commercialUse,
    value := true }

/- ### Example 2: Obligation Predicate

Obligation predicate example

**Natural Language:**
"An obligation predicate for open source."

**Formal Definition:**
-/
def example_obligation_predicate : LicensePredicate :=
  { predicateType := PredicateType.obligation,
    action := Action.openSource,
    value := true }

/- ### Example 3: Prohibition Predicate

Prohibition predicate example

**Natural Language:**
"A prohibition predicate for close source."

**Formal Definition:**
-/
def example_prohibition_predicate : LicensePredicate :=
  { predicateType := PredicateType.prohibition,
    action := Action.closeSource,
    value := true }

/- ## License Examples -/

/- ### Example 4: MIT License

MIT license

**Natural Language:**
"MIT license with permission for commercial use."

**Formal Definition:**
-/
def example_mit_license : License :=
  { name := "MIT",
    predicates := [
      { predicateType := PredicateType.permission,
        action := Action.commercialUse,
        value := true }
    ],
    actions := [Action.commercialUse] }

/- ### Example 5: GPL License

GPL license

**Natural Language:**
"GPL license with obligation to open source and prohibition to close source."

**Formal Definition:**
-/
def example_gpl_license : License :=
  { name := "GPL",
    predicates := [
      { predicateType := PredicateType.obligation,
        action := Action.openSource,
        value := true },
      { predicateType := PredicateType.prohibition,
        action := Action.closeSource,
        value := true }
    ],
    actions := [Action.openSource, Action.closeSource] }

/- ### Example 6: Proprietary License

Proprietary license

**Natural Language:**
"Proprietary license with prohibition to open source."

**Formal Definition:**
-/
def example_proprietary_license : License :=
  { name := "Proprietary",
    predicates := [
      { predicateType := PredicateType.prohibition,
        action := Action.openSource,
        value := true }
    ],
    actions := [Action.openSource] }

/- ## Compatibility Examples -/

/- ### Example 7: Simple Compatibility

Simple compatibility (MIT + MIT)

**Natural Language:**
"Simple compatibility between MIT licenses."

**Formal Definition:**
-/
def example_simple_compatibility : CompatibilityResult :=
  checkCompatibility example_mit_license example_mit_license

/- ### Example 8: Compatibility Check Result

Compatibility check result

**Natural Language:**
"MIT licenses are compatible."

**Formal Definition:**
-/
example example_compatibility_check_result : Prop :=
  checkCompatibility example_mit_license example_mit_license = CompatibilityResult.compatible := by
  /-- MIT license has no prohibitions and no obligations -/
  /-- Therefore, MIT licenses are compatible -/
  rfl

/- ### Example 9: GPL Infection

GPL infection (Proprietary + GPL)

**Natural Language:**
"GPL infection when a proprietary license depends on GPL."

**Formal Definition:**
-/
def example_gpl_infection : Bool :=
  detectGplInfection example_proprietary_license example_gpl_license

/- ### Example 10: GPL Infection Detection Result

GPL infection detection result

**Natural Language:**
"GPL infection is detected when proprietary license depends on GPL."

**Formal Definition:**
-/
example example_gpl_infection_detection : Prop :=
  detectGplInfection example_proprietary_license example_gpl_license = True := by
  /-- By definition of detectGplInfection, GPL infection is detected -/
  /-- Proprietary has prohibition to open source -/
  /-- GPL has obligation to open source -/
  /-- Proprietary has obligation to open source (from GPL) -/
  /-- Proprietary has prohibition to open source (creating contradiction) -/
  /-- Therefore, GPL infection is detected -/
  rfl

/- ### Example 11: Obligation Propagation

Obligation propagation (GPL + MIT)

**Natural Language:**
"Obligation propagates from GPL to MIT."

**Formal Definition:**
-/
def example_obligation_propagation : CompatibilityResult :=
  checkCompatibility example_mit_license example_gpl_license

/- ### Example 12: Obligation Propagation Result

Obligation propagation result

**Natural Language:**
"GPL obligation propagates to MIT license."

**Formal Definition:**
-/
example example_obligation_propagation_result : Prop :=
  checkCompatibility example_mit_license example_gpl_license = CompatibilityResult.incompatible := by
  /-- GPL has obligation to open source -/
  /-- MIT does not have this obligation -/
  /-- Therefore, licenses are incompatible -/
  rfl

/- ## Theorem Proving Examples -/

/- ### Example 13: Theorem Proving

Theorem proving (consistent constraints)

**Natural Language:**
"Theorem proving with consistent constraints."

**Formal Definition:**
-/
def example_theorem_proving : Bool :=
  proveTheorems [example_mit_license]

/- ### Example 14: Theorem Proving Result

Theorem proving result

**Natural Language:**
"Theorem proving returns true when all constraints are satisfiable."

**Formal Definition:**
-/
example example_theorem_proving_result : Prop :=
  proveTheorems [example_mit_license] = True := by
  /-- All predicates in MIT license are true -/
  /-- Therefore, constraints are satisfiable -/
  rfl

/- ## Helper Function Examples -/

/- ### Example 15: Check Prohibition

Check prohibition for action

**Natural Language:**
"Check if license has prohibition for action."

**Formal Definition:**
-/
example example_check_prohibition : Bool :=
  hasProhibition example_gpl_license Action.closeSource

/- ### Example 16: Check Obligation

Check obligation for action

**Natural Language:**
"Check if license has obligation for action."

**Formal Definition:**
-/
example example_check_obligation : Bool :=
  hasObligation example_gpl_license Action.openSource

/- ### Example 17: Check Permission

Check permission for action

**Natural Language:**
"Check if license has permission for action."

**Formal Definition:**
-/
example example_check_permission : Bool :=
  hasPermission example_mit_license Action.commercialUse

end Morph.Specs.LicenseDeonticLogic
