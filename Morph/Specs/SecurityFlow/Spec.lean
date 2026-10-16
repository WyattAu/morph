/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Specs.TaintFlow.Lemmas
import Morph.Syntax
import Morph.Memory
import Morph.Semantics

/-!
# Specification: Security Flow

**Source:** `spec/security/security_flow_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Kilo Code

## Overview

This specification formalizes the Security Flow for the Morph framework, providing mathematical foundation for type-based information flow with security lattices.

## Known Issues

No issues identified. The specification is clear and unambiguous.

## TODO

No pending work items.
-/

namespace Morph.Specs.SecurityFlow

/-!
## 2.1 Security Lattice
-/

structure SecurityLattice where
  /-- The set of elements in the security lattice -/
  elements : Type
  /-- The partial order relation on elements -/
  le : elements → elements → Prop
  /-- The least upper bound operation -/
  lub : elements → elements → elements
  /-- The greatest lower bound operation -/
  glb : elements → elements → elements

/- Security Lattice Properties -/

def SecurityLattice.partial_order (L : SecurityLattice) : Prop :=
  ∀ (x : L.elements), L.le x x ∧
  ∀ (x y z : L.elements),
    L.le x y → L.le y z → L.le x z ∧
  ∀ (x y : L.elements),
    L.le x y → L.le y x → x = y

def SecurityLattice.lub_properties (L : SecurityLattice) : Prop :=
  ∀ (x y : L.elements),
    L.le x (L.lub x y) ∧
    L.le y (L.lub x y) ∧
    ∀ (z : L.elements),
      L.le x z → L.le y z → L.le (L.lub x y) z

def SecurityLattice.glb_properties (L : SecurityLattice) : Prop :=
  ∀ (x y : L.elements),
    L.le (L.glb x y) x ∧
    L.le (L.glb x y) y ∧
    ∀ (z : L.elements),
      L.le z x → L.le z y → L.le z (L.glb x y)

/-!
## 2.2 Security Level
-/

abbrev SecurityLevel (L : SecurityLattice) := L.elements

def SecurityLevel.le (L : SecurityLattice) (x y : SecurityLevel L) : Prop :=
  L.le x y

/-!
## 2.3 Information Flow
-/

structure InformationFlow (L : SecurityLattice) where
  source : SecurityLevel L
  destination : SecurityLevel L

def InformationFlow.allowed (L : SecurityLattice) (flow : InformationFlow L) : Prop :=
  L.le flow.source flow.destination

/-!
## 2.4 Non-Interference
-/

/-- Noninterference. The original version of this specification stated this
over *labels*, as though labels were program states, which made it vacuous.
The real statement lives in `Morph.Specs.TaintFlow` (ADR-019, research
loop 4): an allowed program cannot move a secret into a public variable, and
that property is preserved across dialect translation. This definition now
records the transfer obligation instead of asserting it. -/
def NonInterference (L : SecurityLattice) (high _low : SecurityLevel L) : Prop :=
  True

/-- The formalized noninterference statement, for a two-point lattice: an
allowed program keeps its secret variables secret. -/
def spec_noninterference_statement :
    ∀ (ρ : Morph.Specs.TaintFlow.TEnv) (prog : List (String × Morph.Specs.TaintFlow.TExpr)),
      Morph.Specs.TaintFlow.Allowed ρ prog →
      ∀ y, (Morph.Specs.TaintFlow.run ρ prog) y = .sec → ρ y = .sec :=
  Morph.Specs.TaintFlow.allowed_no_leak

/-!
## 3. Requirements
-/

def spec_security_lattice_support (L : SecurityLattice) : Prop :=
  SecurityLattice.partial_order L ∧
  SecurityLattice.lub_properties L ∧
  SecurityLattice.glb_properties L

def spec_information_flow_policy_support (L : SecurityLattice) : Prop :=
  ∀ (flow : InformationFlow L),
    InformationFlow.allowed L flow ↔ L.le flow.source flow.destination

def spec_non_interference_support (L : SecurityLattice) (high low : SecurityLevel L) : Prop :=
  NonInterference L high low ∧
  (∀ (ρ : Morph.Specs.TaintFlow.TEnv) (prog : List (String × Morph.Specs.TaintFlow.TExpr)),
    Morph.Specs.TaintFlow.Allowed ρ prog →
    ∀ y, (Morph.Specs.TaintFlow.run ρ prog) y = .sec → ρ y = .sec)

/-!
## 4. Correctness Properties
-/

theorem thm_security_lattice_well_formed
  {L : SecurityLattice}
  (h_support : spec_security_lattice_support L)
  : SecurityLattice.partial_order L ∧
    SecurityLattice.lub_properties L ∧
    SecurityLattice.glb_properties L := h_support

theorem inv_security_lattice_well_formed
  {L : SecurityLattice}
  (h_support : spec_security_lattice_support L)
  : SecurityLattice.partial_order L ∧
    SecurityLattice.lub_properties L ∧
    SecurityLattice.glb_properties L := h_support

theorem inv_information_flow_policy_valid
  {L : SecurityLattice}
  (h_support : spec_information_flow_policy_support L)
  : ∀ (flow : InformationFlow L),
      InformationFlow.allowed L flow ↔ L.le flow.source flow.destination :=
  h_support

theorem inv_non_interference_valid
  {L : SecurityLattice}
  {high low : SecurityLevel L}
  (h_support : spec_non_interference_support L high low)
  : NonInterference L high low ∧
    (∀ (ρ : Morph.Specs.TaintFlow.TEnv)
      (prog : List (String × Morph.Specs.TaintFlow.TExpr)),
      Morph.Specs.TaintFlow.Allowed ρ prog →
      ∀ y, (Morph.Specs.TaintFlow.run ρ prog) y = .sec → ρ y = .sec) := h_support

/-- **Noninterference (formalized).** Discharged by the taint-tracking
development in `Morph.Specs.TaintFlow`, not by assertion. -/
theorem noninterference_formalized :
    ∀ (ρ : Morph.Specs.TaintFlow.TEnv) (prog : List (String × Morph.Specs.TaintFlow.TExpr)),
      Morph.Specs.TaintFlow.Allowed ρ prog →
      ∀ y, (Morph.Specs.TaintFlow.run ρ prog) y = .sec → ρ y = .sec :=
  Morph.Specs.TaintFlow.allowed_no_leak

/-- **SG-003.** Taint labels survive a dialect boundary, and with them the
noninterference property. -/
theorem taint_preserved_across_dialects :
    ∀ (ρ : Morph.Specs.TaintFlow.TEnv) (to : Morph.Specs.TaintFlow.Dialect)
      (pc : Morph.Specs.TaintFlow.Label) (e e' : Morph.Specs.TaintFlow.TExpr),
      Morph.Specs.TaintFlow.translate to pc e = some e' →
      Morph.Specs.TaintFlow.taint ρ e' = Morph.Specs.TaintFlow.taint ρ e :=
  Morph.Specs.TaintFlow.taint_preserved

end Morph.Specs.SecurityFlow
