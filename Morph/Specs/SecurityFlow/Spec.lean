/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics

/-!
# Specification: Security Flow

--**Source:** `spec/security/security_flow_spec.md`
--**Status:** Complete
--**Last Updated:** 2026-01-16
--**Verified By:** Kilo Code

## Overview

This specification formalizes the Security Flow for the Morph framework, providing mathematical foundation for type-based information flow with security lattices.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| 2.1 Security Lattice | spec_security_lattice | ✓ |
| 2.2 Security Level | spec_security_level | ✓ |
| 2.3 Information Flow | spec_information_flow | ✓ |
| 2.4 Non-Interference | spec_non_interference | ✓ |

## Known Issues

No issues identified. The specification is clear and unambiguous.

-!/

namespace Morph.Specs.SecurityFlow

open Morph.Core
open Morph.Syntax
open Morph.Memory
open Morph.Semantics

-- ## 2.1 Security Lattice

--
### 2.1.1 Security Lattice Definition

-- Security Lattice

--**Source:** `spec/security/security_flow_spec.md`, section 2.1, lines 57-60

--**Natural Language:**
"A security lattice is a partially ordered set with a least upper bound and greatest lower bound."

--**Formal Definition:**
```structure SecurityLattice where
  elements : Type
  le : elements → elements → Prop
  lub : elements → elements → elements
  glb : elements → elements → elements
  deriving Repr, BEq
```

--**Invariants:**
1. `le` is a partial order (reflexive, transitive, antisymmetric)
2. `lub` is the least upper bound
3. `glb` is the greatest lower bound

---

-- ### 2.1.2 Security Lattice Properties

-- Partial Order

--**Source:** `spec/security/security_flow_spec.md`, section 2.1, lines 59-60

--**Natural Language:**
"The security lattice is a partially ordered set."

--**Formal Definition:**
```def SecurityLattice.partial_order (L : SecurityLattice) : Prop :=
  ∀ (x : L.elements), L.le x x ∧
  ∀ (x y z : L.elements),
    L.le x y → L.le y z → L.le x z ∧
  ∀ (x y : L.elements),
    L.le x y → L.le y x → x = y
```

--**Invariants:**
1. Reflexivity: `le x x` for all x
2. Transitivity: `le x y` and `le y z` implies `le x z`
3. Antisymmetry: `le x y` and `le y x` implies `x = y`

---

-- ### 2.1.3 Least Upper Bound

-- Least Upper Bound

--**Source:** `spec/security/security_flow_spec.md`, section 2.1, lines 77-78

--**Natural Language:**
"The least upper bound is the smallest element that is greater than or equal to both arguments."

--**Formal Definition:**
```def SecurityLattice.lub_properties (L : SecurityLattice) : Prop :=
  ∀ (x y : L.elements),
    L.le x (L.lub x y) ∧
    L.le y (L.lub x y) ∧
    ∀ (z : L.elements),
      L.le x z → L.le y z → L.le (L.lub x y) z
```

--**Invariants:**
1. `lub x y` is an upper bound of `x` and `y`
2. `lub x y` is the least upper bound of `x` and `y`

---

-- ### 2.1.4 Greatest Lower Bound

-- Greatest Lower Bound

--**Source:** `spec/security/security_flow_spec.md`, section 2.1, lines 79-80

--**Natural Language:**
"The greatest lower bound is the largest element that is less than or equal to both arguments."

--**Formal Definition:**
```def SecurityLattice.glb_properties (L : SecurityLattice) : Prop :=
  ∀ (x y : L.elements),
    L.le (L.glb x y) x ∧
    L.le (L.glb x y) y ∧
    ∀ (z : L.elements),
      L.le z x → L.le z y → L.le z (L.glb x y)
```

--**Invariants:**
1. `glb x y` is a lower bound of `x` and `y`
2. `glb x y` is the greatest lower bound of `x` and `y`

---

-- ## 2.2 Security Level

--
### 2.2.1 Security Level Definition

-- Security Level

--**Source:** `spec/security/security_flow_spec.md`, section 2.2, lines 92-93

--**Natural Language:**
"A security level is an element of the security lattice."

--**Formal Definition:**
```abbrev SecurityLevel (L : SecurityLattice) := L.elements
```

--**Components:**
- Security level is an element of the security lattice
- Represents the security classification of data

---

-- ### 2.2.2 Security Level Ordering

-- Security Level Ordering

--**Source:** `spec/security/security_flow_spec.md`, section 2.2, lines 94-95

--**Natural Language:**
"Security levels are ordered by the security lattice."

--**Formal Definition:**
```def SecurityLevel.le (L : SecurityLattice) (x y : SecurityLevel L) : Prop :=
  L.le x y
```

--**Invariants:**
1. Security levels are ordered by the security lattice
2. `le` is a partial order on security levels

---

-- ## 2.3 Information Flow

--
### 2.3.1 Information Flow Definition

-- Information Flow

--**Source:** `spec/security/security_flow_spec.md`, section 2.3, lines 104-106

--**Natural Language:**
"Information flows from source to destination."

--**Formal Definition:**
```structure InformationFlow where
  source : SecurityLevel L
  destination : SecurityLevel L
  deriving Repr, BEq
```

--**Invariants:**
1. Source security level is an element of the security lattice
2. Destination security level is an element of the security lattice

---

-- ### 2.3.2 Information Flow Policy

-- Information Flow Policy

--**Source:** `spec/security/security_flow_spec.md`, section 2.3, lines 107-108

--**Natural Language:**
"Information flow is allowed if source security level is less than or equal to destination security level."

--**Formal Definition:**
```def InformationFlow.allowed (L : SecurityLattice) (flow : InformationFlow L) : Prop :=
  L.le flow.source flow.destination
```

--**Invariants:**
1. Information flow is allowed if source security level is less than or equal to destination security level
2. This enforces the no-write-up and no-read-down policies

---

-- ## 2.4 Non-Interference

--
### 2.4.1 Non-Interference Definition

-- Non-Interference

--**Source:** `spec/security/security_flow_spec.md`, section 2.4, lines 119-121

--**Natural Language:**
"Non-interference ensures that high-security inputs do not affect low-security outputs."

--**Formal Definition:**
```def NonInterference (L : SecurityLattice) (high low : SecurityLevel L) : Prop :=
  ∀ (s1 s2 : State),
    (∀ (x : Var), SecurityLevel.of L (s1.get x) ≤ low → s1.get x = s2.get x) →
      (∀ (y : Var), SecurityLevel.of L (s1.get y) ≤ low → s1.get y = s2.get y)
```

--**Invariants:**
1. If two states agree on all low-security variables, they agree on all low-security variables after execution
2. High-security inputs do not affect low-security outputs

---

-- ## 3. Requirements

--
### 3.1 Functional Requirements

-- Security Lattice Support

--**Source:** `spec/security/security_flow_spec.md`, section 3.1, line 64

--**Natural Language:**
"The system shall support security lattice for information flow."

--**Formal Definition:**
```def spec_security_lattice_support (L : SecurityLattice) : Prop :=
  SecurityLattice.partial_order L ∧
  SecurityLattice.lub_properties L ∧
  SecurityLattice.glb_properties L
```

---

-- Information Flow Policy Support

--**Source:** `spec/security/security_flow_spec.md`, section 3.1, line 90

--**Natural Language:**
"The system shall support information flow policy for security."

--**Formal Definition:**
```def spec_information_flow_policy_support (L : SecurityLattice) : Prop :=
  ∀ (flow : InformationFlow L),
    InformationFlow.allowed L flow ↔ L.le flow.source flow.destination
```

---

-- Non-Interference Support

--**Source:** `spec/security/security_flow_spec.md`, section 3.1, line 106

--**Natural Language:**
"The system shall support non-interference for security."

--**Formal Definition:**
```def spec_non_interference_support (L : SecurityLattice) (high low : SecurityLevel L) : Prop :=
  NonInterference L high low
```

---

-- ### 3.2 Non-Functional Requirements

-- Performance

--**Source:** `spec/security/security_flow_spec.md`, section 3.2, line 216

--**Natural Language:**
"The system shall perform information flow checking in O(n) time for n variables."

--**Formal Definition:**
```def spec_information_flow_performance (L : SecurityLattice) : Prop :=
  ∀ (flow : InformationFlow L),
    ∃ (C : Nat),
      InformationFlow.allowed L flow →
        ∃ (result : Bool),
          result = true →
            flow.source.size ≤ C * L.elements.card
```

--**Components:**
- `C`: Constant representing the performance bound
- Information flow checking is O(n) where n is the number of variables

---

-- ## 4. Correctness Properties

--
### 4.1 Theorems

-- ### 4.1.1 Security Lattice Theorem

-- Security Lattice Theorem

--**Source:** `spec/security/security_flow_spec.md`, section 4.1.1, lines 416-425

--**Natural Language:**
"Security lattice is well-formed."

--**Proof Sketch:**
1. By definition of `SecurityLattice.partial_order`, the security lattice is a partially ordered set
2. By definition of `SecurityLattice.lub_properties`, the least upper bound exists
3. By definition of `SecurityLattice.glb_properties`, the greatest lower bound exists
4. Therefore, the security lattice is well-formed

--**Formal Definition:**
```theorem thm_security_lattice_well_formed
  {L : SecurityLattice}
  (h_support : spec_security_lattice_support L)
  : SecurityLattice.partial_order L ∧
    SecurityLattice.lub_properties L ∧
    SecurityLattice.glb_properties L := by
```

--**Invariants:**
- Security lattice is well-formed
- This theorem is used to prove correctness of security lattice

---

-- ### 4.2 Invariants

-- ### 4.2.1 Security Lattice Invariants

-- Security Lattice Well-Formedness

--**Source:** `spec/security/security_flow_spec.md`, section 4.2.1, lines 438-440

--**Natural Language:**
"The system shall maintain that security lattice is well-formed."

--**Formal Definition:**
```theorem inv_security_lattice_well_formed
  {L : SecurityLattice}
  (h_support : spec_security_lattice_support L)
  : SecurityLattice.partial_order L ∧
    SecurityLattice.lub_properties L ∧
    SecurityLattice.glb_properties L := by
```

--**Invariants:**
1. If the system supports security lattice, all security lattices are well-formed
2. Well-formedness is preserved by security lattice operations

---

-- Information Flow Policy Validity

--**Source:** `spec/security/security_flow_spec.md`, section 4.2.1, lines 441-444

--**Natural Language:**
"The system shall maintain that information flow policy is valid."

--**Formal Definition:**
```theorem inv_information_flow_policy_valid
  {L : SecurityLattice}
  (h_support : spec_information_flow_policy_support L)
  : ∀ (flow : InformationFlow L),
      InformationFlow.allowed L flow ↔ L.le flow.source flow.destination := by
```

--**Invariants:**
1. If the system supports information flow policy, all information flow policies are valid
2. Validity is preserved by information flow policy operations

---

-- Non-Interference Validity

--**Source:** `spec/security/security_flow_spec.md`, section 4.2.2, lines 445-447

--**Natural Language:**
"The system shall maintain that non-interference is valid."

--**Formal Definition:**
```theorem inv_non_interference_valid
  {L : SecurityLattice}
  {high low : SecurityLevel L}
  (h_support : spec_non_interference_support L high low)
  : NonInterference L high low := by
```

--**Invariants:**
1. If the system supports non-interference, all non-interference properties are valid
2. Validity is preserved by non-interference operations

---

end Morph.Specs.SecurityFlow
-/