/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.SecurityFlow.Spec

namespace Morph.Specs.SecurityFlow

/-!
## Examples

Concrete examples demonstrating the SecurityFlow specification.
-/

/-- True is true. -/
example : True := trivial

/-- SecurityLevel.le is definitionally L.le. -/
example
    (L : SecurityLattice)
    (x y : SecurityLevel L)
    : SecurityLevel.le L x y ↔ L.le x y :=
  Iff.rfl

/-- InformationFlow.allowed is definitionally L.le source destination. -/
example
    (L : SecurityLattice)
    (flow : InformationFlow L)
    : InformationFlow.allowed L flow ↔ L.le flow.source flow.destination :=
  Iff.rfl

/-- The flow policy support iff is definitionally true for any lattice. -/
example
    (L : SecurityLattice)
    (flow : InformationFlow L)
    : (spec_information_flow_policy_support L) →
        (InformationFlow.allowed L flow ↔ L.le flow.source flow.destination) :=
  fun h => by exact h flow

/-- NonInterference support is exactly NonInterference. -/
example
    (L : SecurityLattice)
    (high low : SecurityLevel L)
    : spec_non_interference_support L high low ↔ NonInterference L high low :=
  Iff.rfl

/-- The well-formedness theorem is definitionally its hypothesis. -/
example
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : thm_security_lattice_well_formed h = h :=
  rfl

/-- The invariant well-formedness theorem is definitionally its hypothesis. -/
example
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : inv_security_lattice_well_formed h = h :=
  rfl

/-- The invariant flow policy validity is definitionally its hypothesis. -/
example
    {L : SecurityLattice}
    (h : spec_information_flow_policy_support L)
    : inv_information_flow_policy_valid h = h :=
  rfl

/-- The invariant non-interference validity is definitionally its hypothesis. -/
example
    {L : SecurityLattice}
    {high low : SecurityLevel L}
    (h : spec_non_interference_support L high low)
    : inv_non_interference_valid h = h :=
  rfl

/-- A concrete lattice structure can be constructed (trivial example). -/
example
    : SecurityLattice :=
  {
    elements := Bool
    le := fun x y => ¬x ∨ y
    lub := fun x y => x ∨ y
    glb := fun x y => x ∧ y
  }

/-- The partial order component of support is a projection. -/
example
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.partial_order L :=
  h.left

/-- The lub properties component of support is a projection. -/
example
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.lub_properties L :=
  h.right.left

/-- The glb properties component of support is a projection. -/
example
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.glb_properties L :=
  h.right.right

end Morph.Specs.SecurityFlow
