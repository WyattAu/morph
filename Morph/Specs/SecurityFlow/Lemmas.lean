/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.SecurityFlow.Spec

namespace Morph.Specs.SecurityFlow

/-!
## Lemmas

Lemmas and auxiliary results for the SecurityFlow specification.
-/

/-- A lattice with full support has partial order. -/
theorem support_implies_partial_order
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.partial_order L :=
  h.left

/-- A lattice with full support has lub properties. -/
theorem support_implies_lub_properties
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.lub_properties L :=
  h.right.left

/-- A lattice with full support has glb properties. -/
theorem support_implies_glb_properties
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.glb_properties L :=
  h.right.right

/-- InformationFlow.allowed is reflexive when source equals destination. -/
theorem allowed_reflexive
    {L : SecurityLattice}
    (h_po : SecurityLattice.partial_order L)
    (x : SecurityLevel L)
    : InformationFlow.allowed L { source := x, destination := x } :=
  (h_po x).left

/-- If InformationFlow.allowed holds then L.le holds (forward direction). -/
theorem allowed_iff_le_forward
    {L : SecurityLattice}
    (flow : InformationFlow L)
    : InformationFlow.allowed L flow → L.le flow.source flow.destination :=
  id

/-- If L.le holds then InformationFlow.allowed holds (backward direction). -/
theorem allowed_iff_le_backward
    {L : SecurityLattice}
    (flow : InformationFlow L)
    : L.le flow.source flow.destination → InformationFlow.allowed L flow :=
  fun h => h

/-- The flow policy iff is a tautology: allowed ↔ le is definitionally true. -/
theorem flow_policy_iff_tautology
    (L : SecurityLattice)
    (flow : InformationFlow L)
    : InformationFlow.allowed L flow ↔ L.le flow.source flow.destination :=
  Iff.rfl

/-- NonInterference support is exactly NonInterference. -/
theorem non_interference_support_is_noninterference
    {L : SecurityLattice}
    {high low : SecurityLevel L}
    : spec_non_interference_support L high low ↔ NonInterference L high low :=
  Iff.rfl

/-- Well-formedness theorem and its invariant form are definitionally equal. -/
theorem well_formed_eq_inv
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : thm_security_lattice_well_formed h = inv_security_lattice_well_formed h :=
  rfl

/-- Full support implies partial order via the well-formedness theorem. -/
theorem well_formed_gives_partial_order
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.partial_order L :=
  (thm_security_lattice_well_formed h).left

/-- Full support implies lub properties via the well-formedness theorem. -/
theorem well_formed_gives_lub
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.lub_properties L :=
  (thm_security_lattice_well_formed h).right.left

/-- Full support implies glb properties via the well-formedness theorem. -/
theorem well_formed_gives_glb
    {L : SecurityLattice}
    (h : spec_security_lattice_support L)
    : SecurityLattice.glb_properties L :=
  (thm_security_lattice_well_formed h).right.right

/-- The invariant for flow policy validity is definitionally the hypothesis. -/
theorem inv_flow_policy_eq_hypothesis
    {L : SecurityLattice}
    (h : spec_information_flow_policy_support L)
    : inv_information_flow_policy_valid h = h :=
  rfl

/-- The invariant for non-interference is definitionally the hypothesis. -/
theorem inv_non_interference_eq_hypothesis
    {L : SecurityLattice}
    {high low : SecurityLevel L}
    (h : spec_non_interference_support L high low)
    : inv_non_interference_valid h = h :=
  rfl

end Morph.Specs.SecurityFlow
