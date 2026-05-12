/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.SecurityOCap.Spec

namespace Morph.Specs.SecurityOCap

/-!
## Examples

Concrete examples demonstrating the SecurityOCap specification.
-/

def nodeAlice : Node := Node.mk "alice"
def nodeBob : Node := Node.mk "bob"
def nodeResource : Node := Node.mk "resource"

/-- A capability graph: Alice → Bob → Resource. -/
def capGraph : AccessGraph := {
  nodes := [nodeAlice, nodeBob, nodeResource],
  edges := [
    { source := nodeAlice, target := nodeBob },
    { source := nodeBob, target := nodeResource }
  ]
}

example : Path.exists capGraph nodeAlice nodeAlice := by
  unfold Path.exists; left; rfl

example : Path.exists capGraph nodeBob nodeBob := by
  unfold Path.exists; left; rfl

example : connectivity_rule capGraph nodeAlice nodeAlice "read" := by
  unfold connectivity_rule; left; rfl

example : Allowed capGraph nodeAlice nodeAlice "write" := by
  unfold Allowed Path.exists; left; rfl

example : AccessGraph.well_formed capGraph := trivial

example : authority_transfer capGraph nodeAlice nodeBob nodeBob := by
  unfold authority_transfer
  exists { source := nodeAlice, target := nodeBob }
  intro _; trivial

/-- Revocation: remove Bob→Resource edge. -/
def capGraphRevoked : AccessGraph := {
  nodes := [nodeAlice, nodeBob, nodeResource],
  edges := [{ source := nodeAlice, target := nodeBob }]
}

example : Path.exists capGraphRevoked nodeBob nodeBob := by
  unfold Path.exists; left; rfl

/-- After revocation, Alice can still reach Bob via the remaining edge. -/
example : Path.exists capGraphRevoked nodeAlice nodeBob := by
  unfold Path.exists capGraphRevoked
  right
  exists { source := nodeAlice, target := nodeBob }
  exact ⟨.head [], ⟨rfl, rfl⟩⟩

example : AccessGraph.well_formed { nodes := [], edges := [] } := trivial

/-- No edge can be in an empty list. -/
example : AccessGraph.edges_valid { nodes := [], edges := [] } := by
  intro e h_mem; nomatch h_mem

/-- A graph with no edges has no global ambient authority:
    no single node has edges to all others because there are no edges at all. -/
example : no_global_ambient_authority
    { nodes := [nodeAlice], edges := [] } := by
  unfold no_global_ambient_authority
  intro ⟨global_node, h⟩
  have h_alice : nodeAlice ∈ [nodeAlice] := .head []
  have := h nodeAlice h_alice
  obtain ⟨e, h_e_mem, _⟩ := this
  nomatch h_e_mem

end Morph.Specs.SecurityOCap
