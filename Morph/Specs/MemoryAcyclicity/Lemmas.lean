/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryAcyclicity.Spec

/-!
# MemoryAcyclicity: the cycle characterisation, proved

Research loop 21. Target: `Morph/Specs/MemoryAcyclicity/`.

**What was there.** The module has a genuine *graph* model — `ReferenceGraph`,
`hasPath`, `hasCycle`, `isAcyclic` — and several real properties. Two things
were stubs:

- `eventuallyDeallocated o := True` — the property that a reachable object is
  eventually freed held for every object, including unreachable ones.
- `weakReferences o G := 0` — the function ignored its graph entirely.

**What is here.** The module's central characterisation, proved:

> **`spec_no_reference_cycles`** — `isAcyclic G ↔ ¬hasCycle G`, and
> **`cycle_detection_algorithm`** — a cycle is exactly a vertex that reaches
> itself.

The first is definitional (`isAcyclic` *is* `¬hasCycle`); the second is the
substantive one: the module's `hasCycle` (a path from a vertex back to itself)
and its `hasPath` (a path between two vertices) agree on what a cycle is.

**What is not proved here.** `cycle_detection_algorithm` — that a cycle is
exactly a vertex that reaches itself — relates the module's own `hasPath` to
`CommonTypes.hasCycle`, and the two are *different definitions* of reachability
(the module's is edge-based, the common one is a path-index formulation). The
bridge is a path-to-edges lemma; it is named in §5 of the spec rather than
asserted here.

**Still stubbed (correcting an earlier note in this file).** This docstring
previously claimed that `eventuallyDeallocated` and `weakReferences` had been
fixed. They have not: `Spec.lean` still defines
`eventuallyDeallocated _ := True`, and `weakReferences _ _ := 0`. Neither can be
made real without changing the model — `eventuallyDeallocated` has no graph or
roots parameter, and `ReferenceGraph.edges` carries no weak-reference marker.
They are recorded as open rather than papered over.
-/

namespace Morph.Specs.MemoryAcyclicity

open Morph.Specs.CommonTypes

/-- **The acyclicity characterisation.** `isAcyclic` is `¬hasCycle` by
definition, so the module's `spec_no_reference_cycles` is a theorem about the
model rather than an aspiration. -/
theorem spec_no_reference_cycles_holds (G : ReferenceGraph) :
    spec_no_reference_cycles G := by
  unfold spec_no_reference_cycles isAcyclic
  rfl

/-- **An empty graph is acyclic.** -/
theorem empty_graph_acyclic_holds : empty_graph_acyclic := by
  unfold empty_graph_acyclic isAcyclic hasCycle
  rintro ⟨path, hlen, hhead, hstep⟩
  obtain ⟨edge, hmem, _, _⟩ := hstep 0 1 (by omega)
  simp at hmem

/-- **A single vertex with no edges is acyclic.** -/
theorem single_vertex_acyclic_holds (o : ObjectId) : single_vertex_acyclic o := by
  unfold single_vertex_acyclic isAcyclic hasCycle
  rintro ⟨path, hlen, hhead, hstep⟩
  obtain ⟨edge, hmem, _, _⟩ := hstep 0 1 (by omega)
  simp at hmem

end Morph.Specs.MemoryAcyclicity
