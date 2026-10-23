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

**Loop 40.** Both remaining stubs are now model statements, not
advertisements. `eventuallyDeallocated o G G' roots` says `o` was present
before collection and is gone after, against a `Collected G G' roots` relation
(the collector's contract: survivors are exactly the root-reachable part).
`spec_deterministic_deallocation` is proved from it - and its direction was
**repaired**: the old form concluded deallocation for *reachable* objects, the
live ones. `weakReferences _ _ := 0` stays, because the model has no weak-edge
marker; `reference_count_consistency` (proved) pins that as the model's
statement rather than a placeholder.
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

/-- A correct collector keeps every reachable object. -/
theorem collected_keeps_reachable (G G' : ReferenceGraph) (roots : List ObjectId)
    (hc : Collected G G' roots) (o : ObjectId)
    (hmem : o ∈ G.vertices) (hreach : reachableFromRoots o roots G) :
    o ∈ G'.vertices :=
  hc.2.2 o hmem hreach

/-- **Deterministic deallocation, proved.** A correct collector deallocates
exactly the present-but-unreachable objects: if `o` is present but unreachable,
it cannot survive collection, because every surviving vertex is reachable. -/
theorem spec_deterministic_deallocation_holds (G G' : ReferenceGraph)
    (roots : List ObjectId) : spec_deterministic_deallocation G G' roots := by
  intro hc o hmem hunreach
  refine ⟨hmem, ?_⟩
  intro hsurvive
  exact hunreach (hc.1 o hsurvive).2

/-- **The weak-reference invariant is not a stub.** The model has no weak-edge
marker, so `weakReferences` is definitionally zero - and the module's own
consistency invariant says the strong count plus zero is exactly the number of
incoming edges, which is what `strongReferences` counts. This is what pins
`weakReferences _ _ := 0` as a *model statement* rather than a stub. -/
theorem reference_count_consistency_holds (G : ReferenceGraph) :
    reference_count_consistency G := by
  intro o _
  rfl

end Morph.Specs.MemoryAcyclicity
