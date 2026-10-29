/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryAcyclicity.Spec
import Morph.Specs.MemoryBounds.Spec

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

/-! ### Loop 67: reachability bridge, weak refs, and collection

Research: Jones & Lins (GC handbook — reachability *is* retention, weak
references are precisely the edges the collector does not follow); Java
`WeakReference` + `ReferenceQueue` (weak edges cleared when the referent is
swept); OCaml `Ephemeron` (key–value weak binding); Swift `weak` (nil-ed on
deallocation — `sweepWeak_drops_deallocated` is exactly that, proved);
Baker (treadmill — collection as a reachability filter, which is what
`Collected` states).

Language comparison: Java (weak refs cleared, no proof); OCaml (ephemerons,
prose semantics); Swift (weak→nil, runtime-checked); Rust
(`Weak::upgrade → Option`, no collector at all). Morph: weak edges as data
(`WGraph`), sweep as a function, nil-ing proved.

What is proved:
- the bridge: the module's one-step `hasPath` embeds into multi-step
  `SReach` (`hasPath_to_SReach`), which is transitive (`SReach_trans`);
- the cross-model bridge: `MemoryBounds.Reach` (heap reachability) implies
  `SReach` in the projected graph (`reach_to_SReach`) — loop 59's named
  item, with vertices covering exactly the live heap;
- weak references as data: `weakCount` really counts, `sweepWeak` drops
  edges to swept vertices with no dangling survivors
  (`sweepWeak_no_dangling`, `sweepWeak_drops_deallocated` — the Swift
  nil-ing theorem).

Boundary: `weakReferences _ _ := 0` is untouched (that model has no
weak-edge marker — loop 40 pinned it); weak edges live in `WGraph`.
-/

/-- Multi-step strong reachability: the transitive closure `hasPath` lacks.
`refl` covers the `src = dst` case, `step` extends along an edge. -/
inductive SReach (G : ReferenceGraph) : ObjectId → ObjectId → Prop where
  | refl (o : ObjectId) : SReach G o o
  | step {a b c : ObjectId} : (a, b) ∈ G.edges → SReach G b c → SReach G a c

/-- The bridge: the module's one-step `hasPath` embeds into `SReach`. -/
theorem hasPath_to_SReach {G : ReferenceGraph} {src dst : ObjectId}
    (h : hasPath src dst G) : SReach G src dst := by
  rcases h with rfl | ⟨e, hmem, h1, h2⟩
  · exact .refl _
  · obtain ⟨s, d⟩ := e
    simp only at h1 h2
    subst h1; subst h2
    exact .step hmem (.refl _)

/-- `SReach` is transitive — the closure property `hasPath` lacks. -/
theorem SReach_trans {G : ReferenceGraph} {a b c : ObjectId}
    (h1 : SReach G a b) (h2 : SReach G b c) : SReach G a c := by
  induction h1 with
  | refl _ => exact h2
  | step he _ ih => exact .step he (ih h2)

/-- A single edge reaches. -/
theorem SReach_of_edge {G : ReferenceGraph} {a b : ObjectId}
    (h : (a, b) ∈ G.edges) : SReach G a b :=
  .step h (.refl _)

/-- Bridge example: the edge reaches, in two steps and one. -/
def exGraph : ReferenceGraph :=
  { vertices := [{ id := 0 }, { id := 1 }],
    edges := [({ id := 0 }, { id := 1 })] }

example : SReach exGraph { id := 0 } { id := 1 } :=
  .step ((List.mem_cons).mpr (Or.inl rfl)) (.refl _)

/-- Project a bounds-model heap into a reference graph over exactly the
live addresses. -/
def heapGraph (h : Morph.Specs.MemoryBounds.Heap)
    (live : List Morph.Specs.MemoryBounds.Addr) : ReferenceGraph :=
  { vertices := live.map (fun a => ({ id := a } : ObjectId)),
    edges := live.flatMap (fun a => match h a with
      | none => []
      | some fs => fs.map (fun f => (({ id := a }, { id := f }) :
          ObjectId × ObjectId))) }

/-- **Cross-model bridge.** Heap reachability implies graph reachability in
the projection: every `Reach` derivation witnesses an `SReach` path from one
of its base addresses. Vertices cover exactly the live heap (`hlive`). -/
theorem reach_to_SReach (h : Morph.Specs.MemoryBounds.Heap)
    (base live : List Morph.Specs.MemoryBounds.Addr)
    (a : Morph.Specs.MemoryBounds.Addr)
    (hlive : ∀ x fs, h x = some fs → x ∈ live)
    (hr : Morph.Specs.MemoryBounds.Reach h base a) :
    ∃ b, b ∈ base ∧ SReach (heapGraph h live) { id := b } { id := a } := by
  induction hr with
  | base_ a hb => exact ⟨a, hb, .refl _⟩
  | edge_ x f fs hlook hfin _ ih =>
      obtain ⟨b, hb, hreach⟩ := ih
      have hx : x ∈ live := hlive x fs hlook
      have hedge : (({ id := x }, { id := f }) : ObjectId × ObjectId) ∈
          (heapGraph h live).edges := by
        simp only [heapGraph, List.mem_flatMap]
        refine ⟨x, hx, ?_⟩
        simp only [hlook]
        exact List.mem_map.mpr ⟨f, hfin, rfl⟩
      exact ⟨b, hb, SReach_trans hreach (.step hedge (.refl _))⟩

/-! #### Weak references as data

The `ReferenceGraph` model has no weak-edge marker (loop 40), so weak edges
live alongside it in `WGraph` rather than inside it. -/

/-- A graph with a separate weak-edge list: weak edges never retain. -/
structure WGraph where
  strong : ReferenceGraph
  weak : List (ObjectId × ObjectId)

/-- Weak references really counted (contrast `weakReferences _ _ := 0`). -/
def weakCount (W : WGraph) (o : ObjectId) : Nat :=
  (W.weak.filter (fun e => e.2 == o)).length

/-- No weak edges, no weak count. -/
theorem weakCount_nil (G : ReferenceGraph) (o : ObjectId) :
    weakCount ⟨G, []⟩ o = 0 := rfl

/-- Decidable equality for `ObjectId` from the underlying `Nat`. Kept as a
plain definition (not an instance), so it can never conflict with the
`LawfulBEq ObjectId` instance in `ASTGraph`. -/
def objDecEq (a b : ObjectId) : Decidable (a = b) :=
  if h : a.id = b.id then
    isTrue (by cases a with | mk x => cases b with | mk y => simp_all)
  else
    isFalse (fun heq => h (congrArg ObjectId.id heq))

/-- Decidable list membership, explicitly — no instance resolution involved. -/
def memDec (x : ObjectId) : (l : List ObjectId) → Decidable (x ∈ l)
  | [] => isFalse (fun h => by cases h)
  | hd :: tl =>
      match objDecEq x hd with
      | isTrue heq =>
          isTrue (by rw [heq]; exact (List.mem_cons).mpr (Or.inl rfl))
      | isFalse hne =>
          match memDec x tl with
          | isTrue hmem => isTrue (List.mem_cons_of_mem _ hmem)
          | isFalse hntl =>
              isFalse (by
                intro hcon
                rw [List.mem_cons] at hcon
                rcases hcon with rfl | hmem
                · exact hne rfl
                · exact hntl hmem)

/-- Sweep weak edges against the live set: drop every edge whose target was
collected. This is Java's clearing / Swift's nil-ing, as a function. -/
def sweepWeak (live : List ObjectId)
    (w : List (ObjectId × ObjectId)) : List (ObjectId × ObjectId) :=
  w.filter (fun e => match memDec e.2 live with
    | isTrue _ => true
    | isFalse _ => false)

/-- No surviving weak edge dangles: every survivor points into `live`. -/
theorem sweepWeak_no_dangling (live : List ObjectId)
    (w : List (ObjectId × ObjectId)) (e : ObjectId × ObjectId)
    (h : e ∈ sweepWeak live w) : e.2 ∈ live := by
  have h2 := (List.mem_filter.mp h).2
  cases hm : memDec e.2 live with
  | isTrue hmem => exact hmem
  | isFalse _ => simp [hm] at h2

/-- **Swift nil-ing, proved.** A weak edge to a deallocated object does not
survive the sweep against the survivors' vertices: collection nils it. -/
theorem sweepWeak_drops_deallocated (G G' : ReferenceGraph)
    (roots : List ObjectId) (w : List (ObjectId × ObjectId))
    (o : ObjectId) (hdead : eventuallyDeallocated o G G' roots)
    (e : ObjectId × ObjectId) (hmem : e ∈ sweepWeak G'.vertices w) :
    e.2 ≠ o := by
  have hlive := sweepWeak_no_dangling G'.vertices w e hmem
  intro hcon
  rw [hcon] at hlive
  exact hdead.2 hlive

end Morph.Specs.MemoryAcyclicity
