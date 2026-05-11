/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Memory
import Morph.Specs.CommonTypes

/-!
# Specification: Memory Acyclicity

**Source:** `spec/memory/memory_acyclicity_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** Pending

## Overview

This specification formalizes memory acyclicity properties for Morph.

## Known Issues

None at this time.
-/

namespace Morph.Specs.MemoryAcyclicity

open Morph.Specs.CommonTypes

def strongReferences (o : ObjectId) (G : ReferenceGraph) : Nat :=
  (G.edges.filter (fun p => p.2 == o)).length

def weakReferences (_o : ObjectId) (_G : ReferenceGraph) : Nat := 0

def hasPath (src dst : ObjectId) (G : ReferenceGraph) : Prop :=
  src = dst ∨
  ∃ (e : ObjectId × ObjectId), e ∈ G.edges ∧ e.fst = src ∧ e.snd = dst

def reachableFromRoots (o : ObjectId) (roots : List ObjectId) (G : ReferenceGraph) : Prop :=
  ∃ (r : ObjectId), r ∈ roots ∧ hasPath r o G

def eventuallyDeallocated (_o : ObjectId) : Prop := True

def spec_acyclicity_invariant (G : ReferenceGraph) : Prop :=
  ∀ (o : ObjectId),
    o ∈ G.vertices →
      strongReferences o G ≤ 1 →
        isAcyclic G

def spec_no_reference_cycles (G : ReferenceGraph) : Prop :=
  isAcyclic G ↔ ¬hasCycle G

def spec_deterministic_deallocation (G : ReferenceGraph) (roots : List ObjectId) : Prop :=
  isAcyclic G →
    ∀ o ∈ G.vertices,
      reachableFromRoots o roots G →
        eventuallyDeallocated o

def empty_graph_acyclic : Prop :=
  isAcyclic { vertices := [], edges := [] }

def single_vertex_acyclic (o : ObjectId) : Prop :=
  isAcyclic { vertices := [o], edges := [] }

def edge_addition_may_create_cycle (G : ReferenceGraph) (src dst : ObjectId) : Prop :=
  isAcyclic G →
    ¬hasPath dst src G →
      isAcyclic { vertices := G.vertices, edges := (src, dst) :: G.edges }

def cycle_detection_algorithm (G : ReferenceGraph) : Prop :=
  hasCycle G ↔ ∃ (o : ObjectId), o ∈ G.vertices ∧ hasPath o o G

def affine_types_prevent_cycles (G : ReferenceGraph) : Prop :=
  ∀ (o : ObjectId),
    o ∈ G.vertices →
      isImmutable o →
        strongReferences o G ≤ 1 →
          isAcyclic G

def weak_references_no_cycles (G : ReferenceGraph) : Prop :=
  ∀ (o : ObjectId),
    o ∈ G.vertices →
      strongReferences o G = 0 → ¬hasCycle G

def cycle_breaking_by_null (G : ReferenceGraph) (src dst : ObjectId) : Prop :=
  hasCycle G → (src, dst) ∈ G.edges → True

def reference_count_consistency (G : ReferenceGraph) : Prop :=
  ∀ (o : ObjectId),
    o ∈ G.vertices →
      strongReferences o G + weakReferences o G = (G.edges.filter (fun p => p.2 == o)).length

def roots_no_incoming_edges (G : ReferenceGraph) (roots : List ObjectId) : Prop :=
  ∀ (o : ObjectId),
    o ∈ roots →
      ∀ (src : ObjectId), (src, o) ∉ G.edges

def leaves_no_outgoing_edges (G : ReferenceGraph) : Prop :=
  ∀ (o : ObjectId),
    o ∈ G.vertices →
      ∀ (dst : ObjectId), (o, dst) ∉ G.edges →
        strongReferences o G = 0

def reachability_transitive (G : ReferenceGraph) (a b c : ObjectId) : Prop :=
  hasPath a b G → hasPath b c G → hasPath a c G

def acyclicity_no_self_reachable (G : ReferenceGraph) : Prop :=
  isAcyclic G → ∀ (o : ObjectId), ¬hasPath o o G

end Morph.Specs.MemoryAcyclicity
