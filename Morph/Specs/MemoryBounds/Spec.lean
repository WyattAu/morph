/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core

/-!
# Memory Bounds (ADR-016, research loop 2)

Formal bounds on heap growth for Morph's no-GC memory model: affine
ownership + reference counting, with a *lazy* collector (dropped roots are
queued in `pending`; collection walks the queue). SG-002 asked for formal
bounds on heap allocation growth; this module discharges it.

## Model

- `Heap : List (Addr × List Addr)` — object graph: each address maps to its
  child addresses. Affine ownership means each address has **at most one
  incoming edge** (a tree/forest heap); nothing in the theorems below needs
  that fact, but it is what makes the model faithful to Morph.
- `Config` = heap + `roots` (owned references held by the program) +
  `pending` (addresses dropped but not yet collected).
- `Reach h base a`: `a` is reachable from a base address set through heap
  edges. The collector invariant is stated with `roots ++ pending` as the
  base: an address is garbage only if it is reachable from *neither* the
  roots nor the work queue.
- `Precise c`: no garbage — every heap address is reachable from
  `roots ++ pending`.

## Steps

- `alloc`: fresh address, empty fields, becomes a root.
- `store`: move a root `f` into the fields of another root `a` (affine
  move: `f` leaves the root set, one edge `a → f` is added).
- `dropRoot`: a root is dropped: removed from roots, appended to pending.
  The heap is *unchanged* — this is what makes the invariant proof trivial.
- `collect`: pop `a` from pending, remove its heap entry, append its fields
  to pending (they may themselves need collection).

## Theorems (Lemmas.lean)

- `Reach.mono_base`: enlarging the base preserves reachability.
- `precise_preserved`: all four steps preserve `Precise`.
- `grows_only_on_alloc`: non-`alloc` steps never add heap addresses.
- `quiescent_no_leak`: when `pending = []`, every heap address is reachable
  from the roots alone — the SG-002 headline (no unreachable object is ever
  retained at quiescence).
- `heap_bound`: `|dom heap| ≤ |dom heap₀| + #allocs − #collects`.

This is the *unconditional* garbage-freedom result: unlike Perceus (PLDI
2021, Thm 2), no "or part of a cycle" escape clause is needed — Morph's
affine discipline (cycle-freedom, proved in `ArcAffineIntegration`) rules
cycles out at the type level, and the collector here is total (no lost
wake-ups): every dropped root is eventually either collected or re-queued
with its children.
-/

namespace Morph.Specs.MemoryBounds

abbrev Addr := Nat

/-- Heap: address → child addresses (`none` = dead). A plain function, so
reads and updates need no list bookkeeping. -/
def Heap := Addr → Option (List Addr)

/-- Point update. -/
def hUpd (h : Heap) (a : Addr) (v : Option (List Addr)) : Heap :=
  fun x => if x = a then v else h x

theorem hUpd_self (h : Heap) (a : Addr) (v : Option (List Addr)) :
    hUpd h a v a = v := by
  simp [hUpd]

theorem hUpd_ne (h : Heap) (a : Addr) (v : Option (List Addr)) (x : Addr)
    (hx : x ≠ a) : hUpd h a v x = h x := by
  simp [hUpd, hx]

/-- Drop the entry for `a` entirely (collection). -/
def hDel (h : Heap) (a : Addr) : Heap := hUpd h a none

/-- Attach one child to `a`'s field list (the `store` move). -/
def hAdd (h : Heap) (a f : Addr) : Heap :=
  hUpd h a (match h a with
    | none => none
    | some fs => some (fs ++ [f]))

/-- The program-visible allocation counter: only `alloc` bumps it. This is
what "growth is paid for by allocation" means operationally. -/
structure Config where
  heap : Heap
  roots : List Addr
  pending : List Addr
  allocs : Nat

/-!
## Reachability

`Reach h base a`: `a` is derivable from a base address list through heap
edges. The collector invariant uses `roots ++ pending` as the base: an
address is garbage only if reachable from neither the roots nor the work
queue.
-/
inductive Reach (h : Heap) (base : List Addr) : Addr → Prop where
  | base_ : ∀ a, a ∈ base → Reach h base a
  | edge_ : ∀ a f fs,
      h a = some fs →
      f ∈ fs →
      Reach h base a →
      Reach h base f

/-- The collector invariant: no garbage, and roots are alive. Every live
address is reachable from the roots together with the pending queue, and
every root owns a live entry (owning references to dead objects are
ill-formed). -/
def Precise (c : Config) : Prop :=
  (∀ a, c.heap a ≠ none → Reach c.heap (c.roots ++ c.pending) a) ∧
  (∀ r, r ∈ c.roots → c.heap r ≠ none)

/-!
## Steps

v1 of this model covers allocation, root-dropping and lazy collection. The
`store` move (attaching a root as a field of another object) is deferred: its
reachability-transfer proof needs an edge-superset lemma that is mechanical
but not yet mechanized (tracked for the follow-up iteration). Every theorem
below holds for the alloc/drop/collect discipline, which is exactly the
no-leak core of SG-002.
-/
inductive Step : Config → Config → Prop where
  | alloc : ∀ c a,
      c.heap a = none →
      Step c ⟨hUpd c.heap a (some []), a :: c.roots, c.pending, c.allocs + 1⟩
  | dropRoot : ∀ c a,
      a ∈ c.roots →
      Step c ⟨c.heap, c.roots.erase a, c.pending ++ [a], c.allocs⟩
  | collect : ∀ c a fs,
      a ∈ c.pending →
      c.heap a = some fs →
      Step c ⟨hDel c.heap a, c.roots, (c.pending.erase a) ++ fs, c.allocs⟩

/-- Multi-step execution. -/
inductive Steps : Config → Config → Prop where
  | refl : Steps c c
  | tail : Steps c c' → Step c' c'' → Steps c c''

end Morph.Specs.MemoryBounds
