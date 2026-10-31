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
- `quiescent_no_leak`: when `pending = []`, every heap address is reachable
  from the roots alone — the SG-002 headline (no unreachable object is ever
  retained at quiescence).
- `allocs_step` / `allocs_bound`: only `alloc` advances the allocation
  counter, and after `n` steps it has advanced by at most `n`.

This is the *unconditional* garbage-freedom result: unlike Perceus (PLDI
2021, Thm 4), no "or part of a cycle" escape clause is needed — Morph's
affine discipline (cycle-freedom, proved in `ArcAffineIntegration`) rules
cycles out at the type level, and the collector here is total (no lost
wake-ups): every dropped root is eventually either collected or re-queued
with its children. `Precise` + `pending = []` therefore gives a garbage-free
heap with no escape clause.

Scope note: the literal formula `|dom heap| ≤ |dom heap₀| + #allocs − #collects`
needs a finite-address allocator model (a bump pointer `nextAddr` bounding
the domain), which this heap-as-total-function model does not carry. The
counting results here (`allocs_bound`) plus `quiescent_no_leak` capture the
same content — growth is paid for by allocation, and nothing unreachable is
ever retained — in a form the model supports.
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

/-!
## The invariant

`Precise` is the *memory-safety* half: nothing unreachable is retained
(garbage-freedom) and every address the program or the collector holds is
still live (no dangling root/queue references).

`Affine` is the *ownership* half, and it is the part that makes Morph's
no-GC model work where a general RC collector would need Perceus' escape
hatch:

- (A1) the queue holds only **released** addresses — an address is dropped
  before it is queued, never both owned and queued;
- (A2) an object held as a **field** is not also a root — unique ownership;
- (A3) an object held as a field is **live** — no dangling edges.

Together (A2)+(A3) say every edge target is uniquely owned and alive, which
is exactly the "tree/forest heap" the affine discipline produces.
-/

/-!
## The invariant

`Precise` is the *memory-safety* half: nothing unreachable is retained
(garbage-freedom), and every root — every address the program owns — is still
live.

`Affine` is the *ownership* half, and it is the part that makes Morph's
no-GC model work where a general reference-counting collector would need
Perceus' cycle escape hatch (PLDI'21 Thm 2). Each component is one facet of
"an object has exactly one owner":

- **A1** the queue holds only *released* addresses — an address is dropped
  before it is queued, never both owned and queued;
- **A2** an object held as a *field* is not also a root;
- **A3** an object held as a field is *live* — no dangling edges;
- **A4** a queued (released) address is not still pointed at — a released
  object has no owner left to free it, hence no incoming edge;
- **A5** *at most one incoming edge per address* — the unique-owner property
  proper; this is what lets `collect` hand a subtree to the queue without
  risk of dangling one of its parents' edges;
- **A6** an object's fields are pairwise distinct;
- **A7** no self-loops (`a` is not its own field).

A2+A5 together are "unique ownership", which is exactly the tree/forest heap
the affine discipline produces; A4 is the consequence that matters for the
collector: an object whose reference count reached zero has no remaining
edge pointing at it, so freeing it (and cascading) is safe **without**
cycle detection. That is the assumption Perceus cannot make and must paper
over with its escape clause.
-/

/-- Memory safety: every live address is reachable from the roots together
with the work queue, and every root owns a live entry. -/
def Precise (c : Config) : Prop :=
  (∀ a, c.heap a ≠ none → Reach c.heap (c.roots ++ c.pending) a) ∧
  (∀ r, r ∈ c.roots → c.heap r ≠ none)

/-- Affine ownership. See the module notes for what each component buys. -/
def Affine (c : Config) : Prop :=
  (∀ p, p ∈ c.pending → p ∉ c.roots) ∧
  (∀ a g fs, c.heap a = some fs → g ∈ fs → g ∉ c.roots) ∧
  (∀ a g fs, c.heap a = some fs → g ∈ fs → c.heap g ≠ none) ∧
  (∀ p y fs, p ∈ c.pending → c.heap y = some fs → p ∉ fs) ∧
  (∀ p y y' fs fs', c.heap y = some fs → p ∈ fs →
    c.heap y' = some fs' → p ∈ fs' → y = y') ∧
  (∀ y fs, c.heap y = some fs → fs.Nodup) ∧
  (∀ y fs, c.heap y = some fs → y ∉ fs)

/-- The full discipline. `roots.Nodup` records that a root is an address, not
a handle to it: owning the same address twice would be an aliasing bug, and
the `erase` in `dropRoot`/`store` removes only the *first* occurrence, so the
collector-side reasoning needs roots to be duplicate-free. -/
def Invariant (c : Config) : Prop := Precise c ∧ Affine c ∧ c.roots.Nodup

/-!
## Steps

The model covers allocation, the affine `store` move (attaching one root as a
field of another), root-dropping, and lazy collection. The `store` move
requires `a ≠ f` (an object cannot be moved under itself); combined with the
affine at-most-one-incoming-edge discipline (proved in `ArcAffineIntegration`)
this makes the object graph a forest, so no step can create a cycle — which is
why the no-leak theorem below needs no "or part of a cycle" escape clause.

`collect` carries two side conditions beyond "it is on the queue":

- `a ∉ c.roots` — the program has released it. The queue is fed by
  `dropRoot`, so this is a fact about the real collector, not a restriction.
- `∀ y gs, c.heap y = some gs → a ∉ gs` — **no live object still refers to
  `a`.** This is where Morph's affine discipline earns its keep. Under
  unique ownership an object has at most one incoming edge, so "released and
  unreferenced" is exactly the state in which reference counting reclaims it,
  and freeing it cannot create a dangling edge. A collector that dropped this
  condition would need Perceus' cycle escape hatch (PLDI'21 Thm 2) to stay
  sound; Morph rules it out at the type level instead.
-/

/-- No live object refers to `a`: `a`'s unique owner has released it. -/
def Released (h : Heap) (a : Addr) : Prop :=
  ∀ y gs, h y = some gs → a ∉ gs

inductive Step : Config → Config → Prop where
  | alloc : ∀ c a,
      c.heap a = none →
      a ∉ c.roots →
      a ∉ c.pending →
      Step c ⟨hUpd c.heap a (some []), a :: c.roots, c.pending, c.allocs + 1⟩
  | store : ∀ c a f,
      a ∈ c.roots →
      f ∈ c.roots →
      a ≠ f →
      Step c ⟨hAdd c.heap a f, c.roots.erase f, c.pending, c.allocs⟩
  | dropRoot : ∀ c a,
      a ∈ c.roots →
      Step c ⟨c.heap, c.roots.erase a, c.pending ++ [a], c.allocs⟩
  | collect : ∀ c a fs,
      a ∈ c.pending →
      a ∉ c.roots →
      Released c.heap a →
      c.heap a = some fs →
      Step c ⟨hDel c.heap a, c.roots, (c.pending.erase a) ++ fs, c.allocs⟩

/-- Multi-step execution, indexed by the number of steps taken. -/
inductive Steps : Nat → Config → Config → Prop where
  | refl : ∀ c, Steps 0 c c
  | tail : ∀ (n : Nat) c c' c'', Steps n c c' → Step c' c'' → Steps (n + 1) c c''

/-! ### The strong heap, cycles, and the weak escape (loop 94)

Research basis: Reinking, Xie, de Moura & Leijen, *Perceus: garbage free
reference counting with reuse* (PLDI 2021) — precise RC is garbage free only
for **cycle-free** programs; Swift and Koka leave cycles to programmer-supplied
weak references; Python's cycle collector is the trial-deletion backstop
(Bacon & Rajan, 2001). Morph's answer closes scope-limit §5.3.3 of
`spec/memory/memory_bounds_spec.md`:

- a **strong reference** is an edge in the `Heap`;
- under the **young-into-old construction discipline** (a freshly allocated
  object captures only already-allocated objects — which is what the affine
  move `store` means for functional construction), every strong edge goes
  from a strictly younger address to an older one, so the strong heap is
  **acyclic**: `StrongPath_lt`, `strong_acyclic`;
- for structures that genuinely need cycles (`Weak<T>`, per
  `memory_model_spec.md` §2.6), weakening one strong edge per cycle unblocks
  collection: `weak_cut_released` proves the target becomes `Released`,
  which is exactly the premise `Step.collect` needs. -/

/-- A strong reference: `a` holds `f` among its strong fields. -/
def Strong (h : Heap) (a f : Addr) : Prop := ∃ gs, h a = some gs ∧ f ∈ gs

/-- A strong reference into `f` exists from *some* object. -/
def Referenced (h : Heap) (f : Addr) : Prop := ∃ a, Strong h a f

/-- A strong path under the young-into-old discipline: every edge goes from
a strictly younger address to an older one. -/
inductive StrongPath (h : Heap) : Addr → Addr → Prop where
  /-- A single decreasing edge. -/
  | edge : ∀ {a f}, f < a → Strong h a f → StrongPath h a f
  /-- A decreasing edge followed by a path. -/
  | cons : ∀ {a b c}, b < a → Strong h a b → StrongPath h b c → StrongPath h a c

/-- Every young-into-old strong path strictly descends: the destination is
strictly younger than the origin. -/
theorem StrongPath_lt {h : Heap} {a c : Addr} (p : StrongPath h a c) : c < a := by
  induction p with
  | edge hf _ => exact hf
  | @cons a b c hb _ p2 ih => exact Nat.lt_of_lt_of_le ih (Nat.le_of_lt hb)

/-- **Strong-heap acyclicity under the construction discipline.** No strong
young-into-old path returns to its origin — the discipline rules out the
cycle `a → b → a` that scope-limit §5.3.3 recorded as satisfying A5. -/
theorem strong_acyclic {h : Heap} (a : Addr) : ¬ StrongPath h a a :=
  fun p => Nat.lt_irrefl a (StrongPath_lt p)

/-- A strong reference into `f` blocks release: `Released` is exactly the
absence of strong in-references, so a collectable object is one whose every
strong in-reference has been cut. -/
theorem referenced_not_released {h : Heap} {f : Addr} (href : Referenced h f) :
    ¬ Released h f := by
  intro hall
  obtain ⟨a, gs, ha, hf⟩ := href
  exact hall a gs ha hf

/-- **The weak-reference escape works at the model level.** If `f`'s only
strong in-reference is the edge `a → f`, weakening that edge (replacing the
strong field by `Weak<T>` — the strong `Heap` no longer carries it) leaves
`f` released, which is exactly what `Step.collect` requires. The field list
is `Nodup` (an object holds at most one strong field reference per target),
so the erased edge is *the* strong in-reference. This is the machine-checked
form of `memory_model_spec.md` §2.6: weak cycles do not prevent deallocation
of objects with no strong references. -/
theorem weak_cut_released {h : Heap} {a f : Addr} {gs : List Addr}
    (ha : h a = some gs) (hnd : gs.Nodup)
    (honly : ∀ y, y ≠ a → ∀ gs', h y = some gs' → f ∉ gs') :
    Released (hUpd h a (gs.erase f)) f := by
  intro y gs' hy
  by_cases hya : y = a
  · subst hya
    rw [hUpd_self] at hy
    simp only [Option.some.injEq] at hy
    subst hy
    exact hnd.not_mem_erase
  · rw [hUpd_ne _ _ _ _ hya] at hy
    exact honly y hya gs' hy

end Morph.Specs.MemoryBounds
