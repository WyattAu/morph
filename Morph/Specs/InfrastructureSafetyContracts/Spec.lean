/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core

namespace Morph.Specs.InfrastructureSafetyContracts

open Morph.Core

/-!
# Infrastructure Safety Contracts

Formal specification of safety contracts for infrastructure-level operations:
- Memory allocation/deallocation safety
- Stack overflow protection
- Resource exhaustion limits

The contracts are stated over an explicit allocation state (`Heap`): both the
precondition and the postcondition see the heap, which is what makes "the block
is alive before" and "the block is dead after" expressible at all. Earlier
revisions used `pre := fun _ => True` / `post := fun _ _ => True` and documented
those as liveness checks; the comments described behaviour the contracts did
not have.
-/

/-- Maximum number of simultaneously live blocks. -/
def maxActiveHandles : Nat := 4096

/-- Stack depth limit, configurable per target. -/
def maxStackDepth : Nat := 1024

/-- A stack overflow safety predicate. -/
def stackSafe (depth : Nat) : Prop := depth < maxStackDepth

/-- Resource exhaustion limit: the live-handle count must stay below the cap. -/
def handleCountSafe (count : Nat) : Prop := count < maxActiveHandles

/-- Allocation state: the live block ids. Block `0` is the null block and is
never live. -/
structure Heap where
  live : List Nat
  deriving Repr, DecidableEq

namespace Heap

/-- A heap is well formed when its live list has no duplicates and excludes the
null block. -/
def WellFormed (h : Heap) : Prop := h.live.Nodup ∧ 0 ∉ h.live

/-- Is the block live in this heap? -/
def isLive (h : Heap) (id : Nat) : Prop := id ∈ h.live

/-- Allocate a block. -/
def alloc (h : Heap) (id : Nat) : Heap := { live := id :: h.live }

/-- Free a block: drop every occurrence of its id from the live set. -/
def free (h : Heap) (id : Nat) : Heap :=
  { live := h.live.filter (fun x => x != id) }

theorem isLive_alloc (h : Heap) (id y : Nat) :
    (alloc h id).isLive y ↔ y = id ∨ h.isLive y := by
  simp [isLive, alloc]

theorem isLive_free_of_ne (h : Heap) (id y : Nat) (hne : y ≠ id) :
    (free h id).isLive y ↔ h.isLive y := by
  simp [isLive, free, List.mem_filter, bne_iff_ne, hne]

theorem isLive_free_self (h : Heap) (id : Nat) :
    ¬ (free h id).isLive id := by
  simp [isLive, free, List.mem_filter, bne_self_eq_false]

theorem free_non_increasing (h : Heap) (id : Nat) :
    (free h id).live.length ≤ h.live.length :=
  List.length_filter_le _ _

theorem alloc_preserves_wellFormed (h : Heap) (id : Nat) (hne : id ≠ 0)
    (hfresh : id ∉ h.live) (hwf : WellFormed h) :
    WellFormed (alloc h id) := by
  refine ⟨List.nodup_cons.mpr ⟨hfresh, hwf.1⟩, ?_⟩
  intro hmem
  rcases List.mem_cons.mp hmem with h0 | hrest
  · exact hne h0.symm
  · exact hwf.2 hrest

theorem free_preserves_wellFormed (h : Heap) (id : Nat) (hwf : WellFormed h) :
    WellFormed (free h id) := by
  refine ⟨hwf.1.filter _, ?_⟩
  intro hmem
  exact hwf.2 (List.mem_filter.mp hmem).1

end Heap

/-- The null pointer: block `0`. -/
def nullPtr : Pointer := { block := ⟨0⟩, offset := 0, provenance := none }

/-- A pointer to the start of block `id`. -/
def mkPtr (id : Nat) : Pointer := { block := ⟨id⟩, offset := 0, provenance := none }

/-- A safety contract is a precondition/postcondition pair for an operation on
state `σ` with argument (or result) `α`. Both the precondition and the
postcondition see the state, so state-changing obligations are expressible. -/
structure SafetyContract (σ α : Type) where
  /-- The precondition: the state and the argument. -/
  pre : σ → α → Prop
  /-- The postcondition: the pre-state, the argument (or result), the post-state. -/
  post : σ → α → σ → Prop
  name : String

/-- Allocation: there must be room for one more handle, and the result must be a
non-null pointer that is live in the post-state, with exactly one more live
block than before. -/
def allocContract : SafetyContract Heap Pointer :=
  { pre := fun h _ => h.live.length + 1 < maxActiveHandles
  , post := fun h p h' =>
      p.block.id ≠ 0 ∧ h'.isLive p.block.id ∧ h'.live.length = h.live.length + 1
  , name := "alloc-nonnull-live" }

/-- Free: the block must be live beforehand, and must not be live afterwards. -/
def freeContract : SafetyContract Heap Pointer :=
  { pre := fun h p => h.isLive p.block.id
  , post := fun _ p h' => ¬ h'.isLive p.block.id
  , name := "free-valid" }

end Morph.Specs.InfrastructureSafetyContracts
