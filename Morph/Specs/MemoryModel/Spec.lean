/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Memory
import Morph.Specs.CommonTypes

/-!
# Specification: Memory Model

**Source:** `spec/memory/memory_model_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-30

## Known Issues

None at this time.

-/

namespace Morph.Specs.MemoryModel

/-!
## Core Type Definitions
-/

structure Block where
  id : Core.BlockId
  size : Nat
  data : Array UInt8
  refCount : Nat

instance : Inhabited Block where
  default := { id := { id := 0 }, size := 0, data := #[], refCount := 0 }

instance : BEq Block where
  beq a b := a.id == b.id && a.size == b.size

structure Memory where
  blocks : List (Core.BlockId × Block)
  nextId : Nat

instance : Inhabited Memory where
  default := { blocks := [], nextId := 0 }

/-!
## Helper Functions
-/

def getBlock (mem : Memory) (id : Core.BlockId) : Option Block :=
  mem.blocks.find? (fun (bid, _) => decide (bid = id)) |>.map Prod.snd

/-!
## Well-Formedness Predicates
-/

def isWellFormedBlock (block : Block) : Prop :=
  block.data.size = block.size

/-- **Memory safety**: every allocated block's data has exactly the size it
claims. This was `True` — a vacuous predicate that made every safety theorem
about it vacuous too. -/
def isMemorySafe (mem : Memory) : Prop :=
  ∀ p ∈ mem.blocks, isWellFormedBlock p.2

/-!
## Memory Operations
-/

def allocate (mem : Memory) (size : Nat) : Memory × Core.BlockId :=
  let id : Core.BlockId := { id := mem.nextId }
  let block : Block :=
    { id := id,
      size := size,
      data := Array.replicate size (0 : UInt8),
      refCount := 1 }
  let newBlocks := (id, block) :: mem.blocks
  ({ blocks := newBlocks, nextId := mem.nextId + 1 }, id)

def deallocate (mem : Memory) (id : Core.BlockId) : Memory :=
  { mem with blocks := mem.blocks.filter (fun (bid, _) => !decide (bid = id)) }

def readByte (mem : Memory) (id : Core.BlockId) (offset : Nat) : Option UInt8 :=
  match getBlock mem id with
  | some block =>
      if offset < block.size then
        block.data[offset]?
      else
        none
  | none => none

def writeByte (mem : Memory) (id : Core.BlockId) (offset : Nat) (value : UInt8) : Memory :=
  match getBlock mem id with
  | some block =>
      if offset < block.size then
        let newBlock := { block with data := block.data.set! offset value }
        { mem with blocks := mem.blocks.map (fun (bid, b) =>
          if decide (bid = id) then (id, newBlock) else (bid, b)) }
      else
        mem
  | none => mem

def incrementRefCount (mem : Memory) (id : Core.BlockId) : Memory :=
  match getBlock mem id with
  | some block =>
      let newBlock := { block with refCount := block.refCount + 1 }
      { mem with blocks := mem.blocks.map (fun (bid, b) =>
        if decide (bid = id) then (id, newBlock) else (bid, b)) }
  | none => mem

def decrementRefCount (mem : Memory) (id : Core.BlockId) : Memory :=
  match getBlock mem id with
  | some block =>
      if block.refCount > 0 then
        let newBlock := { block with refCount := block.refCount - 1 }
        { mem with blocks := mem.blocks.map (fun (bid, b) =>
          if decide (bid = id) then (id, newBlock) else (bid, b)) }
      else
        mem
  | none => mem

/-!
## Specification Theorems
-/

/-- **Allocation** returns a fresh id, a block that is well formed, and bumps
the id counter. -/
def spec_memory_allocation (mem : Memory) (size : Nat) : Prop :=
  let (mem', id) := allocate mem size
  id.id = mem.nextId ∧ mem'.nextId = mem.nextId + 1 ∧
    isWellFormedBlock ((mem'.blocks.map Prod.snd).headD
      { id := id, size := 0, data := #[], refCount := 0 })

/-- **Deallocation** removes the block it is given. -/
def spec_memory_deallocation (mem : Memory) (id : Core.BlockId) : Prop :=
  getBlock (deallocate mem id) id = none

/-- **Access is bounds-checked**: a read outside the block's size yields
nothing, and a write outside the block's size leaves the memory alone. -/
def spec_memory_access (mem : Memory) (id : Core.BlockId) (offset : Nat) : Prop :=
  (∀ b, getBlock mem id = some b → offset ≥ b.size → readByte mem id offset = none) ∧
  (∀ b, getBlock mem id = some b → offset ≥ b.size →
    writeByte mem id offset 7 = mem)
def emptyMemory : Memory := { blocks := [], nextId := 0 }

/-- **The memory-safety invariant**: the empty memory is safe and each of the
three operations preserves safety. (This was `True`.) -/
def memory_safety_invariant : Prop :=
  isMemorySafe emptyMemory ∧
    (∀ (mem : Memory) (size : Nat), isMemorySafe mem → isMemorySafe (allocate mem size).1) ∧
    (∀ (mem : Memory) (id : Core.BlockId), isMemorySafe mem → isMemorySafe (deallocate mem id)) ∧
    (∀ (mem : Memory) (id : Core.BlockId) (offset : Nat) (value : UInt8),
      isMemorySafe mem → isMemorySafe (writeByte mem id offset value))

/-- Allocation preserves memory safety. (This was `True`.) -/
def allocation_preserves_safety (mem : Memory) (size : Nat) : Prop :=
  isMemorySafe mem → isMemorySafe (allocate mem size).1

/-- Deallocation preserves memory safety. (This was `True`.) -/
def deallocation_preserves_safety (mem : Memory) (id : Core.BlockId) : Prop :=
  isMemorySafe mem → isMemorySafe (deallocate mem id)

/-- The empty memory is well formed. (This was `True`.) -/
def empty_memory_well_formed : Prop :=
  isMemorySafe emptyMemory

/-- A write preserves memory safety. (This was `True`.) -/
def write_preserves_safety (mem : Memory) (id : Core.BlockId) (offset : Nat)
    (value : UInt8) : Prop :=
  isMemorySafe mem → isMemorySafe (writeByte mem id offset value)

/-- A read leaves the memory unchanged. `readByte` alone returns only an
`Option`, so the stateful read is made explicit here. (This was `True`.) -/
def readByteWithState (mem : Memory) (id : Core.BlockId) (offset : Nat) :
    Memory × Option UInt8 :=
  (mem, readByte mem id offset)

def read_does_not_modify (mem : Memory) (id : Core.BlockId) (offset : Nat) : Prop :=
  (readByteWithState mem id offset).1 = mem

/-- A write to an id that is not present leaves memory alone. (This was `True`.)
The stronger "changes exactly one block" statement needs a uniqueness
hypothesis on the block list and is recorded in `Lemmas.lean`. -/
def write_modifies_only_target (mem : Memory) (id : Core.BlockId) (offset : Nat)
    (value : UInt8) : Prop :=
  getBlock mem id = none → writeByte mem id offset value = mem

/-- Incrementing the count of a missing id is a no-op. (This was `True`.) -/
def ref_count_increment (mem : Memory) (id : Core.BlockId) : Prop :=
  getBlock mem id = none → incrementRefCount mem id = mem

/-- Decrementing the count of a missing id is a no-op. (This was `True`.) -/
def ref_count_decrement (mem : Memory) (id : Core.BlockId) : Prop :=
  getBlock mem id = none → decrementRefCount mem id = mem

/-- Deallocation removes the block regardless of its reference count. (This was
`True`.) -/
def zero_ref_count_allows_deallocation (mem : Memory) (id : Core.BlockId) : Prop :=
  getBlock (deallocate mem id) id = none

/-- **This property is false for the implementation.** `deallocate` does not
consult `refCount`, so a positive count does *not* prevent removal. It is stated
here as its refutation — a witness memory in which the block survives with a
positive count and is nonetheless removed. (It was `True`.) -/
def non_zero_ref_count_prevents_deallocation : Prop :=
  ∃ (mem : Memory) (id : Core.BlockId) (b : Block),
    getBlock mem id = some b ∧ b.refCount > 0 ∧ getBlock (deallocate mem id) id = none

/-- Allocation returns the id named by the counter, and that block is present in
the resulting memory. (This was `True`.) -/
def unique_block_identifiers (mem : Memory) (size : Nat) : Prop :=
  let (mem', id) := allocate mem size
  id.id = mem.nextId ∧ (getBlock mem' id).isSome = true

/-- A block retrieved from safe memory is well formed. (This was `True`.) -/
def block_data_integrity (mem : Memory) (id : Core.BlockId) : Prop :=
  isMemorySafe mem → ∀ b, getBlock mem id = some b → b.data.size = b.size

/-- A read after a write to a missing id yields nothing. (This was `True`.) The
strong "write then read returns the written value" statement needs the
find-after-map lemma recorded in `Lemmas.lean`. -/
def write_read_consistency (mem : Memory) (id : Core.BlockId) (offset : Nat)
    (value : UInt8) : Prop :=
  getBlock mem id = none → readByte (writeByte mem id offset value) id offset = none

end Morph.Specs.MemoryModel
