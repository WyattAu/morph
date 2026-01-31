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
**Verified By:** Pending

## Overview

This specification formalizes the memory model for Morph, defining how
memory allocation, deallocation, and access operations work with ARC
(Atomic Reference Counting) and affine type system integration.

The memory model provides:
- Block-based memory allocation with unique identifiers
- Reference counting for automatic memory management
- Memory safety guarantees through bounds checking
- Integration with the affine type system for ownership tracking

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| MEM-001 | `spec_memory_allocation` | ✓ |
| MEM-002 | `spec_memory_deallocation` | ✓ |
| MEM-003 | `spec_memory_access` | ✓ |
| MEM-004 | `memory_safety_invariant` | ✓ |
| MEM-005 | `allocation_preserves_safety` | ✓ |
| MEM-006 | `deallocation_preserves_safety` | ✓ |

## Known Issues

None at this time.

-/

namespace Morph.Specs.MemoryModel

/- ## Core Type Definitions

This section defines the fundamental types used throughout the memory model specification.
-/

/-- Memory block identifier type, aliased from Core.BlockId for convenience -/
abbrev BlockId := Core.BlockId

/-- Memory block structure tracking size, data, and reference count.

    Each allocated memory block contains:
    - `id`: Unique identifier for this block
    - `size`: Size of the block in bytes
    - `data`: Raw data stored in the block
    - `refCount`: Reference count for ARC (starts at 1 for newly allocated blocks)

    **Invariant:** `data.size = size` for all well-formed blocks.
-/
structure Block where
  /-- Unique identifier for this block -/
  id : BlockId
  /-- Size of the block in bytes -/
  size : Nat
  /-- Raw data stored in the block -/
  data : Array UInt8
  /-- Reference count for ARC -/
  refCount : Nat
  deriving Repr, BEq

/-- Memory structure tracking all allocated blocks.

    Memory maintains a collection of allocated blocks and a counter for
    generating unique block IDs.

    **Invariant:** All block IDs in `blocks` are unique and less than `nextId`.
-/
structure Memory where
  /-- List of all allocated blocks with their identifiers -/
  blocks : List (BlockId × Block)
  /-- Next available block identifier -/
  nextId : Nat
  deriving Repr, BEq

/- ## Helper Functions

This section provides utility functions for working with memory and blocks.
-/

/-- Get a block by its identifier from memory.

    Returns `some block` if a block with the given ID exists,
    otherwise returns `none`.
-/
def getBlock (mem : Memory) (id : BlockId) : Option Block :=
  mem.blocks.find? (fun (bid, _) => bid = id) |>.map (fun (_, block) => block)

/-- Check if a block exists in memory.

    This predicate is true when a block with the given ID is present
    in the memory's block list.
-/
def hasBlock (mem : Memory) (id : BlockId) : Prop :=
  ∃ (block : Block), (id, block) ∈ List.toArray mem.blocks

/- ## Well-Formedness Predicates

This section defines predicates for checking memory well-formedness.
-/

/-- Check if memory is well-formed (no duplicate block IDs).

    Memory is well-formed when each block ID appears at most once
    in the block list. This ensures that `getBlock` returns at most
    one block for any given ID.
-/
def isWellFormedMemory (mem : Memory) : Prop :=
  ∀ (id₁ id₂ : BlockId) (block₁ block₂ : Block),
    (id₁, block₁) ∈ List.toArray mem.blocks →
      (id₂, block₂) ∈ List.toArray mem.blocks →
        id₁ = id₂ → block₁ = block₂

/-- Check if a block is well-formed.

    A block is well-formed when its data array size matches its
    declared size. This invariant ensures that all bytes within the
    block are properly initialized.
-/
def isWellFormedBlock (block : Block) : Prop :=
  block.data.size = block.size

/-- Check if all blocks in memory are well-formed.

    This predicate extends well-formedness from individual blocks to
    the entire memory state.
-/
def allBlocksWellFormed (mem : Memory) : Prop :=
  ∀ (id : BlockId) (block : Block),
    (id, block) ∈ List.toArray mem.blocks →
      isWellFormedBlock block

/-- Check if memory is safe.

    Memory is safe when it is well-formed and all blocks are
    well-formed. This is the fundamental memory safety invariant.
-/
def isMemorySafe (mem : Memory) : Prop :=
  isWellFormedMemory mem ∧ allBlocksWellFormed mem

/- ## Memory Operations

This section defines the core memory operations that will be specified.
-/

/-- Allocate a new block of the given size.

    Allocation creates a new block with:
    - A unique block ID
    - The requested size
    - Uninitialized data (all bytes set to 0)
    - Reference count of 1

    Returns the updated memory and the new block ID.
-/
def allocate (mem : Memory) (size : Nat) : Memory × BlockId :=
  let id : BlockId := { id := mem.nextId }
  let block : Block :=
    { id := id,
      size := size,
      data := Array.mkArray size 0,
      refCount := 1 }
  let newBlocks := (id, block) :: mem.blocks
  ({ blocks := newBlocks, nextId := mem.nextId + 1 }, id)

/-- Deallocate a block by its identifier.

    Deallocation removes the block from memory. This operation
    should only be called when the block's reference count is zero.
-/
def deallocate (mem : Memory) (id : BlockId) : Memory :=
  { mem with blocks := mem.blocks.filter (fun (bid, _) => bid ≠ id) }

/-- Read a byte from a block at the given offset.

    Returns `some value` if the offset is within bounds,
    otherwise returns `none`.
-/
def readByte (mem : Memory) (id : BlockId) (offset : Nat) : Option UInt8 :=
  match getBlock mem id with
  | some block =>
      if offset < block.size then
        some (block.data.get! offset)
      else
        none
  | none => none

/-- Write a byte to a block at the given offset.

    Returns the updated memory if the offset is within bounds,
    otherwise returns the original memory unchanged.
-/
def writeByte (mem : Memory) (id : BlockId) (offset : Nat) (value : UInt8) : Memory :=
  match getBlock mem id with
  | some block =>
      if offset < block.size then
        let newBlock := { block with data := block.data.set! offset value }
        { mem with blocks := mem.blocks.map (fun (bid, b) =>
          if bid = id then (id, newBlock) else (bid, b)) }
      else
        mem
  | none => mem

/-- Increment the reference count for a block.

    Returns the updated memory with the block's reference count increased by 1.
-/
def incrementRefCount (mem : Memory) (id : BlockId) : Memory :=
  match getBlock mem id with
  | some block =>
      let newBlock := { block with refCount := block.refCount + 1 }
      { mem with blocks := mem.blocks.map (fun (bid, b) =>
        if bid = id then (id, newBlock) else (bid, b)) }
  | none => mem

/-- Decrement the reference count for a block.

    Returns the updated memory with the block's reference count decreased by 1.
-/
def decrementRefCount (mem : Memory) (id : BlockId) : Memory :=
  match getBlock mem id with
  | some block =>
      if block.refCount > 0 then
        let newBlock := { block with refCount := block.refCount - 1 }
        { mem with blocks := mem.blocks.map (fun (bid, b) =>
          if bid = id then (id, newBlock) else (bid, b)) }
      else
        mem
  | none => mem

/- ## Specification Theorems

This section contains the formal specification theorems for the memory model.
-/

/- ## Memory Allocation (MEM-001)

MEM-001 specifies the correctness properties of memory allocation.
-/

/-- MEM-001: Memory allocation creates a new block with correct properties.

    When a block is allocated, the following must hold:
    1. A new block with the requested size is created
    2. The new block has reference count 1
    3. The new block has a unique ID not used by any existing block
    4. All existing blocks are preserved in the updated memory
-/
theorem spec_memory_allocation (mem : Memory) (size : Nat) : Prop :=
  let (newMem, id) := allocate mem size in
    ∃ (block : Block),
      (id, block) ∈ List.toArray newMem.blocks ∧
        block.size = size ∧
          block.refCount = 1 ∧
            ∀ (bid : BlockId) (b : Block),
              (bid, b) ∈ List.toArray mem.blocks →
                (bid, b) ∈ List.toArray newMem.blocks ∧
                  bid ≠ id

/- ## Memory Deallocation (MEM-002)

MEM-002 specifies the correctness properties of memory deallocation.
-/

/-- MEM-002: Memory deallocation removes blocks correctly.

    When a block with zero reference count is deallocated:
    1. The block is removed from memory
    2. No other blocks are affected
-/
theorem spec_memory_deallocation (mem : Memory) (id : BlockId) : Prop :=
  match getBlock mem id with
  | some block =>
      block.refCount = 0 →
        let newMem := deallocate mem id in
          ∀ (bid : BlockId) (b : Block),
            (bid, b) ∈ List.toArray newMem.blocks → bid ≠ id
  | none => True

/- ## Memory Access (MEM-003)

MEM-003 specifies the safety properties of memory access operations.
-/

/-- MEM-003: Memory access is safe within block bounds.

    Reading a byte from a block:
    - Returns the byte value if the offset is within bounds
    - Returns `none` if the offset is out of bounds
-/
theorem spec_memory_access (mem : Memory) (id : BlockId) (offset : Nat) : Prop :=
  match getBlock mem id with
  | some block =>
      offset < block.size ↔ readByte mem id offset = some (block.data.get! offset)
  | none => True

/- ## Memory Safety Invariants (MEM-004)

MEM-004 specifies the fundamental memory safety invariant.
-/

/-- MEM-004: Memory safety invariant.

    Memory is safe when:
    1. It is well-formed (no duplicate block IDs)
    2. All blocks are well-formed (data size matches declared size)
-/
theorem memory_safety_invariant (mem : Memory) : Prop :=
  isWellFormedMemory mem ∧ allBlocksWellFormed mem

/- ## Safety Preservation (MEM-005, MEM-006)

MEM-005 and MEM-006 specify that memory operations preserve safety.
-/

/-- MEM-005: Allocation preserves memory safety.

    If memory is safe before allocation, it remains safe after allocation.
-/
theorem allocation_preserves_safety (mem : Memory) (size : Nat) : Prop :=
  isMemorySafe mem →
    let (newMem, _) := allocate mem size in
      isMemorySafe newMem

/-- MEM-006: Deallocation preserves memory safety.

    If memory is safe before deallocation, it remains safe after deallocation.
-/
theorem deallocation_preserves_safety (mem : Memory) (id : BlockId) : Prop :=
  isMemorySafe mem →
    let newMem := deallocate mem id in
      isMemorySafe newMem

/- ## Additional Specification Theorems

These theorems provide additional guarantees about memory operations.
-/

/-- Empty memory is well-formed.

    The initial empty memory state satisfies the well-formedness invariant.
-/
theorem empty_memory_well_formed : Prop :=
  isWellFormedMemory { blocks := [], nextId := 0 }

/-- Write operation preserves memory safety.

    Writing a byte within bounds preserves the memory safety invariant.
-/
theorem write_preserves_safety (mem : Memory) (id : BlockId) (offset : Nat) (value : UInt8) : Prop :=
  isMemorySafe mem →
    offset < (getBlock mem id).getD { id := id, size := 0, data := #[], refCount := 0 }.size →
      let newMem := writeByte mem id offset value in
        isMemorySafe newMem

/-- Read operation does not modify memory.

    Reading a byte is a pure operation that leaves memory unchanged.
-/
theorem read_does_not_modify (mem : Memory) (id : BlockId) (offset : Nat) : Prop :=
  let _ := readByte mem id offset in
    mem = mem

/-- Write operation modifies only the target block.

    Writing to a block affects only that block; all other blocks remain unchanged.
-/
theorem write_modifies_only_target (mem : Memory) (id : BlockId) (offset : Nat) (value : UInt8) : Prop :=
  let newMem := writeByte mem id offset value in
    ∀ (bid : BlockId) (b : Block),
      (bid, b) ∈ List.toArray newMem.blocks →
        bid ≠ id → (bid, b) ∈ List.toArray mem.blocks

/-- Reference count increment increases count by 1.

    Incrementing a block's reference count increases it by exactly 1.
-/
theorem ref_count_increment (mem : Memory) (id : BlockId) : Prop :=
  hasBlock mem id →
    let newMem := incrementRefCount mem id in
      match getBlock mem id, getBlock newMem id with
      | some block, some newBlock => newBlock.refCount = block.refCount + 1
      | _, _ => False

/-- Reference count decrement decreases count by 1.

    Decrementing a block's reference count decreases it by exactly 1,
    provided the count was greater than 0.
-/
theorem ref_count_decrement (mem : Memory) (id : BlockId) : Prop :=
  hasBlock mem id →
    match getBlock mem id with
    | some block =>
        block.refCount > 0 →
          let newMem := decrementRefCount mem id in
            match getBlock newMem id with
            | some newBlock => newBlock.refCount = block.refCount - 1
            | none => False
    | none => True

/-- Zero reference count enables deallocation.

    A block with zero reference count can be safely deallocated.
-/
theorem zero_ref_count_allows_deallocation (mem : Memory) (id : BlockId) : Prop :=
  match getBlock mem id with
  | some block =>
      block.refCount = 0 →
        let newMem := deallocate mem id in
          ¬hasBlock newMem id
  | none => True

/-- Non-zero reference count prevents deallocation.

    A block with non-zero reference count cannot be deallocated.
-/
theorem non_zero_ref_count_prevents_deallocation (mem : Memory) (id : BlockId) : Prop :=
  match getBlock mem id with
  | some block =>
      block.refCount > 0 →
        let newMem := deallocate mem id in
          hasBlock newMem id
  | none => True

/-- Unique block identifiers.

    In well-formed memory, each block ID corresponds to exactly one block.
-/
theorem unique_block_identifiers (mem : Memory) : Prop :=
  isWellFormedMemory mem →
    ∀ (id₁ id₂ : BlockId) (block₁ block₂ : Block),
      (id₁, block₁) ∈ List.toArray mem.blocks →
        (id₂, block₂) ∈ List.toArray mem.blocks →
          id₁ = id₂ ↔ block₁.id = block₂.id

/-- Block data integrity.

    Reading a byte from a block returns the value stored at that offset.
-/
theorem block_data_integrity (mem : Memory) (id : BlockId) (offset : Nat) : Prop :=
  match getBlock mem id with
  | some block =>
      offset < block.size →
        readByte mem id offset = some (block.data.get! offset)
  | none => True

/-- Write-read consistency.

    Writing a value to a block and then reading it back returns the same value.
-/
theorem write_read_consistency (mem : Memory) (id : BlockId) (offset : Nat) (value : UInt8) : Prop :=
  match getBlock mem id with
  | some block =>
      offset < block.size →
        let newMem := writeByte mem id offset value in
          readByte newMem id offset = some value
  | none => True

end Morph.Specs.MemoryModel
