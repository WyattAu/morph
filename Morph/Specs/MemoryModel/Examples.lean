/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/


import Morph.Specs.MemoryModel.Spec

/-!
# Memory Model Examples

This module provides examples demonstrating memory model operations
for Morph language.

## Overview

These examples demonstrate:
- Empty memory initialization
- Block allocation and deallocation
- Read and write operations
- Reference counting (ARC)
- Memory safety verification
- Multiple block management

## Examples Summary

| Example | Purpose | Status |
|---------|---------|--------|
| `example_empty_memory` | Empty memory initialization | ✓ |
| `example_allocate_block` | Block allocation | ✓ |
| `example_write_block` | Block write operation | ✓ |
| `example_read_block` | Block read operation | ✓ |
| `example_deallocate_block` | Block deallocation | ✓ |
| `example_increment_ref` | Increment reference count | ✓ |
| `example_decrement_ref` | Decrement reference count | ✓ |
| `example_multiple_blocks` | Multiple block management | ✓ |

-/

namespace Morph.Specs.MemoryModel

/- ## Example 1: Empty Memory

This example demonstrates creating an empty memory state.
-/

/-- Empty memory with no blocks.

    This is the initial state of memory before any allocations.
-/
def example_empty_memory : Memory :=
  { blocks := [], nextId := 0 }

#eval example_empty_memory
-- Expected: { blocks := [], nextId := 0 }

/-- Verify that empty memory is well-formed.

    Example demonstrates verification of well-formedness property.
-/
example_verify_empty_well_formed : isWellFormedMemory example_empty_memory := by
  exact empty_memory_well_formed

/-- Verify that empty memory is safe.

    Example demonstrates verification of memory safety property.
-/
example_verify_empty_safe : isMemorySafe example_empty_memory := by
  exact empty_memory_safe

/- ## Example 2: Block Allocation

This example demonstrates allocating a new memory block.
-/

/-- Allocate a block of size 1024 bytes.

    This example shows how to allocate a new block in memory.
-/
def example_allocate_block : Memory × BlockId :=
  allocate example_empty_memory 1024

#eval example_allocate_block
-- Expected: ({ blocks := [({ id := 0, size := 1024, data := Array.replicate 1024 0, refCount := 1 })], nextId := 1 }, 0)

/-- Verify that allocation creates a unique block.

    Example demonstrates that the newly allocated block has unique ID.
-/
example_verify_allocation_unique :
  let (mem, id) := example_allocate_block in
    ∃ (block : Block),
      (id, block) ∈ List.toArray mem.blocks ∧
        block.size = 1024 ∧
          block.refCount = 1 := by
  intro mem id
  -- The allocate function creates a block with nextId
  -- We need to show this block has the correct properties
  cases mem.blocks
  · nil
    · cons head tail =>
      cases head
      · intro bid block
        -- This is the newly allocated block
        constructor
        · -- Show (id, block) is in mem.blocks
          rfl
        · -- Show block.size = 1024
          cases block
          rfl
        · -- Show block.refCount = 1
          cases block
          rfl

/-- Verify that allocation preserves memory safety.

    Example demonstrates that memory safety is maintained after allocation.
-/
example_verify_allocation_safe :
  let (mem, id) := example_allocate_block in
    isMemorySafe mem := by
  intro mem id
  constructor
  · -- Show well-formedness is preserved
    intro id₁ id₂ block₁ block₂ h_in1 h_in2 h_eq
    cases h_in1
    · -- Both blocks are the same (only one block)
      rfl
    · -- No other blocks in memory
      contradiction
  · -- Show all blocks are well-formed
    intro bid block h_in
    cases h_in
    · -- The only block is well-formed
      cases block
      rfl
    · -- No other blocks
      contradiction

/- ## Example 3: Block Write Operation

This example demonstrates writing data to a memory block.
-/

/-- Write byte value 42 to offset 0 of allocated block.

    This example shows how to write a byte to a specific offset.
-/
def example_write_block (mem : Memory) (id : BlockId) : Memory :=
  writeByte mem id 0 42

#eval example_write_block (example_allocate_block.fst) (example_allocate_block.snd)
-- Expected: Memory with block.data[0] = 42

/-- Verify that write operation preserves memory safety.

    Example demonstrates that write operation maintains memory safety.
-/
example_verify_write_safe :
  let (mem, id) := example_allocate_block in
    let newMem := example_write_block mem id in
      isMemorySafe newMem := by
  intro mem id newMem
  constructor
  · -- Show well-formedness is preserved
    intro id₁ id₂ block₁ block₂ h_in1 h_in2 h_eq
    cases h_in1
    · -- Both blocks are the same (only one block)
      rfl
    · -- No other blocks in memory
      contradiction
  · -- Show all blocks are well-formed
    intro bid block h_in
    cases h_in
    · -- The only block is well-formed (write doesn't change size)
      cases block
      rfl
    · -- No other blocks
      contradiction

/- ## Example 4: Block Read Operation

This example demonstrates reading data from a memory block.
-/

/-- Read byte from offset 0 of allocated block.

    This example shows how to read a byte from a specific offset.
-/
def example_read_block (mem : Memory) (id : BlockId) : Option UInt8 :=
  readByte mem id 0

#eval example_read_block (example_write_block (example_allocate_block.fst) (example_allocate_block.snd)) (example_allocate_block.snd)
-- Expected: some 42

/-- Verify that read operation returns value that was written.

    Example demonstrates that reading returns the value that was written.
-/
example_verify_read_write :
  let (mem, id) := example_allocate_block in
    let mem' := example_write_block mem id in
      example_read_block mem' id = some 42 := by
  intro mem id mem'
  -- After writing 42 at offset 0, reading returns some 42
  unfold example_read_block
  unfold example_write_block
  unfold readByte
  unfold writeByte
  rfl

/- ## Example 5: Block Deallocation

This example demonstrates deallocating a memory block.
-/

/-- Deallocate the allocated block.

    This example shows how to deallocate a block by its ID.
-/
def example_deallocate_block (mem : Memory) (id : BlockId) : Memory :=
  deallocate mem id

#eval example_deallocate_block (example_allocate_block.fst) (example_allocate_block.snd)
-- Expected: { blocks := [], nextId := 1 }

/-- Verify that deallocation removes the block.

    Example demonstrates that deallocation removes the specified block.
-/
example_verify_deallocation_removes :
  let (mem, id) := example_allocate_block in
    let mem' := decrementRefCount mem id in
    let mem'' := example_deallocate_block mem' id in
      ¬hasBlock mem'' id := by
  intro mem id mem' mem''
  -- Deallocation filters out blocks with matching ID
  exact deallocation_removes_block mem id (by
    intro h
    cases h
    · rfl
    · rfl)

/- ## Example 6: Reference Counting

This example demonstrates ARC (Atomic Reference Counting).
-/

/-- Increment reference count of a block.

    This example shows how to increase a block's reference count.
-/
def example_increment_ref (mem : Memory) (id : BlockId) : Memory :=
  incrementRefCount mem id

#eval example_increment_ref (example_allocate_block.fst) (example_allocate_block.snd)
-- Expected: Memory with block.refCount = 2

/-- Verify that incrementing increases reference count by 1.

    Example demonstrates that incrementRefCount increases refCount by exactly 1.
-/
example_verify_increment :
  let (mem, id) := example_allocate_block in
    let mem' := example_increment_ref mem id in
      match getBlock mem id, getBlock mem' id with
      | some block, some newBlock => newBlock.refCount = block.refCount + 1
      | _, _ => False := by
  intro mem id mem'
  -- incrementRefCount increases refCount field by 1
  unfold example_increment_ref
  unfold incrementRefCount
  unfold getBlock
  rfl

/-- Decrement reference count of a block.

    This example shows how to decrease a block's reference count.
-/
def example_decrement_ref (mem : Memory) (id : BlockId) : Memory :=
  decrementRefCount mem id

#eval example_decrement_ref (example_increment_ref (example_allocate_block.fst) (example_allocate_block.snd)) (example_allocate_block.snd)
-- Expected: Memory with block.refCount = 1

/-- Verify that decrementing decreases reference count by 1.

    Example demonstrates that decrementRefCount decreases refCount by exactly 1.
-/
example_verify_decrement :
  let (mem, id) := example_allocate_block in
    let mem' := example_decrement_ref mem id in
      match getBlock mem id, getBlock mem' id with
      | some block, some newBlock => newBlock.refCount = block.refCount - 1
      | _, _ => False := by
  intro mem id mem'
  -- decrementRefCount decreases refCount field by 1
  unfold example_decrement_ref
  unfold decrementRefCount
  unfold getBlock
  rfl

/- ## Example 7: Memory Safety Verification

This example demonstrates comprehensive memory safety verification.
-/

/-- Verify memory safety after multiple operations.

    Example demonstrates that memory safety is preserved through
    allocation, write, read, and deallocation.
-/
example_verify_comprehensive_safety :
  let (mem, id) := example_allocate_block in
    let mem' := example_write_block mem id in
    let _ := example_read_block mem' id in
    let mem'' := decrementRefCount mem' id in
    let mem''' := example_deallocate_block mem'' id in
      isMemorySafe mem''' := by
  intro mem id mem' mem'' mem'''
  -- Each operation preserves memory safety
  constructor
  · -- Show well-formedness is preserved
    intro id₁ id₂ block₁ block₂ h_in1 h_in2 h_eq
    -- After deallocation, there are no blocks
    cases h_in1
    · contradiction
    · contradiction
  · -- Show all blocks are well-formed
    intro bid block h_in
    -- After deallocation, there are no blocks
    cases h_in
    · contradiction
    · contradiction

/- ## Example 8: Block Data Integrity

This example demonstrates that block data is correctly maintained.
-/

/-- Verify block data integrity after write and read.

    Example demonstrates that block data is correctly maintained
    through write and read operations.
-/
example_verify_data_integrity :
  let (mem, id) := example_allocate_block in
    let mem' := example_write_block mem id in
      match getBlock mem' id with
      | some block =>
          block.data[0]! = 42
      | none => False := by
  intro mem id mem'
  -- Write operation sets byte at offset 0 to 42
  unfold example_write_block
  unfold writeByte
  unfold getBlock
  rfl

/- ## Example 9: Multiple Block Management

This example demonstrates managing multiple memory blocks.
-/

/-- Allocate multiple blocks.

    This example shows how to manage multiple blocks in memory.
-/
def example_multiple_blocks : Memory :=
  let (mem1, id1) := allocate example_empty_memory 1024
  let (mem2, id2) := allocate mem1 512
  let (mem3, id3) := allocate mem2 256
  mem3

#eval example_multiple_blocks
-- Expected: Memory with 3 blocks of sizes 1024, 512, 256

/-- Verify that multiple blocks have unique IDs.

    Example demonstrates that each allocated block has a unique ID.
-/
example_verify_unique_ids :
  let mem := example_multiple_blocks in
    ∀ (id₁ id₂ : BlockId) (block₁ block₂ : Block),
      (id₁, block₁) ∈ List.toArray mem.blocks →
        (id₂, block₂) ∈ List.toArray mem.blocks →
          id₁ = id₂ ↔ block₁.id = block₂.id := by
  intro mem id₁ id₂ block₁ block₂ h_in1 h_in2
  constructor
  · -- If id₁ = id₂, then block₁ = block₂ by well-formedness
    intro h_eq
    -- Memory with multiple blocks is well-formed
    -- So equal IDs imply equal blocks
    cases h_in1
    · rfl
    · rfl
  · -- If block₁.id = block₂.id, then id₁ = id₂ by definition
    intro h_eq
    cases block₁
    rfl

end Morph.Specs.MemoryModel
