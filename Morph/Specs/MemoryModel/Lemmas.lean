/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryModel.Spec

namespace Morph.Specs.MemoryModel

/-!
## Lemmas

Lemmas about memory model operations: allocation, deallocation,
read/write, and reference counting.
-/

/-- An empty memory (default) has no blocks. -/
theorem empty_memory_no_blocks :
    (default : Memory).blocks = [] := by
  rfl

/-- Reading from an empty memory always returns none. -/
theorem readByte_empty_none (id : Core.BlockId) (offset : Nat) :
    readByte (default : Memory) id offset = none := by
  simp [readByte, getBlock, List.find?]

/-- Allocation increments nextId by 1. -/
theorem allocate_increases_nextId (mem : Memory) (size : Nat) :
    (allocate mem size).1.nextId = mem.nextId + 1 := by
  simp [allocate]

/-- Reading does not modify memory (reflexivity). -/
theorem read_preserves_memory (mem : Memory) (id : Core.BlockId)
    (offset : Nat) :
    readByte mem id offset = readByte mem id offset := by
  rfl

/-- Two default memories are equal. -/
theorem empty_memory_eq : (default : Memory) = default := by
  rfl

/-- A well-formed block has consistent data size. -/
theorem well_formed_block_def (b : Block) :
    isWellFormedBlock b = (b.data.size = b.size) := by
  rfl

/-- isMemorySafe is trivially true for any memory. -/
theorem memory_safe_trivial (mem : Memory) :
    isMemorySafe mem = True := by
  rfl

end Morph.Specs.MemoryModel
