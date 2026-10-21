/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryModel.Lemmas

namespace Morph.Specs.MemoryModel

/-!
## Examples

Concrete examples demonstrating the MemoryModel specification.
-/

/-- Reading from non-existent block returns none. -/
example : readByte (default : Memory) { id := 99 } 0 = none := by
  simp [readByte, getBlock, List.find?]

/-- A default block (size 0, empty data) is well-formed. -/
example : isWellFormedBlock { id := { id := 0 }, size := 0, data := #[], refCount := 0 } := by
  simp [isWellFormedBlock]

/-- Reading from an empty memory always returns none for any offset. -/
example (id : Core.BlockId) (offset : Nat) :
    readByte (default : Memory) id offset = none := by
  simp [readByte, getBlock, List.find?]

/-- An empty memory has no blocks. -/
example : (default : Memory).blocks = [] := by
  rfl

/-- **Memory safety used to be trivial — it was `True`.** It is now a real
predicate: every block's data has exactly the size it claims. The old
"theorem" was true for every memory because the predicate was; now it is a
statement about a particular memory. -/
example (mem : Memory) (h : isMemorySafe mem) : isMemorySafe mem := h

/-- And the specification's own allocation property, proved. -/
example (mem : Memory) (size : Nat) : spec_memory_allocation mem size :=
  allocation_spec mem size

/-- The bounds check, proved. -/
example (mem : Memory) (id : Core.BlockId) (offset : Nat) :
    spec_memory_access mem id offset :=
  access_spec mem id offset

end Morph.Specs.MemoryModel
