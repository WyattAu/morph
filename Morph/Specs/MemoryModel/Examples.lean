/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryModel.Spec

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

/-- Memory safety is trivially true. -/
example (mem : Memory) : isMemorySafe mem := by
  trivial

end Morph.Specs.MemoryModel
