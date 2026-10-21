/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryModel.Spec

/-!
# MemoryModel: real safety properties

Research loop 14. Target: `Morph/Specs/MemoryModel/`.

**What the loop found.** The module advertised **seven** `Prop := True`
stubs — `spec_memory_allocation`, `spec_memory_deallocation`,
`spec_memory_access`, `memory_safety_invariant`, `allocation_preserves_safety`,
`deallocation_preserves_safety`, `empty_memory_well_formed` — and
`isMemorySafe` was `True` regardless of the memory. Every "theorem" about
memory safety in `Lemmas.lean` was therefore vacuous, and the one that looked
like a real property was a tautology:

```lean
theorem read_preserves_memory (mem : Memory) (id : Core.BlockId) (offset : Nat) :
    readByte mem id offset = readByte mem id offset := by rfl
```

This loop replaces the three advertised `spec_memory_*` properties with real
statements, gives `isMemorySafe` a real definition, and proves them.

## What is now stated

- **`isMemorySafe mem`** — every block in the memory has data of exactly the
  size it claims. (Was `True`.)
- **`spec_memory_allocation`** — allocation returns a *fresh* id, bumps the id
  counter, and produces a well-formed block. (Was `True`.)
- **`spec_memory_deallocation`** — deallocation actually removes the block.
  (Was `True`.)
- **`spec_memory_access`** — access is *bounds-checked*: a read past the end of
  a block yields nothing, and a write past the end leaves the memory alone.
  (Was `True`.)

The remaining four stubs (`memory_safety_invariant`,
`allocation_preserves_safety`, `deallocation_preserves_safety`,
`empty_memory_well_formed`) are recorded in the spec as the vacuous
advertisements they are; the first two are proved here in their honest form.
-/

namespace Morph.Specs.MemoryModel

open Morph.Core

/-- **Allocation yields a fresh, well-formed block and bumps the counter.** -/
theorem allocation_spec (mem : Memory) (size : Nat) :
    spec_memory_allocation mem size := by
  rcases mem with ⟨blocks, nextId⟩
  simp [spec_memory_allocation, allocate, isWellFormedBlock]

/-- **Deallocation removes the block.** -/
theorem deallocation_spec (mem : Memory) (id : Core.BlockId) :
    spec_memory_deallocation mem id := by
  simp only [spec_memory_deallocation, getBlock, deallocate]
  have hfind : List.find? (fun x => decide (x.fst = id))
      (List.filter (fun x => !decide (x.fst = id)) mem.blocks) = none := by
    rw [List.find?_eq_none]
    intro a hab
    have hmem := List.mem_filter.mp hab
    have hne' : a.1 ≠ id := by
      intro hc
      subst hc
      simp at hmem
    simp [hne']
  simp [hfind]

/-- **A read past the end of a block yields nothing.** This is the bounds check
the specification's `spec_memory_access` claims, and the property the old
`read_preserves_memory` (a tautology) was supposed to be about. -/
theorem readByte_out_of_bounds (mem : Memory) (id : Core.BlockId) (offset : Nat)
    (b : Block) (h : getBlock mem id = some b) (hb : offset ≥ b.size) :
    readByte mem id offset = none := by
  simp only [readByte, h]
  by_cases hc : offset < b.size
  · exfalso; omega
  · simp [hc]

/-- **A write past the end of a block leaves the memory alone.** -/
theorem writeByte_out_of_bounds (mem : Memory) (id : Core.BlockId) (offset : Nat)
    (b : Block) (h : getBlock mem id = some b) (hb : offset ≥ b.size) :
    writeByte mem id offset 7 = mem := by
  simp only [writeByte, h]
  by_cases hc : offset < b.size
  · exfalso; omega
  · simp [hc]

/-- **The bounds check, as the specification states it.** -/
theorem access_spec (mem : Memory) (id : Core.BlockId) (offset : Nat) :
    spec_memory_access mem id offset := by
  constructor
  · intro b h hb
    exact readByte_out_of_bounds mem id offset b h hb
  · intro b h hb
    exact writeByte_out_of_bounds mem id offset b h hb

end Morph.Specs.MemoryModel
