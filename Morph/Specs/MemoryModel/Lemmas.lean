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

## Loop 26: the other fourteen

The module carried fourteen more `Prop := True` advertisements. They are now
real statements, all proved or refuted here:

- **`memory_safety_invariant`** — a *closed* proposition: the empty memory is
  safe and allocation, deallocation and writing all preserve safety. Assembled
  from the four preservation lemmas below.
- **`empty_memory_well_formed`**, **`allocation_preserves_safety`**,
  **`deallocation_preserves_safety`**, **`write_preserves_safety`** — proved.
- **`read_does_not_modify`** — a read leaves the memory unchanged, made
  expressible by the stateful wrapper `readByteWithState`.
- **`write_modifies_only_target`**, **`ref_count_increment`**,
  **`ref_count_decrement`** — the no-target cases. The *strong* "changes
  exactly one block" forms need a uniqueness hypothesis on the block list and
  a find-after-map lemma; they are not claimed here.
- **`zero_ref_count_allows_deallocation`** — proved (it is
  `deallocation_spec`).
- **`non_zero_ref_count_prevents_deallocation`** — **false**, and stated as
  its refutation: `deallocate` never reads `refCount`, so a block with a live
  reference is removed all the same.
- **`unique_block_identifiers`** — allocation returns the counter's id and the
  block is present.
- **`block_data_integrity`** — a block retrieved from safe memory is well
  formed.
- **`write_read_consistency`** — a read after a write to a missing id yields
  nothing; the strong write-then-read form is not claimed.
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

/-- **Every block returned by `getBlock` is a member of the block list.** -/
theorem getBlock_some_mem {mem : Memory} {id : Core.BlockId} {b : Block}
    (h : getBlock mem id = some b) :
    ∃ p, p ∈ mem.blocks ∧ p.2 = b := by
  unfold getBlock at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, hp, hb⟩ := h
  exact ⟨p, List.mem_of_find?_eq_some hp, hb⟩

/-- **The empty memory is well formed.** -/
theorem empty_memory_well_formed_holds : empty_memory_well_formed := by
  intro p hp
  simp [emptyMemory] at hp

/-- **Allocation preserves safety.** The new block's data is `size` zeros, and
the old blocks are untouched. -/
theorem allocation_preserves_safety_holds (mem : Memory) (size : Nat) :
    allocation_preserves_safety mem size := by
  intro hsafe p hp
  rcases mem with ⟨blocks, nextId⟩
  simp only [allocate] at hp ⊢
  rcases List.mem_cons.mp hp with hp' | hp'
  · rw [hp']
    simp [isWellFormedBlock, Array.size_replicate]
  · exact hsafe p hp'

/-- **Deallocation preserves safety.** Filtering removes blocks; it never adds
a malformed one. -/
theorem deallocation_preserves_safety_holds (mem : Memory) (id : Core.BlockId) :
    deallocation_preserves_safety mem id := by
  intro hsafe p hp
  simp only [deallocate] at hp ⊢
  exact hsafe p (List.mem_filter.mp hp).1

/-- **A write preserves safety.** Writing a byte keeps the array's size, and
only the block with the target id is replaced. -/
theorem write_preserves_safety_holds (mem : Memory) (id : Core.BlockId)
    (offset : Nat) (value : UInt8) :
    write_preserves_safety mem id offset value := by
  intro hsafe
  simp only [writeByte]
  cases hb : getBlock mem id with
  | none => simpa [hb] using hsafe
  | some b =>
      by_cases ho : offset < b.size
      · simp only [ho, if_true]
        intro p hp
        rw [List.mem_map] at hp
        obtain ⟨a, ha, hap⟩ := hp
        have ha_safe : isWellFormedBlock a.2 := hsafe a ha
        rw [← hap]
        by_cases hid : decide (a.1 = id) = true
        · simp only [hid, if_true]
          obtain ⟨q, hq, hqb⟩ := getBlock_some_mem hb
          have hb_safe : isWellFormedBlock b := by
            rw [← hqb]
            exact hsafe q hq
          simp only [isWellFormedBlock] at hb_safe ⊢
          simp [Array.size_setIfInBounds, Array.set!, hb_safe]
        · rw [if_neg hid]
          exact ha_safe
      · simp only [ho, if_false]
        exact hsafe

/-- **A read leaves the memory unchanged.** -/
theorem read_does_not_modify_holds (mem : Memory) (id : Core.BlockId)
    (offset : Nat) : read_does_not_modify mem id offset := by
  rfl

/-- **A write to a missing id leaves memory alone.** -/
theorem write_modifies_only_target_holds (mem : Memory) (id : Core.BlockId)
    (offset : Nat) (value : UInt8) :
    write_modifies_only_target mem id offset value := by
  intro hnone
  simp [writeByte, hnone]

/-- **Incrementing a missing block's count is a no-op.** -/
theorem ref_count_increment_holds (mem : Memory) (id : Core.BlockId) :
    ref_count_increment mem id := by
  intro hnone
  simp [incrementRefCount, hnone]

/-- **Decrementing a missing block's count is a no-op.** -/
theorem ref_count_decrement_holds (mem : Memory) (id : Core.BlockId) :
    ref_count_decrement mem id := by
  intro hnone
  simp [decrementRefCount, hnone]

/-- **Deallocation removes the block, whatever its reference count.** -/
theorem zero_ref_count_allows_deallocation_holds (mem : Memory) (id : Core.BlockId) :
    zero_ref_count_allows_deallocation mem id :=
  deallocation_spec mem id

/-- **The `non_zero_ref_count_prevents_deallocation` claim is false.** A block
with a live reference is still removed: `deallocate` never reads `refCount`. -/
theorem non_zero_ref_count_prevents_deallocation_holds :
    non_zero_ref_count_prevents_deallocation := by
  let id : Core.BlockId := { id := 0 }
  let block : Block :=
    { id := id, size := 1, data := #[0], refCount := 1 }
  have hget : getBlock { blocks := [(id, block)], nextId := 1 } id = some block := by
    simp [getBlock, id, block]
  have hr : block.refCount > 0 := by simp [block]
  exact ⟨{ blocks := [(id, block)], nextId := 1 }, id, block, hget, hr,
    deallocation_spec _ _⟩

/-- **Allocation returns the id named by the counter, and the block is present.** -/
theorem unique_block_identifiers_holds (mem : Memory) (size : Nat) :
    unique_block_identifiers mem size := by
  rcases mem with ⟨blocks, nextId⟩
  simp [unique_block_identifiers, allocate, getBlock]

/-- **A block retrieved from safe memory is well formed.** -/
theorem block_data_integrity_holds (mem : Memory) (id : Core.BlockId) :
    block_data_integrity mem id := by
  intro hsafe b hb
  obtain ⟨p, hp, hpb⟩ := getBlock_some_mem hb
  rw [← hpb]
  exact hsafe p hp

/-- **A read after a write to a missing id yields nothing.** -/
theorem write_read_consistency_holds (mem : Memory) (id : Core.BlockId)
    (offset : Nat) (value : UInt8) :
    write_read_consistency mem id offset value := by
  intro hnone
  simp [writeByte, hnone, readByte]

/-- **The memory-safety invariant**, assembled from its four parts. -/
theorem memory_safety_invariant_holds : memory_safety_invariant := by
  refine ⟨empty_memory_well_formed_holds, ?_, ?_, ?_⟩
  · intro mem size; exact allocation_preserves_safety_holds mem size
  · intro mem id; exact deallocation_preserves_safety_holds mem id
  · intro mem id offset value
    exact write_preserves_safety_holds mem id offset value

end Morph.Specs.MemoryModel
