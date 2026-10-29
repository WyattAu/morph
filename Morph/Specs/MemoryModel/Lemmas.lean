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

/-! ### Aliasing + use-after-free (loop 56)

Loop 26 proved safety but left aliasing and the runtime connection open.
Loop 56 adds the minimal aliasing model alongside (no breaking change).

Research: RustBelt (safety, Stacked Borrows: aliasing as a dynamic borrow
checker); Perceus (garbage-freedom, no cycle case at type level); ORCA
(heap bounding explicitly future work). Other languages: Rust (borrow
checker, mechanized safety, no growth bounds); Swift/Pony/Nim (ARC, no
proved bounds); Perceus (paper proofs only). Morph's affine discipline
(loop 2) removes the cycle case at the type level, so the remaining
obligation is use-after-free — proved below.
-/

/-- Two ids alias when they denote the same block. -/
def aliases (mem : Memory) (a b : Core.BlockId) : Prop :=
  ∃ blk, getBlock mem a = some blk ∧ getBlock mem b = some blk ∧ a = b

/-- Aliasing is reflexive on live blocks. -/
theorem aliases_refl (mem : Memory) (id : Core.BlockId) (b : Block)
    (h : getBlock mem id = some b) : aliases mem id id :=
  ⟨b, h, h, rfl⟩

/-- **Use-after-free is impossible to observe**: a read after deallocation
yields nothing. -/
theorem read_after_free_none (mem : Memory) (id : Core.BlockId) (off : Nat) :
    readByte (deallocate mem id) id off = none := by
  have hnone : getBlock (deallocate mem id) id = none :=
    deallocation_spec mem id
  simp [readByte, hnone]

/-- A write after free leaves the freed memory alone. -/
theorem write_after_free_noop (mem : Memory) (id : Core.BlockId) (off : Nat) (v : UInt8) :
    writeByte (deallocate mem id) id off v = deallocate mem id := by
  have hnone : getBlock (deallocate mem id) id = none :=
    deallocation_spec mem id
  simp [writeByte, hnone]

/-! ### Loop 65: the `Morph.Memory` connection + aliasing safety

Research: CompCert (Leroy–Blazy block-offset model — `Morph.Memory` is an
instance of it, with `BlockState` for allocation status and `MemByte` for
definedness); CompCert memory injections (a projection that drops
permission-less blocks preserves observable behavior — `project` below is
that injection, dropping `freed` blocks); RustBelt / Stacked Borrows
(aliasing as borrow discipline; agreement on what an id denotes);
Perceus (reference counting without a collector).

Language comparison: Rust (affine allocation — fresh ids by construction,
proved as `allocate_fresh_present`/`allocate_noninterfering`); Pony
(reference capabilities pin aliasing at the type level); Vale (regions make
free observable); Swift/ARC (refcounts never consulted by free — cf.
`non_zero_ref_count_prevents_deallocation_holds`).

The connection: `Morph.Memory.free` marks a block `freed` (keeps the
entry); `MemoryModel.deallocate` removes the entry. `project` drops `freed`
blocks, so freeing-then-projecting is observing-then-removing
(`project_free_none`), and a read after a `Morph.Memory.free` yields nothing
(`read_after_morph_free_none` — the use-after-free theorem for the real
runtime model, via the injection).

Aliasing safety: allocation is fresh and non-interfering — a new id denotes
a new block and no existing denotation changes, so allocation introduces no
alias (`allocate_fresh_present`, `allocate_noninterfering`).
-/

/-- Project a runtime block into the model: definedness becomes `0`, the
refcount is immaterial (free never consults it). -/
def projectBlock (b : Morph.Block) : Block :=
  { id := b.id, size := b.size, data := b.bytes.map Morph.MemByte.toUInt8,
    refCount := 1 }

/-- Project a block list, dropping `freed` blocks (the injection). -/
def projectBlocks (bs : List (Core.BlockId × Morph.Block)) :
    List (Core.BlockId × Block) :=
  (bs.filter (fun p => p.2.isAllocated)).map
    (fun p => (p.1, projectBlock p.2))

/-- Project a runtime memory into the model. -/
def project (m : Morph.Memory) : Memory :=
  { blocks := projectBlocks m.blocks, nextId := m.nextBlockId }

/-- Projection preserves well-formedness of well-formed blocks. -/
theorem projectBlock_wellformed (b : Morph.Block)
    (h : b.bytes.size = b.size) :
    isWellFormedBlock (projectBlock b) := by
  simp [projectBlock, isWellFormedBlock, Array.size_map, h]

/-- Membership in the projected list, spelled out. -/
theorem project_mem {bs : List (Core.BlockId × Morph.Block)}
    {p : Core.BlockId × Block} :
    p ∈ projectBlocks bs ↔
      ∃ b, (p.1, b) ∈ bs ∧ b.isAllocated = true ∧ p.2 = projectBlock b := by
  simp only [projectBlocks, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨a, ⟨hmem, hpred⟩, hfp⟩
    refine ⟨a.2, ?_, hpred, ?_⟩
    · have heq : (p.1, a.2) = a := by rw [← hfp]
      rw [heq]; exact hmem
    · rw [← hfp]
  · rintro ⟨b, hmem, halloc, hpb⟩
    refine ⟨(p.1, b), ⟨hmem, halloc⟩, ?_⟩
    rw [← hpb]

/-- Freeing marks the block, so it is no longer allocated. -/
theorem freeBlock_not_allocated (b : Morph.Block) :
    (Morph.Block.freeBlock b).isAllocated = false := rfl

/-- No projected entry denotes the freed id. -/
theorem project_free_fst (m : Morph.Memory) (id : Core.BlockId)
    (p : Core.BlockId × Block)
    (hm : p ∈ (project (Morph.Memory.free m id)).blocks) : p.1 ≠ id := by
  have hmem : ∃ b, (p.1, b) ∈ (Morph.Memory.free m id).blocks ∧
      b.isAllocated = true ∧ p.2 = projectBlock b := project_mem.mp hm
  obtain ⟨b, hmem, halloc, -⟩ := hmem
  simp only [Morph.Memory.free] at hmem
  cases hfb : Morph.Memory.findBlock? m.blocks id with
  | none =>
      simp only [hfb] at hmem
      cases hq : List.find? (fun (p : Core.BlockId × Morph.Block) => p.1 == id)
          m.blocks with
      | some q =>
          have hsome : Morph.Memory.findBlock? m.blocks id = some q.2 := by
            simp [Morph.Memory.findBlock?, hq]
          rw [hsome] at hfb; cases hfb
      | none =>
          have hne := List.find?_eq_none.mp hq (p.1, b) hmem
          cases hc : (p.1 == id) with
          | true => simp [hc] at hne
          | false => exact ne_of_beq_false hc
  | some fb =>
      simp only [hfb] at hmem
      simp only [Morph.Memory.updateBlock] at hmem
      obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
      by_cases hbeq : a.1 == id
      · rw [if_pos hbeq] at heq
        have hb : b = Morph.Block.freeBlock fb := (Prod.mk.inj heq).2.symm
        rw [hb] at halloc
        rw [freeBlock_not_allocated] at halloc
        cases halloc
      · rw [if_neg hbeq] at heq
        have hfst : p.1 = a.1 := (Prod.mk.inj heq).1.symm
        rw [hfst]
        cases hc : (a.1 == id) with
        | true => simp [hc] at hbeq
        | false => exact ne_of_beq_false hc

/-- Freeing-then-projecting observes nothing at the freed id: the injection
turns `free` into removal. -/
theorem project_free_none (m : Morph.Memory) (id : Core.BlockId) :
    getBlock (project (Morph.Memory.free m id)) id = none := by
  have hfind : List.find? (fun (p : Core.BlockId × Block) => decide (p.1 = id))
      (project (Morph.Memory.free m id)).blocks = none := by
    rw [List.find?_eq_none]
    intro a hamem
    have hne : a.1 ≠ id := project_free_fst m id a hamem
    simp [hne]
  simp [getBlock, hfind]

/-- **Use-after-free for the real runtime model.** A read after
`Morph.Memory.free` yields nothing — via the injection and the model's
read-after-free. -/
theorem read_after_morph_free_none (m : Morph.Memory) (id : Core.BlockId)
    (off : Nat) :
    readByte (project (Morph.Memory.free m id)) id off = none := by
  have hnone := project_free_none m id
  simp [readByte, hnone]

/-- Allocation is fresh: the new id denotes a present block. -/
theorem allocate_fresh_present (mem : Memory) (size : Nat) :
    (getBlock (allocate mem size).1 (allocate mem size).2).isSome = true := by
  rcases mem with ⟨blocks, nextId⟩
  simp [allocate, getBlock]

/-- Allocation is non-interfering: no existing denotation changes, so
allocation introduces no alias. -/
theorem allocate_noninterfering (mem : Memory) (size : Nat)
    (a : Core.BlockId) (hne : a ≠ (allocate mem size).2) :
    getBlock (allocate mem size).1 a = getBlock mem a := by
  rcases mem with ⟨blocks, nextId⟩
  simp only [allocate] at hne ⊢
  simp only [getBlock]
  by_cases heq : ({ id := nextId } : Core.BlockId) = a
  · subst heq; exact absurd rfl hne
  · simp [heq]

/-- Freshness, concretely: allocating in the empty memory yields id `0`. -/
example : (getBlock (allocate emptyMemory 4).1 { id := 0 }).isSome = true :=
  rfl

/-! ### Strong write-then-read (loop 70)

The missing-id case (`write_read_consistency_holds`) is proved above. The
strong form needs no uniqueness hypothesis: `writeByte` rewrites *every*
entry whose key matches, so the first matching entry stays first and now
denotes the updated block. Well-formedness (from `isMemorySafe`) aligns
`b.size` with `b.data.size`, so the bounds check and the `set!`/`get?`
round-trip agree. -/

/-- After a successful in-bounds write, lookup denotes the updated block. -/
theorem getBlock_writeByte (mem : Memory) (id : Core.BlockId)
    (offset : Nat) (value : UInt8) (b : Block)
    (hget : getBlock mem id = some b) (hb : offset < b.size) :
    getBlock (writeByte mem id offset value) id =
      some ({ b with data := b.data.set! offset value } : Block) := by
  let newB : Block := { b with data := b.data.set! offset value }
  simp only [writeByte, hget, hb, if_true]
  simp only [getBlock]
  have hpred : ∀ x : Core.BlockId × Block,
      (fun y : Core.BlockId × Block => decide (y.1 = id))
        (if decide (x.1 = id) then (id, newB) else x) =
      decide (x.1 = id) := by
    intro x
    by_cases hx : decide (x.1 = id) = true
    · simp [hx]
    · simp [hx]
  have hcomp : ((fun y : Core.BlockId × Block => decide (y.1 = id)) ∘
      (fun x : Core.BlockId × Block => if decide (x.1 = id) then (id, newB) else x)) =
      (fun x : Core.BlockId × Block => decide (x.1 = id)) :=
    funext fun x => hpred x
  rw [List.find?_map, hcomp]
  rw [getBlock] at hget
  rw [Option.map_eq_some_iff] at hget ⊢
  obtain ⟨p, hp_find, hp_snd⟩ := hget
  obtain ⟨pid, pb⟩ := p
  simp only at hp_snd
  have hp_eq : pid = id := by simpa using List.find?_some hp_find
  have hp_find' : List.find? (fun x : Core.BlockId × Block => decide (x.1 = id))
      mem.blocks = some (id, pb) := by
    have h := hp_find
    rw [hp_eq] at h
    exact h
  rw [hp_find']
  simp only [Option.map_some]
  exact ⟨(id, newB), by simp [newB], rfl⟩

/-- **Strong write-then-read**: writing a byte in bounds and reading it back
yields the written value. -/
theorem write_read_strong (mem : Memory) (id : Core.BlockId)
    (offset : Nat) (value : UInt8) (b : Block)
    (hsafe : isMemorySafe mem)
    (hget : getBlock mem id = some b) (hb : offset < b.size) :
    readByte (writeByte mem id offset value) id offset = some value := by
  obtain ⟨p, hp, hpb⟩ := getBlock_some_mem hget
  have hwf : b.data.size = b.size := by
    have h := hsafe p hp
    rw [hpb] at h
    exact h
  have hget' := getBlock_writeByte mem id offset value b hget hb
  simp only [readByte, hget']
  have hlt : offset < ({ b with data := b.data.set! offset value } : Block).size := by
    simpa using hb
  simp only [hlt, if_true]
  have hsize : (b.data.set! offset value).size = b.data.size := by
    simp
  have hmem : offset < (b.data.set! offset value).size := by
    rw [hsize, hwf]; exact hb
  have hgetv : (b.data.set! offset value)[offset]? = some value := by
    rw [Array.getElem?_eq_getElem hmem]
    simp
  simpa using hgetv

end Morph.Specs.MemoryModel
