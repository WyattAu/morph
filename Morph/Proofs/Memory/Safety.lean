/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Memory

/-! # D1 preservation (S6)

`HeapSafe` is preserved by allocation and freeing unconditionally, and
by block writes under the allocated premise. Two honest deviations
from the `heapWrite_safe` sketch in `docs/STAGED-SCOPE.md` §4, both
forced by the tree rather than chosen:

- The sketched shape presumes partial wrappers (`= some h'`), but no
  partial memory ops exist — `Block.write`/`read` and `Memory.free`
  are total. The theorems below are the total-op version: `HeapSafe`
  in, `HeapSafe` out, with no `Option` in between.
- `Block.write` performs no state check (the S5/S6 pins exhibit the
  bypass: writing into a freed block and installing it by hand), so
  write-preservation carries the allocated premise. `Memory.free`
  needs no premise — scrub-in-`free` (S6 provisional, revertible)
  makes the freed clause hold by construction.
- Read-preservation is vacuous and so not stated: `Block.read` and
  `Memory.getBlock?` are pure projections; no memory-level read
  modifies state, so there is nothing to preserve.

Provisional status: the scrub-in-`free` default stands in for the S5
attack per the sprint's dated-decision rule; a wrong default here
costs a revert of `Block.freeBlock` plus the two `freeBlock_*`
lemmas below, nothing else.
-/

open Morph

namespace Morph.Proofs.Memory

/-! ## Block-level facts -/

/-- Writes preserve the byte-array size. -/
theorem write_bytes_size (b : Block) (off : Nat) (v : MemByte) :
    (Block.write b off v).bytes.size = b.bytes.size := by
  unfold Block.write
  split
  · simp [Array.size_setIfInBounds]
  · rfl

/-- Writes preserve the block state. -/
theorem write_state (b : Block) (off : Nat) (v : MemByte) :
    (Block.write b off v).state = b.state := by
  unfold Block.write
  split <;> rfl

/-- Writes preserve the size field. -/
theorem write_size (b : Block) (off : Nat) (v : MemByte) :
    (Block.write b off v).size = b.size := by
  unfold Block.write
  split <;> rfl

/-- Writes preserve backing. -/
theorem write_backed (b : Block) (off : Nat) (v : MemByte)
    (h : Memory.blockBacked b = true) :
    Memory.blockBacked (Block.write b off v) = true := by
  have ha : (Block.write b off v).isAllocated = b.isAllocated := by
    simp only [Block.isAllocated, write_state b off v]
  have hs := write_bytes_size b off v
  have hz := write_size b off v
  simp only [Memory.blockBacked, ha, hs, hz]
  exact h

/-- Writes into allocated blocks preserve the scrub clause (vacuously:
an allocated block is not freed). -/
theorem write_scrubbed_of_allocated (b : Block) (off : Nat) (v : MemByte)
    (h : b.isAllocated = true) :
    Memory.blockScrubbed (Block.write b off v) = true := by
  -- No `LawfulBEq BlockState` instance exists (and none is added, to keep
  -- the change surface minimal), so the allocated premise is discharged
  -- by casing on the state instead of bridging `==` to `=`.
  have hs := write_state b off v
  have hbeq : (BlockState.freed == BlockState.allocated) = false := rfl
  have hf : (Block.write b off v).isFreed = false := by
    simp only [Block.isFreed, hs, Block.isAllocated] at h ⊢
    cases st : b.state with
    | allocated => rfl
    | freed =>
      rw [st, hbeq] at h
      exact Bool.noConfusion h
  simp only [Memory.blockScrubbed, hf, Bool.not_false, Bool.true_or]

/-- `make` fixes the state to allocated. -/
theorem make_state (id : Core.BlockId) (size alignment : Nat) :
    (Block.make id size alignment).state = BlockState.allocated := rfl

/-- Fresh blocks are backed. -/
theorem make_backed (id : Core.BlockId) (size alignment : Nat) :
    Memory.blockBacked (Block.make id size alignment) = true := by
  simp [Memory.blockBacked, Block.make, Block.isAllocated]

/-- Fresh blocks satisfy the scrub clause (vacuously: allocated). -/
theorem make_scrubbed (id : Core.BlockId) (size alignment : Nat) :
    Memory.blockScrubbed (Block.make id size alignment) = true := by
  have hf : (Block.make id size alignment).isFreed = false := by
    simp only [Block.isFreed, make_state]
    rfl
  simp only [Memory.blockScrubbed, hf, Bool.not_false, Bool.true_or]

/-- `freeBlock` fixes the state to freed. -/
theorem freeBlock_state (b : Block) :
    (Block.freeBlock b).state = BlockState.freed := rfl

/-- Freed blocks are backed (vacuously: not allocated). Needs no
premise — the state flip alone discharges it. -/
theorem freeBlock_backed (b : Block) :
    Memory.blockBacked (Block.freeBlock b) = true := by
  have h1 : (Block.freeBlock b).isAllocated = false := by
    simp only [Block.isAllocated, freeBlock_state]
    rfl
  simp only [Memory.blockBacked, h1, Bool.not_false, Bool.true_or]

/-- Freed blocks are scrubbed (by construction: bytes are replaced
with `undef`). Needs no premise — this is the payoff of
scrub-in-`free`. -/
theorem freeBlock_scrubbed (b : Block) :
    Memory.blockScrubbed (Block.freeBlock b) = true := by
  have h1 : (Block.freeBlock b).isFreed = true := by
    simp only [Block.isFreed, freeBlock_state]
    rfl
  have h2 : (Block.freeBlock b).bytes =
      Array.replicate b.size MemByte.undef := rfl
  simp only [Memory.blockScrubbed, h1, Bool.not_true, Bool.false_or, h2]
  rw [Array.all_replicate]
  split <;> rfl

/-! ## List transport helpers -/

/-- Pointwise Bool transport under `List.all`. -/
theorem all_mono {p q : α → Bool} (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true)
    (hall : l.all p = true) : l.all q = true := by
  rw [List.all_eq_true] at hall ⊢
  exact fun x hx => h x hx (hall x hx)

/-- `updateBlock` preserves any block predicate the installed block
satisfies. -/
theorem updateBlock_all (P : Block → Bool) (b : Block)
    (hPb : P b = true) (bs : List (Core.BlockId × Block)) (id : Core.BlockId)
    (hall : (bs.all fun p => P p.2) = true) :
    ((Memory.updateBlock bs id b).all fun p => P p.2) = true := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨bid, b'⟩ := hd
    unfold Memory.updateBlock at *
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hall ⊢
    by_cases heq : bid == id
    · rw [if_pos heq] at ⊢
      exact ⟨hPb, ih hall.2⟩
    · rw [if_neg heq] at ⊢
      exact ⟨hall.1, ih hall.2⟩

/-- `updateBlock` preserves id freshness (the installed pair reuses a
numeral already below the cursor). -/
theorem updateBlock_ids (bs : List (Core.BlockId × Block)) (id : Core.BlockId)
    (b : Block) (n : Nat)
    (hall : (bs.all fun p => decide (p.1.id < n)) = true) :
    ((Memory.updateBlock bs id b).all fun p =>
      decide (p.1.id < n)) = true := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨bid, b'⟩ := hd
    unfold Memory.updateBlock at *
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hall ⊢
    by_cases heq : bid == id
    · rw [if_pos heq] at ⊢
      have hid : bid = id := by simpa using heq
      rw [hid] at hall
      exact ⟨hall.1, ih hall.2⟩
    · rw [if_neg heq] at ⊢
      exact ⟨hall.1, ih hall.2⟩

/-- Freshness bounds step upward with the cursor. -/
theorem lt_succ_dec {a b : Nat} (h : decide (a < b) = true) :
    decide (a < b + 1) = true := by
  rw [decide_eq_true_eq]
  have h' := of_decide_eq_true h
  omega

/-! ## Memory-level preservation (the S6 exit) -/

/-- Allocation preserves `HeapSafe`. -/
theorem allocate_preserves (m : Memory) (size alignment : Nat)
    (h : Memory.HeapSafe m) : Memory.HeapSafe (m.allocate size alignment).1 := by
  obtain ⟨hb, hs, hi⟩ := h
  -- Kernel-computed projections (`rfl` proves them; tactics cannot see
  -- through the `let`s and record projections, so they are rewritten).
  have e : ((m.allocate size alignment).1).blocks =
      (({ id := m.nextBlockId },
        Block.make { id := m.nextBlockId } size alignment) ::
        m.blocks) := rfl
  have en : ((m.allocate size alignment).1).nextBlockId =
      m.nextBlockId + 1 := rfl
  unfold Memory.HeapSafe Memory.idsFresh
  rw [e, en]
  simp only [List.all_cons, Bool.and_eq_true]
  exact ⟨⟨make_backed _ _ _, hb⟩,
    ⟨make_scrubbed _ _ _, hs⟩,
    ⟨by simp,
      all_mono _ (fun _ hx hlt => lt_succ_dec hlt) hi⟩⟩

/-- Freeing preserves `HeapSafe` — unconditionally, via the two
premise-free `freeBlock_*` lemmas. -/
theorem free_preserves (m : Memory) (id : Core.BlockId)
    (h : Memory.HeapSafe m) : Memory.HeapSafe (m.free id) := by
  obtain ⟨hb, hs, hi⟩ := h
  unfold Memory.free
  split
  · rename_i block hfind
    have e : ({ m with blocks :=
        Memory.updateBlock m.blocks id (Block.freeBlock block) } :
        Memory).blocks =
        Memory.updateBlock m.blocks id (Block.freeBlock block) := rfl
    unfold Memory.HeapSafe
    rw [e]
    exact ⟨updateBlock_all _ _ (freeBlock_backed _) _ _ hb,
      updateBlock_all _ _ (freeBlock_scrubbed _) _ _ hs,
      updateBlock_ids _ _ _ _ hi⟩
  · exact ⟨hb, hs, hi⟩

end Morph.Proofs.Memory

