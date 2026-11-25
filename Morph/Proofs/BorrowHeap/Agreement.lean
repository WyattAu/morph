/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.BorrowHeap
import Morph.Proofs.Memory.Safety

/-!
# D2 agreement: `WFBorrow` implies `HeapSafe` (S8)

The cheapest real Stage-D theorem: a borrow-checked provenance set
projects (via `Morph.BorrowHeap.heapOf`) to a heap satisfying the whole
S5/S6 predicate. The agreement rests on the projection's faithfulness —
the canonical heap is safe by construction (`make` blocks are backed
and scrubbed, the cursor sits past every block id) — closed under the
S6 preservation theorems by reuse (`make_backed`, `make_scrubbed`).

## Stage-1 note (for the audit)

`WFBorrow` holds of *every* loan list (`WFBorrow_of_any`): field-equal
loans are value-equal by structure eta, contradicting distinctness.
The premise is kept because the sprint sketch demands the shape; the
proof's work is the projection, not the premise. Stage-2 NLL kill
(`killLoans`, already in the tree) is what makes borrow
well-formedness real — named future work, not a silent gap.
-/

namespace Morph.Proofs.BorrowHeap

open Morph.Borrows
open Morph.BorrowHeap
open Morph.MIR (ValId)

/-! ## The canonical heap is safe, clause by clause -/

/-- Blocks equation, kernel-computed (`rfl`). -/
theorem canonicalHeap_blocks (ps : List ValId) :
    (canonicalHeap ps).blocks =
      ps.map (fun v => ({ id := v }, Block.make { id := v } 1 1)) := rfl

/-- Every canonical block is backed (a `make` block always is — S6). -/
theorem canonicalHeap_backed (ps : List ValId) :
    ((canonicalHeap ps).blocks.all fun p => Morph.Memory.blockBacked p.2)
      = true := by
  rw [canonicalHeap_blocks, List.all_eq_true]
  intro v hv
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
  exact Morph.Proofs.Memory.make_backed _ 1 1

/-- Every canonical block satisfies the scrub clause (vacuously:
allocated — S6). -/
theorem canonicalHeap_scrubbed (ps : List ValId) :
    ((canonicalHeap ps).blocks.all fun p => Morph.Memory.blockScrubbed p.2)
      = true := by
  rw [canonicalHeap_blocks, List.all_eq_true]
  intro v hv
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
  exact Morph.Proofs.Memory.make_scrubbed _ 1 1

/-- `foldl max` is an upper bound for its seed. -/
theorem foldl_max_ge (b : Nat) (tl : List Nat) :
    b ≤ tl.foldl Nat.max b := by
  induction tl generalizing b with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    have hfold : (hd :: tl).foldl Nat.max b =
        tl.foldl Nat.max (Nat.max b hd) := rfl
    rw [hfold]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- `Nat.max` is monotone in its left argument — via the `max_le`
characterization and transitivity. -/
theorem max_mono_right {b₁ b₂ hd : Nat} (h : b₁ ≤ b₂) :
    Nat.max b₁ hd ≤ Nat.max b₂ hd := by
  rw [Nat.max_le]
  exact ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

/-- `foldl max` is monotone in its seed. -/
theorem foldl_max_mono {b₁ b₂ : Nat} (h : b₁ ≤ b₂) (tl : List Nat) :
    tl.foldl Nat.max b₁ ≤ tl.foldl Nat.max b₂ := by
  induction tl generalizing b₁ b₂ with
  | nil => exact h
  | cons hd tl ih =>
    have h1 : (hd :: tl).foldl Nat.max b₁ =
        tl.foldl Nat.max (Nat.max b₁ hd) := rfl
    have h2 : (hd :: tl).foldl Nat.max b₂ =
        tl.foldl Nat.max (Nat.max b₂ hd) := rfl
    rw [h1, h2]
    exact ih (max_mono_right h)

/-- Every member sits below the `foldl max` cursor seed. -/
theorem mem_le_foldl_max {v : Nat} {ps : List Nat} (hm : v ∈ ps) :
    v ≤ ps.foldl Nat.max 0 := by
  induction ps with
  | nil => simp at hm
  | cons hd tl ih =>
    have hfold : (hd :: tl).foldl Nat.max 0 =
        tl.foldl Nat.max (Nat.max 0 hd) := rfl
    rw [hfold]
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge _ _)
    · exact Nat.le_trans (ih hm) (foldl_max_mono (Nat.le_max_left _ _) _)

/-- Cursor equation, kernel-computed (`rfl`). -/
theorem canonicalHeap_next (ps : List ValId) :
    (canonicalHeap ps).nextBlockId = ps.foldl Nat.max 0 + 1 := rfl

/-- Every block id sits below the cursor — the freshness clause. -/
theorem canonicalHeap_fresh (ps : List ValId) :
    Morph.Memory.idsFresh (canonicalHeap ps) = true := by
  unfold Morph.Memory.idsFresh
  rw [canonicalHeap_blocks, canonicalHeap_next, List.all_eq_true]
  intro v hv
  obtain ⟨w, hmem, rfl⟩ := List.mem_map.mp hv
  rw [decide_eq_true_eq]
  show w < ps.foldl Nat.max 0 + 1
  have hle : w ≤ ps.foldl Nat.max 0 := mem_le_foldl_max hmem
  omega

/-! ## No spurious blocks -/

/-- Every projected block comes from a borrowed register: the bridge
creates nothing the provenance set does not name. -/
theorem canonicalHeap_mem {ps : List ValId} {id : Core.BlockId} {b : Block}
    (hmem : (id, b) ∈ (canonicalHeap ps).blocks) :
    ∃ v ∈ ps, id = { id := v } ∧ b = Block.make { id := v } 1 1 := by
  rw [canonicalHeap_blocks, List.mem_map] at hmem
  obtain ⟨v, hmem, heq⟩ := hmem
  exact ⟨v, hmem, (congrArg Prod.fst heq).symm,
    (congrArg Prod.snd heq).symm⟩

/-! ## The agreement -/

/-- Stage-1 `WFBorrow` holds of every loan list. -/
theorem WFBorrow_of_any (π : Provenances) : WFBorrow π := by
  intro l₁ _ l₂ _ hne hdup
  obtain ⟨hp, hc, hl⟩ := hdup
  exact absurd (Loan.ext hp hc hl) hne

/-- Premise-free core: a projected heap is safe. -/
theorem wfBorrow_heapSafe_of_projection {π : Provenances} {h : Memory}
    (hh : heapOf π = some h) :
    Morph.Memory.HeapSafe h := by
  have hf : heapFragment π = true := by
    cases hb : heapFragment π with
    | true => rfl
    | false =>
      rw [heapOf_none_of_fragment_false hb] at hh
      cases hh
  have hB : canonicalHeap ((basePlaces π).eraseDups) = h := by
    have hh2 := hh
    unfold heapOf at hh2
    rw [if_pos hf] at hh2
    exact Option.some.inj hh2
  subst h
  unfold Morph.Memory.HeapSafe
  exact ⟨canonicalHeap_backed _, canonicalHeap_scrubbed _,
    canonicalHeap_fresh _⟩

/-- S8 agreement, sketch shape: `WFBorrow` implies `HeapSafe` over the
projection. The premise is discharged by `WFBorrow_of_any`; kept for
the `STAGED-SCOPE.md` §4 shape. -/
theorem wfBorrow_heapSafe {π : Provenances} {h : Memory}
    (_hwf : WFBorrow π) (hh : heapOf π = some h) :
    Morph.Memory.HeapSafe h :=
  wfBorrow_heapSafe_of_projection hh

end Morph.Proofs.BorrowHeap
