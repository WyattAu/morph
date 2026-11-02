/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP3.Spec

/-!
# Feasible-50 kernels — P3 lemmas

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms.
-/

namespace Morph.Specs.BatchP3

/-! ## E-177: transitions are exact -/

/-- Every write ends modified. -/
theorem wrM_is_M (s : MESI) : wrM s = .M := by
  cases s <;> rfl

/-- Reading an invalid line shares it. -/
theorem rdM_I : rdM .I = .S := rfl

/-- Reading a shared line is stable. -/
theorem rdM_S : rdM .S = .S := rfl

/-- Reading an exclusive line is stable. -/
theorem rdM_E : rdM .E = .E := rfl

/-- Reading a modified line is stable. -/
theorem rdM_M : rdM .M = .M := rfl

/-! ## E-178: forwarding is exact -/

/-- A buffered store forwards to a later read. -/
theorem read_write_hit (buf : List (Nat × Nat)) (a v dflt : Nat) :
    readB (writeB buf a v) a dflt = v := by
  simp [writeB, readB]

/-- An unrelated address reads through. -/
theorem read_write_miss (buf : List (Nat × Nat)) (a b v dflt : Nat)
    (h : b ≠ a) : readB (writeB buf a v) b dflt = readB buf b dflt := by
  simp [writeB, readB, h]

/-! ## E-187: the ordering certificate -/

/-- A singleton trace is ordered. -/
theorem checkOrder_single (d : Desc) : checkOrder [d] = true := rfl

/-- A positive check names the head pair plus the tail. -/
theorem checkOrder_cons (d1 d2 : Desc) (rest : List Desc)
    (h : checkOrder (d1 :: d2 :: rest) = true) :
    orderedB d1 d2 = true ∧ checkOrder (d2 :: rest) = true := by
  simp only [checkOrder, Bool.and_eq_true] at h
  exact h

/-- The order test agrees with the proposition. -/
theorem orderedB_iff (d1 d2 : Desc) :
    orderedB d1 d2 = true ↔ d1.doorbell ≤ d2.doorbell := by
  simp only [orderedB, decide_eq_true_eq]

/-! ## E-199: the suite runner -/

/-- A matching case passes. -/
theorem runLitmus_match (n : Nat) : runLitmus n n = true := by
  simp [runLitmus]

/-- A positive suite means every case matched. -/
theorem suiteAll_sound : ∀ (l : List (Nat × Nat)),
    suiteAll l = true → ∀ p ∈ l, p.1 = p.2 := by
  intro l
  induction l with
  | nil => intro _ p hm; simp at hm
  | cons q qs ih =>
    intro h p hm
    simp only [suiteAll, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact h1
    · exact ih h2 p hm

/-- All-matching cases pass the suite. -/
theorem suiteAll_complete : ∀ (l : List (Nat × Nat)),
    (∀ p ∈ l, p.1 = p.2) → suiteAll l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons q qs ih =>
    intro hall
    simp only [suiteAll, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact hall q (by simp)
    · exact ih (fun p hm => hall p (List.mem_cons_of_mem _ hm))

/-! ## E-354: probes stay home and in bounds -/

/-- Offset zero stays at the home slot. -/
theorem probe_hit (h n : Nat) : probe h 0 n = h % n := by
  simp [probe]

/-- Probes stay inside the table. -/
theorem probe_bound (h i n : Nat) (hn : 0 < n) : probe h i n < n := by
  simp only [probe]
  exact Nat.mod_lt _ hn

/-! ## E-355: no false negatives -/

/-- An added index queries true. -/
theorem query_add_hit (bs hs : Bloom) (h : Nat) (hm : h ∈ hs) :
    queryB (addB bs hs) h = true := by
  simp only [queryB, decide_eq_true_eq, addB, List.mem_append]
  right
  exact hm

/-- Old indices survive an add. -/
theorem query_add_old (bs hs : Bloom) (h : Nat) (hm : h ∈ bs) :
    queryB (addB bs hs) h = true := by
  simp only [queryB, decide_eq_true_eq, addB, List.mem_append]
  left
  exact hm

/-! ## E-360: replay splits, truncation keeps the tail -/

/-- Replay over append is replay in two halves. -/
theorem replayW_append : ∀ (l1 l2 : List Nat) (s : Nat),
    replayW s (l1 ++ l2) = replayW (replayW s l1) l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 s; simp [replayW]
  | cons op ops ih =>
    intro l2 s
    simp only [List.cons_append, replayW]
    exact ih l2 (applyOp s op)

/-- Truncation keeps only checkpointed entries. -/
theorem trunc_mem (lsn : Nat) (log : List (Nat × Nat)) (e : Nat × Nat)
    (h : e ∈ trunc lsn log) : lsn ≤ e.1 := by
  simp only [trunc, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

/-! ## E-362: isolation by construction -/

/-- A written key reads back. -/
theorem write_hit (s : List (Nat × Nat)) (k v : Nat) :
    readStore (writeStore s k v) k = some v := by
  simp [writeStore, readStore]

/-- Other keys read through. -/
theorem write_miss (s : List (Nat × Nat)) (k key v : Nat) (h : key ≠ k) :
    readStore (writeStore s k v) key = readStore s key := by
  simp [writeStore, readStore, h]

/-- Snapshots read what the store read. -/
theorem snap_read (s : List (Nat × Nat)) (k : Nat) :
    readSnap (takeSnap s) k = readStore s k := rfl

/-- A snapshot taken over a write sees the write. -/
theorem snap_write (s : List (Nat × Nat)) (k v : Nat) :
    readSnap (takeSnap (writeStore s k v)) k = some v := by
  simp [readSnap, takeSnap, write_hit]

/-! ## E-363: begun-and-live is visible -/

/-- A live row begun before `ts` is visible. -/
theorem vis_live (v : Ver) (ts : Nat) (h1 : v.beginV ≤ ts) (h2 : v.endV = 0) :
    visible v ts = true := by
  simp only [visible, decide_eq_true_eq]
  rw [h2]
  exact ⟨h1, Or.inl rfl⟩

/-- A row begun after `ts` is invisible. -/
theorem invis_future (v : Ver) (ts : Nat) (h : ts < v.beginV) :
    visible v ts = false := by
  simp only [visible, decide_eq_false_iff_not]
  intro hc
  omega

/-! ## E-366: the view tracks the base -/

/-- Adding a row adds to the view. -/
theorem view_add (bs : List Nat) (x : Nat) :
    view (addView bs x) = x + view bs := by
  simp [view, addView, List.sum_cons]

end Morph.Specs.BatchP3
