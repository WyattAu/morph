/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchHIJ.Spec

/-!
# Frontier Kernels — lemmas (E-58–E-67)

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms: every
theorem is proved by structural induction with `simp`/`omega` (plus `ring`
for the ADHM commutator) over the definitions above. BatchHIJ covers
ADR-019 Batch H remainder (E-58–E-60), Batch I (E-61–E-65), and Batch J
start (E-66, E-67).
-/

namespace Morph.Specs.BatchHIJ

/-! ## E-58: the drop-free certificate -/

/-- A drop-free step accounts exactly: level plus drain equals inflow. -/
theorem dropFree_sound (buf burst drain : Nat)
    (h : dropFree buf burst drain = true) :
    stepBuf buf burst drain + drain = buf + burst := by
  simp only [dropFree, decide_eq_true_eq] at h
  simp only [stepBuf]
  omega

/-- The level never exceeds what arrived. -/
theorem stepBuf_le (buf burst drain : Nat) :
    stepBuf buf burst drain ≤ buf + burst := by
  simp only [stepBuf]
  omega

/-- An all-zero schedule preserves the level. -/
theorem drainAll_zero (buf : Nat) :
    ∀ n : Nat, drainAll buf (List.replicate n (0, 0)) = buf := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, drainAll, stepBuf, ih]

/-! ## E-59: the wall-crossing certificate -/

/-- A positive wall test names a wall strictly on the update path. -/
theorem between_sound (l l' w : Nat) (h : between l l' w = true) :
    l < w ∧ w ≤ l' := by
  simp only [between, decide_eq_true_eq] at h
  exact h

/-- The empty barcode is never crossed. -/
theorem crosses_empty (l l' : Nat) : crosses l l' [] = false := rfl

/-- A positive crossing test names a tracked wall on the path. -/
theorem crosses_sound : ∀ (l l' : Nat) (ws : List Nat),
    crosses l l' ws = true → ∃ w ∈ ws, l < w ∧ w ≤ l' := by
  intro l l' ws
  induction ws with
  | nil => intro h; simp [crosses] at h
  | cons w ws ih =>
    intro h
    simp only [crosses, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨w, by simp,
        by simp only [between, decide_eq_true_eq] at h; exact h⟩
    · obtain ⟨v, hm, hlt, hle⟩ := ih h
      exact ⟨v, List.mem_cons_of_mem _ hm, hlt, hle⟩

/-- A negative crossing test means no tracked wall lies on the path. -/
theorem crosses_none : ∀ (l l' : Nat) (ws : List Nat),
    crosses l l' ws = false → ∀ w ∈ ws, ¬(l < w ∧ w ≤ l') := by
  intro l l' ws
  induction ws with
  | nil => intro _ w hm; simp at hm
  | cons w ws ih =>
    intro h v hv
    simp only [crosses] at h
    have hb : between l l' w = false := by
      cases hc : between l l' w with
      | true => simp [hc] at h
      | false => rfl
    simp [hb] at h
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hm
    · simp only [between, decide_eq_false_iff_not] at hb
      exact hb
    · exact ih h v hm

/-! ## E-60: the HN-sign certificate -/

/-- The flag agrees with positivity of the degree. -/
theorem hnFlag_iff (b : Bundle) : hnFlag b = true ↔ 0 < b.deg := by
  simp only [hnFlag, decide_eq_true_eq]

/-- A positive polygon test names a positive-slope bundle. -/
theorem flagAll_sound : ∀ bs : List Bundle,
    flagAll bs = true → ∃ b ∈ bs, 0 < b.deg := by
  intro bs
  induction bs with
  | nil => intro h; simp [flagAll] at h
  | cons b bs ih =>
    intro h
    simp only [flagAll, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨b, by simp,
        by simp only [hnFlag, decide_eq_true_eq] at h; exact h⟩
    · obtain ⟨c, hm, hp⟩ := ih h
      exact ⟨c, List.mem_cons_of_mem _ hm, hp⟩

/-- A positive-slope bundle anywhere raises the polygon flag. -/
theorem flagAll_complete : ∀ bs : List Bundle,
    (∃ b ∈ bs, 0 < b.deg) → flagAll bs = true := by
  intro bs
  induction bs with
  | nil => intro h; obtain ⟨b, hm, _⟩ := h; simp at hm
  | cons b bs ih =>
    intro h
    obtain ⟨c, hm, hp⟩ := h
    simp only [List.mem_cons] at hm
    simp only [flagAll, Bool.or_eq_true]
    rcases hm with rfl | hm
    · left
      simp only [hnFlag, decide_eq_true_eq]
      exact hp
    · right
      exact ih ⟨c, hm, hp⟩

/-! ## E-61: independent linear flows -/

/-- A flow never goes negative past its starting quantity. -/
theorem flow1_le (q r t : Nat) : flow1 q r t ≤ q := by
  simp only [flow1]
  omega

/-- Drained plus remaining equals the starting quantity. -/
theorem drained_add (q r t : Nat) : flow1 q r t + drained q r t = q := by
  simp only [drained, flow1]
  omega

/-- A zero rate leaves every quantity untouched. -/
theorem flow1_zero (q t : Nat) : flow1 q 0 t = q := by
  simp [flow1]

/-- Decoupling preserves the asset count. -/
theorem liquidate_length : ∀ (qs : List Nat) (r t : Nat),
    (liquidate qs r t).length = qs.length := by
  intro qs
  induction qs with
  | nil => intro r t; rfl
  | cons q qs ih => intro r t; simp [liquidate, ih]

/-! ## E-62: the descent step -/

/-- One migration preserves total load. -/
theorem stepKN_sum (p : KNPair) :
    (stepKN p).lo + (stepKN p).hi = p.lo + p.hi := by
  unfold stepKN
  by_cases h : (p.lo < p.hi ∧ 1 < knGap p)
  · rw [if_pos h]
    show p.lo + 1 + (p.hi - 1) = p.lo + p.hi
    have hlo : p.lo < p.hi := h.1
    omega
  · rw [if_neg h]

/-- A live migration shrinks the gap by exactly two. -/
theorem stepKN_gap2 (p : KNPair) (h1 : p.lo < p.hi) (h2 : 1 < knGap p) :
    knGap (stepKN p) + 2 = knGap p := by
  have h : (p.lo < p.hi ∧ 1 < knGap p) := ⟨h1, h2⟩
  have h3 : knGap p = p.hi - p.lo := rfl
  unfold stepKN
  rw [if_pos h]
  simp only [knGap]
  omega

/-- At gap 0 or 1 the state is μ-equilibrium: the flow stops. -/
theorem stepKN_stable (p : KNPair) (h : knGap p ≤ 1) : stepKN p = p := by
  have h2 : knGap p = p.hi - p.lo := rfl
  unfold stepKN
  exact if_neg (by omega)

/-! ## E-63: the ADHM equation over commuting scalars -/

/-- The commutator vanishes, so the error is `I * J`. -/
theorem adhmErr_eq (a : ADHM) : adhmErr a = a.i * a.j := by
  simp only [adhmErr]
  have h : a.b1 * a.b2 = a.b2 * a.b1 := Int.mul_comm _ _
  omega

/-- Admission is exactly the vanishing of `I * J`. -/
theorem admitA_iff (a : ADHM) : admitA a = true ↔ a.i * a.j = 0 := by
  simp only [admitA, decide_eq_true_eq, adhmErr_eq]

/-- A zero left leg always admits. -/
theorem admitA_zero (a : ADHM) (h : a.i = 0) : admitA a = true := by
  rw [admitA_iff, h, Int.zero_mul]

/-- Exact admission implies tolerant admission. -/
theorem admitTol_of_admit (a : ADHM) (tol : Int) (h : admitA a = true) :
    admitTol a tol = true := by
  simp only [admitTol, decide_eq_true_eq]
  simp only [admitA, decide_eq_true_eq] at h
  left
  exact h

/-! ## E-64: the contractive-regime guard -/

/-- Staying agrees with the expansion bound. -/
theorem stay_iff (e T : Nat) : stay e T = true ↔ e < T := by
  simp only [stay, decide_eq_true_eq]

/-- Pruned branches never exceed the trace length. -/
theorem pruneCount_le : ∀ (es : List Nat) (T : Nat),
    pruneCount es T ≤ es.length := by
  intro es
  induction es with
  | nil => intro T; simp [pruneCount]
  | cons e es ih =>
    intro T
    simp only [pruneCount, List.length_cons]
    have ihT := ih T
    by_cases h : stay e T = true <;> simp [h] <;> omega

/-- An all-contractive trace is never pruned. -/
theorem pruneCount_all_stay : ∀ (es : List Nat) (T : Nat),
    (∀ e ∈ es, e < T) → pruneCount es T = 0 := by
  intro es
  induction es with
  | nil => intro T _; rfl
  | cons e es ih =>
    intro T hall
    have he : e < T := hall e (by simp)
    have ht : ∀ x ∈ es, x < T :=
      fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have hs : stay e T = true := by simp [stay, he]
    simp only [pruneCount, hs, if_true, ih T ht, Nat.add_zero]

/-! ## E-65: the two-slice shaper -/

/-- The slices add back to the order. -/
theorem split2_add (total : Nat) :
    (split2 total).1 + (split2 total).2 = total := by
  simp only [split2]
  omega

/-- Each slice fits inside the order. -/
theorem split2_fst_le (total : Nat) : (split2 total).1 ≤ total := by
  simp only [split2]
  exact Nat.div_le_self _ _

/-- The second slice fits inside the order. -/
theorem split2_snd_le (total : Nat) : (split2 total).2 ≤ total := by
  simp only [split2]
  omega

/-- Splitting never increases the linear impact model. -/
theorem shapeImpact_le (total : Nat) :
    shapeImpact total ≤ total * total := by
  have hab : total / 2 + (total - total / 2) = total := by omega
  have d1 := Nat.add_mul (total / 2) (total - total / 2)
    (total / 2 + (total - total / 2))
  have d2 := Nat.mul_add (total / 2) (total / 2) (total - total / 2)
  have d3 := Nat.mul_add (total - total / 2) (total / 2) (total - total / 2)
  have e : (total / 2 + (total - total / 2)) * (total / 2 + (total - total / 2))
      = (total / 2) * (total / 2) + (total - total / 2) * (total - total / 2)
        + ((total / 2) * (total - total / 2)
          + (total - total / 2) * (total / 2)) := by
    omega
  have ht : total * total
      = (total / 2 + (total - total / 2)) * (total / 2 + (total - total / 2)) := by
    rw [hab]
  simp only [shapeImpact, split2]
  omega

/-! ## E-66: the Hörmander disjointness check -/

/-- A positive disjointness test means no shared covector. -/
theorem disjointD_sound : ∀ (l1 l2 : List Nat),
    disjointD l1 l2 = true → ∀ d ∈ l1, d ∉ l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _ d hm; simp at hm
  | cons x xs ih =>
    intro l2 h d hd
    simp only [disjointD, Bool.and_eq_true] at h
    obtain ⟨hx, hrest⟩ := h
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hm
    · simp only [decide_eq_true_eq] at hx
      exact hx
    · exact ih l2 hrest d hm

/-- No shared covector makes the test pass. -/
theorem disjointD_complete : ∀ (l1 l2 : List Nat),
    (∀ d ∈ l1, d ∉ l2) → disjointD l1 l2 = true := by
  intro l1
  induction l1 with
  | nil => intro l2 _; rfl
  | cons x xs ih =>
    intro l2 hall
    simp only [disjointD, Bool.and_eq_true]
    constructor
    · simp only [decide_eq_true_eq]
      exact hall x (by simp)
    · exact ih l2 (fun d hd => hall d (List.mem_cons_of_mem _ hd))

/-- An elided fence shares no wave-front direction. -/
theorem elideFence_sound (wf1 wf2 : List Nat) (h : elideFence wf1 wf2 = true) :
    ∀ d ∈ wf1, d ∉ wf2 := by
  simp only [elideFence] at h
  exact disjointD_sound _ _ h

/-! ## E-67: the chamber-exit guard -/

/-- A fired anchor names a chamber exit. -/
theorem anchor_sound (d i d' i' : Nat) (h : anchor d i d' i' = true) :
    0 < charge d i ∧ charge d' i' ≤ 0 := by
  simp only [anchor, decide_eq_true_eq] at h
  exact h

/-- A still-positive book never anchors. -/
theorem anchor_stable (d i d' i' : Nat) (h : 0 < charge d' i') :
    anchor d i d' i' = false := by
  unfold anchor
  rw [decide_eq_false_iff_not]
  intro hc
  simp only [charge] at h hc
  omega

/-- Firing the guard holds the quoted depth. -/
theorem heldAfter_anchor (d i d' i' : Nat) (h : anchor d i d' i' = true) :
    heldAfter d i d' i' = d := by
  simp [heldAfter, h]

/-- A quiet guard passes inventory through. -/
theorem heldAfter_noanchor (d i d' i' : Nat) (h : anchor d i d' i' = false) :
    heldAfter d i d' i' = i' := by
  simp [heldAfter, h]

end Morph.Specs.BatchHIJ
