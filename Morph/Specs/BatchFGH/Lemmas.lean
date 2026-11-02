/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchFGH.Spec

/-!
# Frontier Kernels — lemmas (E-48–E-57)

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms: every
theorem is proved by structural induction with `simp`/`omega` over the
definitions above. BatchFGH covers ADR-019 Batch F remainder (E-48–E-50),
Batch G (E-51–E-55), and Batch H start (E-56, E-57).
-/

namespace Morph.Specs.BatchFGH

/-! ## E-48: mutation is an involution and preserves positivity -/

/-- Mutating twice with the exchange data returns the seed. -/
theorem mut0_invol : ∀ (s : Seed) (num q : Int),
    num == q * s.x → mut0 (mut0 s num q) num s.x = s := by
  intro s num q h
  have hc : s.x * q = q * s.x := Int.mul_comm _ _
  have e1 : mut0 s num q = ⟨q, s.y⟩ := by simp only [mut0, h, if_true]
  have e2 : mut0 ⟨q, s.y⟩ num s.x = ⟨s.x, s.y⟩ := by
    simp only [mut0, hc, h, if_true]
  rw [e1, e2]

/-- Mutation preserves Laurent positivity when the quotient is positive. -/
theorem mut0_pos : ∀ (s : Seed) (num q : Int),
    seedPos s → 0 < q → num == q * s.x → seedPos (mut0 s num q) := by
  intro s num q hs hq h
  simp only [mut0, h, if_true, seedPos]
  exact ⟨hq, hs.2⟩

/-- The decidable check agrees with the proposition. -/
theorem seedPosB_eq : ∀ s : Seed, seedPosB s = true ↔ seedPos s := by
  intro s
  simp only [seedPosB, Bool.and_eq_true, decide_eq_true_eq, seedPos]

/-! ## E-49: the cone certificate -/

/-- A safe reader sits strictly outside the light cone. -/
theorem safeR_sound : ∀ (v m r t : Nat),
    safeR v m r t = true → v * t + m < r := by
  intro v m r t h
  simp only [safeR, decide_eq_true_eq] at h
  obtain ⟨hm, hl⟩ := h
  omega

/-- A safe placement keeps every mutator outside the cone. -/
theorem placeAll_sound : ∀ (v : Nat) (muts : List Nat) (r t : Nat),
    placeAll v muts r t = true → ∀ m ∈ muts, v * t + m < r
  | _, [], _, _, _, _, hm => by simp at hm
  | v, m :: ms, r, t, h, x, hx => by
    simp only [placeAll, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hm
    · exact safeR_sound v _ r t h1
    · exact placeAll_sound v ms r t h2 x hm

/-! ## E-50: certified separation growth -/

/-- One repulsion step grows the gap by exactly two. -/
theorem repel_gap : ∀ p : Pair2, p.lo < p.hi → gap (repel p) = gap p + 2 := by
  intro p h
  simp only [repel, h, if_true, gap]
  show (p.hi + 1) - (p.lo - 1) = (p.hi - p.lo) + 2
  omega

/-- Repulsion preserves strict separation. -/
theorem repel_ordered : ∀ p : Pair2, p.lo < p.hi →
    (repel p).lo < (repel p).hi := by
  intro p h
  simp only [repel, h, if_true]
  show p.lo - 1 < p.hi + 1
  omega

/-- Iterated repulsion grows the gap linearly. -/
theorem repelN_gap : ∀ (n : Nat) (p : Pair2), p.lo < p.hi →
    gap (repelN n p) = gap p + 2 * n := by
  intro n
  induction n with
  | zero =>
    intro p h
    simp [repelN, gap]
  | succ n ih =>
    intro p h
    have ho := repel_ordered p h
    have e1 := ih (repel p) ho
    have e2 := repel_gap p h
    simp only [repelN]
    omega

/-! ## E-51: the measure drops on every step -/

/-- Every expression costs at least one. -/
theorem msize_pos : ∀ e : Mex, 1 ≤ msize e
  | .const _ => by simp [msize]
  | .add _ _ => by simp only [msize]; omega

/-- Each rewrite strictly shrinks the measure. -/
theorem stepM_shrink : ∀ (e e' : Mex), stepM e = some e' → msize e' < msize e
  | .const _, _, h => by simp [stepM] at h
  | .add l r, _, h => by
    simp only [stepM] at h
    by_cases h0 : l = .const 0
    · simp only [h0, if_true] at h
      cases h
      rw [h0]
      simp only [msize]
      omega
    · simp only [h0, if_false] at h
      by_cases h1 : r = .const 0
      · simp only [h1, if_true] at h
        cases h
        rw [h1]
        simp only [msize]
        omega
      · simp only [h1, if_false] at h
        by_cases hl : stepM l = none
        · simp only [hl] at h
          by_cases hr : stepM r = none
          · simp only [hr] at h
            simp at h
          · obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.mp hr
            simp only [hr'] at h
            cases h
            have ih := stepM_shrink r r' hr'
            simp only [msize]
            omega
        · obtain ⟨l', hl'⟩ := Option.ne_none_iff_exists'.mp hl
          simp only [hl'] at h
          cases h
          have ih := stepM_shrink l l' hl'
          simp only [msize]
          omega

/-- Fuel covering the measure reaches a normal form. -/
theorem normM_normal : ∀ (fuel : Nat) (e : Mex),
    msize e ≤ fuel → isNormal (normM fuel e) = true := by
  intro fuel e
  induction fuel generalizing e with
  | zero =>
    intro h
    have hp := msize_pos e
    have hc : False := by omega
    exact False.elim hc
  | succ n ih =>
    intro h
    simp only [normM]
    cases he : stepM e with
    | some e' =>
      have hs := stepM_shrink e e' he
      exact ih e' (by omega)
    | none =>
      simp [isNormal, he]

/-! ## E-52: the pushforward is a chain map -/

/-- The reroute commutes with the boundary. -/
theorem cmap_chain : ∀ x : CS, (bdyC x).map cmap = bdyD (cmap x)
  | .c0 => by simp [bdyC, bdyD, cmap]
  | .c1 => by simp [bdyC, bdyD, cmap]

/-- Cycles push forward to cycles. -/
theorem cmap_cycle : ∀ x : CS, isCycleC x = true → isCycleD (cmap x) = true
  | .c0, h => by simp [isCycleC] at h
  | .c1, _ => by simp [isCycleD, cmap]

/-! ## E-53: re-derived routes are live end to end -/

/-- Every emitted route starts and finishes where asked. -/
theorem route2_ends : ∀ (e : List (Nat × Nat)) (a b : Nat)
    (dead : List (Nat × Nat)) (q : List Nat),
    route2 e a b dead = some q → q.head? = some a ∧ q.getLast? = some b := by
  intro e a b dead q h
  simp only [route2] at h
  by_cases hd : alive e dead a b = true
  · simp only [hd, if_true] at h
    cases h
    exact ⟨rfl, rfl⟩
  · simp only [hd, reduceCtorEq, if_false] at h
    cases hm : mids e dead a b with
    | nil =>
      simp only [hm] at h
      simp at h
    | cons m ms =>
      simp only [hm] at h
      cases h
      exact ⟨rfl, rfl⟩

/-- Every hop of an emitted route is live. -/
theorem route2_alive : ∀ (e : List (Nat × Nat)) (a b : Nat)
    (dead : List (Nat × Nat)) (q : List Nat),
    route2 e a b dead = some q → hopsAlive e dead q = true := by
  intro e a b dead q h
  simp only [route2] at h
  by_cases hd : alive e dead a b = true
  · simp only [hd, if_true] at h
    cases h
    simp only [hopsAlive, hd, Bool.true_and]
  · simp only [hd, reduceCtorEq, if_false] at h
    cases hm : mids e dead a b with
    | nil =>
      simp only [hm] at h
      simp at h
    | cons m ms =>
      simp only [hm] at h
      cases h
      have hmem : m ∈ mids e dead a b := by
        rw [hm]
        exact List.mem_cons.mpr (Or.inl rfl)
      simp only [mids] at hmem
      have h2 := List.mem_filter.mp hmem
      obtain ⟨_, hal⟩ := h2
      simp only [Bool.and_eq_true] at hal
      obtain ⟨ha1, ha2⟩ := hal
      simp only [hopsAlive, ha1, ha2, Bool.true_and]

/-! ## E-54: localization and the tail bound -/

/-- Symmetric pair weights collapse to twice the representatives. -/
theorem pairSum : ∀ (w : Nat → Int) (ps : List (Nat × Nat)),
    (∀ p ∈ ps, w p.1 = w p.2) →
    isum (ps.map fun p => w p.1 + w p.2) = 2 * isum (ps.map fun p => w p.1)
  | _, [], _ => by simp [isum]
  | w, p :: ps, h => by
    have hp : w p.1 = w p.2 := h p (List.mem_cons.mpr (Or.inl rfl))
    have ih := pairSum w ps (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))
    simp only [List.map_cons, isum, hp]
    omega

/-- The total localizes to the fixed locus. -/
theorem localize : ∀ (w : Nat → Int) (o : Orb),
    (∀ p ∈ o.pairs, w p.1 = w p.2) →
    total w o = isum (o.fixed.map w) + 2 * isum (o.pairs.map fun p => w p.1)
  | w, o, h => by
    have hp := pairSum w o.pairs h
    simp only [total, hp]

/-- Markov: exceedances times threshold fit in the sum. -/
theorem markov : ∀ (xs : List Nat) (t : Nat), 0 < t →
    countGt xs t * t ≤ lsumN xs
  | [], _, _ => by simp [countGt, lsumN]
  | x :: xs, t, ht => by
    have ih := markov xs t ht
    have ih' : ((xs.filter fun x => decide (t < x)).length) * t ≤ lsumN xs := ih
    simp only [countGt, List.filter_cons, lsumN]
    by_cases h : t < x
    · have hd : decide (t < x) = true := by simpa using h
      simp only [hd, if_true, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · have hd : decide (t < x) = false := by simpa using h
      simp only [hd, reduceCtorEq, if_false]
      omega

/-! ## E-55: admission is exact -/

/-- Admission means all three checks. -/
theorem admit_sound : ∀ (mem : Nat) (d : Desc),
    admit mem d = true →
    within mem d = true ∧ aligned d = true ∧ d.flag = true := by
  intro mem d h
  simp only [admit, Bool.and_eq_true] at h
  obtain ⟨⟨hw, ha⟩, hf⟩ := h
  exact ⟨hw, ha, hf⟩

/-- All three checks admit. -/
theorem admit_complete : ∀ (mem : Nat) (d : Desc),
    within mem d = true → aligned d = true → d.flag = true →
    admit mem d = true := by
  intro mem d h1 h2 h3
  simp [admit, h1, h2, h3]

/-- Rejection agrees with non-admission, naming the offender. -/
theorem reject_iff : ∀ (mem : Nat) (d : Desc),
    rejectReason mem d = none ↔ admit mem d = true := by
  intro mem d
  constructor
  · intro h
    simp only [rejectReason] at h
    by_cases hw : within mem d = true
    · simp only [hw, Bool.not_true, reduceCtorEq, if_false] at h
      by_cases ha : aligned d = true
      · simp only [ha, Bool.not_true, reduceCtorEq, if_false] at h
        by_cases hf : d.flag = true
        · simp only [hf, Bool.not_true, reduceCtorEq, if_false] at h
          simp [admit, hw, ha, hf]
        · simp only [hf, Bool.not_false, if_true] at h
          simp at h
      · simp only [ha, Bool.not_false, if_true] at h
        simp at h
    · simp only [hw, Bool.not_false, if_true] at h
      simp at h
  · intro h
    simp only [admit, Bool.and_eq_true] at h
    obtain ⟨⟨hw, ha⟩, hf⟩ := h
    simp only [rejectReason, hw, ha, hf, Bool.not_true, reduceCtorEq, if_false]

/-! ## E-56: evaluation commutes with translation -/

/-- One opcode translates faithfully. -/
theorem transp_correct : ∀ (o : XOp) (r : Nat),
    aeval (transp o) r = xeval o r := by
  intro o r
  cases o <;> simp [transp, xeval, aeval]

/-- Whole programs translate faithfully. -/
theorem transpL_correct : ∀ (os : List XOp) (r : Nat),
    arun (transpL os) r = xrun os r
  | [], _ => by simp [transpL, arun, xrun]
  | o :: os, r => by
    simp only [transpL, List.map_cons, arun, xrun, transp_correct]
    exact transpL_correct os _

/-! ## E-57: minimization preserves acceptance -/

/-- A run from a reachable state stays reachable. -/
theorem run_mem_reachN : ∀ (d : DFA) (w : List Bool) (s : Nat) (k : Nat),
    s ∈ reachN d k → run d w s ∈ reachN d (k + w.length)
  | _, [], _, _ => by
    intro h
    simpa using h
  | d, b :: bs, s, k => by
    intro h
    have hstep : d.step s b ∈ reachN d (k + 1) := by
      simp only [reachN]
      exact List.mem_append.mpr
        (Or.inr ((List.mem_flatMap).mpr ⟨s, h, by cases b <;> simp⟩))
    have ih := run_mem_reachN d bs (d.step s b) (k + 1) hstep
    simp only [run, List.length_cons]
    have he : (k + 1) + bs.length = k + (bs.length + 1) := by omega
    rw [he] at ih
    exact ih

/-- Reachability grows monotonically with fuel. -/
theorem reachN_mono : ∀ (d : DFA) (n m : Nat) (_h : n ≤ m) (x : Nat),
    x ∈ reachN d n → x ∈ reachN d m := by
  intro d n m h x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have he : n + (k + 1) = (n + k) + 1 := by omega
    rw [he]
    simp only [reachN]
    exact List.mem_append.mpr (Or.inl ih)

/-- Filtering a list never lengthens it. -/
theorem filter_len_le : ∀ (l : List Nat) (p : Nat → Bool),
    (l.filter p).length ≤ l.length
  | [], _ => by simp
  | x :: xs, p => by
    have ih := filter_len_le xs p
    by_cases h : p x = true
    · simp only [List.filter_cons, h, if_true, List.length_cons] at ⊢
      omega
    · simp only [List.filter_cons, h, reduceCtorEq, if_false,
        List.length_cons] at ⊢
      omega

/-- Minimization never adds states. -/
theorem minimize_le : ∀ d : DFA,
    (minimize d).states.length ≤ d.states.length := by
  intro d
  have hs : (minimize d).states = d.states.filter (reachableB d) := rfl
  rw [hs]
  exact filter_len_le _ _

/-- The minimized start is the start. -/
theorem minimize_start : ∀ d : DFA, (minimize d).start = d.start :=
  fun _ => rfl

/-- The minimized step is the step. -/
theorem minimize_step : ∀ (d : DFA) (s : Nat) (b : Bool),
    (minimize d).step s b = d.step s b := fun _ _ _ => rfl

/-- Runs ignore minimization. -/
theorem run_minimize : ∀ (d : DFA) (w : List Bool) (s : Nat),
    run (minimize d) w s = run d w s
  | _, [], _ => rfl
  | d, b :: bs, s => by
    simp only [run, minimize_step]
    exact run_minimize d bs _

/-- Minimization preserves acceptance on in-budget words. -/
theorem accepts_min : ∀ (d : DFA) (w : List Bool),
    w.length ≤ d.states.length → accepts (minimize d) w = accepts d w := by
  intro d w hw
  have hmem : run d w d.start ∈ reachN d d.states.length := by
    have h0 : d.start ∈ reachN d 0 := by simp [reachN]
    have h1 := run_mem_reachN d w d.start 0 h0
    simp only [Nat.zero_add] at h1
    exact reachN_mono d w.length d.states.length hw _ h1
  have hb : reachableB d (run d w d.start) = true := by
    simp only [reachableB, decide_eq_true_eq]
    exact hmem
  have hrw : run (minimize d) w (minimize d).start = run d w d.start := by
    rw [minimize_start]
    exact run_minimize d w _
  have ha : (minimize d).accept = d.accept.filter (reachableB d) := rfl
  simp only [accepts, hrw, ha, List.mem_filter, hb, and_true]

end Morph.Specs.BatchFGH
