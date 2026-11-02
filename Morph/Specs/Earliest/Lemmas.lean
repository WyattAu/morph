/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.Earliest.Spec

/-!
# Earliest Frontier Kernels — lemmas (E-03, E-06, E-10, E-21–E-27)

Status: first cycle complete (loop 105).

Every theorem here is about the computable core in `Spec.lean`. Where a row
depends on mathematics outside the fragment (Itô correction derivations,
energy-drift analysis, the Langlands correspondence) the docstring says so
and only the checkable algebra is proved.
-/

namespace Morph.Specs.Earliest

/-! ## E-03: acausality checking and drift conversion -/

/-- The executable check agrees with the semantic validity. -/
theorem strategyOk_iff {ss : List Stage} :
    strategyOk ss = true ↔ StrategyValid ss := by
  induction ss with
  | nil => simp [strategyOk, StrategyValid]
  | cons s ss ih =>
    simp only [strategyOk, StrategyValid, Bool.and_eq_true]
    constructor
    · rintro ⟨hno, hok⟩ t ht
      rcases List.mem_cons.mp ht with hts | hin
      · intro hac
        rw [hts] at hac
        obtain ⟨u, hu, hlt⟩ := hac
        have htrue : (s.needs.any (fun t => decide (s.time < t))) = true := by
          rw [List.any_eq_true]
          exact ⟨u, hu, by rw [decide_eq_true_eq]; exact hlt⟩
        rw [htrue] at hno
        exact Bool.false_ne_true hno
      · exact ih.mp hok t hin
    · intro h
      have hss : ∀ t ∈ ss, ¬ acausal t := fun t ht =>
        h t (by simp only [List.mem_cons]; exact Or.inr ht)
      refine ⟨?_, ih.mpr hss⟩
      have hfalse : (s.needs.any (fun t => decide (s.time < t))) = false := by
        rw [List.any_eq_false]
        intro u hu
        simp only [decide_eq_true_eq]
        intro hlt
        exact h s (List.mem_cons_self ..) ⟨u, hu, hlt⟩
      simpa using hfalse

/-- The drift conversion round-trips. -/
theorem ito_strat_roundtrip (A B D : Int) :
    itoOfStrat (stratOfIto A B D) B D = A := by
  simp [stratOfIto, itoOfStrat]

/-- The drift conversion round-trips the other way. -/
theorem strat_ito_roundtrip (S B D : Int) :
    stratOfIto (itoOfStrat S B D) B D = S := by
  simp [stratOfIto, itoOfStrat]

/-! ## E-06: max-plus algebra and WCET bounds -/

/-- Tropical addition is associative. -/
theorem tadd_assoc (a b c : Trop) : tadd (tadd a b) c = tadd a (tadd b c) := by
  cases a <;> cases b <;> cases c <;> simp [tadd] <;> omega

/-- Tropical addition is commutative. -/
theorem tadd_comm (a b : Trop) : tadd a b = tadd b a := by
  cases a <;> cases b <;> simp [tadd] <;> omega

/-- Tropical addition is idempotent. -/
theorem tadd_idem (a : Trop) : tadd a a = a := by
  cases a <;> simp [tadd]

/-- Zero is a left identity. -/
theorem tzero_add (a : Trop) : tadd tzero a = a := by
  cases a <;> simp [tadd, tzero]

/-- Zero is a right identity. -/
theorem add_tzero (a : Trop) : tadd a tzero = a := by
  cases a <;> simp [tadd, tzero]

/-- Tropical multiplication is associative. -/
theorem tmul_assoc (a b c : Trop) : tmul (tmul a b) c = tmul a (tmul b c) := by
  cases a <;> cases b <;> cases c <;> simp [tmul] <;> omega

/-- One is a left identity. -/
theorem tone_mul (a : Trop) : tmul tone a = a := by
  cases a <;> simp [tmul, tone] <;> omega

/-- One is a right identity. -/
theorem mul_tone (a : Trop) : tmul a tone = a := by
  cases a <;> simp [tmul, tone] <;> omega

/-- Zero annihilates. -/
theorem tzero_mul (a : Trop) : tmul tzero a = tzero := by
  cases a <;> simp [tmul, tzero]

/-- Multiplication distributes over addition: the longest-path law. -/
theorem tmul_add_distrib (a b c : Trop) :
    tmul a (tadd b c) = tadd (tmul a b) (tmul a c) := by
  cases a <;> cases b <;> cases c <;> simp [tmul, tadd] <;> omega

/-- Blocks concatenate additively. -/
theorem blockWCET_append (l₁ l₂ : List Nat) :
    blockWCET (l₁ ++ l₂) = blockWCET l₁ + blockWCET l₂ := by
  induction l₁ with
  | nil => simp [blockWCET]
  | cons hd tl ih => simp [blockWCET, ih, Nat.add_assoc]

/-- A uniform per-op bound scales with the block length. -/
theorem blockWCET_le : ∀ (ls : List Nat) (B : Nat),
    (∀ x ∈ ls, x ≤ B) → blockWCET ls ≤ ls.length * B
  | [], _, _ => by simp [blockWCET]
  | x :: xs, B, h => by
    have hx : x ≤ B := h x (List.mem_cons_self ..)
    have hs : ∀ y ∈ xs, y ≤ B := fun y hy =>
      h y (by simp only [List.mem_cons]; exact Or.inr hy)
    have ih := blockWCET_le xs B hs
    simp only [blockWCET, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The branch bound dominates every alternative. -/
theorem branchWCET_ge : ∀ (alts : List Nat) (a : Nat),
    a ∈ alts → a ≤ branchWCET alts
  | [], _, h => by simp at h
  | b :: bs, a, h => by
    simp only [branchWCET]
    rcases List.mem_cons.mp h with rfl | hin
    · omega
    · have h2 := branchWCET_ge bs a hin
      omega

/-! ## E-10: shear symplecticity and reversibility -/

/-- Position shears preserve the area form. -/
theorem shearX_area (c : Int) (u v : Int × Int) :
    area (shearX c u) (shearX c v) = area u v := by
  have key : (c * u.2) * v.2 = u.2 * (c * v.2) := by ac_rfl
  simp only [shearX, area, Int.add_mul, Int.mul_add]
  omega

/-- Momentum shears preserve the area form. -/
theorem shearY_area (c : Int) (u v : Int × Int) :
    area (shearY c u) (shearY c v) = area u v := by
  have key : u.1 * (c * v.1) = (c * u.1) * v.1 := by ac_rfl
  simp only [shearY, area, Int.add_mul, Int.mul_add]
  omega

/-- Leapfrog is symplectic: it preserves the area form. -/
theorem leapfrog_area (h k : Int) (u v : Int × Int) :
    area (leapfrog h k u) (leapfrog h k v) = area u v := by
  simp only [leapfrog]
  rw [shearX_area, shearY_area, shearX_area]

/-- Negated position shear inverts. -/
theorem shearX_neg (c : Int) (u : Int × Int) :
    shearX (-c) (shearX c u) = u := by
  cases u with
  | mk q p =>
    refine Prod.ext ?_ rfl
    simp only [shearX, Int.neg_mul]
    omega

/-- Negated momentum shear inverts. -/
theorem shearY_neg (c : Int) (u : Int × Int) :
    shearY (-c) (shearY c u) = u := by
  cases u with
  | mk q p =>
    refine Prod.ext rfl ?_
    simp only [shearY, Int.neg_mul]
    omega

/-- Leapfrog is reversible: negated steps undo it. -/
theorem leapfrog_rev (h k : Int) (u : Int × Int) :
    leapfrog (-h) (-k) (leapfrog h k u) = u := by
  simp only [leapfrog, shearX_neg, shearY_neg]

/-- The origin is a fixed point. -/
theorem leapfrog_origin (h k : Int) : leapfrog h k (0, 0) = (0, 0) := by
  simp [leapfrog, shearX, shearY]

/-! ## E-21: synthesis completeness and checker soundness -/

/-- Every skeleton edge comes from a protocol transition. -/
theorem synth_complete {spec : List Trans} {s l t' : Nat}
    (h : (l, t') ∈ outEdges spec s) :
    ∃ tr ∈ spec, tr.from_ = s ∧ tr.label = l ∧ tr.to = t' := by
  unfold outEdges at h
  rw [List.mem_map] at h
  obtain ⟨tr, hmem, hpair⟩ := h
  rw [List.mem_filter] at hmem
  obtain ⟨hmem', hcond⟩ := hmem
  have hfrom : tr.from_ = s := beq_iff_eq.mp hcond
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hlab, hto⟩ := hpair
  exact ⟨tr, hmem', hfrom, hlab, hto⟩

/-- The checker only accepts genuine simulations. -/
theorem checkSim_sound {R : Nat → Nat → Bool} {sys impl : Nat → Nat → List Nat}
    {states labels : List Nat}
    (h : checkSim R sys impl states labels = true) :
    ∀ s ∈ states, ∀ t ∈ states, R s t = true →
      ∀ l ∈ labels, ∀ s' ∈ sys s l, ∃ t' ∈ impl t l, R s' t' = true := by
  unfold checkSim at h
  rw [List.all_eq_true] at h
  intro s hs t ht hR l hl s' hs'
  have h1 := h s hs
  rw [List.all_eq_true] at h1
  have h1t := h1 t ht
  rw [hR] at h1t
  simp at h1t
  have h2 := h1t l hl
  have h3 := h2 s' hs'
  obtain ⟨t', ht', hRt'⟩ := h3
  exact ⟨t', ht', hRt'⟩

/-- Identity simulation. -/
theorem sim_refl (sys : Nat → Nat → List Nat) : simulates (· = ·) sys sys := by
  intro s t h
  obtain rfl := h
  intro l s' hs'
  exact ⟨s', hs', rfl⟩

/-- Simulations compose. -/
theorem sim_comp {R S : Nat → Nat → Prop} {sys mid impl : Nat → Nat → List Nat}
    (hR : simulates R sys mid) (hS : simulates S mid impl) :
    simulates (fun s u => ∃ m, R s m ∧ S m u) sys impl := by
  intro s u h l s' hs'
  obtain ⟨m, hRm, hSm⟩ := h
  obtain ⟨m', hm', hRm'⟩ := hR s m hRm l s' hs'
  obtain ⟨u', hu', hSu'⟩ := hS m u hSm l m' hm'
  exact ⟨u', hu', m', hRm', hSu'⟩

/-! ## E-22: cut algebra and the move-gain formula -/

/-- Bridge: a refuted decidable proposition decides to false. -/
theorem decide_eq_false_of_not {p : Prop} [Decidable p] (h : ¬p) :
    decide p = false := by
  cases hdec : decide p with
  | true => exact absurd (of_decide_eq_true hdec) h
  | false => rfl

/-- Membership in the moved-out side, away from the moved vertex. -/
theorem mem_moveOut_eq (side : List Nat) (v x : Nat) (hx : x ≠ v) :
    decide (x ∈ moveOut side v) = decide (x ∈ side) := by
  have hmem : x ∈ moveOut side v ↔ x ∈ side := by
    simp only [moveOut, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
  simp only [hmem]

/-- The moved vertex is gone. -/
theorem not_mem_moveOut_self (side : List Nat) (v : Nat) :
    v ∉ moveOut side v := by
  intro h
  simp only [moveOut, List.mem_filter, decide_eq_true_eq] at h
  exact absurd rfl h.2

/-- The empty side cuts nothing. -/
theorem cut_empty (edges : List Edge) : cutWeight edges [] = 0 := by
  induction edges with
  | nil => rfl
  | cons e es ih => simp [cutWeight, crosses, ih]

/-- Moving `v` out changes the cut by exactly `ext − int`. -/
theorem move_delta (edges : List Edge) (side : List Nat) (v : Nat)
    (hv : v ∈ side) :
    (cutWeight edges (moveOut side v) : Int) =
      (cutWeight edges side : Int) - (extW edges side v : Int)
        + (intW edges side v : Int) := by
  have hvin : decide (v ∈ side) = true := by
    rw [decide_eq_true_eq]; exact hv
  have hvout : decide (v ∈ moveOut side v) = false :=
    decide_eq_false_of_not (not_mem_moveOut_self side v)
  have _hvvF : decide (v ≠ v) = false :=
  decide_eq_false_of_not (not_not_intro rfl)
  have n : ¬((false : Bool) = true) := by decide
  induction edges with
  | nil => simp [cutWeight, extW, intW]
  | cons e es ih =>
    simp only [cutWeight, extW, intW] at ⊢
    by_cases heu : e.u = v <;> by_cases hev : e.v = v
    · -- loop at v: never crosses, never counted
      have c1 : crosses side e = false := by simp [crosses, heu, hev, hvin]
      have c2 : crosses (moveOut side v) e = false := by
        simp [crosses, heu, hev, hvout]
      have x1 : ((decide (e.u = v) && !decide (e.v ∈ side)) ||
          (decide (e.v = v) && !decide (e.u ∈ side))) = false := by
        simp [heu, hev, hvin]
      have x2 : ((decide (e.u = v) && decide (e.v ∈ side) && decide (e.v ≠ v)) ||
          (decide (e.v = v) && decide (e.u ∈ side) && decide (e.u ≠ v))) = false := by
        simp [heu, hev, hvin]
      rw [c1, c2, x1, x2] at ⊢
      simp only [if_neg n] at ⊢
      omega
    · -- head endpoint is v: the cut toggles on the other end
      have hevF : decide (e.v = v) = false := decide_eq_false_of_not hev
      have hnevT : decide (e.v ≠ v) = true := by
        rw [decide_eq_true_eq]; exact hev
      have hmem' : decide (e.v ∈ moveOut side v) = decide (e.v ∈ side) :=
        mem_moveOut_eq side v e.v hev
      by_cases hmem : e.v ∈ side
      · have hD : decide (e.v ∈ side) = true := by
          rw [decide_eq_true_eq]; exact hmem
        have c1 : crosses side e = false := by simp [crosses, heu, hD, hvin]
        have c2 : crosses (moveOut side v) e = true := by
          simp [crosses, heu, hvout, hmem', hD]
        have x1 : ((decide (e.u = v) && !decide (e.v ∈ side)) ||
            (decide (e.v = v) && !decide (e.u ∈ side))) = false := by
          simp [heu, hevF, hD]
        have x2 : ((decide (e.u = v) && decide (e.v ∈ side) && decide (e.v ≠ v)) ||
            (decide (e.v = v) && decide (e.u ∈ side) && decide (e.u ≠ v))) = true := by
          simp [heu, hevF, hD, hnevT]
        rw [c1, c2, x1, x2] at ⊢
        simp only [if_neg n, if_true] at ⊢
        omega
      · have hD : decide (e.v ∈ side) = false := decide_eq_false_of_not hmem
        have c1 : crosses side e = true := by simp [crosses, heu, hD, hvin]
        have c2 : crosses (moveOut side v) e = false := by
          simp [crosses, heu, hvout, hmem', hD]
        have x1 : ((decide (e.u = v) && !decide (e.v ∈ side)) ||
            (decide (e.v = v) && !decide (e.u ∈ side))) = true := by
          simp [heu, hevF, hD]
        have x2 : ((decide (e.u = v) && decide (e.v ∈ side) && decide (e.v ≠ v)) ||
            (decide (e.v = v) && decide (e.u ∈ side) && decide (e.u ≠ v))) = false := by
          simp [heu, hevF, hD, hnevT]
        rw [c1, c2, x1, x2] at ⊢
        simp only [if_neg n, if_true] at ⊢
        omega
    · -- tail endpoint is v: symmetric
      have heuF : decide (e.u = v) = false := decide_eq_false_of_not heu
      have hneuT : decide (e.u ≠ v) = true := by
        rw [decide_eq_true_eq]; exact heu
      have hmem' : decide (e.u ∈ moveOut side v) = decide (e.u ∈ side) :=
        mem_moveOut_eq side v e.u heu
      by_cases hmem : e.u ∈ side
      · have hD : decide (e.u ∈ side) = true := by
          rw [decide_eq_true_eq]; exact hmem
        have c1 : crosses side e = false := by simp [crosses, hev, hD, hvin]
        have c2 : crosses (moveOut side v) e = true := by
          simp [crosses, hev, hvout, hmem', hD]
        have x1 : ((decide (e.u = v) && !decide (e.v ∈ side)) ||
            (decide (e.v = v) && !decide (e.u ∈ side))) = false := by
          simp [heuF, hev, hD]
        have x2 : ((decide (e.u = v) && decide (e.v ∈ side) && decide (e.v ≠ v)) ||
            (decide (e.v = v) && decide (e.u ∈ side) && decide (e.u ≠ v))) = true := by
          simp [heuF, hev, hD, hneuT]
        rw [c1, c2, x1, x2] at ⊢
        simp only [if_neg n, if_true] at ⊢
        omega
      · have hD : decide (e.u ∈ side) = false := decide_eq_false_of_not hmem
        have c1 : crosses side e = true := by simp [crosses, hev, hD, hvin]
        have c2 : crosses (moveOut side v) e = false := by
          simp [crosses, hev, hvout, hmem', hD]
        have x1 : ((decide (e.u = v) && !decide (e.v ∈ side)) ||
            (decide (e.v = v) && !decide (e.u ∈ side))) = true := by
          simp [heuF, hev, hD]
        have x2 : ((decide (e.u = v) && decide (e.v ∈ side) && decide (e.v ≠ v)) ||
            (decide (e.v = v) && decide (e.u ∈ side) && decide (e.u ≠ v))) = false := by
          simp [heuF, hev, hD, hneuT]
        rw [c1, c2, x1, x2] at ⊢
        simp only [if_neg n, if_true] at ⊢
        omega
    · -- unincident: nothing changes
      have heuF : decide (e.u = v) = false := decide_eq_false_of_not heu
      have hevF : decide (e.v = v) = false := decide_eq_false_of_not hev
      have hmemu : decide (e.u ∈ moveOut side v) = decide (e.u ∈ side) :=
        mem_moveOut_eq side v e.u heu
      have c1 : crosses (moveOut side v) e = crosses side e := by
        simp [crosses, hmemu, mem_moveOut_eq side v e.v hev]
      have x1 : ((decide (e.u = v) && !decide (e.v ∈ side)) ||
          (decide (e.v = v) && !decide (e.u ∈ side))) = false := by
        simp [heuF, hevF]
      have x2 : ((decide (e.u = v) && decide (e.v ∈ side) && decide (e.v ≠ v)) ||
          (decide (e.v = v) && decide (e.u ∈ side) && decide (e.u ≠ v))) = false := by
        simp [heuF, hevF]
      rw [c1, x1, x2] at ⊢
      simp only [if_neg n] at ⊢
      by_cases hc : crosses side e = true
      · simp only [if_pos hc] at ⊢; omega
      · simp only [if_neg hc] at ⊢; omega

/-! ## E-23: the power rule and critical-point verification -/

/-- The formal derivative evaluates to the explicit derivative sum. -/
theorem derivAux_eval (x : Int) : ∀ (cs : List Int) (n : Nat),
    evalPoly (derivAux cs n) x = dsum cs n x
  | [], _ => by simp [derivAux, evalPoly, dsum]
  | c :: cs, n => by
    have ih := derivAux_eval x cs (n + 1)
    simp only [derivAux, evalPoly, dsum]
    rw [ih]

/-- The derivative of the evaluated polynomial is the derivative sum. -/
theorem derivPoly_eval : ∀ (p : List Int) (x : Int),
    evalPoly (derivPoly p) x = dsum (p.drop 1) 1 x
  | [], _ => by simp [derivPoly, evalPoly, dsum]
  | _ :: _, _ => by simp [derivPoly, derivAux_eval]

/-- An accepted critical point really zeroes the derivative. -/
theorem isCritical_sound {p : List Int} {x : Int}
    (h : isCritical p x = true) : evalPoly (derivPoly p) x = 0 := by
  unfold isCritical at h
  exact of_decide_eq_true h

/-! ## E-24: optimal speculation depth -/

/-- The fold stays inside the candidate list. -/
theorem foldMin_mem : ∀ (b : Region) (rs : List Region),
    foldMin b rs ∈ b :: rs
  | _, [] => by simp [foldMin]
  | b, r :: rs => by
    simp only [foldMin]
    split
    · have h1 := foldMin_mem r rs
      simp only [List.mem_cons] at h1 ⊢
      rcases h1 with h1l | hmem
      · rw [h1l] at ⊢
        exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr hmem)
    · have h1 := foldMin_mem b rs
      simp only [List.mem_cons] at h1 ⊢
      rcases h1 with h1l | hmem
      · rw [h1l] at ⊢
        exact Or.inl rfl
      · exact Or.inr (Or.inr hmem)

/-- The fold is optimal among the candidates. -/
theorem foldMin_best : ∀ (b : Region) (rs : List Region) (r : Region),
    r ∈ b :: rs → expectedCost (foldMin b rs) ≤ expectedCost r := by
  intro b rs
  induction rs generalizing b with
  | nil =>
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [foldMin]
    rw [hr]
    exact Nat.le_refl _
  | cons r' rs ih =>
    intro r hr
    simp only [foldMin]
    split
    · rename_i hlt
      have h1 : expectedCost (foldMin r' rs) ≤ expectedCost r' :=
        ih r' r' List.mem_cons_self
      have h2 : r = b ∨ r ∈ r' :: rs := by simpa using hr
      rcases h2 with heq | hin
      · rw [heq]; omega
      · exact ih r' r hin
    · rename_i hge
      have h1 : expectedCost (foldMin b rs) ≤ expectedCost b :=
        ih b b List.mem_cons_self
      have h2 : r = b ∨ r = r' ∨ r ∈ rs := by simpa using hr
      rcases h2 with heq | h2'
      · rw [heq]; exact h1
      · rcases h2' with heq' | hin
        · rw [heq']; omega
        · have hmem : r ∈ b :: rs := by
            simp only [List.mem_cons]
            exact Or.inr hin
          exact ih b r hmem

/-- The compiler's choice is optimal: no candidate beats it. -/
theorem best_optimal : ∀ (rs : List Region) (b : Region),
    best rs = some b → ∀ r ∈ rs, expectedCost b ≤ expectedCost r
  | [], _, h, _, _ => by simp [best] at h
  | r :: rs, b, h, q, hq => by
    simp only [best] at h
    injection h with hb
    subst hb
    have h2 : q = r ∨ q ∈ rs := by simpa using hq
    rcases h2 with heq | hin
    · rw [heq]
      exact foldMin_best r rs r (List.mem_cons_self ..)
    · have hmem : q ∈ r :: rs := by
        simp only [List.mem_cons]
        exact Or.inr hin
      exact foldMin_best r rs q hmem

/-- Higher rollback likelihood never lowers expected cost. -/
theorem cost_mono {r r' : Region} (hw : r.work = r'.work) (hd : r.redo = r'.redo)
    (hp : r.rollback ≤ r'.rollback) : expectedCost r ≤ expectedCost r' := by
  simp only [expectedCost, hw, hd]
  have hmul := Nat.mul_le_mul_right r'.redo hp
  omega

/-! ## E-25: one-step spread law and monotonicity -/

/-- Spread from `v` in zero steps is just `v`. -/
theorem mem_spread_zero (edges : List (Nat × Nat)) (v x : Nat) :
    x ∈ spread edges 0 v ↔ x = v := by
  simp [spread]

/-- Exact one-step law: the next cone is the current cone plus its targets. -/
theorem mem_spread_succ (edges : List (Nat × Nat)) (n v x : Nat) :
    x ∈ spread edges (n + 1) v ↔
      x ∈ spread edges n v ∨ (∃ y ∈ spread edges n v, (y, x) ∈ edges) := by
  simp only [spread, step, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · rw [List.mem_filterMap] at h
      obtain ⟨y, hy, heq⟩ := h
      by_cases hmem : y.1 ∈ spread edges n v
      · rw [if_pos hmem] at heq
        injection heq with heq'
        have hmem2 : (y.1, x) ∈ edges := by
          rw [← heq']
          cases y with
          | mk a b => exact hy
        exact Or.inr ⟨y.1, hmem, hmem2⟩
      · rw [if_neg hmem] at heq
        cases heq
  · rintro (h | ⟨y, hy, hedge⟩)
    · exact Or.inl h
    · refine Or.inr ?_
      rw [List.mem_filterMap]
      exact ⟨(y, x), hedge, by
        show (if y ∈ spread edges n v then some x else none) = some x
        rw [if_pos hy]⟩

/-- Cones only grow. -/
theorem spread_mono_mem (edges : List (Nat × Nat)) (n v x : Nat)
    (h : x ∈ spread edges n v) : x ∈ spread edges (n + 1) v :=
  (mem_spread_succ edges n v x).mpr (Or.inl h)

/-! ## E-26: backend agreement and corpus conformance -/

/-- The affine closed form agrees with direct interpretation on every input. -/
theorem compileAff_correct : ∀ (ops : List KerOp) (x : Nat),
    affApply (compileAff ops) x = evalKer ops x
  | [], _ => by simp [compileAff, affApply, evalKer]
  | .addConst c :: ops, x => by
    have ih := compileAff_correct ops (x + c)
    simp only [compileAff, affApply, evalKer] at ih ⊢
    rw [← ih, Nat.mul_add]
    omega
  | .mulConst c :: ops, x => by
    have ih := compileAff_correct ops (x * c)
    simp only [compileAff, affApply, evalKer] at ih ⊢
    rw [← ih]
    ac_rfl

/-- The executable corpus check agrees with pointwise equality. -/
theorem conformant_iff {f g : Nat → Nat} {corpus : List Nat} :
    conformant f g corpus = true ↔ ∀ x ∈ corpus, f x = g x := by
  simp [conformant, List.all_eq_true, beq_iff_eq]

/-- Both backends conform on every corpus. -/
theorem backends_conformant (ops : List KerOp) (corpus : List Nat) :
    conformant (evalKer ops) (affApply (compileAff ops)) corpus = true := by
  rw [conformant_iff]
  intro x _
  exact (compileAff_correct ops x).symm

/-! ## E-27: stability checking and witness extraction -/

/-- Negating the subgroup negates the weight. -/
theorem mu_neg : ∀ (x lam : List Int),
    mu x (lam.map fun b => -b) = -mu x lam
  | [], _ => by simp [mu, dot]
  | _ :: _, [] => by simp [mu, dot]
  | a :: as, b :: bs => by
    simp only [mu, dot, List.map_cons, Int.mul_neg]
    have ih := mu_neg as bs
    simp only [mu] at ih
    omega

/-- The executable check agrees with stability against the sample. -/
theorem checkStable_iff {x : List Int} {lams : List (List Int)} :
    checkStable x lams = true ↔ ∀ lam ∈ lams, mu x lam ≤ 0 := by
  simp [checkStable, List.all_eq_true, decide_eq_true_eq]

/-- A returned witness is a genuine destabilizer from the sample. -/
theorem findWitness_sound (x : List Int) : ∀ (lams : List (List Int))
    (lam : List Int),
    findWitness x lams = some lam → lam ∈ lams ∧ 0 < mu x lam
  | [], _, h => by simp [findWitness] at h
  | lam' :: lams, lam, h => by
    simp only [findWitness] at h
    split at h
    · rename_i hle
      have ih := findWitness_sound x lams lam h
      have hmem : lam ∈ lam' :: lams := by
        simp only [List.mem_cons]
        exact Or.inr ih.1
      exact ⟨hmem, ih.2⟩
    · rename_i hle
      injection h with heq
      subst heq
      exact ⟨List.mem_cons_self .., by omega⟩

/-- A checked config admits no destabilizer from the sample. -/
theorem stable_of_check {x : List Int} {lams : List (List Int)}
    (h : checkStable x lams = true) : ∀ lam ∈ lams, ¬ Unstable x lam := by
  rw [checkStable_iff] at h
  intro lam hlam huns
  unfold Unstable at huns
  have := h lam hlam
  omega

end Morph.Specs.Earliest
