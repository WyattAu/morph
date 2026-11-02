/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchBCD.Spec

/-!
# Frontier Kernels — lemmas (E-28–E-37)

Status: In Progress (loop 106, second-ten first cycle).

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms: every
theorem is proved by structural induction with `simp`/`ac_rfl`/`omega` over
the project-local recursive definitions, or by `decide` over finite types.
-/

namespace Morph.Specs.BatchBCD

/-! ## E-28: pipeline totals and certificates -/

/-- Totals do not depend on parenthesization: the crossing identity. -/
theorem totalHi_append (ss₁ ss₂ : List Stage) :
    totalHi (ss₁ ++ ss₂) = totalHi ss₁ + totalHi ss₂ := by
  induction ss₁ with
  | nil => simp [totalHi]
  | cons hd tl ih => simp only [totalHi, List.cons_append, ih]; ac_rfl

/-- Best-case totals split the same way. -/
theorem totalLo_append (ss₁ ss₂ : List Stage) :
    totalLo (ss₁ ++ ss₂) = totalLo ss₁ + totalLo ss₂ := by
  induction ss₁ with
  | nil => simp [totalLo]
  | cons hd tl ih => simp only [totalLo, List.cons_append, ih]; ac_rfl

/-- Every realization is dominated by the worst-case total. -/
theorem sum_le_totalHi : ∀ (ss : List Stage) (as : List Nat),
    realizes ss as → lsum as ≤ totalHi ss
  | [], [], _ => by simp [lsum, totalHi]
  | [], _ :: _, h => by simp [realizes] at h
  | _ :: _, [], h => by simp [realizes] at h
  | s :: ss, a :: as, h => by
    simp only [realizes] at h
    obtain ⟨_, ha, ihr⟩ := h
    have ih := sum_le_totalHi ss as ihr
    simp only [lsum, totalHi]
    omega

/-- A certificate covers every realization. -/
theorem certify_sound (b : Nat) (ss : List Stage) (as : List Nat)
    (hc : certify b ss = true) (hr : realizes ss as) : lsum as ≤ b := by
  have h1 : totalHi ss ≤ b := by
    simp only [certify] at hc
    exact of_decide_eq_true hc
  have h2 := sum_le_totalHi ss as hr
  omega

/-! ## E-29: fusion laws and the price-time-priority engine -/

/-- Vacuum is the two-sided unit. -/
theorem fuse_unit (c : ACharge) : fuse .vac c = c ∧ fuse c .vac = c := by
  cases c <;> simp [fuse]

/-- Fusion commutes. -/
theorem fuse_comm (a b : ACharge) : fuse a b = fuse b a := by
  cases a <;> cases b <;> rfl

/-- Fusion associates. -/
theorem fuse_assoc (a b c : ACharge) :
    fuse (fuse a b) c = fuse a (fuse b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- A four-way boolean conjunction splits (decided once, used often). -/
private theorem and4_true : ∀ a b c d : Bool, (a && b && c && d) = true →
    a = true ∧ b = true ∧ c = true ∧ d = true := by
  decide

/-- Membership in a buy's candidate list pins down the pair. -/
theorem mem_pairsWith {b : Order} {sells : List Order} {p : Order × Order}
    (h : p ∈ pairsWith b sells) :
    ∃ s ∈ sells, p = (b, s) ∧ b.buy = true ∧ s.buy = false ∧
      neutral b.charge s.charge = true ∧ s.price ≤ b.price := by
  induction sells with
  | nil => simp [pairsWith] at h
  | cons hd tl ih =>
    simp only [pairsWith] at h
    cases hcond : (b.buy && !hd.buy && neutral b.charge hd.charge &&
      decide (hd.price ≤ b.price)) with
    | true =>
      simp only [hcond, if_true] at h
      rw [List.mem_cons] at h
      cases h with
      | inl heq =>
        have h4 := and4_true _ _ _ _ hcond
        obtain ⟨hb, hnb, hneu, hle⟩ := h4
        have hle' : hd.price ≤ b.price := of_decide_eq_true hle
        have hnb' : hd.buy = false := by
          cases hs : hd.buy with
          | true => simp [hs] at hnb
          | false => rfl
        exact ⟨hd, List.mem_cons.mpr (Or.inl rfl), heq, hb, hnb', hneu, hle'⟩
      | inr hmem =>
        obtain ⟨s, hs, heq, hb, hnb, hneu, hle⟩ := ih hmem
        exact ⟨s, List.mem_cons.mpr (Or.inr hs), heq, hb, hnb, hneu, hle⟩
    | false =>
      simp only [hcond] at h
      obtain ⟨s, hs, heq, hb, hnb, hneu, hle⟩ := ih h
      exact ⟨s, List.mem_cons.mpr (Or.inr hs), heq, hb, hnb, hneu, hle⟩

/-- Membership in the candidate set pins down the fill. -/
theorem mem_candidates {buys sells : List Order} {p : Order × Order}
    (h : p ∈ candidates buys sells) :
    p.1.buy = true ∧ p.2.buy = false ∧ neutral p.1.charge p.2.charge = true ∧
      p.2.price ≤ p.1.price ∧ p.1 ∈ buys ∧ p.2 ∈ sells := by
  induction buys with
  | nil => simp [candidates] at h
  | cons b bs ih =>
    simp only [candidates] at h
    rw [List.mem_append] at h
    cases h with
    | inl hmem =>
      obtain ⟨s, hs, heq, hb, hnb, hneu, hle⟩ := mem_pairsWith hmem
      subst heq
      exact ⟨hb, hnb, hneu, hle,
        List.mem_cons.mpr (Or.inl rfl), hs⟩
    | inr hmem =>
      obtain ⟨hb, hnb, hneu, hle, h1, h2⟩ := ih hmem
      exact ⟨hb, hnb, hneu, hle, List.mem_cons.mpr (Or.inr h1), h2⟩

/-- The fold returns its input or a list member. -/
theorem fold_pick_mem (l : List (Order × Order)) (acc : Option (Order × Order))
    (p : Order × Order) (h : l.foldl pickStep acc = some p) :
    p ∈ l ∨ acc = some p := by
  induction l generalizing acc with
  | nil => exact Or.inr h
  | cons x xs ih =>
    have hfold : (x :: xs).foldl pickStep acc =
        xs.foldl pickStep (pickStep acc x) := rfl
    rw [hfold] at h
    cases ha' : acc with
    | none =>
      have hx : pickStep none x = some x := rfl
      have h' : xs.foldl pickStep (some x) = some p := by
        have hpx : pickStep acc x = some x := by rw [ha']; exact hx
        rw [hpx] at h
        exact h
      have ihm := ih _ h'
      cases ihm with
      | inl hmem => exact Or.inl (List.mem_cons.mpr (Or.inr hmem))
      | inr h2 =>
        have heq : x = p := by simpa using h2
        subst heq
        exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
    | some q =>
      by_cases hb : better x q = true
      · have hx : pickStep (some q) x = some x := by simp [pickStep, hb]
        have h' : xs.foldl pickStep (some x) = some p := by
          have hpx : pickStep acc x = some x := by rw [ha']; exact hx
          rw [hpx] at h
          exact h
        have ihm := ih _ h'
        cases ihm with
        | inl hmem => exact Or.inl (List.mem_cons.mpr (Or.inr hmem))
        | inr h2 =>
          have heq : x = p := by simpa using h2
          subst heq
          exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
      · have hx : pickStep (some q) x = some q := by simp [pickStep, hb]
        have h' : xs.foldl pickStep (some q) = some p := by
          have hpx : pickStep acc x = some q := by rw [ha']; exact hx
          rw [hpx] at h
          exact h
        have ihm := ih _ h'
        cases ihm with
        | inl hmem => exact Or.inl (List.mem_cons.mpr (Or.inr hmem))
        | inr h2 => exact Or.inr h2

/-- A strictly better fill has a strictly better buy price. -/
theorem better_buy {p q : Order × Order} (h : better p q = true) :
    q.1.price ≤ p.1.price := by
  simp only [better, decide_eq_true_eq] at h
  omega

/-- The fold result beats every member on buy price. -/
theorem fold_pick_buy (l : List (Order × Order)) (acc : Option (Order × Order))
    (p : Order × Order) (h : l.foldl pickStep acc = some p) :
    (∀ a, acc = some a → a.1.price ≤ p.1.price) ∧
      ∀ q ∈ l, q.1.price ≤ p.1.price := by
  induction l generalizing acc with
  | nil =>
    have h' : acc = some p := h
    constructor
    · intro a ha
      have h2 : some a = some p := by rw [← ha]; exact h'
      have hap : a = p := by simpa using h2
      have hle1 : a.1.price = p.1.price := congrArg (·.1.price) hap
      omega
    · intro q hq
      simp at hq
  | cons x xs ih =>
    have hfold : (x :: xs).foldl pickStep acc =
        xs.foldl pickStep (pickStep acc x) := rfl
    rw [hfold] at h
    cases ha' : acc with
    | none =>
      have hx : pickStep none x = some x := rfl
      have haccx : pickStep acc x = some x := by rw [ha']; exact hx
      rw [haccx] at h
      have ihm := ih _ h
      obtain ⟨ihacc, ihm⟩ := ihm
      constructor
      · intro a ha
        cases ha
      · intro q hq
        rw [List.mem_cons] at hq
        cases hq with
        | inl heq =>
          have hqeq : q.1.price = x.1.price := congrArg (·.1.price) heq
          rw [hqeq]
          exact ihacc x rfl
        | inr hmem => exact ihm q hmem
    | some q =>
      by_cases hb : better x q = true
      · have hx : pickStep (some q) x = some x := by simp [pickStep, hb]
        have haccx : pickStep acc x = some x := by rw [ha']; exact hx
        rw [haccx] at h
        have ihm := ih _ h
        obtain ⟨ihacc, ihm⟩ := ihm
        have hle : q.1.price ≤ x.1.price := better_buy hb
        constructor
        · intro a ha
          have hap : a = q := by simpa using ha.symm
          have hle1 : a.1.price = q.1.price := congrArg (·.1.price) hap
          have hle2 : x.1.price ≤ p.1.price := ihacc x rfl
          omega
        · intro r hr
          rw [List.mem_cons] at hr
          cases hr with
          | inl heq =>
            have hreq : r.1.price = x.1.price := congrArg (·.1.price) heq
            rw [hreq]
            exact ihacc x rfl
          | inr hmem => exact ihm r hmem
      · have hx : pickStep (some q) x = some q := by simp [pickStep, hb]
        have haccx : pickStep acc x = some q := by rw [ha']; exact hx
        rw [haccx] at h
        have ihm := ih _ h
        obtain ⟨ihacc, ihm⟩ := ihm
        constructor
        · intro a ha
          have hap : a = q := by simpa using ha.symm
          have hle1 : a.1.price = q.1.price := congrArg (·.1.price) hap
          have hle2 : q.1.price ≤ p.1.price := ihacc q rfl
          omega
        · intro r hr
          rw [List.mem_cons] at hr
          cases hr with
          | inl heq =>
            have hreq : r.1.price = x.1.price := congrArg (·.1.price) heq
            have hle : x.1.price ≤ q.1.price := by
              rcases Nat.lt_or_ge x.1.price q.1.price with hlt | hge
              · exact Nat.le_of_lt hlt
              · by_cases heq2 : q.1.price = x.1.price
                · omega
                · have hlt' : q.1.price < x.1.price := by omega
                  have hbt : better x q = true := by
                    simp only [better, decide_eq_true_eq]
                    exact Or.inl hlt'
                  exact absurd hbt hb
            have hle2 : q.1.price ≤ p.1.price := ihacc q rfl
            omega
          | inr hmem => exact ihm r hmem

/-- The engine's fill comes from the candidate set. -/
theorem bestFill_mem {buys sells : List Order} {p : Order × Order}
    (h : bestFill buys sells = some p) : p ∈ candidates buys sells := by
  have hbf : bestFill buys sells =
      (candidates buys sells).foldl pickStep none := rfl
  rw [hbf] at h
  have hmem := fold_pick_mem _ _ _ h
  cases hmem with
  | inl hm => exact hm
  | inr hnone => cases hnone

/-- The engine's fill is sound: neutral, crossing, from both books. -/
theorem bestFill_sound {buys sells : List Order} {p : Order × Order}
    (h : bestFill buys sells = some p) :
    p.1.buy = true ∧ p.2.buy = false ∧ neutral p.1.charge p.2.charge = true ∧
      p.2.price ≤ p.1.price ∧ p.1 ∈ buys ∧ p.2 ∈ sells :=
  mem_candidates (bestFill_mem h)

/-- The engine's fill has the best buy price of any candidate. -/
theorem bestFill_best_buy {buys sells : List Order} {p : Order × Order}
    (h : bestFill buys sells = some p) :
    ∀ q ∈ candidates buys sells, q.1.price ≤ p.1.price := by
  have hbf : bestFill buys sells =
      (candidates buys sells).foldl pickStep none := rfl
  rw [hbf] at h
  have hmem := fold_pick_buy _ _ _ h
  intro q hq
  exact hmem.2 q hq

/-! ## E-30: layout lookup and obstruction reports -/

/-- A successful lookup names a member with matching values. -/
theorem findField_some {ls : Layout} {n : String} {o s : Nat}
    (h : findField ls n = some (o, s)) :
    ∃ f ∈ ls, f.name = n ∧ f.off = o ∧ f.size = s := by
  induction ls with
  | nil => simp [findField] at h
  | cons f fs ih =>
    simp only [findField] at h
    cases heq : (f.name == n) with
    | true =>
      simp only [heq, if_true] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ho, hs⟩ := h
      exact ⟨f, List.mem_cons.mpr (Or.inl rfl), beq_iff_eq.mp heq, ho, hs⟩
    | false =>
      simp only [heq] at h
      obtain ⟨f', hm, hn, ho, hs⟩ := ih h
      exact ⟨f', List.mem_cons.mpr (Or.inr hm), hn, ho, hs⟩

/-- An admitted reload preserves every field's offset and size. -/
theorem admit_sound_aux : ∀ (l1 l2 : Layout),
    obstructions l1 l2 = [] → ∀ f ∈ l1, findField l2 f.name = some (f.off, f.size)
  | [], _, _, f, hf => by simp at hf
  | f :: fs, l2, h', g, hg => by
    by_cases hff : findField l2 f.name = none
    · simp only [obstructions, hff] at h'
      simp at h'
    · have hsome : ∃ v, findField l2 f.name = some v :=
        Option.ne_none_iff_exists'.mp hff
      obtain ⟨⟨o, s⟩, hfs⟩ := hsome
      simp only [obstructions, hfs] at h'
      rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h'
      obtain ⟨⟨hA, hB⟩, hC⟩ := h'
      by_cases ho : (o == f.off) = true
      · by_cases hs : (s == f.size) = true
        · have ho' : o = f.off := beq_iff_eq.mp ho
          have hs' : s = f.size := beq_iff_eq.mp hs
          rw [List.mem_cons] at hg
          cases hg with
          | inl heq =>
            subst heq
            rw [ho', hs'] at hfs
            exact hfs
          | inr hmem => exact admit_sound_aux fs l2 hC g hmem
        · simp [hs] at hB
      · simp [ho] at hA

/-- An admitted reload preserves every field. -/
theorem admit_sound {l1 l2 : Layout} (h : admitReload l1 l2 = true) :
    ∀ f ∈ l1, findField l2 f.name = some (f.off, f.size) := by
  have h' : obstructions l1 l2 = [] := by
    simp only [admitReload] at h
    exact of_decide_eq_true h
  exact admit_sound_aux l1 l2 h'

/-- A removed-field report means the field is gone. -/
theorem removed_sound : ∀ (l1 l2 : Layout) (n : String),
    .removed n ∈ obstructions l1 l2 → findField l2 n = none
  | [], _, _, h => by simp [obstructions] at h
  | f :: fs, l2, n, h => by
    by_cases hff : findField l2 f.name = none
    · simp only [obstructions, hff, List.mem_cons] at h
      rcases h with heq | hmem
      · simp only [Obstr.removed.injEq] at heq
        subst heq
        exact hff
      · exact removed_sound fs l2 n hmem
    · have hsome : ∃ v, findField l2 f.name = some v :=
        Option.ne_none_iff_exists'.mp hff
      obtain ⟨⟨o, s⟩, hfs⟩ := hsome
      simp only [obstructions, hfs, List.mem_append] at h
      rcases h with (hA | hB) | hmem
      · by_cases ho : (o == f.off) = true
        · simp only [ho] at hA
          simp at hA
        · simp only [ho, reduceCtorEq, if_false, List.mem_cons] at hA
          rcases hA with heq | hmem
          · simp at heq
          · simp at hmem
      · by_cases hs : (s == f.size) = true
        · simp only [hs] at hB
          simp at hB
        · simp only [hs, reduceCtorEq, if_false, List.mem_cons] at hB
          rcases hB with heq | hmem
          · simp at heq
          · simp at hmem
      · exact removed_sound fs l2 n hmem

/-- A shifted-field report names the new offset and a genuine change. -/
theorem shifted_sound : ∀ (l1 l2 : Layout) (n : String) (o n' : Nat),
    .shifted n o n' ∈ obstructions l1 l2 →
    ∃ s, findField l2 n = some (n', s) ∧ n' ≠ o
  | [], _, _, _, _, h => by simp [obstructions] at h
  | f :: fs, l2, n, o, n', h => by
    by_cases hff : findField l2 f.name = none
    · simp only [obstructions, hff, List.mem_cons] at h
      rcases h with heq | hmem
      · simp at heq
      · exact shifted_sound fs l2 n o n' hmem
    · have hsome : ∃ v, findField l2 f.name = some v :=
        Option.ne_none_iff_exists'.mp hff
      obtain ⟨⟨o2, s2⟩, hfs⟩ := hsome
      simp only [obstructions, hfs, List.mem_append] at h
      rcases h with (hA | hB) | hmem
      · by_cases ho : (o2 == f.off) = true
        · simp only [ho] at hA
          simp at hA
        · simp only [ho, reduceCtorEq, if_false, List.mem_cons] at hA
          rcases hA with heq | hmem
          · simp only [Obstr.shifted.injEq] at heq
            obtain ⟨hn1, hn2, hn3⟩ := heq
            subst hn1
            refine ⟨s2, by rw [hn3]; exact hfs, ?_⟩
            intro hc
            have heq2 : o2 = f.off := by rw [← hn3, hc, hn2]
            have ht : (o2 == f.off) = true := by
              rw [heq2]
              exact beq_self_eq_true _
            rw [ht] at ho
            simp at ho
          · simp at hmem
      · by_cases hs : (s2 == f.size) = true
        · simp only [hs] at hB
          simp at hB
        · simp only [hs, reduceCtorEq, if_false, List.mem_cons] at hB
          rcases hB with heq | hmem
          · simp at heq
          · simp at hmem
      · exact shifted_sound fs l2 n o n' hmem

/-! ## E-31: reachability, leaks, and the witness -/

/-- Exact one-step law: the next set is the current set plus its targets. -/
theorem mem_reachSet_succ (loans : List (Nat × Nat)) (n : Nat) (roots : List Nat)
    (x : Nat) :
    x ∈ reachSet loans (n + 1) roots ↔
      x ∈ reachSet loans n roots ∨
        (∃ y ∈ reachSet loans n roots, (y, x) ∈ loans) := by
  simp only [reachSet, stepL, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · rw [List.mem_filterMap] at h
      obtain ⟨y, hy, heq⟩ := h
      by_cases hmem : y.1 ∈ reachSet loans n roots
      · rw [if_pos hmem] at heq
        injection heq with heq'
        have hmem2 : (y.1, x) ∈ loans := by
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
        show (if y ∈ reachSet loans n roots then some x else none) = some x
        rw [if_pos hy]⟩

/-- Reachable sets only grow. -/
theorem reachSet_mono_mem (loans : List (Nat × Nat)) (n : Nat) (roots : List Nat)
    (x : Nat) (h : x ∈ reachSet loans n roots) : x ∈ reachSet loans (n + 1) roots :=
  (mem_reachSet_succ loans n roots x).mpr (Or.inl h)

/-- Roots are reachable in any number of steps. -/
theorem roots_mem_reachSet : ∀ (loans : List (Nat × Nat)) (n : Nat)
    (roots : List Nat) (r : Nat),
    r ∈ roots → r ∈ reachSet loans n roots
  | _, 0, _, _, hr => by simpa [reachSet] using hr
  | loans, n + 1, roots, r, hr => by
    exact reachSet_mono_mem loans n roots r (roots_mem_reachSet loans n roots r hr)

/-- The leak witness is genuine: it is a loan outside the reachable set. -/
theorem findLeakAux_sound : ∀ (all : List (Nat × Nat)) (roots : List Nat)
    (l : List (Nat × Nat)) (x : Nat × Nat),
    findLeakAux all roots l = some x →
    x ∈ l ∧ x.2 ∉ reachSet all all.length roots
  | _, _, [], _, h => by simp [findLeakAux] at h
  | all, roots, l :: ls, x, h => by
    simp only [findLeakAux] at h
    cases hdec : decide (l.2 ∈ reachSet all all.length roots) with
    | true =>
      simp only [hdec, if_true] at h
      obtain ⟨hm, hnr⟩ := findLeakAux_sound all roots ls x h
      exact ⟨List.mem_cons.mpr (Or.inr hm), hnr⟩
    | false =>
      simp only [hdec] at h
      have heq : l = x := by simpa using h
      have hmem : x ∈ l :: ls := by
        rw [heq]
        exact List.mem_cons.mpr (Or.inl rfl)
      have hnr : x.2 ∉ reachSet all all.length roots := by
        rw [← heq]
        intro hc
        have hdt : decide (l.2 ∈ reachSet all all.length roots) = true := by
          simp only [decide_eq_true_eq]
          exact hc
        rw [hdt] at hdec
        simp at hdec
      exact ⟨hmem, hnr⟩

/-- Silence of the witness means every loan in the list is live. -/
theorem findLeakAux_none : ∀ (all : List (Nat × Nat)) (roots : List Nat)
    (l : List (Nat × Nat)),
    findLeakAux all roots l = none → ∀ x ∈ l, x.2 ∈ reachSet all all.length roots
  | _, _, [], _, x, hx => by simp at hx
  | all, roots, l :: ls, h, x, hx => by
    simp only [findLeakAux] at h
    cases hdec : decide (l.2 ∈ reachSet all all.length roots) with
    | true =>
      simp only [hdec, if_true] at h
      have ih := findLeakAux_none all roots ls h

      rw [List.mem_cons] at hx
      cases hx with
      | inl heq =>
        subst heq
        exact of_decide_eq_true hdec
      | inr hmem => exact ih x hmem
    | false =>
      simp only [hdec] at h
      simp at h

/-- No witness: the loan book is leak-free. -/
theorem leakFree_of_findLeak_none {loans : List (Nat × Nat)} {roots : List Nat}
    (h : findLeak loans roots = none) : leakFree loans roots = true := by
  simp only [findLeak] at h
  simp only [leakFree, List.all_eq_true]
  intro l hl
  have hlive := findLeakAux_none loans roots loans h l hl
  simp only [decide_eq_true_eq]
  exact hlive

/-! ## E-32: the fixed-point reduction -/

/-- Sums split over appends. -/
theorem lsum_append (xs ys : List Nat) : lsum (xs ++ ys) = lsum xs + lsum ys := by
  induction xs with
  | nil => simp [lsum]
  | cons hd tl ih => simp only [lsum, List.cons_append, ih]; ac_rfl

/-- Reversal helper, generalizing the accumulator. -/
theorem lsum_reverseAux (l acc : List Nat) :
    lsum (List.reverseAux l acc) = lsum l + lsum acc := by
  induction l generalizing acc with
  | nil => simp [lsum, List.reverseAux]
  | cons hd tl ih =>
    simp only [List.reverseAux, lsum]
    have h := ih (hd :: acc)
    simp only [lsum] at h
    omega

/-- Reversal preserves the sum. -/
theorem lsum_reverse (l : List Nat) : lsum l.reverse = lsum l := by
  have hr : l.reverse = List.reverseAux l [] := rfl
  rw [hr]
  have h := lsum_reverseAux l []
  simp only [lsum] at h
  omega

/-- Localization: the orbit sum is twice the fundamental-domain sum. -/
theorem localize (xs : List Nat) (f : Nat → Nat) :
    orbitSum f xs = 2 * halfSum f xs := by
  simp only [orbitSum, halfSum, lsum_append, lsum_reverse]
  omega

/-! ## E-33: the reflection-positivity certificate -/

/-- Every square is nonnegative. -/
theorem sq_nonneg' (z : Int) : 0 ≤ z * z := by
  have h : z * z = ((z.natAbs * z.natAbs : Nat) : Int) :=
    (Int.natAbs_mul_self).symm
  rw [h]
  exact Int.natCast_nonneg _

/-- An accepted Gram matrix certifies a nonnegative value. -/
theorem rp_nonneg (g : Gram) (h : rpCheck g = true) (x y : Int) :
    0 ≤ sosVal g x y := by
  have hc : 0 < g.a ∧ 0 ≤ g.a * g.c - g.b * g.b := by
    simp only [rpCheck] at h
    exact of_decide_eq_true h
  obtain ⟨-, hdet⟩ := hc
  have hsq1 := sq_nonneg' (g.a * x + g.b * y)
  have hsq2 := sq_nonneg' y
  have hbb := sq_nonneg' g.b
  have hgac : 0 ≤ g.a * g.c := by omega
  have hmul := Int.mul_nonneg hgac hsq2
  simp only [sosVal]
  exact Int.add_nonneg hsq1 hmul

/-- The certificate value is `a` times the correlator, up to the square. -/
theorem rp_identity (g : Gram) (x y : Int) :
    sosVal g x y =
      g.a * correlator g x y + (g.b * g.b) * (y * y) := by
  have k1 : (g.a * x) * (g.a * x) = g.a * (g.a * (x * x)) := by ac_rfl
  have k2 : (g.a * x) * (g.b * y) = g.a * g.b * (x * y) := by ac_rfl
  have k3 : (g.b * y) * (g.a * x) = g.a * g.b * (x * y) := by ac_rfl
  have k4 : (g.b * y) * (g.b * y) = (g.b * g.b) * (y * y) := by ac_rfl
  have k6 : g.a * (g.b * (x * y)) = g.a * g.b * (x * y) := by ac_rfl
  have k7 : g.a * (g.c * (y * y)) = g.a * g.c * (y * y) := by ac_rfl
  simp only [sosVal, correlator, Int.add_mul, Int.mul_add,
    Int.two_mul, k1, k2, k3, k4, k6, k7]
  omega

/-! ## E-34: Cauchy–Schwarz and the uniform schedule -/

/-- Pointwise: twice the product is bounded by the sum of squares. -/
theorem two_mul_le_add_sq : ∀ x y : Nat, 2 * x * y ≤ x * x + y * y := by
  intro x
  induction x with
  | zero => intro y; simp
  | succ x ih =>
    intro y
    cases y with
    | zero => simp
    | succ y =>
      have h := ih y
      have eL : 2 * (x + 1) * (y + 1) = 2 * x * y + (2 * x + 2 * y) + 2 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
        ac_rfl
      have eR : (x + 1) * (x + 1) + (y + 1) * (y + 1) =
          ((x * x + x) + (x + 1)) + ((y * y + y) + (y + 1)) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega

/-- Summed: the cross term is bounded by length times square plus impact. -/
theorem sum_cs (x : Nat) : ∀ xs : List Nat,
    2 * x * lsum xs ≤ xs.length * (x * x) + schedSq xs
  | [] => by simp [lsum, schedSq, List.length]
  | z :: zs => by
    have ih := sum_cs x zs
    have hpt := two_mul_le_add_sq x z
    have e1 : lsum (z :: zs) = z + lsum zs := rfl
    have e2 : schedSq (z :: zs) = z * z + schedSq zs := rfl
    have eL2 : (z :: zs).length = zs.length + 1 := rfl
    rw [e1, e2, eL2, Nat.mul_add, Nat.add_mul, Nat.one_mul]
    omega

/-- Cauchy–Schwarz: the squared sum is bounded by length times impact. -/
theorem cs_ineq : ∀ xs : List Nat, lsum xs * lsum xs ≤ xs.length * schedSq xs
  | [] => by simp [lsum, schedSq, List.length]
  | z :: zs => by
    have ih := cs_ineq zs
    have hs := sum_cs z zs
    have e1 : lsum (z :: zs) = z + lsum zs := rfl
    have e2 : schedSq (z :: zs) = z * z + schedSq zs := rfl
    have eL2 : (z :: zs).length = zs.length + 1 := rfl
    have eL : (z + lsum zs) * (z + lsum zs) =
        z * z + (z * lsum zs + (z * lsum zs + lsum zs * lsum zs)) := by
      simp only [Nat.add_mul, Nat.mul_add]
      ac_rfl
    have eR : (zs.length + 1) * (z * z + schedSq zs) =
        zs.length * (z * z) +
          (zs.length * schedSq zs + (z * z + schedSq zs)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      ac_rfl
    have g1 : lsum (z :: zs) * lsum (z :: zs) =
        z * z + (z * lsum zs + (z * lsum zs + lsum zs * lsum zs)) := by
      rw [e1]
      exact eL
    have g2 : (z :: zs).length * schedSq (z :: zs) =
        zs.length * (z * z) +
          (zs.length * schedSq zs + (z * z + schedSq zs)) := by
      rw [eL2, e2]
      exact eR
    have hcomm : (2 * z) * lsum zs = 2 * (z * lsum zs) := by ac_rfl
    rw [hcomm] at hs
    rw [g1, g2]
    omega

/-- Any schedule's impact, scaled by length, dominates the squared target. -/
theorem schedule_bound (sched : List Nat) (Q : Nat) (h : lsum sched = Q) :
    sched.length * schedSq sched ≥ Q * Q := by
  have hcs := cs_ineq sched
  rw [h] at hcs
  exact hcs

/-! ## E-35: the cube expansion certificate -/

set_option maxRecDepth 10000 in
/-- The cube is 3-regular. -/
theorem cube_regular : ∀ v ∈ [0,1,2,3,4,5,6,7], deg v = 3 := by
  decide

set_option maxRecDepth 10000 in
/-- Every small cut meets the expansion bound. -/
theorem cube_expansion : ∀ m, m < 256 → (maskVerts m).length ≤ 4 →
    (maskVerts m).length ≤ (boundary (maskVerts m)).length := by
  decide

/-- An accepted cut meets the bound. -/
theorem goodCut_sound (S : List Nat) (h : goodCut S = true) :
    S.length ≤ (boundary S).length := by
  simp only [goodCut] at h
  exact of_decide_eq_true h

/-! ## E-36: chip-firing conservation and stabilization -/

/-- Cons on configurations splits the total. -/
theorem total_cons (w c : Nat) (rest : List (Nat × Nat)) :
    total ((w, c) :: rest) = c + total rest := rfl

/-- Reading back a set vertex. -/
theorem get_put_same : ∀ (cfg : List (Nat × Nat)) (v c : Nat),
    get (put cfg v c) v = c
  | [], _, _ => by simp [put, get]
  | (w, c') :: rest, v, c => by
    cases heq : (w == v) with
    | true => simp only [put, get, heq, if_true]
    | false =>
      simp [put, get, heq]
      exact get_put_same rest v c

/-- Other vertices are untouched. -/
theorem get_put_other : ∀ (cfg : List (Nat × Nat)) (v w c : Nat),
    w ≠ v → get (put cfg v c) w = get cfg w
  | [], v, w, c, hne => by
    by_cases heq : (v == w) = true
    · have h1 : v = w := beq_iff_eq.mp heq
      exact absurd h1.symm hne
    · simp [put, get, heq]
  | (u, c') :: rest, v, w, c, hne => by
    by_cases heq : (u == v) = true
    · by_cases heq2 : (u == w) = true
      · have h1 : u = v := beq_iff_eq.mp heq
        have h2 : u = w := beq_iff_eq.mp heq2
        have h3 : w = v := by omega
        exact absurd h3 hne
      · simp [put, get, heq, heq2]
    · by_cases heq2 : (u == w) = true
      · simp [put, get, heq, heq2]
      · simp [put, get, heq, heq2]
        exact get_put_other rest v w c hne

/-- A vertex holds no more than the total. -/
theorem get_le_total : ∀ (cfg : List (Nat × Nat)) (v : Nat),
    get cfg v ≤ total cfg
  | [], _ => by simp [get, total, lsum]
  | (w, c') :: rest, v => by
    cases heq : (w == v) with
    | true =>
      simp only [get, total_cons, heq, if_true]
      omega
    | false =>
      simp only [get, total_cons, heq, reduceCtorEq, if_false]
      have ih := get_le_total rest v
      omega

/-- Setting a vertex adjusts the total by the difference. -/
theorem total_put : ∀ (cfg : List (Nat × Nat)) (v c : Nat),
    total (put cfg v c) = total cfg - get cfg v + c
  | [], v, c => by simp [total, put, get, lsum]
  | (w, c') :: rest, v, c => by
    cases heq : (w == v) with
    | true =>
      simp only [put, get, total_cons, heq, if_true]
      omega
    | false =>
      simp [put, get, total_cons, heq]
      have ih := total_put rest v c
      have hle := get_le_total rest v
      omega

/-- Distributing one chip to each vertex adds the count. -/
theorem total_fold_add (ws : List Nat) (cfg : List (Nat × Nat)) :
    total (ws.foldl (fun c w => put c w (get c w + 1)) cfg) =
      total cfg + ws.length := by
  induction ws generalizing cfg with
  | nil => rfl
  | cons w ws ih =>
    have hfold : (w :: ws).foldl (fun c w => put c w (get c w + 1)) cfg =
        ws.foldl (fun c w => put c w (get c w + 1))
          (put cfg w (get cfg w + 1)) := rfl
    have hlen : (w :: ws).length = ws.length + 1 := rfl
    rw [hfold, hlen]
    have h1 : total (put cfg w (get cfg w + 1)) = total cfg + 1 := by
      have hput := total_put cfg w (get cfg w + 1)
      have hle := get_le_total cfg w
      omega
    have ih' := ih (put cfg w (get cfg w + 1))
    omega

/-- Firing conserves chips. -/
theorem fire_total (edges : List (Nat × Nat)) (cfg : List (Nat × Nat))
    (v : Nat) : total (fire edges cfg v) = total cfg := by
  simp only [fire]
  by_cases h : (neighbors edges v).length ≤ get cfg v
  · simp only [h, if_true]
    have hfold := total_fold_add (neighbors edges v)
      (put cfg v (get cfg v - (neighbors edges v).length))
    have hput := total_put cfg v (get cfg v - (neighbors edges v).length)
    have hle := get_le_total cfg v
    omega
  · simp only [h, if_false]

/-- Stabilization conserves chips. -/
theorem stabilize_total : ∀ (fuel : Nat) (edges cfg : List (Nat × Nat))
    (bank : Nat) (verts : List Nat),
    total (stabilize fuel edges cfg bank verts) = total cfg
  | 0, _, cfg, _, _ => by simp [stabilize]
  | fuel + 1, edges, cfg, bank, verts => by
    simp only [stabilize]
    cases hfu : findUnstable edges cfg bank verts with
    | none => simp
    | some v =>
      dsimp only
      have ih := stabilize_total fuel edges (fire edges cfg v) bank verts
      have hf := fire_total edges cfg v
      omega

/-- A stable configuration has no unstable vertex. -/
theorem findUnstable_none : ∀ (edges cfg : List (Nat × Nat)) (bank : Nat)
    (verts : List Nat), Stable edges cfg bank verts →
    findUnstable edges cfg bank verts = none
  | _, _, _, [], _ => by simp [findUnstable]
  | edges, cfg, bank, v :: vs, hstab => by
    simp only [findUnstable]
    cases heq : (v == bank) with
    | true =>
      simp only [if_true]
      have hrest : Stable edges cfg bank vs :=
        fun w hw hne => hstab w (List.mem_cons.mpr (Or.inr hw)) hne
      exact findUnstable_none edges cfg bank vs hrest
    | false =>
      have hne : v ≠ bank := by
        intro hcontra
        have h1 : (bank == bank) = true := beq_self_eq_true bank
        rw [hcontra, h1] at heq
        exact absurd heq (by decide)
      have hlt : get cfg v < (neighbors edges v).length :=
        hstab v (List.mem_cons.mpr (Or.inl rfl)) hne
      have hnp : ¬ (neighbors edges v).length ≤ get cfg v := by omega
      have hdec : decide ((neighbors edges v).length ≤ get cfg v) = false := by
        simp [hnp]
      simp [hdec]
      have hrest : Stable edges cfg bank vs :=
        fun w hw hne2 => hstab w (List.mem_cons.mpr (Or.inr hw)) hne2
      exact findUnstable_none edges cfg bank vs hrest

/-- Stabilizing a stable configuration is the identity. -/
theorem stable_stabilize : ∀ (fuel : Nat) (edges cfg : List (Nat × Nat))
    (bank : Nat) (verts : List Nat), Stable edges cfg bank verts →
    stabilize fuel edges cfg bank verts = cfg
  | 0, _, cfg, _, _, _ => by simp [stabilize]    | fuel + 1, edges, cfg, bank, verts, hstab => by
    simp only [stabilize]
    have hfu := findUnstable_none edges cfg bank verts hstab
    simp only [hfu]

/-- Fast-path admission covers the genus. -/
theorem admitFast_sound (edges : List (Nat × Nat)) (verts : List Nat)
    (cfg : List (Nat × Nat)) (h : admitFast edges verts cfg = true) :
    genus edges verts ≤ total cfg := by
  simp only [admitFast] at h
  exact of_decide_eq_true h

/-! ## E-37: the exceptional-point gap law -/

/-- The residual determinant is the squared shift minus the perturbation. -/
theorem gapLaw (d e : Int) : det2 d 1 e d = d * d - e := by
  simp [det2]

/-- At zero perturbation the residual is nilpotent: the EP certificate. -/
theorem ep_nilpotent : matMul2 nilMat nilMat = zeroMat := by
  decide

/-- A fired alarm names a reading whose square clears the threshold. -/
theorem detect_sound (t : Int) (rs : List Int) (h : detect t rs = true) :
    ∃ d ∈ rs, t ≤ d * d := by
  simp only [detect, List.any_eq_true] at h
  obtain ⟨d, hmem, hd⟩ := h
  exact ⟨d, hmem, of_decide_eq_true hd⟩

/-- A vanishing residual pins the perturbation to the squared shift. -/
theorem gap_zero (d e : Int) (h : det2 d 1 e d = 0) : e = d * d := by
  have g := gapLaw d e
  omega

end Morph.Specs.BatchBCD
