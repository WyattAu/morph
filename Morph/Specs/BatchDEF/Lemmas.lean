/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchDEF.Spec

/-!
# Frontier Kernels — lemmas (E-38–E-47)

Status: In Progress (loop 107, third-ten first cycle).

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms: every
theorem is proved by structural induction with `simp`/`omega` over the
project-local recursive definitions, or by `decide` over finite types.
-/

namespace Morph.Specs.BatchDEF

/-! ## E-38: graded routing outcomes -/

/-- The pairwise check agrees with universal membership. -/
theorem loadsOK_all : ∀ (ls : List Nat) (cs : List Link),
    loadsOK ls cs = true ↔ ∀ p ∈ ls.zip cs, p.1 ≤ p.2.cap
  | [], _ => by simp [loadsOK]
  | _ :: _, [] => by simp [loadsOK]
  | l :: ls, c :: cs => by
    simp only [loadsOK, List.zip_cons_cons, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hm
      · exact of_decide_eq_true h1
      · exact (loadsOK_all ls cs).mp h2 p hm
    · intro h
      refine ⟨?_, (loadsOK_all ls cs).mpr ?_⟩
      · have hm : (l, c) ∈ (l :: ls).zip (c :: cs) := by
          rw [List.zip_cons_cons]
          exact List.mem_cons.mpr (Or.inl rfl)
        simpa using h (l, c) hm
      · intro p hp
        have hm : p ∈ (l :: ls).zip (c :: cs) := by
          rw [List.zip_cons_cons]
          exact List.mem_cons.mpr (Or.inr hp)
        exact h p hm

/-- Silence means every pair fits. -/
theorem firstBad_none : ∀ (ls : List Nat) (cs : List Link),
    firstBad ls cs = none → loadsOK ls cs = true
  | [], _, _ => by simp [loadsOK]
  | _ :: _, [], _ => by simp [loadsOK]
  | l :: ls, c :: cs, h => by
    simp only [firstBad] at h
    by_cases hc : l ≤ c.cap
    · have hd : decide (l ≤ c.cap) = true := by simpa using hc
      simp only [hd, if_true] at h
      simp only [loadsOK, hd, Bool.true_and]
      exact firstBad_none ls cs h
    · have hd : decide (l ≤ c.cap) = false := by simpa using hc
      simp only [hd, reduceCtorEq, if_false] at h

/-- A clean check finds nothing. -/
theorem firstBad_of_ok : ∀ (ls : List Nat) (cs : List Link),
    loadsOK ls cs = true → firstBad ls cs = none
  | [], _, _ => by simp [firstBad]
  | _ :: _, [], _ => by simp [firstBad]
  | l :: ls, c :: cs, h => by
    simp only [loadsOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hc : l ≤ c.cap := of_decide_eq_true h1
    have hd : decide (l ≤ c.cap) = true := by simpa using hc
    simp only [firstBad, hd, if_true]
    exact firstBad_of_ok ls cs h2

/-- A reported conflict really violates its cap. -/
theorem firstBad_some_mem : ∀ (ls : List Nat) (cs : List Link) (l : Nat)
    (c : Link), firstBad ls cs = some (l, c) →
    (l, c) ∈ ls.zip cs ∧ c.cap < l
  | [], _, _, _, h => by simp [firstBad] at h
  | _ :: _, [], _, _, h => by simp [firstBad] at h
  | l :: ls, c :: cs, l', c', h => by
    simp only [firstBad] at h
    by_cases hc : l ≤ c.cap
    · have hd : decide (l ≤ c.cap) = true := by simpa using hc
      simp only [hd, if_true] at h
      have ih := firstBad_some_mem ls cs l' c' h
      exact ⟨List.mem_cons.mpr (Or.inr ih.1), ih.2⟩
    · have hd : decide (l ≤ c.cap) = false := by simpa using hc
      simp only [hd, reduceCtorEq, if_false] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons.mpr (Or.inl rfl), by omega⟩

/-- The solver is feasible exactly on clean instances. -/
theorem solve_ok : ∀ (ls : List Nat) (cs : List Link),
    solve ls cs = .ok ↔ loadsOK ls cs = true := by
  intro ls cs
  constructor
  · intro h
    by_cases hfb : firstBad ls cs = none
    · exact firstBad_none ls cs hfb
    · have hs : ∃ p, firstBad ls cs = some p :=
        Option.ne_none_iff_exists'.mp hfb
      obtain ⟨p, hsome⟩ := hs
      obtain ⟨l, c⟩ := p
      simp only [solve, hsome] at h
      cases h
  · intro h
    have hfb := firstBad_of_ok ls cs h
    unfold solve
    rw [hfb]

/-- A blocked certificate names a genuine violation. -/
theorem solve_blocked_viol : ∀ (ls : List Nat) (cs : List Link) (c : Cert),
    solve ls cs = .blocked c →
    ∃ l k, (l, k) ∈ ls.zip cs ∧ l = c.load ∧ k.name = c.link ∧ k.cap < l := by
  intro ls cs c h
  simp only [solve] at h
  cases hfb : firstBad ls cs with
  | none => simp [hfb] at h
  | some p =>
    obtain ⟨l, k⟩ := p
    have hmem := firstBad_some_mem ls cs l k hfb
    simp only [hfb] at h
    cases h
    exact ⟨l, k, hmem.1, rfl, rfl, hmem.2⟩

/-- A blocked certificate carries the true maximal feasible fraction. -/
theorem solve_blocked_frac : ∀ (ls : List Nat) (cs : List Link) (c : Cert),
    solve ls cs = .blocked c →
    c.sat = satCount ls cs ∧ c.tot = (ls.zip cs).length := by
  intro ls cs c h
  simp only [solve] at h
  cases hfb : firstBad ls cs with
  | none => simp [hfb] at h
  | some p =>
    obtain ⟨l, k⟩ := p
    simp only [hfb] at h
    cases h
    exact ⟨rfl, rfl⟩

/-- Satisfied pairs never exceed total pairs. -/
theorem satCount_le : ∀ (ls : List Nat) (cs : List Link),
    satCount ls cs ≤ (ls.zip cs).length
  | [], _ => by simp [satCount]
  | _ :: _, [] => by simp [satCount]
  | l :: ls, c :: cs => by
    have ih := satCount_le ls cs
    by_cases hc : l ≤ c.cap
    · simp only [satCount, List.zip_cons_cons, List.length_cons, hc, if_true]
      omega
    · simp only [satCount, List.zip_cons_cons, List.length_cons, hc, if_false]
      omega

/-- On clean instances the fraction is one. -/
theorem loadsOK_sat : ∀ (ls : List Nat) (cs : List Link),
    loadsOK ls cs = true → satCount ls cs = (ls.zip cs).length
  | [], _, _ => by simp [satCount]
  | _ :: _, [], _ => by simp [satCount]
  | l :: ls, c :: cs, h => by
    simp only [loadsOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hc : l ≤ c.cap := of_decide_eq_true h1
    have ih := loadsOK_sat ls cs h2
    simp only [satCount, List.zip_cons_cons, List.length_cons, hc, if_true]
    omega

/-! ## E-39: slicing preserves evaluation -/

/-- Slicing preserves the observable value. -/
theorem eval_prune : ∀ t : Tree, eval (prune t) = eval t
  | .const _ => rfl
  | .add l r => by
    have ihl := eval_prune l
    have ihr := eval_prune r
    by_cases h1 : eval (prune l) = 0
    · have e1 : eval l = 0 := by rw [← ihl]; exact h1
      have hp : prune (.add l r) = prune r := by simp [prune, h1]
      calc eval (prune (.add l r)) = eval (prune r) := by rw [hp]
        _ = eval r := ihr
        _ = eval l + eval r := by rw [e1]; omega
    · by_cases h2 : eval (prune r) = 0
      · have e2 : eval r = 0 := by rw [← ihr]; exact h2
        have hp : prune (.add l r) = prune l := by simp [prune, h1, h2]
        calc eval (prune (.add l r)) = eval (prune l) := by rw [hp]
          _ = eval l := ihl
          _ = eval l + eval r := by rw [e2]; omega
      · have hp : prune (.add l r) = .add (prune l) (prune r) := by
          simp [prune, h1, h2]
        calc eval (prune (.add l r)) = eval (prune l) + eval (prune r) := by
              rw [hp]; rfl
          _ = eval l + eval r := by rw [ihl, ihr]

/-- Slicing removes all dead weight. -/
theorem prune_noDead : ∀ t : Tree, deadCount (prune t) = 0
  | .const _ => by simp [prune, deadCount]
  | .add l r => by
    have ihl := prune_noDead l
    have ihr := prune_noDead r
    by_cases h1 : eval (prune l) = 0
    · have hp : prune (.add l r) = prune r := by simp [prune, h1]
      simp only [hp]
      exact ihr
    · by_cases h2 : eval (prune r) = 0
      · have hp : prune (.add l r) = prune l := by simp [prune, h1, h2]
        simp only [hp]
        exact ihl
      · have hp : prune (.add l r) = .add (prune l) (prune r) := by
          simp [prune, h1, h2]
        simp [hp, deadCount, h1, h2, ihl, ihr]

/-- The trivial cut (whole tree, zero remainder) always exists. -/
theorem mem_cuts_self : ∀ t : Tree, (t, .const 0) ∈ cuts t
  | .const _ => by
    simp only [cuts]
    exact List.mem_cons.mpr (Or.inl rfl)
  | .add _ _ => by
    simp only [cuts]
    exact List.mem_cons.mpr (Or.inl rfl)

/-- Every coproduct cut splits evaluation additively. -/
theorem cut_eval : ∀ (t : Tree) (c : Tree × Tree),
    c ∈ cuts t → eval c.1 + eval c.2 = eval t
  | .const _, _ => by
    intro hc
    simp only [cuts, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain rfl := hc
    simp [eval]
  | .add l r, c => by
    intro hc
    have hc3 : c = (.add l r, .const 0) ∨
        c ∈ (cuts l).map (fun c => (c.1, .add c.2 r)) ∨
        c ∈ (cuts r).map (fun c => (c.1, .add l c.2)) := by
      simpa [cuts, List.mem_cons, List.mem_append] using hc
    rcases hc3 with rfl | hml | hmr
    · simp [eval]
    · simp only [List.mem_map] at hml
      obtain ⟨c', hc', rfl⟩ := hml
      have ih := cut_eval l c' hc'
      show eval c'.1 + eval (.add c'.2 r) = eval (.add l r)
      simp only [eval]
      omega
    · simp only [List.mem_map] at hmr
      obtain ⟨c', hc', rfl⟩ := hmr
      have ih := cut_eval r c' hc'
      show eval c'.1 + eval (.add l c'.2) = eval (.add l r)
      simp only [eval]
      omega

/-- The antipode negates the observable. -/
theorem neg_eval : ∀ t : Tree, eval (neg t) = -eval t
  | .const _ => by simp only [neg, eval]
  | .add l r => by
    have ihl := neg_eval l
    have ihr := neg_eval r
    simp only [neg, eval, ihl, ihr]
    omega

/-! ## E-40: two polarizations, one spectrum -/

/-- Register cells sum to the two coordinate sums. -/
theorem lowerReg_eval : ∀ k : List (Nat × Nat),
    lsum (lowerReg k) = lsum (k.map (·.1)) + lsum (k.map (·.2))
  | [] => by simp [lowerReg, lsum]
  | (a, b) :: k => by
    have ih := lowerReg_eval k
    simp only [lowerReg, List.map_cons, lsum]
    omega

/-- List sum distributes over append. -/
theorem lsum_append : ∀ (a b : List Nat), lsum (a ++ b) = lsum a + lsum b
  | [], _ => by simp [lsum]
  | x :: xs, b => by
    have ih := lsum_append xs b
    simp only [List.cons_append, lsum]
    omega

/-- BKS conformance: both polarizations give the same spectrum. -/
theorem conform_eval : ∀ k : List (Nat × Nat),
    evalCells (lowerReg k) = evalCells (lowerStack k) := by
  intro k
  simp only [evalCells, lowerStack, lsum_append]
  exact lowerReg_eval k

/-- The register polarization preserves phase volume. -/
theorem volReg : ∀ k : List (Nat × Nat), (lowerReg k).length = 2 * k.length
  | [] => by simp [lowerReg]
  | _ :: k => by
    have ih := volReg k
    simp only [lowerReg, List.length_cons]
    omega

/-- The stack polarization preserves phase volume. -/
theorem volStack : ∀ k : List (Nat × Nat), (lowerStack k).length = 2 * k.length
  | [] => by simp [lowerStack]
  | _ :: k => by
    have ih := volStack k
    simp only [lowerStack, List.length_append, List.length_map, List.length_cons]
    omega

/-! ## E-41: the ternary check refines the global one -/

/-- One-step reachability is sound. -/
theorem step_mem : ∀ (e : List (Nat × Nat)) (front : List Nat) (x y : Nat),
    (x, y) ∈ e → x ∈ front → y ∈ stepE e front := by
  intro e front x y hmem hx
  simp only [stepE, List.mem_append]
  exact Or.inr (by
    rw [List.mem_filterMap]
    exact ⟨(x, y), hmem, by simp [hx]⟩)

/-- A directed 3-cycle reaches around in three steps. -/
theorem mem3 : ∀ (e : List (Nat × Nat)) (a b c : Nat),
    (a, b) ∈ e → (b, c) ∈ e → (c, a) ∈ e → a ∈ reachE e 3 [a] := by
  intro e a b c h1 h2 h3
  simp only [reachE]
  have hb : b ∈ stepE e [a] := step_mem e [a] a b h1 (by simp)
  have hc : c ∈ stepE e (stepE e [a]) := step_mem e _ b c h2 hb
  exact step_mem e _ c a h3 hc

/-- Reachability persists forward in fuel. -/
theorem reach_succ_mem : ∀ (e : List (Nat × Nat)) (n : Nat) (r : List Nat)
    (x : Nat), x ∈ reachE e n r → x ∈ reachE e (n + 1) r := by
  intro e n r x h
  simp only [reachE, stepE, List.mem_append]
  exact Or.inl h

/-- Reachability is monotone in fuel. -/
theorem reach_le : ∀ (e : List (Nat × Nat)) (k n : Nat) (r : List Nat)
    (x : Nat), x ∈ reachE e n r → x ∈ reachE e (n + k) r
  | _, 0, _, _, _, h => h
  | e, k + 1, n, r, x, h => by
    have ih := reach_le e k n r x h
    have heq : n + (k + 1) = (n + k) + 1 := by omega
    rw [heq]
    exact reach_succ_mem e (n + k) r x ih

/-- A Massey triple always triggers the global cycle check. -/
theorem massey_sound : ∀ (e : List (Nat × Nat)) (a b c : Nat),
    massey3 a b c e = true → hasCycle e = true := by
  intro e a b c h
  simp only [massey3, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, -, -, -⟩ := h
  simp only [hasCycle, List.any_eq_true]
  refine ⟨(a, b), h1, ?_⟩
  simp only [decide_eq_true_eq]
  have hm := mem3 e a b c h1 h2 h3
  have heq : e.length + 3 = 3 + e.length := by omega
  rw [heq]
  exact reach_le e e.length 3 [a] a hm

/-- A Massey triple excludes every back-edge. -/
theorem massey_excl : ∀ (e : List (Nat × Nat)) (a b c : Nat),
    massey3 a b c e = true → (b, a) ∉ e ∧ (c, b) ∉ e ∧ (a, c) ∉ e := by
  intro e a b c h
  simp only [massey3, decide_eq_true_eq] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ## E-42: packing preserves the ABI boundary -/

/-- Offsets grow with the field list. -/
theorem extentsAux_length : ∀ (b : Nat) (fs : List Nat),
    (extentsAux b fs).length = fs.length
  | _, [] => by simp [extentsAux]
  | b, f :: fs => by
    have ih := extentsAux_length (b + f) fs
    simp only [extentsAux, List.length_cons]
    omega

/-- Every offset clears the base. -/
theorem extentsAux_ge : ∀ (b : Nat) (fs : List Nat) (p : Nat × Nat),
    p ∈ extentsAux b fs → b ≤ p.1
  | _, [], _, hm => by simp [extentsAux] at hm
  | b, f :: fs, p, hm => by
    simp only [extentsAux, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact Nat.le_refl _
    · have ih := extentsAux_ge (b + f) fs p hm
      omega

/-- Packed extents are pairwise disjoint. -/
theorem aux_disjoint : ∀ (b : Nat) (fs : List Nat),
    (extentsAux b fs).Pairwise fun p q => disj p q
  | _, [] => by simp [extentsAux]
  | b, f :: fs => by
    have ih := aux_disjoint (b + f) fs
    have hge := extentsAux_ge (b + f) fs
    simp only [extentsAux, List.pairwise_cons]
    refine ⟨?_, ih⟩
    intro q hq
    have hq1 := hge q hq
    simp only [disj]
    exact Or.inl hq1

/-- Packing never resizes a field. -/
theorem sizes_preserved : ∀ (b : Nat) (fs : List Nat),
    (extentsAux b fs).map Prod.snd = fs
  | _, [] => by simp [extentsAux]
  | b, f :: fs => by
    have ih := sizes_preserved (b + f) fs
    simp only [extentsAux, List.map_cons, ih]

/-- The Boolean and propositional disjointness agree. -/
theorem disjB_eq : ∀ (p q : Nat × Nat), disjB p q = true ↔ disj p q := by
  intro p q
  simp only [disjB, disj, decide_eq_true_eq]

/-- One extent against a tail: check iff universal disjointness. -/
theorem allDisjoint_all : ∀ (p : Nat × Nat) (qs : List (Nat × Nat)),
    allDisjoint p qs = true ↔ ∀ q ∈ qs, disj p q
  | _, [] => by simp [allDisjoint]
  | p, q :: qs => by
    simp only [allDisjoint, Bool.and_eq_true, List.mem_cons, disjB_eq]
    constructor
    · rintro ⟨h1, h2⟩ r hr
      rcases hr with rfl | hm
      · exact h1
      · exact (allDisjoint_all p qs).mp h2 r hm
    · intro h
      refine ⟨?_, (allDisjoint_all p qs).mpr ?_⟩
      · exact h q (Or.inl rfl)
      · intro r hr
        exact h r (Or.inr hr)

/-- A passing certificate means genuine pairwise disjointness. -/
theorem cert_sound : ∀ (es : List (Nat × Nat)),
    disjointCheck es = true → es.Pairwise fun p q => disj p q
  | [] => by simp [disjointCheck]
  | p :: ps => by
    intro h
    simp only [disjointCheck, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.pairwise_cons]
    exact ⟨(allDisjoint_all p ps).mp h1, cert_sound ps h2⟩

/-- Genuine disjointness always passes the certificate. -/
theorem cert_complete : ∀ (es : List (Nat × Nat)),
    es.Pairwise (fun p q => disj p q) → disjointCheck es = true
  | [] => by simp [disjointCheck]
  | p :: ps => by
    intro h
    simp only [List.pairwise_cons] at h
    obtain ⟨h1, h2⟩ := h
    simp only [disjointCheck, Bool.and_eq_true]
    exact ⟨(allDisjoint_all p ps).mpr h1, cert_complete ps h2⟩

/-- The greedy pack always certifies. -/
theorem pack_cert : ∀ (fs : List Nat), disjointCheck (extents fs) = true :=
  fun fs => cert_complete _ (aux_disjoint 0 fs)

/-! ## E-43: reroutes stay on the graph and off the locus -/

/-- neighbours really are edges. -/
theorem mem_neighbors : ∀ (e : List (Nat × Nat)) (v w : Nat),
    w ∈ neighbors e v → (v, w) ∈ e := by
  intro e v w h
  simp only [neighbors, List.mem_filterMap] at h
  obtain ⟨e', he', heq⟩ := h
  by_cases hc : (e'.1 == v) = true
  · simp only [hc, if_true, Option.some.injEq] at heq
    have h1 : e'.1 = v := beq_iff_eq.mp hc
    obtain ⟨a, b⟩ := e'
    subst h1
    subst heq
    exact he'
  · simp only [hc, reduceCtorEq, if_false] at heq

/-- A path plus one more hop is a path. -/
theorem isPath_cons : ∀ (e : List (Nat × Nat)) (a b : Nat) (r : List Nat),
    isPath (a :: b :: r) e = true →
    decide ((a, b) ∈ e) = true ∧ isPath (b :: r) e = true := by
  intro e a b r h
  by_cases hc : (a, b) ∈ e
  · have hd : decide ((a, b) ∈ e) = true := by simpa using hc
    simp only [isPath, hd, if_true] at h
    exact ⟨hd, h⟩
  · have hd : decide ((a, b) ∈ e) = false := by simpa using hc
    simp only [isPath, hd, reduceCtorEq, if_false] at h

/-- Appending a linked hop preserves path validity. -/
theorem isPath_append_single : ∀ (e : List (Nat × Nat)) (p : List Nat)
    (w : Nat), isPath p e = true → (∀ v, p.getLast? = some v → (v, w) ∈ e) →
    isPath (p ++ [w]) e = true
  | _, [], _, _, _ => by simp [isPath]
  | e, [x], w, _, hl => by
    have hxw := hl x rfl
    simp [isPath, hxw]
  | e, a :: b :: r, w, h, hl => by
    have hpair := isPath_cons e a b r h
    have hl2 : ∀ v, (b :: r).getLast? = some v → (v, w) ∈ e := by
      intro v hv
      have heq : (a :: b :: r).getLast? = (b :: r).getLast? := rfl
      exact hl v (by rw [heq]; exact hv)
    have ih := isPath_append_single e (b :: r) w hpair.2 hl2
    show isPath (a :: b :: (r ++ [w])) e = true
    simp only [isPath, hpair.1, if_true]
    exact ih

/-- Every nonempty path has a last node. -/
theorem exists_last : ∀ (l : List Nat), l ≠ [] → ∃ v, l.getLast? = some v
  | [], h => absurd rfl h
  | [x], _ => ⟨x, rfl⟩
  | _ :: y :: ys, _ => exists_last (y :: ys) (by simp)

/-- Avoidance distributes over append. -/
theorem avoids_append : ∀ (l₁ l₂ bad : List Nat),
    avoids (l₁ ++ l₂) bad = true ↔ avoids l₁ bad = true ∧ avoids l₂ bad = true
  | [], _, _ => by simp [avoids]
  | x :: xs, l₂, bad => by
    have ih := avoids_append xs l₂ bad
    by_cases hx : x ∈ bad
    · have hd : decide (x ∈ bad) = true := by simpa using hx
      simp [avoids, hd]
    · have hd : decide (x ∈ bad) = false := by simpa using hx
      simp only [avoids, hd, reduceCtorEq, if_false, List.cons_append]
      exact ih

/-- Expansion preserves the frontier invariant. -/
theorem expand_sound : ∀ (e : List (Nat × Nat)) (bad : List Nat)
    (p0 : List Nat) (s : Nat) (p : List Nat), p ∈ expand e bad p0 →
    p0.head? = some s ∧ isPath p0 e = true ∧ avoids p0 bad = true →
    p.head? = some s ∧ isPath p e = true ∧ avoids p bad = true := by
  intro e bad p0 s p hmem hi0
  cases p0 with
  | nil => simp [expand] at hmem
  | cons x xs =>
    obtain ⟨u, hu⟩ := exists_last (x :: xs) (by simp)
    simp only [expand, hu] at hmem
    simp only [List.mem_map, List.mem_filter] at hmem
    obtain ⟨w, hmemW, hpw⟩ := hmem
    obtain ⟨hW, hWc⟩ := hmemW
    have hWbad := (of_decide_eq_true hWc).1
    have hedge := mem_neighbors e u w hW
    have hsx : x = s := by simpa using hi0.1
    have hhead : p.head? = some s := by
      rw [← hpw]
      simp [hsx]
    have hpath : isPath p e = true := by
      rw [← hpw]
      exact isPath_append_single e (x :: xs) w hi0.2.1 (fun v hv2 => by
        have hvv : v = u := Option.some.inj (hv2.symm.trans hu)
        rw [hvv]
        exact hedge)
    have havo : avoids p bad = true := by
      rw [← hpw, avoids_append]
      refine ⟨hi0.2.2, ?_⟩
      simp only [avoids]
      have hd : decide (w ∈ bad) = false := by simpa using hWbad
      simp only [hd, reduceCtorEq, if_false]
    exact ⟨hhead, hpath, havo⟩

/-- Every expanded path reaching `dst` off the locus is admissible. -/
theorem findGood_some : ∀ (front : List (List Nat)) (bad : List Nat)
    (dst : Nat) (q : List Nat), findGood front bad dst = some q →
    q ∈ front ∧ q.getLast? = some dst ∧ avoids q bad = true
  | [], _, _, _, h => by simp [findGood] at h
  | f :: fs, bad, dst, q, h => by
    simp only [findGood] at h
    by_cases hc : (decide (f.getLast? = some dst) && avoids f bad) = true
    · simp only [hc, if_true] at h
      rw [Bool.and_eq_true] at hc
      obtain ⟨h1, h2⟩ := hc
      cases h
      exact ⟨List.mem_cons.mpr (Or.inl rfl), of_decide_eq_true h1, h2⟩
    · simp only [hc, reduceCtorEq, if_false] at h
      have ih := findGood_some fs bad dst q h
      exact ⟨List.mem_cons.mpr (Or.inr ih.1), ih.2.1, ih.2.2⟩

/-- Single-source frontier paths satisfy the invariant. -/
theorem bfs_single_inv : ∀ (e : List (Nat × Nat)) (bad : List Nat) (s : Nat),
    s ∉ bad → ∀ r ∈ [[s]],
    r.head? = some s ∧ isPath r e = true ∧ avoids r bad = true := by
  intro e bad s hs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  have hd : decide (s ∈ bad) = false := by simpa using hs
  refine ⟨rfl, by simp [isPath], by simp [avoids, hd]⟩

/-- BFS only returns admissible paths with the right endpoints. -/
theorem bfs_sound : ∀ (fuel : Nat) (front : List (List Nat))
    (e : List (Nat × Nat)) (bad : List Nat) (s dst : Nat),
    (∀ p ∈ front, p.head? = some s ∧ isPath p e = true ∧ avoids p bad = true) →
    ∀ (q : List Nat), bfs front e bad dst fuel = some q →
    q.head? = some s ∧ isPath q e = true ∧ avoids q bad = true ∧
      q.getLast? = some dst
  | 0, front, e, bad, s, dst, hinv, q, h => by
    simp only [bfs] at h
    have hm := findGood_some front bad dst q h
    have hi := hinv q hm.1
    exact ⟨hi.1, hi.2.1, hm.2.2, hm.2.1⟩
  | n + 1, front, e, bad, s, dst, hinv, q, h => by
    simp only [bfs] at h
    by_cases hfg : findGood front bad dst = none
    · simp only [hfg] at h
      have hinv2 : ∀ p ∈ front.flatMap (expand e bad),
          p.head? = some s ∧ isPath p e = true ∧ avoids p bad = true := by
        intro p hp
        rw [List.mem_flatMap] at hp
        obtain ⟨p0, hp0, hpm⟩ := hp
        have hi0 := hinv p0 hp0
        exact expand_sound e bad p0 s p hpm hi0
      exact bfs_sound n _ e bad s dst hinv2 q h
    · have hs : ∃ r, findGood front bad dst = some r :=
        Option.ne_none_iff_exists'.mp hfg
      obtain ⟨r, hr⟩ := hs
      simp only [hr] at h
      have hrq : r = q := by cases h; rfl
      subst hrq
      have hm := findGood_some front bad dst r hr
      have hi := hinv r hm.1
      exact ⟨hi.1, hi.2.1, hm.2.2, hm.2.1⟩

/-- Deformation only returns admissible paths. -/
theorem deform_sound : ∀ (p : List Nat) (e : List (Nat × Nat)) (bad : List Nat)
    (q : List Nat), deform p e bad = some q → checkPath q e bad = true := by
  intro p e bad q h
  cases hs : p.head? with
  | none => simp [deform, hs] at h
  | some s =>
    cases hd : p.getLast? with
    | none => simp [deform, hs, hd] at h
    | some d =>
      simp only [deform, hs, hd] at h
      by_cases hc : checkPath p e bad = true
      · simp only [hc, if_true] at h
        cases h
        exact hc
      · simp only [hc, reduceCtorEq, if_false] at h
        by_cases hsb : s ∈ bad
        · have hd2 : decide (s ∈ bad) = true := by simpa using hsb
          simp only [hd2, if_true] at h
          cases h
        · have hd2 : decide (s ∈ bad) = false := by simpa using hsb
          simp only [hd2, reduceCtorEq, if_false] at h
          have hinv := bfs_single_inv e bad s hsb
          have hb := bfs_sound (e.length + 1) [[s]] e bad s d hinv q h
          simp [checkPath, hb.2.1, hb.2.2.1]

/-- Deformation preserves both endpoints. -/
theorem deform_ends : ∀ (p : List Nat) (e : List (Nat × Nat)) (bad : List Nat)
    (q : List Nat), deform p e bad = some q →
    q.head? = p.head? ∧ q.getLast? = p.getLast? := by
  intro p e bad q h
  cases hs : p.head? with
  | none => simp [deform, hs] at h
  | some s =>
    cases hd : p.getLast? with
    | none => simp [deform, hs, hd] at h
    | some d =>
      simp only [deform, hs, hd] at h
      by_cases hc : checkPath p e bad = true
      · simp only [hc, if_true] at h
        cases h
        exact ⟨hs, hd⟩
      · simp only [hc, reduceCtorEq, if_false] at h
        by_cases hsb : s ∈ bad
        · have hd2 : decide (s ∈ bad) = true := by simpa using hsb
          simp only [hd2, if_true] at h
          cases h
        · have hd2 : decide (s ∈ bad) = false := by simpa using hsb
          simp only [hd2, reduceCtorEq, if_false] at h
          have hinv := bfs_single_inv e bad s hsb
          have hb := bfs_sound (e.length + 1) [[s]] e bad s d hinv q h
          exact ⟨hb.1, hb.2.2.2⟩

/-! ## E-44: failover invents nothing and keeps the newest -/

/-- Upsert only inserts the entry or keeps old ones. -/
theorem mem_upsert : ∀ (e y : Entry) (acc : List Entry),
    y ∈ upsert e acc → y = e ∨ y ∈ acc
  | _, _, [] => by simp [upsert]
  | e, y, x :: xs => by
    by_cases hke : (x.key == e.key) = true
    · by_cases hver : e.ver ≤ x.ver
      · simp only [upsert, hke, hver, if_true]
        intro hy
        rcases List.mem_cons.mp hy with rfl | hm
        · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · exact Or.inr (List.mem_cons.mpr (Or.inr hm))
      · simp only [upsert, hke, hver, if_true, if_false]
        intro hy
        rcases List.mem_cons.mp hy with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons.mpr (Or.inr hm))
    · have ih := mem_upsert e y xs
      simp only [upsert, hke, reduceCtorEq, if_false]
      intro hy
      rcases List.mem_cons.mp hy with rfl | hm
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · rcases ih hm with rfl | hm2
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons.mpr (Or.inr hm2))

/-- Folding upserts draws only from the input or the accumulator. -/
theorem mem_fold : ∀ (l acc : List Entry) (y : Entry),
    y ∈ l.foldl (fun a e => upsert e a) acc → y ∈ acc ∨ y ∈ l
  | [], _, _ => by exact fun h => Or.inl h
  | x :: xs, acc, y => by
    intro h
    simp only [List.foldl] at h
    have ih := mem_fold xs (upsert x acc) y h
    rcases ih with ha | hl
    · have hm := mem_upsert x y acc ha
      rcases hm with rfl | hm2
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · exact Or.inl hm2
    · exact Or.inr (List.mem_cons.mpr (Or.inr hl))

/-- Reconciliation invents no entries. -/
theorem mem_reconcile : ∀ (p s : List Entry) (y : Entry),
    y ∈ reconcile p s → y ∈ p ∨ y ∈ s := by
  intro p s y h
  simp only [reconcile] at h
  have hm := mem_fold (p ++ s) [] y h
  simpa using hm

/-- Hitting lookup pushes the upsert through. -/
theorem findK_upsert_hit : ∀ (e : Entry) (acc : List Entry) (k : Nat),
    e.key = k → findK k (upsert e acc) = best e (findK k acc)
  | e, [], k, h => by simp [upsert, findK, best, h]
  | e, x :: xs, k, h => by
    by_cases hke : (x.key == e.key) = true
    · have hx : x.key = e.key := beq_iff_eq.mp hke
      have hxk : (x.key == k) = true := by rw [hx, h]; exact beq_self_eq_true k
      have hek : (e.key == k) = true := by rw [h]; exact beq_self_eq_true k
      by_cases hver : e.ver ≤ x.ver
      · simp only [upsert, hke, findK, hxk, best, hver, if_true]
      · simp only [upsert, hke, findK, hek, hxk, best, hver, if_true, if_false]
    · have ih := findK_upsert_hit e xs k h
      by_cases hxk : (x.key == k) = true
      · have hxx : x.key = e.key := by
          have a1 := beq_iff_eq.mp hxk
          rw [a1, h]
        have hcon : (x.key == e.key) = true := by
          rw [hxx]
          exact beq_self_eq_true _
        exact absurd hcon hke
      · simp only [upsert, hke, reduceCtorEq, if_false, findK, hxk,
          reduceCtorEq, if_false]
        exact ih

/-- Missing lookup passes through the upsert. -/
theorem findK_upsert_miss : ∀ (e : Entry) (acc : List Entry) (k : Nat),
    e.key ≠ k → findK k (upsert e acc) = findK k acc
  | e, [], k, h => by simp [upsert, findK, h]
  | e, x :: xs, k, h => by
    by_cases hke : (x.key == e.key) = true
    · have hx : x.key = e.key := beq_iff_eq.mp hke
      have hxk : (x.key == k) = false := by
        have hne : x.key ≠ k := by rw [hx]; exact h
        simpa using hne
      have hem : (e.key == k) = false := by
        cases he : (e.key == k) with
        | true => exact absurd (beq_iff_eq.mp he) h
        | false => rfl
      by_cases hver : e.ver ≤ x.ver
      · simp only [upsert, hke, findK, hxk, hver, reduceCtorEq, if_true,
          if_false]
      · simp only [upsert, hke, findK, hem, hxk, hver, reduceCtorEq, if_true,
          if_false]
    · have ih := findK_upsert_miss e xs k h
      by_cases hxk : (x.key == k) = true
      · simp only [upsert, hke, reduceCtorEq, if_false, findK, hxk, if_true]
      · simp only [upsert, hke, reduceCtorEq, if_false, findK, hxk,
          reduceCtorEq, if_false]
        exact ih

/-- Lookup folds to the pointwise max over the doubled state. -/
theorem findK_fold : ∀ (l acc : List Entry) (k : Nat),
    findK k (l.foldl (fun a e => upsert e a) acc) =
    l.foldl (fun o e => if e.key == k then best e o else o) (findK k acc)
  | [], _, _ => by simp
  | x :: xs, acc, k => by
    simp only [List.foldl]
    by_cases hxk : (x.key == k) = true
    · have hx : x.key = k := beq_iff_eq.mp hxk
      have hstep : best x (findK k acc) = findK k (upsert x acc) :=
        (findK_upsert_hit x acc k hx).symm
      simp only [hxk, if_true, hstep]
      exact findK_fold xs (upsert x acc) k
    · have hne : x.key ≠ k := by
        intro hc
        have hc2 : (x.key == k) = true := by
          rw [hc]
          exact beq_self_eq_true k
        exact hxk hc2
      have hstep : findK k (upsert x acc) = findK k acc :=
        findK_upsert_miss x acc k hne
      simp only [hxk, reduceCtorEq, if_false]
      rw [← hstep]
      exact findK_fold xs (upsert x acc) k

/-- Failover reads the max version of each key. -/
theorem findK_reconcile : ∀ (p s : List Entry) (k : Nat),
    findK k (reconcile p s) =
    (p ++ s).foldl (fun o e => if e.key == k then best e o else o) none := by
  intro p s k
  have h := findK_fold (p ++ s) [] k
  simp only [findK] at h
  simp only [reconcile]
  exact h

/-- Repeating an upsert is stable. -/
theorem upsert_idem : ∀ (e : Entry) (acc : List Entry),
    upsert e (upsert e acc) = upsert e acc
  | _, [] => by simp [upsert]
  | e, x :: xs => by
    by_cases hke : (x.key == e.key) = true
    · by_cases hver : e.ver ≤ x.ver
      · simp [upsert, hke, hver]
      · simp [upsert, hke, hver]
    · have ih := upsert_idem e xs
      simp only [upsert, hke, reduceCtorEq, if_false, ih]

/-! ## E-45: scattering inverts exactly and splits energy -/

/-- Masks and filters rebuild the signal. -/
theorem recon_roundtrip : ∀ (sig : List Int) (t : Nat),
    reconstruct (sig.map (isBound t)) (sig.filter (isBound t))
      (sig.filter fun x => !(isBound t x)) = sig
  | [], _ => by simp [reconstruct]
  | x :: xs, t => by
    have ih := recon_roundtrip xs t
    by_cases hb : (isBound t x) = true
    · simp only [List.map_cons, List.filter_cons, hb, Bool.not_true,
        reduceCtorEq, if_true, if_false, reconstruct, ih]
    · simp only [List.map_cons, List.filter_cons, hb, Bool.not_false,
        reduceCtorEq, if_true, if_false, reconstruct, ih]

/-- Energy splits across bound states and radiation. -/
theorem scatter_parseval : ∀ (sig : List Int) (t : Nat),
    sumsq (sig.filter (isBound t)) +
      sumsq (sig.filter fun x => !(isBound t x)) = sumsq sig
  | [], _ => by simp [sumsq]
  | x :: xs, t => by
    have ih := scatter_parseval xs t
    by_cases hb : (isBound t x) = true
    · simp only [List.filter_cons, hb, Bool.not_true, reduceCtorEq, if_true,
        if_false, sumsq]
      omega
    · simp only [List.filter_cons, hb, Bool.not_false, reduceCtorEq, if_true,
        if_false, sumsq]
      omega

/-- Scattering preserves sample count. -/
theorem scatter_lengths : ∀ (sig : List Int) (t : Nat),
    (sig.filter (isBound t)).length +
      (sig.filter fun x => !(isBound t x)).length = sig.length
  | [], _ => by simp
  | x :: xs, t => by
    have ih := scatter_lengths xs t
    by_cases hb : (isBound t x) = true
    · simp only [List.filter_cons, hb, Bool.not_true, reduceCtorEq, if_true,
        if_false, List.length_cons]
      omega
    · simp only [List.filter_cons, hb, Bool.not_false, reduceCtorEq, if_true,
        if_false, List.length_cons]
      omega

/-! ## E-46: the truncated product is order-explicit -/

/-- The bracket is antisymmetric. -/
theorem bracket_antisym : ∀ (a b : Int), bracket a b = -bracket b a := by
  intro a b
  simp only [bracket]
  omega

/-- One row of the correction table. -/
theorem cross_single : ∀ (l : List Int) (x : Int),
    cross l [x] = lsumI (l.map fun y => bracket y x)
  | [], _ => by simp [cross, lsumI]
  | y :: ys, x => by
    have ih := cross_single ys x
    simp only [cross, List.map_cons, List.map_nil, lsumI, ih]
    omega

/-- Corrections distribute over a split window. -/
theorem cross_second : ∀ (l : List Int) (y : Int) (ys : List Int),
    cross l (y :: ys) = lsumI (l.map fun x => bracket x y) + cross l ys
  | [], _, _ => by simp [cross, lsumI]
  | x :: xs, y, ys => by
    have ih := cross_second xs y ys
    simp only [cross, ih, List.map_cons, lsumI]
    omega

/-- Flipping a row negates it. -/
theorem lsumI_bracket_flip : ∀ (l : List Int) (x : Int),
    lsumI (l.map fun y => bracket y x) = -lsumI (l.map (bracket x))
  | [], _ => by simp [lsumI]
  | y :: ys, x => by
    have ih := lsumI_bracket_flip ys x
    have ha := bracket_antisym y x
    simp only [List.map_cons, lsumI]
    omega

/-- Corrections against the empty window vanish. -/
theorem cross_nil_r : ∀ (l : List Int), cross l [] = 0
  | [] => by simp [cross]
  | x :: xs => by
    have ih := cross_nil_r xs
    simp [cross, List.map_nil, lsumI, ih]

/-- Swapping the windows negates the correction. -/
theorem cross_sym : ∀ (l₁ l₂ : List Int), cross l₁ l₂ = -cross l₂ l₁
  | [], l₂ => by simp [cross, cross_nil_r l₂]
  | x :: xs, l₂ => by
    have ih := cross_sym xs l₂
    have hs := cross_single l₂ x
    have hf := lsumI_bracket_flip l₂ x
    have hc := cross_second l₂ x xs
    simp only [cross]
    omega

/-- Integer sums distribute over append. -/
theorem lsumI_append : ∀ (a b : List Int), lsumI (a ++ b) = lsumI a + lsumI b
  | [], _ => by simp [lsumI]
  | x :: xs, b => by
    have ih := lsumI_append xs b
    simp only [List.cons_append, lsumI]
    omega

/-- Corrections concatenate with the cross term. -/
theorem corr_append : ∀ (l₁ l₂ : List Int),
    corr (l₁ ++ l₂) = corr l₁ + corr l₂ + cross l₁ l₂
  | [], _ => by simp [corr, cross]
  | x :: xs, l₂ => by
    have ih := corr_append xs l₂
    simp only [corr, List.cons_append, cross, List.map_append, lsumI_append,
      ih]
    omega

/-- Reversal commutes with summation. -/
theorem lsumI_reverse : ∀ (l : List Int), lsumI l.reverse = lsumI l
  | [] => by simp [lsumI]
  | x :: xs => by
    have ih := lsumI_reverse xs
    have ha := lsumI_append xs.reverse [x]
    have hr : (x :: xs).reverse = xs.reverse ++ [x] := by simp
    simp only [hr, ha, lsumI]
    omega

/-- Mapping then summing commutes with reversal. -/
theorem lsumI_map_reverse : ∀ (l : List Int) (f : Int → Int),
    lsumI (l.reverse.map f) = lsumI (l.map f)
  | [], _ => by simp [lsumI]
  | x :: xs, f => by
    have ih := lsumI_map_reverse xs f
    have hr : (x :: xs).reverse = xs.reverse ++ [x] := by simp
    simp only [hr, List.map_append, lsumI_append, List.map_cons, List.map_nil,
      lsumI, ih]
    omega

/-- Reversal negates the correction. -/
theorem corr_rev : ∀ (l : List Int), corr l.reverse = -corr l
  | [] => by simp [corr]
  | x :: xs => by
    have ih := corr_rev xs
    have ha := corr_append xs.reverse [x]
    have hs := cross_single xs.reverse x
    have hf := lsumI_bracket_flip xs.reverse x
    have hmap := lsumI_map_reverse xs (bracket x)
    have h1 : corr [x] = 0 := by simp [corr, lsumI]
    have h2 : corr (x :: xs) = lsumI (xs.map (bracket x)) + corr xs := by
      simp [corr]
    have hr : (x :: xs).reverse = xs.reverse ++ [x] := by simp
    rw [hr, ha, h1, hs, hf, hmap, h2]
    omega

/-- Reversing the window reflects the product around the classical sum. -/
theorem star_reverse : ∀ (ops : List Int),
    star ops.reverse = 2 * lsumI ops - star ops := by
  intro ops
  have hc := corr_rev ops
  have hl := lsumI_reverse ops
  simp only [star]
  omega

/-- Zero corrections sum to zero. -/
theorem lsumI_map_zero : ∀ (l : List Int) (f : Int → Int),
    (∀ y ∈ l, f y = 0) → lsumI (l.map f) = 0
  | [], _, _ => by simp [lsumI]
  | y :: ys, f, h => by
    have ih := lsumI_map_zero ys f
      (fun z hz => h z (List.mem_cons.mpr (Or.inr hz)))
    have hy := h y (List.mem_cons.mpr (Or.inl rfl))
    simp only [List.map_cons, lsumI, hy, ih]
    omega

/-- Vanishing brackets kill the correction. -/
theorem corr_zero : ∀ (ops : List Int),
    (∀ a ∈ ops, ∀ b ∈ ops, bracket a b = 0) → corr ops = 0
  | [], _ => by simp [corr]
  | x :: xs, h => by
    have ih := corr_zero xs (fun a ha b hb =>
      h a (List.mem_cons.mpr (Or.inr ha)) b (List.mem_cons.mpr (Or.inr hb)))
    have hsum := lsumI_map_zero xs (bracket x) (fun y hy =>
      h x (List.mem_cons.mpr (Or.inl rfl)) y (List.mem_cons.mpr (Or.inr hy)))
    simp only [corr, hsum, ih]
    omega

/-- The classical limit: no brackets, no correction. -/
theorem star_classical : ∀ (ops : List Int),
    (∀ a ∈ ops, ∀ b ∈ ops, bracket a b = 0) → star ops = lsumI ops := by
  intro ops h
  have hz := corr_zero ops h
  simp [star, hz]

/-! ## E-47: spacelike and timelike never coincide -/

/-- Every operator gets a verdict. -/
theorem classify_total : ∀ (m : EvOp) (g : Nat),
    classify m g = .space ∨ classify m g = .time ∨ classify m g = .light := by
  intro m g
  by_cases h1 : disc m < 0
  · have hc : classify m g = .space := by simp [classify, h1]
    exact Or.inl hc
  · by_cases h2 : (g : Int) ≤ disc m
    · have hc : classify m g = .time := by simp [classify, h1, h2]
      exact Or.inr (Or.inl hc)
    · have hc : classify m g = .light := by simp [classify, h1, h2]
      exact Or.inr (Or.inr hc)

/-- Spacelike excludes timelike. -/
theorem space_not_time : ∀ (m : EvOp) (g : Nat),
    classify m g = .space → classify m g ≠ .time := by
  intro m g h
  rw [h]
  decide

/-- Small non-negative discriminant is lightlike. -/
theorem light_of_small : ∀ (m : EvOp) (g : Nat),
    0 ≤ disc m → disc m < (g : Int) → classify m g = .light := by
  intro m g h0 hg
  simp only [classify]
  by_cases h1 : disc m < 0
  · omega
  · simp only [h1, if_false]
    by_cases h2 : (g : Int) ≤ disc m
    · omega
    · simp only [h2, if_false]

/-- Spacelike events skip the fence. -/
theorem space_fenceless : ∀ (m : EvOp) (g : Nat),
    classify m g = .space → needsFence (classify m g) = false := by
  intro m g h
  simp [h, needsFence]

end Morph.Specs.BatchDEF
