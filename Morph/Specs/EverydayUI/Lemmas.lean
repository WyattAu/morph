/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.EverydayUI.Spec

/-!
# Everyday UI Kernel — lemmas (E-1351–E-1360)

Status: In Progress (loop 103).

Proofs for the ten computable cores in `Spec.lean`. Every theorem here is
about the *model*, not about a browser: the register rows are graded L1/L2
until a benchmark against the baselines named in ADR-030 is run.
-/

namespace Morph.Specs.EverydayUI

/-! ## Shared geometry -/

theorem Rect.disjoint_symm {a b : Rect} (h : a.disjoint b) : b.disjoint a := by
  unfold Rect.disjoint Rect.right at *
  rcases h with h | h | h | h <;> omega

theorem Rect.contains_refl (a : Rect) : a.contains a := by
  unfold Rect.contains Rect.right Rect.bottom
  omega

theorem Rect.contains_trans {a b c : Rect} (hab : a.contains b) (hbc : b.contains c) :
    a.contains c := by
  unfold Rect.contains Rect.right Rect.bottom at *
  obtain ⟨h1, h2, h3, h4⟩ := hab
  obtain ⟨g1, g2, g3, g4⟩ := hbc
  omega

/-! ## E-1354: row layout -/

theorem rowBoxes_length (ws : List Nat) (x : Nat) :
    (rowBoxes ws x).length = ws.length := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih => simp [rowBoxes, ih]

/-- Layout preserves every intrinsic width, in order. -/
theorem rowBoxes_widths (ws : List Nat) (x : Nat) :
    (rowBoxes ws x).map Prod.snd = ws := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih => simp [rowBoxes, ih]

/-- Every laid-out box starts at or after the row origin. -/
theorem rowBoxes_start_ge (ws : List Nat) (x : Nat) :
    ∀ b ∈ rowBoxes ws x, x ≤ b.1 := by
  induction ws generalizing x with
  | nil => intro b hb; simp [rowBoxes] at hb
  | cons w ws ih =>
      intro b hb
      simp only [rowBoxes, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact Nat.le_refl x
      · exact Nat.le_trans (Nat.le_add_right x w) (ih (x + w) b hb)

/-- **Single-pass confinement.** Every box of a row lies in the parent span:
the affine fragment's restriction maps never escape the section. -/
theorem rowBoxes_confined (ws : List Nat) (x : Nat) :
    Confined (rowBoxes ws x) x ws.sum := by
  intro b hb
  induction ws generalizing x with
  | nil => simp [rowBoxes] at hb
  | cons w ws ih =>
      simp only [rowBoxes, List.mem_cons] at hb
      rcases hb with rfl | hb
      · refine ⟨Nat.le_refl x, ?_⟩
        simp only [List.sum_cons]
        omega
      · obtain ⟨h1, h2⟩ := ih (x + w) hb
        refine ⟨Nat.le_trans (Nat.le_add_right x w) h1, ?_⟩
        simp only [List.sum_cons]
        omega

/-- **No overlap.** Earlier boxes end before later boxes begin. -/
theorem rowBoxes_pairwise (ws : List Nat) (x : Nat) :
    (rowBoxes ws x).Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  induction ws generalizing x with
  | nil => simp [rowBoxes]
  | cons w ws ih =>
      simp only [rowBoxes]
      refine List.Pairwise.cons ?_ (ih (x + w))
      intro b hb
      exact rowBoxes_start_ge ws (x + w) b hb

/-- The offset invariant lifts to geometry: rendered row rectangles are
pairwise disjoint. This is the form in which E-1354's no-overlap claim is
observable (rectangles, not offsets). -/
theorem rowRects_disjoint (ws : List Nat) (x y h : Nat) :
    (rowRects ws x y h).Pairwise Rect.disjoint := by
  unfold rowRects
  refine List.Pairwise.map (f := fun b => (⟨b.1, y, b.2, h⟩ : Rect)) ?_
    (rowBoxes_pairwise ws x)
  intro a b hab
  unfold Rect.disjoint Rect.right Rect.bottom
  exact Or.inl hab

/-- **Translation invariance.** Laying a row out at `x + y` is the layout at
`x` shifted by `y` — the affine, no-backtracking property. -/
theorem rowBoxes_translate (ws : List Nat) (x y : Nat) :
    rowBoxes ws (x + y) = (rowBoxes ws x).map (fun b => (b.1 + y, b.2)) := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
      simp only [rowBoxes, List.map_cons]
      have h : x + y + w = x + w + y := by omega
      rw [h, ih (x + w)]

/-! ## E-1351: coverage (the sheaf/gluing condition, 1-D) -/

/-- **Row coverage.** Every point of the parent span lies in some child box:
the sections of a row cover the parent, so local layout facts glue. -/
theorem rowBoxes_covered (ws : List Nat) (x p : Nat)
    (hx : x ≤ p) (hp : p < x + ws.sum) : Covered (rowBoxes ws x) p := by
  induction ws generalizing x with
  | nil =>
      simp only [List.sum_nil, Nat.add_zero] at hp
      omega
  | cons w ws ih =>
      by_cases hw : p < x + w
      · exact ⟨(x, w), by simp [rowBoxes], hx, hw⟩
      · have hw' : x + w ≤ p := Nat.le_of_not_lt hw
        have hp' : p < (x + w) + ws.sum := by
          simp only [List.sum_cons] at hp
          omega
        obtain ⟨b, hb, h1, h2⟩ := ih (x + w) hw' hp'
        exact ⟨b, by simp [rowBoxes, hb], h1, h2⟩

/-! ## E-1352: Kleene stabilisation -/

theorem iterate_succ (f : Nat → Nat) (n : Nat) : iterate f (n + 1) = f (iterate f n) := rfl

/-- Iterates never exceed the pass height. -/
theorem iterate_bounded (f : Nat → Nat) (N : Nat)
    (hbound : ∀ a, a ≤ N → f a ≤ N) : ∀ k, iterate f k ≤ N := by
  intro k
  induction k with
  | zero => exact Nat.zero_le N
  | succ k ih =>
      show f (iterate f k) ≤ N
      exact hbound _ ih

theorem iterate_le_succ (f : Nat → Nat) (N : Nat)
    (hext : ∀ a, a ≤ N → a ≤ f a) (hbound : ∀ a, a ≤ N → f a ≤ N) :
    ∀ k, iterate f k ≤ iterate f (k + 1) := by
  intro k
  have hk : iterate f k ≤ N := iterate_bounded f N hbound k
  show iterate f k ≤ f (iterate f k)
  exact hext _ hk

theorem iterate_mono (f : Nat → Nat) (N : Nat)
    (hext : ∀ a, a ≤ N → a ≤ f a)
    (hbound : ∀ a, a ≤ N → f a ≤ N) :
    ∀ m n, m ≤ n → iterate f m ≤ iterate f n := by
  intro m n h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (iterate_le_succ f N hext hbound _)

/-- Once an iterate is fixed, every later iterate has the same value. -/
theorem iterate_eq_of_fixed (f : Nat → Nat) (n : Nat)
    (h : iterate f (n + 1) = iterate f n) :
    ∀ j, n ≤ j → iterate f j = iterate f n := by
  intro j hj
  induction hj with
  | refl => rfl
  | step _ ih =>
      rw [iterate_succ, ih]
      exact h

/-- **Kleene stabilisation.** An extensive endomap of the finite segment
`0 … N` reaches a fixed point within `N` iterations. Monotonicity is *not*
needed for stabilisation here (the iterate is increasing and bounded, so it
must stop), which is why the lemma states the stronger result; `UpdatePass.mono`
remains a modelling constraint for future commutation lemmas. -/
theorem kleene_stabilizes (f : Nat → Nat) (N : Nat)
    (hext : ∀ a, a ≤ N → a ≤ f a)
    (hbound : ∀ a, a ≤ N → f a ≤ N) :
    f (iterate f N) = iterate f N := by
  apply Classical.byContradiction
  intro hne
  have hstep : iterate f (N + 1) = f (iterate f N) := iterate_succ f N
  have hlt : iterate f N < iterate f (N + 1) := by
    have hle := iterate_le_succ f N hext hbound N
    have hne' : iterate f N ≠ iterate f (N + 1) := by
      intro h
      apply hne
      rw [← hstep]
      exact h.symm
    omega
  have hstrict : ∀ k, k ≤ N → iterate f k < iterate f (k + 1) := by
    intro k hk
    apply Classical.byContradiction
    intro hge
    have hle : iterate f (k + 1) ≤ iterate f k := Nat.le_of_not_lt hge
    have heq : iterate f (k + 1) = iterate f k :=
      Nat.le_antisymm hle (iterate_le_succ f N hext hbound k)
    have hN : iterate f N = iterate f k := iterate_eq_of_fixed f k heq N hk
    have hN1 : iterate f (N + 1) = iterate f k :=
      iterate_eq_of_fixed f k heq (N + 1) (by omega)
    omega
  have hchain : ∀ k, k ≤ N → k ≤ iterate f k := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
        intro hk
        have h1 := hstrict k (by omega)
        have h2 := ih (by omega)
        omega
  have hNge : N ≤ iterate f N := hchain N (Nat.le_refl N)
  have hNbound : iterate f (N + 1) ≤ N := by
    rw [hstep]
    exact hbound _ (iterate_bounded f N hbound N)
  omega

/-- The same result stated for an abstract `UpdatePass`. -/
theorem UpdatePass.stabilizes (p : UpdatePass) :
    p.step (iterate p.step p.height) = iterate p.step p.height :=
  kleene_stabilizes p.step p.height p.extensive p.bounded

/-! ## E-1353: lens composition -/

/-- **Lawful lenses compose.** The three lens laws are preserved by
composition, so a field path assembled from lawful accessors is lawful. -/
theorem Lens.lawful_comp {S A B : Type} (l₁ : Lens S A) (l₂ : Lens A B)
    (h₁ : Lawful l₁) (h₂ : Lawful l₂) : Lawful (l₁.comp l₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s b
    simp [Lens.comp, h₁.putGet, h₂.putGet]
  · intro s
    simp [Lens.comp, h₂.getPut, h₁.getPut]
  · intro s a b
    simp [Lens.comp, h₁.putPut, h₁.putGet, h₂.putPut]

/-! ## E-1355: routing soundness -/

/-- **Routing soundness.** A routed event lands in a subtree that actually
contains its target, so it cannot be delivered to a non-containing sibling. -/
theorem BTree.route_sound : ∀ (t : BTree) (target : Nat) (z : BTree),
    t.route target = some z → target ∈ z.ids := by
  intro t
  induction t with
  | empty =>
      intro target z h
      simp [BTree.route] at h
  | leaf i =>
      intro target z h
      simp only [BTree.route] at h
      split at h
      · rename_i heq
        have hz : z = .leaf i := (Option.some.inj h).symm
        rw [hz]
        simp [BTree.ids, heq]
      · simp at h
  | node i l r ihl ihr =>
      intro target z h
      simp only [BTree.route] at h
      split at h
      · rename_i heq
        have hz : z = .node i l r := (Option.some.inj h).symm
        rw [hz]
        simp [BTree.ids, heq]
      · cases hl : l.route target with
        | some z' =>
            simp only [hl, Option.orElse] at h
            have hz : z = z' := (Option.some.inj h).symm
            rw [hz]
            exact ihl target z' hl
        | none =>
            simp only [hl, Option.orElse] at h
            exact ihr target z h

/-- Routing is total on every non-empty node. -/
theorem BTree.route_self (t : BTree) (h : t ≠ .empty) : t.route t.id = some t := by
  cases t with
  | empty => exact absurd rfl h
  | leaf i => simp [BTree.route, BTree.id]
  | node i l r => simp [BTree.route, BTree.id]

/-! ## E-1356: compiled continuations -/

/-- Resumption is compositional in the instruction sequence. -/
theorem run_append : ∀ (is js : List Instr) (st st' : List Nat),
    run is st = some st' → run (is ++ js) st = run js st' := by
  intro is
  induction is with
  | nil =>
      intro js st st' h
      simp only [List.nil_append, run] at h ⊢
      rw [Option.some.inj h]
  | cons i is ih =>
      intro js st st' h
      cases i with
      | push n =>
          simp only [run] at h ⊢
          exact ih js _ _ h
      | iadd =>
          cases st with
          | nil => simp [run] at h
          | cons a st1 =>
              cases st1 with
              | nil => simp [run] at h
              | cons b st2 =>
                  simp only [run] at h ⊢
                  exact ih js _ _ h
      | imul =>
          cases st with
          | nil => simp [run] at h
          | cons a st1 =>
              cases st1 with
              | nil => simp [run] at h
              | cons b st2 =>
                  simp only [run] at h ⊢
                  exact ih js _ _ h

/-- **Compilation correctness.** The compiled instruction sequence, resumed on
any stack, computes `eval` and leaves the rest of the stack untouched. This is
the formal kernel of "serialize the continuation, resume it on the client". -/
theorem run_compile (e : Expr) (st : List Nat) :
    run e.compile st = some (e.eval :: st) := by
  induction e generalizing st with
  | lit n => simp [Expr.compile, run, Expr.eval]
  | add a b iha ihb =>
      simp only [Expr.compile, List.append_assoc, Expr.eval]
      rw [run_append a.compile (b.compile ++ [Instr.iadd]) st (a.eval :: st) (iha st)]
      rw [run_append b.compile [Instr.iadd] (a.eval :: st) (b.eval :: a.eval :: st) (ihb _)]
      rfl
  | mul a b iha ihb =>
      simp only [Expr.compile, List.append_assoc, Expr.eval]
      rw [run_append a.compile (b.compile ++ [Instr.imul]) st (a.eval :: st) (iha st)]
      rw [run_append b.compile [Instr.imul] (a.eval :: st) (b.eval :: a.eval :: st) (ihb _)]
      rfl

/-- The compiled program evaluates to a singleton stack. -/
theorem run_compile_nil (e : Expr) : run e.compile [] = some [e.eval] := by
  simpa using run_compile e []

/-! ## E-1357: interpolation identities -/

theorem lerp_zero (a b : Nat) : lerp a b 0 = a := by
  simp only [lerp, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
  rw [Nat.mul_comm a 100]
  exact Nat.mul_div_right a (by decide : 0 < 100)

theorem lerp_hundred (a b : Nat) : lerp a b 100 = b := by
  simp only [lerp, Nat.sub_self, Nat.mul_zero, Nat.zero_add]
  rw [Nat.mul_comm b 100]
  exact Nat.mul_div_right b (by decide : 0 < 100)

/-- Blending equal endpoints changes nothing. -/
theorem lerp_const (a s : Nat) (h : s ≤ 100) : lerp a a s = a := by
  simp only [lerp]
  rw [← Nat.mul_add, Nat.sub_add_cancel h, Nat.mul_comm a 100]
  exact Nat.mul_div_right a (by decide : 0 < 100)

/-- Reversal symmetry: blending `a→b` at `s` is blending `b→a` at `100-s`. -/
theorem lerp_reverse (a b s : Nat) (h : s ≤ 100) :
    lerp a b s = lerp b a (100 - s) := by
  simp only [lerp]
  rw [Nat.sub_sub_self h]
  congr 1
  omega

/-! ## E-1358: affine usage -/

theorem Usage.linear_seq {a b : Usage} (h : (Usage.seq a b).Linear) :
    a.Linear ∧ b.Linear := by
  constructor
  · intro x
    have := h x
    simp only [Usage.handles, List.count_append] at this
    omega
  · intro x
    have := h x
    simp only [Usage.handles, List.count_append] at this
    omega

theorem Usage.linear_pure (v : Nat) : (Usage.pure v).Linear := by
  intro h
  simp [Usage.handles]

theorem Usage.linear_use (h : Nat) : (Usage.use h).Linear := by
  intro x
  simp only [Usage.handles, List.count_cons, List.count_nil]
  split <;> omega

/-- **Double use is rejected.** Two linear fragments that both use the same
handle do not compose: the composed expression is not linear. This is why
`Usage.Linear` is a whole-expression check, not a per-fragment one. -/
theorem double_use_rejected (h : Nat) : ¬ (Usage.seq (.use h) (.use h)).Linear := by
  intro hl
  have hc := hl h
  simp [Usage.handles] at hc

/-! ## E-1359: operadic substitution laws -/

theorem Op.composeAt_output (f : Op) (i : Nat) (g : Op) :
    (f.composeAt i g).output = f.output := rfl

/-- Substituting into an in-range slot changes the arity by `|g| - 1`. -/
theorem Op.composeAt_inputs_length (f : Op) (i : Nat) (g : Op)
    (h : i < f.inputs.length) :
    (f.composeAt i g).inputs.length = f.inputs.length - 1 + g.inputs.length := by
  have hmin : min i f.inputs.length = i := Nat.min_eq_left (Nat.le_of_lt h)
  show (f.inputs.take i ++ g.inputs ++ f.inputs.drop (i + 1)).length = _
  simp only [List.length_append, List.length_take, List.length_drop, hmin]
  omega

/-! ## E-1360: single-pass DAG evaluation -/

theorem foldl_ids (nodes : List DagNode) (acc : List (Nat × Nat)) :
    (nodes.foldl dagStep acc).map Prod.fst = acc.map Prod.fst ++ nodes.map DagNode.id := by
  induction nodes generalizing acc with
  | nil => simp
  | cons n ns ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [dagStep, List.map_append, List.append_assoc]

/-- **Single evaluation.** The pass emits exactly one value per node, in the
order the nodes are listed — no node twice, none skipped. -/
theorem evalDag_ids (nodes : List DagNode) :
    (evalDag nodes).map Prod.fst = nodes.map DagNode.id := by
  rw [evalDag, foldl_ids]
  simp

theorem evalDag_length (nodes : List DagNode) :
    (evalDag nodes).length = nodes.length := by
  have h := congrArg List.length (evalDag_ids nodes)
  rw [List.length_map, List.length_map] at h
  exact h

end Morph.Specs.EverydayUI
