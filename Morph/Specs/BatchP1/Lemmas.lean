/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP1.Spec

/-!
# Feasible-50 kernels — P1 lemmas

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms.
-/

namespace Morph.Specs.BatchP1

/-! ## E-104: the peephole rule is sound -/

/-- A positive zero test means evaluation at zero. -/
theorem isZero_eval (e : PExpr) (h : isZero e = true) : peval e = 0 := by
  cases e with
  | const n =>
    simp only [isZero, decide_eq_true_eq] at h
    simp [peval, h]
  | add a b => simp [isZero] at h

/-- The optimizer preserves evaluation. -/
theorem popt_sound : ∀ e : PExpr, peval (popt e) = peval e := by
  intro e
  induction e with
  | const n => rfl
  | add a b iha ihb =>
    cases hb : isZero b with
    | true =>
      simp [popt, hb, peval]
      have e2 := isZero_eval b hb
      omega
    | false =>
      cases ha : isZero a with
      | true =>
        simp [popt, hb, ha, peval]
        have e1 := isZero_eval a ha
        omega
      | false =>
        simp [popt, hb, ha, peval, iha, ihb]

/-- The validator accepts the optimizer output. -/
theorem validOpt_of_opt (e : PExpr) : validOpt e (popt e) = true := by
  simp only [validOpt, decide_eq_true_eq, popt_sound]

/-- The validator agrees with semantic equality. -/
theorem validOpt_iff (a b : PExpr) : validOpt a b = true ↔ peval a = peval b := by
  simp only [validOpt, decide_eq_true_eq]

/-! ## E-113: agreement is equality -/

/-- Agreement is reflexive. -/
theorem agree_refl (c : Bool) : agree c c = true := by
  cases c <;> rfl

/-- A positive agreement test means equality. -/
theorem agree_sound (c o : Bool) (h : agree c o = true) : c = o := by
  simp only [agree, BEq.beq] at h
  cases c <;> cases o <;> simp_all

/-- Equality passes the agreement test. -/
theorem agree_complete (c o : Bool) (h : c = o) : agree c o = true := by
  subst h
  exact agree_refl _

/-! ## E-116: transfer keeps uses, drops the def -/

/-- Every use is live before. -/
theorem mem_transfer_use (i : Instr) (live : List Nat) (v : Nat)
    (h : v ∈ i.uses) : v ∈ transfer i live := by
  simp only [transfer, List.mem_append]
  left
  exact h

/-- A defined value not reused is not live before. -/
theorem not_mem_transfer_def (i : Instr) (live : List Nat)
    (h : i.defv ∉ i.uses) : i.defv ∉ transfer i live := by
  simp only [transfer, List.mem_append, List.mem_filter]
  intro hmem
  rcases hmem with h1 | ⟨_, hne⟩
  · exact h h1
  · simp at hne

/-- The empty block changes nothing. -/
theorem seqLive_nil (live : List Nat) : seqLive [] live = live := rfl

/-! ## E-120: acceptance means no conflict -/

/-- The empty context conflicts with nothing. -/
theorem conflicts_empty (h : Nat) : conflicts [] h = false := rfl

/-- The empty context accepts every loan. -/
theorem acceptLoan_empty (h b : Nat) : acceptLoan [] h b = true := rfl

/-- Acceptance means no conflict. -/
theorem acceptLoan_sound (ls : List Loan) (h b : Nat)
    (ha : acceptLoan ls h b = true) : conflicts ls h = false := by
  simp only [acceptLoan] at ha
  simp only [Bool.not_eq_true'] at ha
  exact ha

/-- No conflict means acceptance. -/
theorem acceptLoan_complete (ls : List Loan) (h b : Nat)
    (hc : conflicts ls h = false) : acceptLoan ls h b = true := by
  simp only [acceptLoan, hc, Bool.not_false]

/-! ## E-123: join bounds, transfer monotone -/

/-- Join bounds the left argument. -/
theorem le_mj_left (a b : Nat) : a ≤ mj a b := Nat.le_max_left a b

/-- Join bounds the right argument. -/
theorem le_mj_right (a b : Nat) : b ≤ mj a b := Nat.le_max_right a b

/-- Transfer is monotone. -/
theorem mono_mtrans (t a b : Nat) (h : a ≤ b) :
    mtrans t a ≤ mtrans t b := by
  simp only [mtrans]
  omega

/-- The empty block is the identity. -/
theorem runM_nil (x : Nat) : runM [] x = x := rfl

/-- The block run is monotone in the input. -/
theorem runM_mono : ∀ (ts : List Nat) (a b : Nat),
    a ≤ b → runM ts a ≤ runM ts b := by
  intro ts
  induction ts with
  | nil => intro a b h; simpa
  | cons t ts ih =>
    intro a b h
    simp only [runM]
    exact ih _ _ (by simp only [mtrans]; omega)

/-! ## E-124: hulls and widening -/

/-- Join covers the left lower bound. -/
theorem ivalJoin_lo (a b : Ival) : (ivalJoin a b).lo ≤ a.lo :=
  Nat.min_le_left _ _

/-- Join covers the left upper bound. -/
theorem ivalJoin_hi (a b : Ival) : a.hi ≤ (ivalJoin a b).hi :=
  Nat.le_max_left _ _

/-- Join of valid intervals is valid. -/
theorem ivalJoin_valid (a b : Ival) (ha : ivalOk a) (_hb : ivalOk b) :
    ivalOk (ivalJoin a b) := by
  simp only [ivalOk, ivalJoin] at *
  exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans ha (Nat.le_max_left _ _))

/-- Widening never lowers the upper bound below `a.hi`. -/
theorem widen_hi (a b : Ival) : a.hi ≤ (widen a b).hi := by
  simp only [widen]
  have h : a.hi ≤ Nat.max a.hi b.hi := Nat.le_max_left _ _
  omega

/-- Widening never raises the lower bound above `a.lo`. -/
theorem widen_lo (a b : Ival) : (widen a b).lo ≤ a.lo := Nat.min_le_left _ _

/-! ## E-137: the lifecycle is exact -/

/-- Placed acks to acked. -/
theorem ostep_placed_ack : ostep .placed .ack = some .acked := rfl

/-- Acked fills to filled. -/
theorem ostep_acked_fill : ostep .acked .fill = some .filled := rfl

/-- Placed cannot fill directly. -/
theorem ostep_placed_fill_none : ostep .placed .fill = none := rfl

/-- Filled admits no transition. -/
theorem ostep_filled (e : OEv) : ostep .filled e = none := by
  cases e <;> rfl

/-! ## E-141: brands match exactly -/

/-- Every order matches itself. -/
theorem matchSame_refl (o : BOrder) : matchSame o o = true := by
  simp [matchSame]

/-- A positive match names equal venues. -/
theorem matchSame_sound (a b : BOrder) (h : matchSame a b = true) :
    a.venue = b.venue := by
  simp only [matchSame, decide_eq_true_eq] at h
  exact h

/-- Equal venues always match. -/
theorem matchSame_complete (a b : BOrder) (h : a.venue = b.venue) :
    matchSame a b = true := by
  simp only [matchSame, decide_eq_true_eq]
  exact h

/-! ## E-148: wildcards cover -/

/-- The empty row covers nothing. -/
theorem coversAny_nil (v : Option Nat) : coversAny [] v = false := rfl

/-- A leading wildcard covers any value. -/
theorem coversAny_wild (ps : List Pat) (v : Option Nat) :
    coversAny (.wild :: ps) v = true := rfl

/-- A wildcard-headed row is flagged exhaustive. -/
theorem hasWild_wild (ps : List Pat) : hasWild (.wild :: ps) = true := by
  simp [hasWild]

/-! ## E-149: composition is concatenation -/

/-- Composition adds the field counts. -/
theorem compose_length (r1 r2 : Row) :
    (compose r1 r2).length = r1.length + r2.length := by simp [compose]

/-- Left fields survive composition. -/
theorem mem_compose_left (r1 r2 : Row) (f : Nat) (h : f ∈ r1) :
    f ∈ compose r1 r2 := List.mem_append_left _ h

/-- Right fields survive composition. -/
theorem mem_compose_right (r1 r2 : Row) (f : Nat) (h : f ∈ r2) :
    f ∈ compose r1 r2 := List.mem_append_right _ h

/-- The membership test agrees with the proposition. -/
theorem hasField_iff (r : Row) (f : Nat) : hasField r f = true ↔ f ∈ r := by
  simp only [hasField, decide_eq_true_eq]

end Morph.Specs.BatchP1
