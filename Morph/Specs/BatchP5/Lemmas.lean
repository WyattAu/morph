/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP5.Spec

/-!
# Feasible-50 kernels — P5 lemmas

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms.
-/

namespace Morph.Specs.BatchP5

/-! ## E-1455: single execution -/

/-- A fresh token executes and is recorded. -/
theorem invoke_fresh (consumed : List Nat) (id : Nat) (h : id ∉ consumed) :
    invoke consumed id = some (id :: consumed) := by
  simp [invoke, h]

/-- A consumed token is refused. -/
theorem invoke_dup (consumed : List Nat) (id : Nat) (h : id ∈ consumed) :
    invoke consumed id = none := by
  simp [invoke, h]

/-- Execution records the token. -/
theorem invoke_records (consumed : List Nat) (id : Nat) (rest : List Nat)
    (h : invoke consumed id = some rest) : id ∈ rest := by
  simp only [invoke] at h
  split at h
  · simp at h
  · obtain rfl := Option.some_inj.mp h
    simp

/-! ## E-1460: the meet admits the intersection -/

/-- Admission names the bounds. -/
theorem admitR_sound (r : Rule) (n : Nat) (h : admitR r n = true) :
    r.lo ≤ n ∧ n ≤ r.hi := by
  simp only [admitR, decide_eq_true_eq] at h
  exact h

/-- In-bounds requests are admitted. -/
theorem admitR_complete (r : Rule) (n : Nat)
    (h : r.lo ≤ n ∧ n ≤ r.hi) : admitR r n = true := by
  simp only [admitR, decide_eq_true_eq]
  exact h

/-- The meet admits exactly the jointly-admitted. -/
theorem meet_sound (r1 r2 : Rule) (n : Nat)
    (h : admitR (meet r1 r2) n = true) :
    admitR r1 n = true ∧ admitR r2 n = true := by
  simp only [admitR, decide_eq_true_eq, meet] at h ⊢
  obtain ⟨hlo, hhi⟩ := h
  have l1 : r1.lo ≤ Nat.max r1.lo r2.lo := Nat.le_max_left _ _
  have l2 : r2.lo ≤ Nat.max r1.lo r2.lo := Nat.le_max_right _ _
  have u1 : Nat.min r1.hi r2.hi ≤ r1.hi := Nat.min_le_left _ _
  have u2 : Nat.min r1.hi r2.hi ≤ r2.hi := Nat.min_le_right _ _
  omega

/-! ## E-1463: duality is an involution -/

/-- Dualizing twice returns the end. -/
theorem dual_invol (e : ChanEnd) : dualOf (dualOf e) = e := rfl

/-- An end matches its dual. -/
theorem match_self (e : ChanEnd) : matchC e (dualOf e) = true := by
  simp [matchC, dualOf]

/-- A match names the duality. -/
theorem match_sound (a b : ChanEnd) (h : matchC a b = true) :
    b.id = a.dual ∧ b.dual = a.id := by
  simp only [matchC, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h2.symm, h1.symm⟩

/-! ## E-1468: order is enforced -/

/-- The expected message advances the box. -/
theorem receive_ok (m : Mbox) :
    receive m m.expect = some ⟨m.expect, m.expect + 1⟩ := by
  simp [receive]

/-- Anything else is rejected. -/
theorem receive_reject (m : Mbox) (msg : Nat) (h : msg ≠ m.expect) :
    receive m msg = none := by
  simp [receive, h]

/-- The advance increments the expectation. -/
theorem receive_seq (m : Mbox) (m' : Mbox)
    (h : receive m m.expect = some m') : m'.expect = m.expect + 1 := by
  simp only [receive, if_true] at h
  have e := Option.some_inj.mp h
  rw [← e]

/-! ## E-1469: cursor accounting -/

/-- Producing buffers one more (head never passes tail). -/
theorem push_used (r : Ring) (h : r.head ≤ r.tail) :
    used (push r) = used r + 1 := by
  show (r.tail + 1) - r.head = (r.tail - r.head) + 1
  omega

/-- Consuming a buffered item frees one (never pop an empty ring). -/
theorem pop_used (r : Ring) (h : r.head < r.tail) :
    used (pop r) + 1 = used r := by
  show (r.tail - (r.head + 1)) + 1 = r.tail - r.head
  omega

/-- A push followed by a pop nets zero. -/
theorem push_pop (r : Ring) (h : r.head ≤ r.tail) :
    used (pop (push r)) = used r := by
  show (r.tail + 1) - (r.head + 1) = r.tail - r.head
  omega

/-! ## E-1470: one value per node, in order -/

/-- Combination adds the values. -/
theorem combine_val (a b : Sig) : (combine a b).val = a.val + b.val := rfl

/-- Combination covers the left stamp. -/
theorem combine_stamp_l (a b : Sig) : a.stamp ≤ (combine a b).stamp :=
  Nat.le_max_left _ _

/-- Combination is commutative. -/
theorem combine_comm (a b : Sig) : combine a b = combine b a := by
  simp only [combine, Nat.add_comm a.val, Nat.max_comm a.stamp]

/-- Mapped sums distribute over append. -/
theorem sum_append_sig : ∀ (l1 l2 : List Sig),
    ((l1 ++ l2).map Sig.val).sum
      = (l1.map Sig.val).sum + (l2.map Sig.val).sum := by
  intro l1
  induction l1 with
  | nil => intro l2; simp
  | cons s ss ih =>
    intro l2
    simp only [List.cons_append, List.map_cons, List.sum_cons, ih]
    omega

/-- Evaluation splits over append. -/
theorem evalOnce_append (l1 l2 : List Sig) :
    evalOnce (l1 ++ l2) = evalOnce l1 + evalOnce l2 := by
  simp only [evalOnce, sum_append_sig]

/-! ## E-1484: the deny list decides -/

/-- A denied permission is refused. -/
theorem deny_banned (denied : List Nat) (p : Nat) (h : p ∈ denied) :
    denyCheck denied p = false := by
  simp [denyCheck, h]

/-- Anything else is allowed. -/
theorem deny_ok (denied : List Nat) (p : Nat) (h : p ∉ denied) :
    denyCheck denied p = true := by
  simp [denyCheck, h]

/-! ## E-1487: capabilities gate use -/

/-- Grants start live. -/
theorem use_grant (p : Nat) : useC (grant p) = true := rfl

/-- Revocation kills use. -/
theorem revoke_dead (c : Cap) : useC (revoke c) = false := rfl

/-- Revocation keeps the label. -/
theorem revoke_perm (c : Cap) : (revoke c).perm = c.perm := rfl

/-! ## E-1489: restore wins -/

/-- Restore installs the snapshot. -/
theorem restore_snap (killed snap : App) : restoreA killed snap = snap := rfl

/-- Snapshots keep the data. -/
theorem snap_data (a : App) : (snapA a).dat = a.dat := rfl

/-- Rotation keeps the data. -/
theorem rotate_data (a : App) : (rotate a).dat = a.dat := rfl

/-! ## E-1490: the link walk -/

/-- Idle advertising starts. -/
theorem bstep_adv : bstep .idle .startAdv = some .advertising := rfl

/-- Advertising connects. -/
theorem bstep_conn : bstep .advertising .connect = some .connected := rfl

/-- Connected drops to idle. -/
theorem bstep_drop : bstep .connected .drop = some .idle := rfl

/-- Advertising timeouts fall back. -/
theorem bstep_timeout_adv : bstep .advertising .timeout = some .idle := rfl

/-- Connected timeouts hold. -/
theorem bstep_timeout_conn : bstep .connected .timeout = some .connected := rfl

/-- Idle never connects directly. -/
theorem bstep_idle_conn : bstep .idle .connect = none := rfl

end Morph.Specs.BatchP5
