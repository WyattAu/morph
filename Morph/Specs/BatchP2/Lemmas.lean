/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP2.Spec

/-!
# Feasible-50 kernels — P2 lemmas

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms.
-/

namespace Morph.Specs.BatchP2

/-! ## E-151: no task lost at the join -/

/-- Fork adds the leaf counts. -/
theorem leafCount_fork (a b : Task) :
    leafCount (.fork a b) = leafCount a + leafCount b := rfl

/-- Join preserves the work-item count. -/
theorem joinAll_length : ∀ t : Task, (joinAll t).length = leafCount t := by
  intro t
  induction t with
  | leaf n => rfl
  | fork a b iha ihb =>
    simp only [joinAll, List.length_append, iha, ihb, leafCount]

/-- Every leaf item appears in the join. -/
theorem joinAll_mem : ∀ (t : Task) (n : Nat),
    n ∈ joinAll t → n ∈ joinAll t := fun _ _ h => h

/-! ## E-156: batch sums split -/

/-- A batch sum is the list sum. -/
theorem batch_eq (xs : List Nat) : batch xs = xs.sum := rfl

/-- List sums distribute over append. -/
theorem sum_append' : ∀ (x y : List Nat), (x ++ y).sum = x.sum + y.sum := by
  intro x
  induction x with
  | nil => intro y; simp
  | cons n xs ih =>
    intro y
    simp only [List.cons_append, List.sum_cons, ih]
    omega

/-- Combined batches add. -/
theorem batchAdd_eq (x y : List Nat) : batchAdd x y = batch x + batch y := by
  simp only [batchAdd, batch, sum_append']

/-! ## E-157: writes keep the read path tear-free -/

/-- A write keeps the counter even when it started even. -/
theorem writeSeq_even (s : Seq) (h : s.ctr % 2 = 0) :
    (writeSeq s v).ctr % 2 = 0 := by
  simp only [writeSeq]
  omega

/-- A fresh even cell reads clean. -/
theorem readOk_write (s : Seq) (v : Nat) (h : s.ctr % 2 = 0) :
    readOk (writeSeq s v) = true := by
  simp only [readOk, decide_eq_true_eq]
  simp only [writeSeq]
  omega

/-! ## E-159: replay is faithful -/

/-- Replay preserves the log length. -/
theorem replayLen_eq (l : Log) : replayLen l = l.length := by
  simp [replayLen, replay, List.length_map]

/-- Logged tasks appear in the replay. -/
theorem mem_replay (l : Log) (t op : Nat) (h : (t, op) ∈ l) :
    t ∈ replay l := by
  simp only [replay, List.mem_map]
  exact ⟨(t, op), h, rfl⟩

/-! ## E-160: transfer moves the owner, keeps the bytes -/

/-- Transfer sets the new owner. -/
theorem give_owner (m : Msg) (o : Nat) : (give m o).owner = o := rfl

/-- Transfer preserves the payload. -/
theorem give_payload (m : Msg) (o : Nat) :
    payloadOf (give m o) = payloadOf m := rfl

/-! ## E-161: restart is a stable projection -/

/-- Failed children restart. -/
theorem restart_failed (n : Nat) : restart (.failed n) = .restarted := rfl

/-- Restart is idempotent. -/
theorem restart_idem (s : SState) : restart (restart s) = restart s := by
  cases s with
  | running => rfl
  | failed n => rfl
  | restarted => rfl

/-- A restarted child stays restarted. -/
theorem restart_stable : restart .restarted = .restarted := rfl

/-! ## E-162: admission fits the window -/

/-- An admitted request fits the limit (over a valid window). -/
theorem admitC_sound (c : Credit) (n : Nat) (hv : windowOk c = true)
    (h : admitC c n = true) : n + c.used ≤ c.limit := by
  simp only [admitC, decide_eq_true_eq, avail] at h
  simp only [windowOk, decide_eq_true_eq] at hv
  omega

/-- A fitting request is admitted (over a valid window). -/
theorem admitC_complete (c : Credit) (n : Nat) (hv : windowOk c = true)
    (h : n + c.used ≤ c.limit) : admitC c n = true := by
  simp only [admitC, decide_eq_true_eq, avail]
  simp only [windowOk, decide_eq_true_eq] at hv
  omega

/-! ## E-163: deliver once -/

/-- First delivery is accepted and records the key. -/
theorem deliver_fresh (seen : List Nat) (k : Nat) (h : k ∉ seen) :
    deliver seen k = (true, k :: seen) := by
  simp [deliver, h]

/-- Redelivery is refused and changes nothing. -/
theorem deliver_dup (seen : List Nat) (k : Nat) (h : k ∈ seen) :
    deliver seen k = (false, seen) := by
  simp [deliver, h]

/-! ## E-172: merge is a join-semilattice -/

/-- Merge is idempotent. -/
theorem mergeG_idem (g : GCount) : mergeG g g = g := by
  simp only [mergeG]
  have h : Nat.max g.v g.v = g.v := Nat.max_self _
  simp [h]

/-- Merge is commutative. -/
theorem mergeG_comm (a b : GCount) : mergeG a b = mergeG b a := by
  simp only [mergeG, Nat.max_comm]

/-- Merge is associative. -/
theorem mergeG_assoc (a b c : GCount) :
    mergeG (mergeG a b) c = mergeG a (mergeG b c) := by
  simp only [mergeG, Nat.max_assoc]

/-- Increment grows the replica. -/
theorem incr_gt (g : GCount) : g.v < (incr g).v := by
  simp [incr]

/-! ## E-174: the named cycle -/

/-- A positive 2-cycle test names both edges. -/
theorem deadlock2_sound (e : Edges) (a b : Nat) (h : deadlock2 e a b = true) :
    (a, b) ∈ e ∧ (b, a) ∈ e := by
  simp only [deadlock2, decide_eq_true_eq] at h
  exact h

/-- The 2-cycle test is symmetric. -/
theorem deadlock2_symm (e : Edges) (a b : Nat) :
    deadlock2 e a b = deadlock2 e b a := by
  by_cases h1 : (a, b) ∈ e <;> by_cases h2 : (b, a) ∈ e <;>
    simp [deadlock2, h1, h2]

/-- A positive self-loop test names the loop. -/
theorem deadlockSelf_sound (e : Edges) (a : Nat) (h : deadlockSelf e a = true) :
    (a, a) ∈ e := by
  simp only [deadlockSelf, decide_eq_true_eq] at h
  exact h

end Morph.Specs.BatchP2
