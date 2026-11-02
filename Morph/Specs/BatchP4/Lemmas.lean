/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP4.Spec

/-!
# Feasible-50 kernels — P4 lemmas

Proofs for the ten cores of `Spec.lean`. Sorry-free, no axioms.
-/

namespace Morph.Specs.BatchP4

/-! ## E-380: framing roundtrips -/

/-- Framed payloads parse back. -/
theorem parse_mk (bs : List Nat) : parseFrame (mkFrame bs) = some bs := by
  simp [mkFrame, parseFrame]

/-- Length mismatches are rejected. -/
theorem parse_bad (n : Nat) (bs : List Nat) (h : bs.length ≠ n) :
    parseFrame (n, bs) = none := by
  simp [parseFrame, h]

/-! ## E-381: every encoding conforms -/

/-- Tags encode in range. -/
theorem tag_bound (t : Tag) : tagToNat t ≤ 2 := by
  cases t <;> decide

/-- Every encoded message conforms. -/
theorem encode_conforms (m : WireMsg) : conforms (encodeM m) = true := by
  simp only [conforms, decide_eq_true_eq, encodeM]
  exact tag_bound m.tag

/-! ## E-382: the session walk -/

/-- Down plus logon reaches sync. -/
theorem sstep_logon : sstep .down .logon = some .sync := rfl

/-- Sync plus gap-fill reaches up. -/
theorem sstep_gapfill : sstep .sync .gapfill = some .up := rfl

/-- Up heartbeats stay up. -/
theorem sstep_heartbeat : sstep .up .heartbeat = some .up := rfl

/-- Close always lands down. -/
theorem sstep_close (s : Sess) : sstep s .close = some .down := by
  cases s <;> rfl

/-- Down admits no heartbeat. -/
theorem sstep_down_hb : sstep .down .heartbeat = none := rfl

/-! ## E-383: the bucket accounts -/

/-- A successful take preserves the account. -/
theorem takeB_sound (b : Bucket) (n : Nat) (b' : Bucket)
    (h : takeB b n = some b') : b'.tokens + n = b.tokens ∧ b'.cap = b.cap := by
  unfold takeB at h
  by_cases hc : n ≤ b.tokens
  · simp only [hc, if_true] at h
    obtain rfl := Option.some_inj.mp h
    constructor
    · show b.tokens - n + n = b.tokens
      omega
    · rfl
  · simp only [hc, if_false] at h
    simp at h

/-- Refill never exceeds the cap. -/
theorem refill_cap (b : Bucket) (n : Nat) : (refill b n).tokens ≤ b.cap := by
  simp only [refill]
  exact Nat.min_le_left _ _

/-- An empty bucket refuses. -/
theorem takeB_empty (b : Bucket) (n : Nat) (h : b.tokens < n) :
    takeB b n = none := by
  simp only [takeB]
  rw [if_neg (by omega)]

/-! ## E-384: disconnect drops everything -/

/-- Disconnect kills liveness. -/
theorem disconnect_dead (c : Conn) : (disconnect c).alive = false := rfl

/-- Disconnect clears the pending list. -/
theorem disconnect_empty (c : Conn) : (disconnect c).pending = [] := rfl

/-! ## E-385: sync restores agreement -/

/-- Syncing makes the backup consistent. -/
theorem sync_consistent (b : Backup) (p : Prim) :
    consistent (syncB b p) p = true := by
  simp [syncB, consistent]

/-- Consistency names the agreement. -/
theorem consistent_sound (b : Backup) (p : Prim)
    (h : consistent b p = true) : b.seq = p.seq ∧ b.dat = p.dat := by
  simp only [consistent, decide_eq_true_eq] at h
  exact h

/-! ## E-392: priority is strict -/

/-- A nonempty high queue wins. -/
theorem sched_hi (h : Nat) (hs lo : List Nat) :
    sched (h :: hs) lo = some h := rfl

/-- An empty high queue defers to low. -/
theorem sched_lo (l : Nat) (ls : List Nat) :
    sched [] (l :: ls) = some l := rfl

/-- Two empty queues idle. -/
theorem sched_none : sched [] [] = none := rfl

/-! ## E-393: the budget is monotone -/

/-- An admitted burst fits rate plus burst. -/
theorem allow_sound (s : Shaper) (n : Nat) (h : allow s n = true) :
    n ≤ s.rate + s.burst := by
  simp only [allow, decide_eq_true_eq] at h
  exact h

/-- Fitting bursts are admitted. -/
theorem allow_complete (s : Shaper) (n : Nat) (h : n ≤ s.rate + s.burst) :
    allow s n = true := by
  simp only [allow, decide_eq_true_eq]
  exact h

/-- More burst admits more. -/
theorem allow_burst (s : Shaper) (n : Nat) (h : allow s n = true) :
    allow ⟨s.rate, s.burst + 1⟩ n = true := by
  simp only [allow, decide_eq_true_eq] at h ⊢
  omega

/-! ## E-396: capture roundtrips in order -/

/-- Records parse back. -/
theorem cap_roundtrip (ts : Nat) (dat : List Nat) :
    parseCap (mkCap ts dat) = some (ts, dat) := by
  simp [mkCap, parseCap]

/-- Capture preserves the batch length. -/
theorem caps_length (ts : Nat) (ds : List (List Nat)) :
    (caps ts ds).length = ds.length := List.length_map _

/-- Captured records keep their payloads. -/
theorem caps_mem (ts : Nat) (ds : List (List Nat)) (d : List Nat)
    (h : d ∈ ds) : (ts, d) ∈ caps ts ds := by
  simp only [caps, List.mem_map]
  exact ⟨d, h, rfl⟩

/-! ## E-398: clocks only move forward -/

/-- Sends tick forward. -/
theorem sendL_gt (s : Nat) : s < sendL s := by
  simp [sendL]

/-- Receives cover the local clock. -/
theorem recvL_left (a b : Nat) : a ≤ recvL a b := by
  simp only [recvL]
  have h : a ≤ Nat.max a b := Nat.le_max_left _ _
  omega

/-- Receives cover the remote clock. -/
theorem recvL_right (a b : Nat) : b ≤ recvL a b := by
  simp only [recvL]
  have h : b ≤ Nat.max a b := Nat.le_max_right _ _
  omega

/-- Merging is symmetric. -/
theorem recvL_symm (a b : Nat) : recvL a b = recvL b a := by
  simp only [recvL, Nat.max_comm]

end Morph.Specs.BatchP4
