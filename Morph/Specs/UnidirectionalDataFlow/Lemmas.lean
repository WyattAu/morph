/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.UnidirectionalDataFlow.Spec

/-!
# Unidirectional Data Flow: proofs

Research loop 48. `Morph/Specs/UnidirectionalDataFlow/Spec.lean` used to be an
empty module (`TODO: Implement this module`) and `Lemmas.lean` contained only
generic list/Nat facts. This file proves the guarantees the UDF specification
names:

| Theorem | Statement |
|---|---|
| `allows_iff` | the polarity policy accepts exactly (source, read) and (sink, write) |
| `wellPolarized_iff` | well-polarized endpoints are exactly those pairs |
| `reaches_rank_le` | a rank that increases along edges never decreases along a path |
| `acyclic_of_rank` | a ranked graph is acyclic (UDF-THM-001) |
| `immediate_acyclic` | dropping feedback edges preserves acyclicity (UDF-REQ-002) |
| `runOut_length` | a run emits one output per input |
| `runState_append` / `runOut_append` | runs compose over input concatenation |
| `run_ext` | pointwise-equal pure reducers are interchangeable (UDF-THM-002) |
| `send_length` / `send_bounded` | a send adds one element and stays within capacity (UDF-THM-003) |
| `send_full` | a full buffer refuses sends (backpressure) |
| `receive_length` | a receive removes one element |
| `fuse_assoc` / `chain_append` / `chain_foldl` | fusion is associative and preserves semantics (UDF-THM-004) |
-/

namespace Morph.Specs.UnidirectionalDataFlow

/-! ### Polarity -/

theorem source_read_only : allows .source .write = false := rfl

theorem sink_write_only : allows .sink .read = false := rfl

theorem source_can_read : allows .source .read = true := rfl

theorem sink_can_write : allows .sink .write = true := rfl

/-- **The policy is exactly source-read and sink-write.** -/
theorem allows_iff (p : Polarity) (a : Access) :
    allows p a = true ↔
      (p = .source ∧ a = .read) ∨ (p = .sink ∧ a = .write) := by
  cases p <;> cases a <;> simp [allows]

/-- **Well polarization, unfolded into the two legal endpoint shapes.** -/
theorem wellPolarized_iff (eps : List Endpoint) :
    WellPolarized eps ↔
      ∀ e ∈ eps,
        (e.polarity = .source ∧ e.access = .read) ∨
          (e.polarity = .sink ∧ e.access = .write) := by
  unfold WellPolarized
  constructor
  · intro h e he
    exact (allows_iff e.polarity e.access).mp (h e he)
  · intro h e he
    exact (allows_iff e.polarity e.access).mpr (h e he)

/-! ### Acyclicity from a rank function -/

/-- **A rank that increases along every edge never decreases along a path.** -/
theorem reaches_rank_le {g : List Edge} {rank : Nat → Nat} (h : Respects g rank)
    {u v : Nat} (hr : Reaches g u v) : rank u ≤ rank v := by
  induction hr with
  | refl u => exact Nat.le_refl _
  | step he _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (h ⟨_, _⟩ he)) ih

/-- **A ranked graph is acyclic** (UDF-THM-001): a cycle would force the rank to
be strictly below itself. -/
theorem acyclic_of_rank {g : List Edge} {rank : Nat → Nat}
    (h : Respects g rank) : Acyclic g := by
  intro u v he hv
  have h1 : rank v ≤ rank u := reaches_rank_le h hv
  have h2 : rank u < rank v := h ⟨u, v⟩ he
  omega

/-- Removing feedback edges keeps a rank valid. -/
theorem respects_immediate {g feedback : List Edge} {rank : Nat → Nat}
    (h : Respects g rank) : Respects (immediate g feedback) rank := by
  intro e he
  exact h e (List.mem_filter.mp he).1

/-- **Feedback is the only allowed cycle** (UDF-REQ-002): if the rank increases
on every *non-feedback* edge, the instantaneous graph is acyclic. A feedback
edge may decrease the rank (it crosses a delay), which is exactly why it cannot
appear in the instantaneous graph. -/
theorem immediate_acyclic {g feedback : List Edge} {rank : Nat → Nat}
    (h : ∀ e, e ∈ g → isFeedback feedback e = false → rank e.src < rank e.dst) :
    Acyclic (immediate g feedback) := by
  apply acyclic_of_rank
  intro e he
  have hm := List.mem_filter.mp he
  have hfb : isFeedback feedback e = false := by simpa using hm.2
  exact h e hm.1 hfb

/-- The instantaneous graph never contains a feedback edge. -/
theorem not_mem_immediate_of_feedback {g feedback : List Edge} {e : Edge}
    (h : isFeedback feedback e = true) : e ∉ immediate g feedback := by
  intro he
  have := (List.mem_filter.mp he).2
  simp [h] at this

/-! ### Reducers -/

/-- **A run emits one output per input.** -/
theorem runOut_length {σ α β : Type} (r : Reducer σ α β) (s : σ) (as : List α) :
    (runOut r s as).length = as.length := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [runOut, ih]

/-- **State evolution composes over concatenated input.** -/
theorem runState_append {σ α β : Type} (r : Reducer σ α β) (s : σ)
    (xs ys : List α) :
    runState r s (xs ++ ys) = runState r (runState r s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih => simp [runState, ih]

/-- **Outputs compose over concatenated input**, with the second run starting
from the first run's final state. -/
theorem runOut_append {σ α β : Type} (r : Reducer σ α β) (s : σ)
    (xs ys : List α) :
    runOut r s (xs ++ ys) =
      runOut r s xs ++ runOut r (runState r s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih => simp [runOut, runState, ih]

/-- The full run composes. -/
theorem run_append {σ α β : Type} (r : Reducer σ α β) (s : σ)
    (xs ys : List α) :
    run r s (xs ++ ys) =
      let p := run r s xs
      let q := run r p.1 ys
      (q.1, p.2 ++ q.2) := by
  simp only [run, runState_append, runOut_append]

theorem stepState_ext {σ α β : Type} {r r' : Reducer σ α β}
    (h : ∀ s a, r s a = r' s a) (s : σ) (a : α) :
    stepState r s a = stepState r' s a := by
  unfold stepState
  rw [h s a]

theorem stepOut_ext {σ α β : Type} {r r' : Reducer σ α β}
    (h : ∀ s a, r s a = r' s a) (s : σ) (a : α) :
    stepOut r s a = stepOut r' s a := by
  unfold stepOut
  rw [h s a]

/-- Pointwise-equal reducers compute the same state sequence. -/
theorem runState_ext {σ α β : Type} {r r' : Reducer σ α β}
    (h : ∀ s a, r s a = r' s a) (s : σ) (as : List α) :
    runState r s as = runState r' s as := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp [runState, stepState_ext h, ih]

/-- Pointwise-equal reducers compute the same outputs. -/
theorem runOut_ext {σ α β : Type} {r r' : Reducer σ α β}
    (h : ∀ s a, r s a = r' s a) (s : σ) (as : List α) :
    runOut r s as = runOut r' s as := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp [runOut, stepState_ext h, stepOut_ext h, ih]

/-- **Purity makes reducers interchangeable** (UDF-THM-002): two reducers that
agree pointwise produce the same run. There is no hidden state to disagree
about. -/
theorem run_ext {σ α β : Type} {r r' : Reducer σ α β}
    (h : ∀ s a, r s a = r' s a) (s : σ) (as : List α) :
    run r s as = run r' s as := by
  unfold run
  rw [runState_ext h, runOut_ext h]

/-! ### Backpressure -/

/-- **A successful send adds exactly one element.** -/
theorem send_length (st : Stream) (x : Nat) (st' : Stream)
    (h : send st x = some st') :
    st'.buffer.length = st.buffer.length + 1 := by
  unfold send at h
  split at h
  · next hc =>
      obtain rfl := Option.some.inj h
      simp
  · simp at h

/-- **A send never changes the capacity** — only the buffer. -/
theorem send_capacity (st : Stream) (x : Nat) (st' : Stream)
    (h : send st x = some st') :
    st'.capacity = st.capacity := by
  unfold send at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · simp at h

/-- **A successful send stays within capacity** (UDF-THM-003). -/
theorem send_bounded (st : Stream) (x : Nat) (st' : Stream)
    (h : send st x = some st') :
    st'.buffer.length ≤ st.capacity := by
  have hlen := send_length st x st' h
  unfold send at h
  split at h
  · next hc =>
      simp [canSend] at hc
      omega
  · simp at h

/-- **A full buffer refuses sends** — the credit is the backpressure signal. -/
theorem send_full (st : Stream) (x : Nat)
    (h : ¬ st.buffer.length < st.capacity) :
    send st x = none := by
  unfold send canSend
  simp [h]

/-- **A successful receive removes exactly one element.** -/
theorem receive_length (st : Stream) (x : Nat) (st' : Stream)
    (h : receive st = some (x, st')) :
    st'.buffer.length + 1 = st.buffer.length := by
  cases hbuf : st.buffer with
  | nil => simp [receive, hbuf] at h
  | cons y ys =>
      simp [receive, hbuf] at h
      obtain ⟨-, rfl⟩ := h
      simp

/-- **Sends never exceed capacity, from any starting buffer.** -/
theorem send_never_exceeds (st : Stream) (x : Nat) (st' : Stream)
    (h : send st x = some st') :
    st'.buffer.length ≤ max st.buffer.length st.capacity := by
  have h1 := send_bounded st x st' h
  have h2 : st.buffer.length ≤ max st.buffer.length st.capacity := Nat.le_max_left _ _
  omega

/-! ### Fusion -/

/-- **Fusion is associative.** -/
theorem fuse_assoc {α β γ δ : Type} (h : γ → δ) (g : β → γ) (f : α → β) :
    fuse h (fuse g f) = fuse (fuse h g) f := rfl

/-- **A chain composes over concatenation.** -/
theorem chain_append (fs gs : List (Nat → Nat)) (x : Nat) :
    chain (fs ++ gs) x = chain gs (chain fs x) := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih => simp [chain, ih]

/-- **Fusion preserves semantics**: running a fused chain is folding the
functions left to right (UDF-THM-004). -/
theorem chain_foldl (fs : List (Nat → Nat)) (x : Nat) :
    chain fs x = fs.foldl (fun acc f => f acc) x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih => simp [chain, ih, List.foldl]

/-- A two-element chain is exactly the fused transducer. -/
theorem chain_two (f g : Nat → Nat) (x : Nat) :
    chain [f, g] x = fuse g f x := rfl

end Morph.Specs.UnidirectionalDataFlow
