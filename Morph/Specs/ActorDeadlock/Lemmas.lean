/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ActorDeadlock.Spec

namespace Morph.Specs.ActorDeadlock

/-!
## The wait-for chain

`chain s k p` is the actor reached from `p` after following `k` wait edges.
Two facts drive every theorem below: the chain stays inside `actors`, and it
*strictly increases* any rank that respects waits.
-/

theorem chain_zero (s : Sys) (p : Actor) : chain s 0 p = p := rfl

theorem chain_succ (s : Sys) (k : Nat) (p q : Actor) (h : s.waitOn p = some q) :
    chain s (k + 1) p = chain s k q := by
  simp [chain, h]

theorem chain_succ_none (s : Sys) (k : Nat) (p : Actor) (h : s.waitOn p = none) :
    chain s (k + 1) p = p := by
  simp [chain, h]

/-- Following a wait edge never leaves the system. -/
theorem chain_mem (s : Sys) (hc : Closed s) :
    ∀ (k : Nat) (p : Actor), p ∈ s.actors → chain s k p ∈ s.actors := by
  intro k
  induction k with
  | zero => intro p hp; exact hp
  | succ k ih =>
      intro p hp
      by_cases hw : ∃ q, s.waitOn p = some q
      · obtain ⟨q, hq⟩ := hw
        rw [chain_succ s k p q hq]
        exact ih q (hc.1 p q hq)
      · cases hopt : s.waitOn p with
        | none => rw [chain_succ_none s k p hopt]; exact hp
        | some q => exact absurd ⟨q, hopt⟩ hw

/-- **Ranks strictly increase along the chain.** This is what rules out a
cycle, and it is the entire content of `Ranked`. -/
theorem chain_rank_lt (s : Sys) (rank : Actor → Nat) (hr : Ranked s rank)
    (hc : Closed s) (hall : ∀ a ∈ s.actors, ∃ q, s.waitOn a = some q) :
    ∀ (k : Nat) (p : Actor), p ∈ s.actors → rank (chain s k p) < rank (chain s (k + 1) p) := by
  intro k
  induction k with
  | zero =>
      intro p hp
      obtain ⟨q, hq⟩ := hall p hp
      rw [chain_zero s p, chain_succ s 0 p q hq, chain_zero s q]
      exact hr p q hq
  | succ k ih =>
      intro p hp
      obtain ⟨q, hq⟩ := hall p hp
      rw [chain_succ s (k + 1) p q hq, chain_succ s k p q hq]
      exact ih q (hc.1 p q hq)

/-- `chain s k p` has rank at least `k` more than `p` when every actor of `s`
is blocked. -/
theorem chain_rank_ge (s : Sys) (rank : Actor → Nat) (hr : Ranked s rank)
    (hc : Closed s) (hall : ∀ a ∈ s.actors, ∃ q, s.waitOn a = some q) :
    ∀ (k : Nat) (p : Actor), p ∈ s.actors → rank p + k ≤ rank (chain s k p) := by
  intro k
  induction k with
  | zero =>
      intro p hp
      rw [chain_zero s p]
      omega
  | succ k ih =>
      intro p hp
      obtain ⟨q, hq⟩ := hall p hp
      rw [chain_succ s k p q hq]
      have hlt := hr p q hq
      have hstep := ih q (hc.1 p q hq)
      omega

/-! ## Ranks are bounded on a finite system

`foldlMax` is an upper bound on the rank of every member of the list. -/

def foldlMax (rank : Actor → Nat) : List Actor → Nat
  | [] => 0
  | a :: l => max (rank a) (foldlMax rank l)

theorem foldlMax_mem (rank : Actor → Nat) :
    ∀ (l : List Actor) (a : Actor), a ∈ l → rank a ≤ foldlMax rank l := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons b t ih =>
      intro a h
      simp only [List.mem_cons] at h
      rcases h with h | h
      · rw [h, foldlMax]
        exact Nat.le_max_left _ _
      · rw [foldlMax]
        exact Nat.le_trans (ih a h) (Nat.le_max_right _ _)

/-! ## Deadlock freedom under a rank order -/

/-- **Deadlock freedom from a rank order (SG-004).** If every wait goes from a
lower to a strictly higher rank, then the system always has a runnable actor.

The argument is the classical one for wait-for graphs, in a form a runtime can
check without searching for cycles: assume a deadlock, follow the wait chain
from any actor — the rank has to increase `m + 1` times, but every actor's
rank is at most `m`. -/
theorem ranked_implies_progress (s : Sys) (rank : Actor → Nat) (hwf : WF s)
    (hr : Ranked s rank) (hp : p ∈ s.actors) : s.run ≠ [] := by
  obtain ⟨hlive, hclosed⟩ := hwf
  intro hrun
  -- In a deadlock nobody is runnable, so `Live` forces every actor to block.
  have hblocked : ∀ a, a ∈ s.actors → ∃ q, s.waitOn a = some q := by
    intro a ha
    rcases hlive a ha with h | h
    · exact h
    · have h' : a ∈ s.run := h
      rw [hrun] at h'
      simp at h'
  -- Ranks are bounded on the system.
  let m : Nat := foldlMax rank s.actors
  have hbound : ∀ a, a ∈ s.actors → rank a ≤ m := by
    intro a ha
    exact foldlMax_mem rank s.actors a ha
  -- The chain stays in the system, so its rank is bounded ...
  have hmem : ∀ (k : Nat) (a : Actor), a ∈ s.actors → chain s k a ∈ s.actors :=
    chain_mem s hclosed
  -- ... while the rank increases by one per step.
  have hge : ∀ (k : Nat) (a : Actor), a ∈ s.actors → rank a + k ≤ rank (chain s k a) :=
    chain_rank_ge s rank hr hclosed hblocked
  -- At k = m + 1 the chain's rank is at least m + 1, but it is an actor's rank.
  have hlow : rank p + (m + 1) ≤ rank (chain s (m + 1) p) := hge (m + 1) p hp
  have hhi : rank (chain s (m + 1) p) ≤ m := hbound _ (hmem (m + 1) p hp)
  omega

/-- Convenience form: if every actor is blocked by a well-formed, rank-ordered
state, then it is not a deadlock. -/
theorem ranked_not_deadlocked (s : Sys) (rank : Actor → Nat) (hwf : WF s)
    (hr : Ranked s rank) (hp : p ∈ s.actors) : ¬ Deadlock s :=
  fun h => ranked_implies_progress s rank hwf hr hp h

/-! ## Well-formedness and the rank condition are invariants -/

/-- `Live` is preserved by `ask`. -/
theorem Live_ask (s : Sys) (p q : Actor) (hlive : Live s) : Live (Ask s p q) := by
  intro a ha
  by_cases hpa : a = p
  · refine Or.inl ?_
    refine ⟨q, ?_⟩
    simp [Ask, hpa]
  · rcases hlive a ha with h | h
    · obtain ⟨r, hr⟩ := h
      refine Or.inl ⟨r, ?_⟩
      simp [Ask, hpa, hr]
    · refine Or.inr ?_
      simp only [Ask, Runnable]
      exact (List.mem_erase_of_ne hpa).mpr h

/-- `Closed` is preserved by `ask` (the only new edge is `p → q`). -/
theorem Closed_ask (s : Sys) (p q : Actor) (hclosed : Closed s) (hq : q ∈ s.actors)
    (hqne : q ≠ p) : Closed (Ask s p q) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    by_cases hpa : a = p
    · rw [hpa] at h
      simp [Ask] at h
      subst h
      exact hq
    · simp [Ask, hpa] at h
      exact hclosed.1 a b h
  · intro a hne
    by_cases hpa : a = p
    · simp [Ask, hpa] at hne
      exact hqne hne
    · simp [Ask, hpa] at hne
      exact hclosed.2 a hne

/-- `WF` is preserved by `ask`. -/
theorem WF_ask (s : Sys) (p q : Actor) (hwf : WF s) (hq : q ∈ s.actors)
    (hqne : q ≠ p) : WF (Ask s p q) :=
  ⟨Live_ask s p q hwf.1, Closed_ask s p q hwf.2 hq hqne⟩

/-- `Live` is preserved by `serve`. -/
theorem Live_serve (s : Sys) (q p : Actor) (hlive : Live s) : Live (Serve s q p) := by
  intro a ha
  by_cases hpa : a = p
  · refine Or.inr ?_
    rw [hpa]
    simp [Serve, Runnable]
  · rcases hlive a ha with h | h
    · obtain ⟨r, hr⟩ := h
      refine Or.inl ⟨r, ?_⟩
      simp [Serve, hpa, hr]
    · refine Or.inr ?_
      simp only [Serve, Runnable, List.mem_cons]
      exact Or.inr h

/-- `Closed` is preserved by `serve` (it only *removes* an edge). -/
theorem Closed_serve (s : Sys) (q p : Actor) (hclosed : Closed s) :
    Closed (Serve s q p) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    by_cases hpa : a = p
    · rw [hpa] at h
      simp [Serve] at h
    · simp [Serve, hpa] at h
      exact hclosed.1 a b h
  · intro a hne
    by_cases hpa : a = p
    · simp [Serve, hpa] at hne
    · simp [Serve, hpa] at hne
      exact hclosed.2 a hne

/-- `WF` is preserved by `serve`. -/
theorem WF_serve (s : Sys) (q p : Actor) (hwf : WF s) : WF (Serve s q p) :=
  ⟨Live_serve s q p hwf.1, Closed_serve s q p hwf.2⟩

/-- `Ranked` is preserved by both transitions. -/
theorem Ranked_ask (s : Sys) (rank : Actor → Nat) (p q : Actor)
    (hr : Ranked s rank) (hlt : rank p < rank q) : Ranked (Ask s p q) rank := by
  intro a b h
  by_cases hpa : a = p
  · rw [hpa] at h ⊢
    simp [Ask] at h
    subst h
    exact hlt
  · simp [Ask, hpa] at h
    exact hr a b h

theorem Ranked_serve (s : Sys) (rank : Actor → Nat) (q p : Actor)
    (hr : Ranked s rank) : Ranked (Serve s q p) rank := by
  intro a b h
  by_cases hpa : a = p
  · rw [hpa] at h
    simp [Serve] at h
  · simp [Serve, hpa] at h
    exact hr a b h

/-! ## Deadlock freedom of the whole system -/

/-- **No deadlock from a well-formed, rank-ordered state (SG-004).** Every
state reachable by *any* scheduler has a runnable actor: the well-formedness
and rank conditions are invariants, and at every such state the rank
argument rules out a deadlock. -/
theorem wf_step (s s' : Sys) (rank : Actor → Nat) (h : WF s)
    (hstep : Step rank s s') : WF s' := by
  cases hstep with
  | ask p q hp' hq hlt =>
      exact WF_ask _ _ _ h hq (fun he => (Nat.ne_of_lt hlt) (he ▸ rfl))
  | serve q p hq hw => exact WF_serve _ _ _ h

theorem ranked_step (s s' : Sys) (rank : Actor → Nat) (h : Ranked s rank)
    (hstep : Step rank s s') : Ranked s' rank := by
  cases hstep with
  | ask p q hp' hq hlt => exact Ranked_ask _ _ _ _ h hlt
  | serve q p hq hw => exact Ranked_serve _ _ _ _ h

theorem WF_preserved (rank : Actor → Nat) (s s' : Sys) (hrun : Steps rank s s') :
    WF s → WF s' := by
  induction hrun with
  | refl => intro h; exact h
  | tail x mid hsteps hstep =>
      intro h
      rename_i ih
      exact wf_step _ _ rank (ih h) hstep

theorem Ranked_preserved (rank : Actor → Nat) (s s' : Sys)
    (hrun : Steps rank s s') : Ranked s rank → Ranked s' rank := by
  induction hrun with
  | refl => intro h; exact h
  | tail x mid hsteps hstep =>
      intro h
      rename_i ih
      exact ranked_step _ _ rank (ih h) hstep

theorem progress_invariant (s s' : Sys) (rank : Actor → Nat)
    (hwf : WF s) (hr : Ranked s rank) (_hp : p ∈ s.actors)
    (hrun : Steps rank s s') (hmem : p ∈ s'.actors) : s'.run ≠ [] :=
  ranked_implies_progress s' rank (WF_preserved rank s s' hrun hwf)
    (Ranked_preserved rank s s' hrun hr) hmem

/-- A deadlocked state has no runnable actor and therefore cannot step — the
operational content of `Deadlock`. -/
theorem deadlock_is_stuck (s s' : Sys) (rank : Actor → Nat) (hd : Deadlock s) :
    ¬ Step rank s s' := by
  intro hstep
  cases hstep with
  | ask p q hp' hq hlt => rw [hd] at hp'; simp at hp'
  | serve q p hq hw => rw [hd] at hq; simp at hq

/-- Conversely, a state with a runnable actor is never a deadlock. -/
theorem progress_not_deadlock (s : Sys) (_rank : Actor → Nat) (p : Actor)
    (hp : p ∈ s.run) : ¬ Deadlock s := by
  intro hd
  rw [hd] at hp
  simp at hp

/-! ## Acyclicity of the wait-for graph -/

/-- Ranks increase along the chain as long as the chain is made of real
waits. This is the engine behind `ranked_acyclic`. -/
theorem chain_rank_ge' (s : Sys) (rank : Actor → Nat) (hr : Ranked s rank) :
    ∀ (k : Nat) (p : Actor),
      (∀ j, j < k → ∃ q, s.waitOn (chain s j p) = some q) →
      rank p + k ≤ rank (chain s k p) := by
  intro k
  induction k with
  | zero =>
      intro p _
      rw [chain_zero s p]
      omega
  | succ k ih =>
      intro p hall
      obtain ⟨q, hq⟩ := hall 0 (by omega)
      have hprev : ∀ j, j < k → ∃ r, s.waitOn (chain s j q) = some r := by
        intro j hj
        obtain ⟨r, hr⟩ := hall (j + 1) (by omega)
        refine ⟨r, ?_⟩
        rw [← chain_succ s j p q hq]
        exact hr
      have h1 := ih q hprev
      have h2 := hr p q hq
      rw [chain_succ s k p q hq]
      omega

/-- **A rank order makes the wait-for graph acyclic.** If every wait goes from
a lower to a strictly higher rank, no walk along waits can return to its
start. -/
theorem ranked_acyclic (s : Sys) (rank : Actor → Nat) (hr : Ranked s rank) :
    Acyclic s := by
  intro start k hcyc
  obtain ⟨hk, _, hback, hwaits⟩ := hcyc
  have hge := chain_rank_ge' s rank hr k start hwaits
  rw [hback] at hge
  omega

end Morph.Specs.ActorDeadlock