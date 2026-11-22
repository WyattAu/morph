/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal

/-!
# Proof crate `Merge` (L0 leaf): arm-merge allocation helpers

Estate-style leaf: depends on `Core`/`Total` only, never on
`Morph.HIRToMIRBranch` or another leaf. `Morph.HIRToMIRBranch` imports this
module back; the tree stays green between cuts.

Provenance (statements unchanged, proofs verbatim):
- `mergeIds`, `rhoLookup_some_of_mem`, `mergeIds_mem_lookup`,
  `mkMergePhis`, `mkMergePhis_le`, `mkMergePhis_growth_fresh` — extracted
  from `Morph/HIRToMIRBranch.lean` § "Arm-merge helpers (C2c groundwork)".
- `boundIds` — extracted from beside `runHIRStmts_arm_lookup_diff`
  (which stays in Branch: it cites the worker `runHIRStmts_arm_lookup`,
  so moving it would drag the worker with it).

An `if` arm that rebinds needs one phi per merged binding at the join, not
just the value phi. The HIR runs the taken arm in the pre-branch env and
continues the rest in that arm's exit env, so the join must reproduce the
taken side: every id mapped pre-branch whose binding either arm changed gets
a fresh register fed from both arm exits. Ids unmapped pre-branch are never
merged — a fresh arm declaration is invisible on the other path, and a static
merged register for it would break `RelEnv` there.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR

/-- Ids rebound in either arm exit env relative to the pre-branch env, in
pre-branch order, without duplicates. -/
def mergeIds (ρ ltρ leρ : List (HIR.Id × ValId)) : List HIR.Id :=
  (ρ.map Prod.fst).foldl (fun acc j =>
    if acc.contains j then acc
    else if rhoLookup ltρ j != rhoLookup ρ j ||
            rhoLookup leρ j != rhoLookup ρ j then acc ++ [j]
    else acc) []

/-- `rhoLookup` succeeds (for some register) at any id occurring in `ρ`. -/
theorem rhoLookup_some_of_mem {ρ : List (HIR.Id × ValId)} {id : HIR.Id}
    {v : ValId} (hmem : (id, v) ∈ ρ) : ∃ v', rhoLookup ρ id = some v' := by
  induction ρ with
  | nil => simp at hmem
  | cons p rest ih =>
      obtain ⟨j, w⟩ := p
      simp only [rhoLookup]
      by_cases hj : j = id
      · subst hj
        exact ⟨w, by simp⟩
      · rw [if_neg hj]
        have htail : (id, v) ∈ rest := by
          rcases List.mem_cons.mp hmem with h | h
          · obtain ⟨h1, _⟩ := Prod.mk.inj h
            exact absurd h1.symm hj
          · exact h
        exact ih htail

/-- Merged members come from the pre-branch domain, so the pre-branch lookup
succeeds for them. -/
theorem mergeIds_mem_lookup {ρ ltρ leρ : List (HIR.Id × ValId)} {id : HIR.Id}
    (hmem : id ∈ mergeIds ρ ltρ leρ) : ∃ v, rhoLookup ρ id = some v := by
  have hmemfst : id ∈ ρ.map Prod.fst := by
    unfold mergeIds at hmem
    have inv : ∀ (l : List HIR.Id) (acc : List HIR.Id),
        (∀ x ∈ acc, x ∈ ρ.map Prod.fst) → (∀ x ∈ l, x ∈ ρ.map Prod.fst) →
        ∀ x ∈ l.foldl (fun acc j =>
          if acc.contains j then acc
          else if rhoLookup ltρ j != rhoLookup ρ j ||
                  rhoLookup leρ j != rhoLookup ρ j then acc ++ [j]
          else acc) acc, x ∈ ρ.map Prod.fst := by
      intro l acc hacc hl
      induction l generalizing acc with
      | nil =>
          simp only [List.foldl_nil]
          exact hacc
      | cons hd tl ih =>
          simp only [List.foldl_cons]
          by_cases hc : acc.contains hd = true
          · rw [if_pos hc]
            exact ih _ hacc (fun x hx => hl x (List.mem_cons_of_mem _ hx))
          · rw [if_neg hc]
            by_cases hd2 : (rhoLookup ltρ hd != rhoLookup ρ hd ||
                rhoLookup leρ hd != rhoLookup ρ hd) = true
            · rw [if_pos hd2]
              apply ih
              · intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hacc x hx
                · rw [List.mem_singleton.mp hx]
                  exact hl hd (List.mem_cons_self ..)
              · intro x hx
                exact hl x (List.mem_cons_of_mem _ hx)
            · rw [if_neg hd2]
              exact ih _ hacc (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    exact inv _ _ (by intro x hx; simp at hx) (fun x hx => hx) _ hmem
  obtain ⟨⟨_, _⟩, hp, rfl⟩ := List.mem_map.mp hmemfst
  exact rhoLookup_some_of_mem hp

/-- Allocate one fresh merged register per id with merge phis from both arm
exits. `none` when an arm exit lacks a merged id (impossible for
lowering-produced envs, which only grow — the `none` branch keeps the
definition total). -/
def mkMergePhis (ρ ltρ leρ : List (HIR.Id × ValId)) (s : Nat)
    (predT predE : MIR.BlockId) : List HIR.Id →
    Option (List Instr × Nat × List (HIR.Id × ValId))
  | [] => some ([], s, ρ)
  | id :: ids =>
      match rhoLookup ltρ id with
      | none => none
      | some srcT =>
          match rhoLookup leρ id with
          | none => none
          | some srcE =>
              match mkMergePhis ρ ltρ leρ (s + 1) predT predE ids with
              | none => none
              | some (phis, s', ρ') =>
                  some ([.phi s predT srcT, .phi s predE srcE] ++ phis, s',
                    (id, s) :: ρ')

/-- Merging only bumps the supply. -/
theorem mkMergePhis_le {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {ids : List HIR.Id} {phis : List Instr}
    {s' : Nat} {ρ' : List (HIR.Id × ValId)}
    (h : mkMergePhis ρ ltρ leρ s predT predE ids = some (phis, s', ρ')) :
    s ≤ s' := by
  induction ids generalizing ρ s phis s' ρ' with
  | nil =>
      simp only [mkMergePhis] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      exact Nat.le_refl _
  | cons id ids ih =>
      simp only [mkMergePhis] at h
      cases hT : rhoLookup ltρ id with
      | none => rw [hT] at h; simp at h
      | some _ =>
          rw [hT] at h
          cases hE : rhoLookup leρ id with
          | none => rw [hE] at h; simp at h
          | some _ =>
              rw [hE] at h
              cases hrec : mkMergePhis ρ ltρ leρ (s + 1) predT predE ids with
              | none => rw [hrec] at h; simp at h
              | some q =>
                  obtain ⟨phis', s'', ρ''⟩ := q
                  rw [hrec] at h
                  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
                  exact Nat.le_trans (Nat.le_succ _) (ih hrec)

/-- Allocation only bumps the supply, and the resulting env is fresh above
it: the new pair sits below `s + 1`, and every older member was already
below `s`. -/
theorem mkMergePhis_growth_fresh {ρ ltρ leρ : List (HIR.Id × ValId)} {s : Nat}
    {predT predE : MIR.BlockId} {ids : List HIR.Id} {phis : List Instr}
    {s' : Nat} {ρ' : List (HIR.Id × ValId)} (hf : FreshAbove ρ s)
    (h : mkMergePhis ρ ltρ leρ s predT predE ids = some (phis, s', ρ')) :
    s ≤ s' ∧ FreshAbove ρ' s' := by
  have hmem_cons : ∀ (σ : List (HIR.Id × ValId)) (id : HIR.Id) (sv : Nat)
      (j : HIR.Id) (v : Nat),
      (j, v) ∈ (id, sv) :: σ → (j, v) ∈ σ ∨ (j = id ∧ v = sv) := by
    intro σ id sv j v hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with h0 | h0
    · exact Or.inr ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
    · exact Or.inl h0
  induction ids generalizing ρ s phis s' ρ' with
  | nil =>
      simp only [mkMergePhis] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      exact ⟨Nat.le_refl _, hf⟩
  | cons id ids ih =>
      simp only [mkMergePhis] at h
      cases hT : rhoLookup ltρ id with
      | none => rw [hT] at h; simp at h
      | some _ =>
          rw [hT] at h
          cases hE : rhoLookup leρ id with
          | none => rw [hE] at h; simp at h
          | some _ =>
              rw [hE] at h
              cases hrec : mkMergePhis ρ ltρ leρ (s + 1) predT predE ids with
              | none => rw [hrec] at h; simp at h
              | some q =>
                  obtain ⟨phis', s'', ρ''⟩ := q
                  rw [hrec] at h
                  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
                  have hfρ : FreshAbove ρ (s + 1) :=
                    FreshAbove.mono ρ s (s + 1) (Nat.le_succ _) hf
                  obtain ⟨hle, hfr⟩ := ih hfρ hrec
                  refine ⟨Nat.le_trans (Nat.le_succ _) hle, ?_⟩
                  intro j v hmem
                  rcases hmem_cons _ _ _ _ _ hmem with hmem | ⟨rfl, rfl⟩
                  · exact hfr _ _ hmem
                  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle

/-- The merge set is empty when neither arm exit rebinds: both `if`s in the
step function then keep `acc`, so the fold is the identity. The C3 workers
cite this (with `arm_rho`, which gives `lt.ρ = ρ` and `le.ρ = ρ` for
binding-free arms) to discharge the merge decision on the old join path. -/
theorem mergeIds_self (ρ : List (HIR.Id × ValId)) : mergeIds ρ ρ ρ = [] := by
  unfold mergeIds
  suffices h : ∀ (l : List HIR.Id) (acc : List HIR.Id),
      l.foldl (fun acc j =>
        if acc.contains j then acc
        else if rhoLookup ρ j != rhoLookup ρ j ||
                rhoLookup ρ j != rhoLookup ρ j then acc ++ [j]
        else acc) acc = acc by
    exact h _ _
  intro l acc
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil]
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      by_cases hc : acc.contains hd = true
      · rw [if_pos hc]
        exact ih _
      · rw [if_neg hc]
        have hn : ¬ (rhoLookup ρ hd != rhoLookup ρ hd ||
            rhoLookup ρ hd != rhoLookup ρ hd) := by simp
        rw [if_neg hn]
        exact ih _

/-- Merge allocation shadows only the merged ids: an unmerged id looks up
in the merged env exactly as in the pre-branch env (every consed pair has a
merged head, which the first-match lookup skips). The future merge-join
proof cites this for the unmerged part of `RelEnv` transport. -/
theorem mkMergePhis_lookup_unmerged {ρ ltρ leρ : List (HIR.Id × ValId)}
    {s : Nat} {predT predE : MIR.BlockId} {ids : List HIR.Id}
    {phis : List Instr} {s' : Nat} {ρm : List (HIR.Id × ValId)} {id : HIR.Id}
    (h : mkMergePhis ρ ltρ leρ s predT predE ids = some (phis, s', ρm))
    (hnin : id ∉ ids) :
    rhoLookup ρm id = rhoLookup ρ id := by
  induction ids generalizing ρ s phis s' ρm with
  | nil =>
      simp only [mkMergePhis] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      rfl
  | cons mid mids ih =>
      simp only [mkMergePhis] at h
      cases hT : rhoLookup ltρ mid with
      | none => rw [hT] at h; simp at h
      | some _ =>
          rw [hT] at h
          cases hE : rhoLookup leρ mid with
          | none => rw [hE] at h; simp at h
          | some _ =>
              rw [hE] at h
              cases hrec : mkMergePhis ρ ltρ leρ (s + 1) predT predE mids with
              | none => rw [hrec] at h; simp at h
              | some q =>
                  obtain ⟨phis', s'', ρ''⟩ := q
                  rw [hrec] at h
                  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
                  have hne : ¬ mid = id := by
                    intro heq
                    subst heq
                    simp at hnin
                  have hnin_tail : id ∉ mids :=
                    fun hm => hnin (List.mem_cons_of_mem _ hm)
                  have hrec' := ih hrec hnin_tail
                  have hstep : rhoLookup ((mid, s) :: ρ'') id =
                      rhoLookup ρ'' id := by
                    simp [rhoLookup, hne]
                  rw [hstep, hrec']

/-- Merged ids map to fresh registers inside the merge window: the head
takes `s`, deeper ids take whatever the recursive call assigned (all at or
above `s + 1`, all below `s'`). Together with `mkMergePhis_lookup_unmerged`
and `mkMergePhis_growth_fresh` this fully characterizes the merged env for
the future merge-join proof. -/
theorem mkMergePhis_lookup_mem {ρ ltρ leρ : List (HIR.Id × ValId)}
    {s : Nat} {predT predE : MIR.BlockId} {ids : List HIR.Id}
    {phis : List Instr} {s' : Nat} {ρm : List (HIR.Id × ValId)} {id : HIR.Id}
    (h : mkMergePhis ρ ltρ leρ s predT predE ids = some (phis, s', ρm))
    (hmem : id ∈ ids) :
    ∃ r, rhoLookup ρm id = some r ∧ s ≤ r ∧ r < s' := by
  induction ids generalizing ρ s phis s' ρm with
  | nil => simp at hmem
  | cons mid mids ih =>
      simp only [mkMergePhis] at h
      cases hT : rhoLookup ltρ mid with
      | none => rw [hT] at h; simp at h
      | some _ =>
          rw [hT] at h
          cases hE : rhoLookup leρ mid with
          | none => rw [hE] at h; simp at h
          | some _ =>
              rw [hE] at h
              cases hrec : mkMergePhis ρ ltρ leρ (s + 1) predT predE mids with
              | none => rw [hrec] at h; simp at h
              | some q =>
                  obtain ⟨phis', s'', ρ''⟩ := q
                  rw [hrec] at h
                  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
                  -- NOTE: the `rfl` above substitutes the outer `s'` with the
                  -- recursive supply, so `hle` and the goal speak of `s'`.
                  have hle : s + 1 ≤ s' := mkMergePhis_le hrec
                  by_cases heq : mid = id
                  · subst heq
                    exact ⟨s, by simp [rhoLookup], Nat.le_refl _,
                      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle⟩
                  · have hmem_tail : id ∈ mids := by
                      rcases List.mem_cons.mp hmem with h | h
                      · exact absurd h (Ne.symm heq)
                      · exact h
                    obtain ⟨r, hr, hlo, hhi⟩ := ih hrec hmem_tail
                    refine ⟨r, ?_, Nat.le_trans (Nat.le_succ _) hlo, hhi⟩
                    have hstep : rhoLookup ((mid, s) :: ρ'') id =
                        rhoLookup ρ'' id := by
                      simp [rhoLookup, heq]
                    rw [hstep]
                    exact hr

/-- Ids an arm run may rebind: `assign` targets plus `varDecl` introductions,
through nested arm `if`s. `assignedIds` misses `varDecl` (it falls in the
catch-all), so arms need their own measure; loop bodies keep `assignedIds`
because `varDecl` under `loop = some` contradicts the lowering. -/
def boundIds : List HIR.Stmt → List HIR.Id
  | [] => []
  | .varDecl id _ _ :: rest => id :: boundIds rest
  | .assign id _ :: rest => id :: boundIds rest
  | .ifStmt _ th el :: rest => boundIds th ++ boundIds el ++ boundIds rest
  | .whileLoop _ body :: rest => boundIds body ++ boundIds rest
  | _ :: rest => boundIds rest

end Morph.HIRToMIRCorrect
