/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.LinearContext

/-!
# Level-Keyed Linear Contexts

This module defines the level-keyed context API that the binder rules of
`HasType` will migrate to (ADR-010, "The remaining piece of 1c-β-2").

## The problem it solves

When a `let` binds a linear value, the binder's slot must leave the context
when the `let` ends. Positional erasure (`List.eraseIdx`, `List.drop`) cannot
express this composably: under a *prefix* of outer binders, the slot's index
shifts as inner binders come and go, and an erasure phrased positionally,
re-applied, removes a *different* entry. Concretely, with `pfx = [A, B]` and an
inner `let` binding `C`, the context is `[C, A, B, T, x]` with `T` the
substituted slot:

* nested path: erase `T` (index 3), then erase `C` (index 0) → `[A, B, x]` ✓
* outer form re-applied: `[A, B, x].eraseIdx 2` → `[A, B]` ✗ drops `x`

## The fix: erase by binder level, not by position

Each entry records the **level** it was introduced at — a natural number
fresh with respect to the context it was pushed onto (`nextLevel` = one above
the highest level present). Levels are attached to entries and never change,
so a level identifies a binding *no matter where the entry currently sits*.

Erasure is `filter (·.level != k)`, which gives the two properties the
substitution lemma needs, for free:

* **Idempotent** — `eraseBinding k (eraseBinding k ctx) = eraseBinding k ctx`.
  The double-erase that arises when an outer substitution crosses an inner
  `let` collapses instead of removing a second, unrelated entry.
* **Commuting** — erasures at any two levels commute, so the order in which
  binders close does not matter.

Both hold for *any* predicate, by the nature of `filter`; the level discipline
(`DistinctLevels`) is only needed for the *counting* lemma (exactly one entry
removed).

## Status

Staged. `HasType` does not use this representation yet; the binder rules
(`let_type`, `lam_type`, `for_type`, `ArmsTyped.cons`) migrate to it in
ADR-010 Phase 1c-β-2 part 2.
-/

namespace Morph

open Morph.Core

/-! ## Level-Carrying Entries -/

/-- A context entry that remembers the binder level it was introduced at.

    The level is assigned when the entry is pushed, as `nextLevel` of the
    context being pushed onto, and is never subsequently changed. Two live
    entries in a level-distinct context never share a level (see
    `DistinctLevels`). -/
structure LinIdEntry where
  typ   : Typ
  usage : Usage
  level : Nat

/-- A level-keyed linear context. Index 0 is still the most recently bound
    variable (de Bruijn *index* addressing, which `bvar_type` uses); the
    `level` field is the de Bruijn *level* view used for keyed erasure. -/
abbrev LinIdCtx := List LinIdEntry

namespace LinIdCtx

/-! ## Fresh Levels -/

/-- The next fresh level for `ctx`: one above the highest level present.
    Freshness needs no side conditions — `nextLevel_gt` shows it exceeds every
    level in `ctx`, so a freshly pushed entry cannot collide. -/
def nextLevel (ctx : LinIdCtx) : Nat :=
  ctx.foldr (fun e acc => max e.level acc) 0 + 1

theorem nextLevel_gt (ctx : LinIdCtx) : ∀ e ∈ ctx, e.level < ctx.nextLevel := by
  induction ctx with
  | nil => intro e he; cases he
  | cons head tail ih =>
    intro e he
    simp only [nextLevel, List.foldr_cons]
    rcases List.mem_cons.mp he with rfl | he'
    · omega
    · have h1 := ih e he'
      simp only [nextLevel] at h1
      omega

theorem nextLevel_pos (ctx : LinIdCtx) : 0 < ctx.nextLevel := by
  simp only [nextLevel]
  omega

/-- Unrolling: pushing `a` takes the fresh level to `max (a.level + 1) (nextLevel l)`. -/
theorem nextLevel_cons (a : LinIdEntry) (l : LinIdCtx) :
    nextLevel (a :: l) = max (a.level + 1) (nextLevel l) := by
  simp only [nextLevel, List.foldr_cons]
  omega

/-! ## Construction -/

/-- Push a binding, assigning it a fresh level. -/
def pushId (ctx : LinIdCtx) (τ : Typ) (u : Usage) : LinIdCtx :=
  LinIdEntry.mk τ u ctx.nextLevel :: ctx

/-- Drop the `n` most recently bound entries (positional, as in `LinCtx.drop`). -/
abbrev drop (ctx : LinIdCtx) (n : Nat) : LinIdCtx := List.drop n ctx

/-! ## Keyed Erasure -/

/-- Erase every entry bound at level `k`.

    In a level-distinct context this removes at most one entry — the binding
    identified by `k`, wherever it currently sits. Idempotent by construction. -/
def eraseBinding (k : Nat) (ctx : LinIdCtx) : LinIdCtx :=
  ctx.filter (fun e => !(e.level == k))

/-- Erasing a level absent from the context is the identity. -/
theorem eraseBinding_of_not_mem (ctx : LinIdCtx) (k : Nat)
    (h : ∀ e ∈ ctx, e.level ≠ k) : eraseBinding k ctx = ctx := by
  induction ctx with
  | nil => rfl
  | cons head tail ih =>
    have h1 : head.level ≠ k := h head List.mem_cons_self
    have h2 : ∀ e ∈ tail, e.level ≠ k := fun e he => h e (List.mem_cons_of_mem head he)
    have hc : (!(head.level == k)) = true := by simp [h1]
    rw [eraseBinding, List.filter_cons, hc]
    simp only [if_true]
    exact congrArg _ (ih h2)

/-- **Idempotent.** The double-erase that arises when an outer substitution
    crosses an inner `let` collapses instead of removing a second, unrelated
    entry. -/
theorem eraseBinding_idempotent (ctx : LinIdCtx) (k : Nat) :
    eraseBinding k (eraseBinding k ctx) = eraseBinding k ctx := by
  simp only [eraseBinding, List.filter_filter]
  congr 1
  funext e
  cases hc : (e.level == k) <;> simp

/-- **Commuting.** Erasures at any two levels commute: an entry survives both
    applications iff its level differs from both. -/
theorem eraseBinding_comm (ctx : LinIdCtx) (j k : Nat) :
    eraseBinding j (eraseBinding k ctx) = eraseBinding k (eraseBinding j ctx) := by
  simp only [eraseBinding, List.filter_filter]
  congr 1
  funext e
  cases hj : (e.level == j) <;> cases hk : (e.level == k) <;> simp

/-- The collapse the substitution lemma needs: erasing `k`, then `j`, then `k`
    again equals erasing `k` then `j`. This is what lets an outer substitution
    crossing an inner `let` close, instead of removing an unrelated entry. -/
theorem eraseBinding_triple (ctx : LinIdCtx) (j k : Nat) :
    eraseBinding j (eraseBinding k (eraseBinding j ctx))
      = eraseBinding j (eraseBinding k ctx) := by
  rw [eraseBinding_comm, eraseBinding_idempotent, eraseBinding_comm]

/-! ## Interaction with `pushId` -/

/-- Erasing a freshly pushed binder's own level restores the context: a `let`
    that pushes a binder and consumes it exactly once nets out to nothing. -/
theorem eraseBinding_top (ctx : LinIdCtx) (τ : Typ) (u : Usage) :
    eraseBinding ctx.nextLevel (pushId ctx τ u) = ctx := by
  have hne : ∀ e ∈ ctx, e.level ≠ ctx.nextLevel := fun e he =>
    Nat.ne_of_lt (nextLevel_gt ctx e he)
  rw [eraseBinding, pushId, List.filter_cons, if_neg (by simp)]
  exact eraseBinding_of_not_mem ctx ctx.nextLevel hne

/-! ## Projections -/

/-- Type projection, mirroring `LinCtx.types`. -/
def types (ctx : LinIdCtx) : List Typ :=
  ctx.map LinIdEntry.typ

theorem types_length (ctx : LinIdCtx) : (types ctx).length = ctx.length := by
  simp [types]

/-- Erasure never grows the context. -/
theorem length_eraseBinding (ctx : LinIdCtx) (k : Nat) :
    (eraseBinding k ctx).length ≤ ctx.length := by
  exact List.length_filter_le _ ctx

/-! ## Level Distinctness -/

/-- A context has distinct levels when no two entries share one. `pushId`
    preserves this, and under distinctness an erasure removes exactly one
    entry (or none, if the level is absent). -/
def DistinctLevels : LinIdCtx → Prop
  | [] => True
  | e :: rest => (∀ e' ∈ rest, e'.level ≠ e.level) ∧ DistinctLevels rest

theorem distinct_pushId (ctx : LinIdCtx) (τ : Typ) (u : Usage)
    (h : DistinctLevels ctx) : DistinctLevels (pushId ctx τ u) := by
  refine ⟨fun e' he' hEq => ?_, h⟩
  have hlt := nextLevel_gt ctx e' he'
  exact Nat.ne_of_lt hlt hEq

/-- Under distinctness, erasing a level that is present removes exactly one
    entry. -/
theorem eraseBinding_length_distinct (ctx : LinIdCtx) (k : Nat)
    (h : DistinctLevels ctx)
    (hpresent : ctx.any (fun e => e.level == k) = true) :
    (eraseBinding k ctx).length + 1 = ctx.length := by
  cases ctx with
  | nil => simp at hpresent
  | cons head tail =>
    by_cases hhead : head.level = k
    · -- head is the k-entry; distinctness excludes every tail entry from k
      obtain ⟨hhead', _⟩ := h
      have htail : ∀ e ∈ tail, e.level ≠ k := fun e he hEq =>
        hhead' e he (hEq.trans hhead.symm)
      rw [eraseBinding, List.filter_cons]
      split
      · -- condition true: head survives — contradicts head.level = k
        next hc => simp [hhead] at hc
      · -- head erased: the tail has no k-entries, so the filter is the identity
        next hc =>
          have hfil : List.filter (fun e => !(e.level == k)) tail = tail :=
            eraseBinding_of_not_mem tail k htail
          rw [hfil]
          simp
    · -- head survives; the k-entry is somewhere in the tail
      have hpresent' : tail.any (fun e => e.level == k) = true := by
        rcases List.any_eq_true.mp hpresent with ⟨e, he, heEq⟩
        rcases List.mem_cons.mp he with rfl | he'
        · exact absurd heEq (by simp [hhead])
        · exact List.any_eq_true.mpr ⟨e, he', heEq⟩
      obtain ⟨_, hrest⟩ := h
      have hlen := eraseBinding_length_distinct tail k hrest hpresent'
      have hlen' : (List.filter (fun e => !(e.level == k)) tail).length + 1
          = tail.length := hlen
      rw [eraseBinding, List.filter_cons, if_pos (by simp [hhead]),
          List.length_cons, List.length_cons, hlen']

end LinIdCtx

end Morph
