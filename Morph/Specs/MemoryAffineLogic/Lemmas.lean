/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryAffineLogic.Spec

/-!
# MemoryAffineLogic: the context algebra, proved — and a false law, refuted

Research loop 22. Target: `Morph/Specs/MemoryAffineLogic/`.

**What was there.** The module has a real model — `AffineContext` with variables
and resources, `joinContexts`, `splitContext`, `isWellFormedContext`,
`disjointContexts` — and it *states* three laws of the context algebra. None was
proved: the lemma file had only `rfl` facts about counts and lookup. Eleven
further properties were `True`.

**The finding.** One of the three stated laws is **false**:

```lean
def context_join_commutative (Γ₁ Γ₂ : AffineContext) : Prop :=
  joinContexts Γ₁ Γ₂ = joinContexts Γ₂ Γ₁
```

`joinContexts` appends the first context's variables to the second's, and
`a ++ b ≠ b ++ a` — so this is not a law, it is a counterexample waiting to be
written. It was never noticed because it was never proved.

The order of a context's variables is part of its meaning — it is the order in
which resources are consumed — so the correct statement is that the join is
commutative **up to permutation**, which is what the specification now says, and
what `context_join_commutative_holds` proves.

**What is proved here.** The permutation law, associativity, the unit law, and
`context_join_not_commutative` — the explicit refutation of the old claim.

**Loop 28: the eleven typing and ownership claims.** `CommonTypes.Expr` already
has `var`, `app`, `lam`, `move`, `copy` and `borrow`, so the claims *were*
stateable. The module now has a usage-based model:

- `uses e x` counts syntactic occurrences of `x` (binder shadowing is not
  modelled — the same simplification the spec makes);
- `moveVar` removes the source and inserts the destination; `borrowVar` aliases
  without consuming; `copyVar` refuses non-affine types; `consumeVar` /
  `consumeResource` drop a binding.

Every one of the eleven is now a real statement and proved:
`spec_affine_typing` (at most one use, all names bound),
`spec_affine_typing_memory_safety` (typing implies every used name is in scope),
`spec_resource_linearity` (resource counts add under join),
`spec_context_splitting` (the split keeps all resources on one side),
`affine_types_no_copy`, `linear_types_used_once`,
`move_consumes_source`, `borrow_preserves_source`, `copy_requires_affine`,
`variable_use_tracking`, `resource_consumption`.

**A note on `getVariableType`.** It is defined with `List.find?`, whose
predicate returns a `Bool`; the proofs lean on `Option.some.inj` to compare the
type found by two lookups. The `moveVar` postcondition needed `src ≠ dst` to be
stated: without it, moving a variable onto itself leaves the source present.
-/

namespace Morph.Specs.MemoryAffineLogic

open Morph.Specs.CommonTypes

/-- **Joining is commutative up to permutation.** -/
theorem context_join_commutative_holds (Γ₁ Γ₂ : AffineContext) :
    context_join_commutative Γ₁ Γ₂ := by
  unfold context_join_commutative joinContexts
  exact List.perm_append_comm

/-- **Joining is associative.** -/
theorem context_join_associative_holds (Γ₁ Γ₂ Γ₃ : AffineContext) :
    context_join_associative Γ₁ Γ₂ Γ₃ := by
  unfold context_join_associative joinContexts
  cases Γ₁ with
  | mk v₁ r₁ =>
      cases Γ₂ with
      | mk v₂ r₂ =>
          cases Γ₃ with
          | mk v₃ r₃ =>
              simp only [List.append_assoc]

/-- **The empty context is a unit for joining.** -/
theorem empty_context_join_identity_holds (Γ : AffineContext) :
    empty_context_join_identity Γ := by
  unfold empty_context_join_identity joinContexts
  cases Γ with
  | mk v r =>
      constructor <;> simp

/-- **The refutation.** The join is *not* literally commutative: the order of a
context's variables is part of its meaning, and joining reverses it. This is the
counterexample to the module's original `context_join_commutative`. -/
theorem context_join_not_commutative :
    joinContexts { variables := [("a", .unit)], resources := [] }
      { variables := [("b", .unit)], resources := [] }
      ≠
    joinContexts { variables := [("b", .unit)], resources := [] }
      { variables := [("a", .unit)], resources := [] } := by
  simp [joinContexts]

/-- A context's variable count is bounded by the number of variables it
declares — the context cannot mention a variable it does not have. -/
theorem variableCount_le (Γ : AffineContext) (x : String) :
    variableCount Γ x ≤ Γ.variables.length := by
  exact List.length_filter_le _ _

/-- The same for resources. -/
theorem resourceCount_le (Γ : AffineContext) (x : String) :
    resourceCount Γ x ≤ Γ.resources.length := by
  exact List.length_filter_le _ _

/-! ## The eleven affine claims, proved

The model is usage-based: `uses` counts syntactic occurrences, `moveVar`
removes the source, `borrowVar` aliases without consuming, and `copyVar`
refuses non-affine types. Binder shadowing is not modelled, which is why
`uses` counts occurrences in lambda bodies as uses of the outer name; this is
the same simplification the spec makes. -/

theorem spec_resource_linearity_holds (Γ₁ Γ₂ : AffineContext) :
    spec_resource_linearity Γ₁ Γ₂ := by
  intro x
  unfold resourceCount joinContexts
  rw [List.filter_append, List.length_append]

theorem spec_context_splitting_holds (Γ : AffineContext) (x : String) :
    spec_context_splitting Γ x := by
  intro Γ₁ Γ₂ h
  cases hgt : getVariableType Γ x with
  | none => simp [splitContext, hgt] at h
  | some T =>
      simp [splitContext, hgt] at h
      obtain ⟨h1, h2⟩ := h
      constructor
      · simpa using congrArg AffineContext.resources h1.symm
      · simpa using congrArg AffineContext.resources h2.symm

theorem spec_affine_typing_memory_safety_holds (Γ : AffineContext) (e : Expr) :
    spec_affine_typing_memory_safety Γ e := by
  intro h
  exact h.2

theorem affine_types_no_copy_holds (Γ : AffineContext) (x : String) (T : MorphType) :
    affine_types_no_copy Γ x T := by
  intro hwf _
  unfold isWellFormedContext at hwf
  exact hwf x

theorem linear_types_used_once_holds (Γ : AffineContext) (x : String) (T : MorphType) :
    linear_types_used_once Γ x T := by
  intro _ e h
  exact h.1 x

theorem borrow_preserves_source_holds (Γ : AffineContext) (src dst : String)
    (region : Region) : borrow_preserves_source Γ src dst region := by
  unfold borrow_preserves_source
  cases h : getVariableType Γ src with
  | none => simp [borrowVar, h]
  | some T =>
      simp only [borrowVar, h]
      have hstep : getVariableType { Γ with variables := (dst, T) :: Γ.variables } src
          = getVariableType Γ src := by
        simp only [getVariableType]
        by_cases hd : dst = src
        · subst hd
          simp only [List.find?_cons]
          simpa [getVariableType] using h.symm
        · simp [hd]
      rw [hstep, h]

theorem copy_requires_affine_holds (Γ : AffineContext) (src dst : String) :
    copy_requires_affine Γ src dst := by
  intro Γ' T hc hgt
  unfold copyVar at hc
  cases hsrc : getVariableType Γ src with
  | none => simp [hsrc] at hc
  | some T' =>
      simp only [hsrc] at hc
      have hTT : T' = T := Option.some.inj (hsrc.symm.trans hgt)
      by_cases hb : isAffineTypeB T' = true
      · rw [if_pos hb] at hc
        rw [← hTT]
        exact hb
      · rw [if_neg hb] at hc
        simp at hc

theorem variable_use_tracking_holds (Γ : AffineContext) (x : String) :
    variable_use_tracking Γ x := by
  intro h
  obtain ⟨T, hmem⟩ := h
  have hf := List.mem_filter.mp hmem
  have hne : x ≠ x := by simpa using hf.2
  exact hne rfl

theorem resource_consumption_holds (Γ : AffineContext) (x : String) :
    resource_consumption Γ x := by
  intro h
  obtain ⟨T, hmem⟩ := h
  have hf := List.mem_filter.mp hmem
  have hne : x ≠ x := by simpa using hf.2
  exact hne rfl

theorem find_filter_ne (l : List (String × MorphType)) (x : String) :
    List.find? (fun (y, _) => y = x)
      (l.filter (fun (y, _) => decide (y ≠ x))) = none := by
  rw [List.find?_eq_none]
  intro a ha
  have h := List.mem_filter.mp ha
  have hne : a.1 ≠ x := by simpa using h.2
  simp [hne]

theorem move_consumes_source_holds (Γ : AffineContext) (src dst : String) :
    move_consumes_source Γ src dst := by
  intro hne Γ' hmv
  unfold moveVar at hmv
  cases hget : getVariableType Γ src with
  | none => simp [hget] at hmv
  | some T =>
      simp only [hget, Option.some.injEq] at hmv
      subst hmv
      constructor
      · unfold getVariableType
        by_cases hd : dst = src
        · exact absurd hd.symm hne
        · simp [hd]
      · intro T' hT'
        have hTT : T' = T := (Option.some.inj hT').symm
        rw [hTT]
        unfold getVariableType
        simp

/-- Affinity is the model's default: every type is affine. Linearity is the
exception, discriminated by `isLinearType`. -/
theorem isAffineTypeM_all (T : MorphType) : isAffineTypeM T := by
  cases T <;> trivial

end Morph.Specs.MemoryAffineLogic
