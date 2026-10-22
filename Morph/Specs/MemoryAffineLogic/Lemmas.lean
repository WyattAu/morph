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

**What is not proved.** The eleven `True` properties are about *typing* and
*copying*: `spec_affine_typing` needs a typing judgment for expressions, and
`affine_types_no_copy` / `copy_requires_affine` need a copy operation. The module
has neither, so those claims are unstateable here for the same reason the
concurrency module's message-passing claims were (research loop 20): the
operation they constrain does not exist. They are named in §5 of the spec.
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

end Morph.Specs.MemoryAffineLogic
