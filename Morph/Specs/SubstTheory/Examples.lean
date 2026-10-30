/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SubstTheory.Lemmas

/-!
# Worked examples: substitution computes β-reduction

The no-capture theorem is only worth having if substitution computes what it is
supposed to. These examples check the actual reduction behaviour on terms that
exercise the binder cases POPLmark cares about: nested lambdas, `let`,
multi-parameter arrows, and pattern-bound match arms.

**The index offset.** `lam n` adds `n` binders, so a reference to the `k`-th
variable of the enclosing context appears as `.bvar (k + n)` in the body.
Substitution at the outer index `k` therefore hits body index `k + n`.
-/

namespace Morph.Specs.SubstTheory

open Morph.Syntax Morph.Core

/-- `fun x -> x` applied to its own parameter index: the hitting case fires at
body index 0 and the substitute is lifted by the binder depth (0 here). -/
example : subst' 0 (.lam 1 (.bvar 0)) (.bvar 0) = .lam 1 (.bvar 0) := by
  simp [subst', liftUnder, lift]

/-- A reference to the enclosing context inside a two-parameter arrow is body
index 3 (`k + n` with `k = 1`, `n = 2`). Substituting the outer variable lifts
the substitute by 3, so the reference still points at the right slot: this is
the step that prevents capture. -/
example : subst' 1 (.lam 2 (.bvar 3)) (.bvar 0) = .lam 2 (.bvar 3) := by
  simp [subst', liftUnder, lift]

/-- The same term, but referring to the arrow's own second parameter (body index
1) rather than the enclosing context: substitution at the outer index leaves it
alone. -/
example : subst' 1 (.lam 2 (.bvar 1)) (.bvar 0) = .lam 2 (.bvar 1) := by
  simp [subst', liftUnder, lift]

/-- A `let` binds one variable, so its body sees the enclosing context at index
1. Substituting index 0 lifts the substitute by 1. -/
example : subst' 0 (.let_ (.bvar 0) (.bvar 1)) (.bvar 0) = .let_ (.bvar 0) (.bvar 1) := by
  simp [subst', liftUnder, lift]

/-- A `match` pattern binds one variable, so an arm body is substituted one
level below the scrutinee; a reference to the enclosing context is arm index 1.
Here the substitute (lifted past the binder) coincides with the original. -/
example : substArms 0 (.bvar 0) [((.some_ (.var_ "x")), .bvar 1)] =
    [((.some_ (.var_ "x")), .bvar 1)] := by
  simp [substArms, subst', liftUnder, lift, patBindCount]

/-- Substitution never touches a scoped term, whatever the substitute: the
scoping hypothesis is the whole content of `subst_above`. -/
example (n : Nat) (v : Expr) (h : n < 3) : subst' 3 (.bvar n) v = .bvar n :=
  subst_above 3 (.bvar n) v (by simpa [Scoped] using h)

/-- No capture survives a lambda: `fun x -> bvar 0` is scoped at 1. -/
example (v : Expr) : subst' 1 (.lam 1 (.bvar 0)) v = .lam 1 (.bvar 0) :=
  subst_above 1 (.lam 1 (.bvar 0)) v (by simp [Scoped])

/-- And survives `let`, whose body is scoped one level deeper. -/
example (v : Expr) : subst' 1 (.let_ (.bvar 0) (.bvar 0)) v = .let_ (.bvar 0) (.bvar 0) :=
  subst_above 1 (.let_ (.bvar 0) (.bvar 0)) v (by simp [Scoped])

end Morph.Specs.SubstTheory
