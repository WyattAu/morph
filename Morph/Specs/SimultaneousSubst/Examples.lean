/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SimultaneousSubst.Lemmas

/-!
# Worked examples: the lifting law, computed
-/

namespace Morph.Specs.SimultaneousSubst

open Morph.Syntax Morph.Core

/-- **Substituting into a lifted term shifts it down, and only that.** The
inserted value is not hit (its indices are all above the substitution point),
so every index simply drops by one — which is exactly the lift by one fewer. -/
example (k m : Nat) (w : Expr) (v : Expr) :
    subst' (k + m) (liftUnder m (k + 1) w) v = liftUnder m k w :=
  subst_lifted k m w v

/-- At offset zero: substituting under a term whose indices are all above the
substitution point just renumbers them. -/
example (w v : Expr) : subst' 0 (lift 1 w) v = lift 0 w := by
  simpa [lift] using (subst_lifted 0 0 w v)

/-- The same, with the offset the recursion actually threads through a binder:
under a `lam`, the body is lifted at `m + n` and substituted at `k + m + n`. -/
example (k m n : Nat) (body : Expr) (v : Expr) :
    subst' (k + m + n) (liftUnder (m + n) (k + 1) body) v = liftUnder (m + n) k body := by
  rw [show k + m + n = k + (m + n) by omega]
  exact subst_lifted k (m + n) body v

/-- Concretely: a value lifted above a binder and substituted back is the same
value lifted one level less. -/
example : subst' 1 (liftUnder 1 2 (.bvar 0)) (.lit (.int 7)) = .bvar 0 := by
  simp [subst', liftUnder]

/-! ### Simultaneous = sequential, computed (loop 49)

The generic theorem is `substAll'_eq_seqSubst`; these examples check the
interesting `bvar` cases and a small term. -/

/-- The first value replaces the variable at the offset. -/
example : substAll' 0 [.lit (.int 1), .lit (.int 2)] (.bvar 0) =
    .lit (.int 1) := by
  simp [substAll', lift, liftUnder]

/-- The second value replaces the next variable. -/
example : substAll' 0 [.lit (.int 1), .lit (.int 2)] (.bvar 1) =
    .lit (.int 2) := by
  simp [substAll', lift, liftUnder]

/-- A variable above the value list is shifted down by its length — the
fallback is `n - vs.length`, not `n - k - vs.length`. -/
example : substAll' 0 [.lit (.int 1), .lit (.int 2)] (.bvar 2) =
    .bvar 0 := by
  simp [substAll', lift, liftUnder]

/-- A term with two holes and a free variable. -/
example : substAll' 0 [.lit (.int 1), .lit (.int 2)]
    (.app (.bvar 1) [.bvar 0, .bvar 2]) =
    .app (.lit (.int 2)) [.lit (.int 1), .bvar 0] := by
  simp [substAll', lift, liftUnder]

/-- Under a binder the offset moves with it. -/
example : substAll' 1 [.lit (.int 1)] (.lam 1 (.bvar 2)) =
    .lam 1 (.lit (.int 1)) := by
  simp [substAll', lift, liftUnder]

/-- The shipped offset-0 form agrees with the sequential definition. -/
example (e : Expr) :
    substAll [.lit (.int 1), .lit (.int 2)] e =
      seqSubst 0 [.lit (.int 1), .lit (.int 2)] e :=
  substAll_eq_seqSubst _ e

/-- The absorption step, at a concrete offset. -/
example (e : Expr) :
    substAll' 3 [.lit (.int 1), .lit (.int 2)] e =
      subst' 3 (substAll' 4 [.lit (.int 2)] e) (.lit (.int 1)) :=
  substAll_cons 3 (.lit (.int 1)) [.lit (.int 2)] e

end Morph.Specs.SimultaneousSubst
