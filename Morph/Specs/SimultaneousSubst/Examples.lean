/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SimultaneousSubst.Spec

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

end Morph.Specs.SimultaneousSubst
