/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MachineRelation.Lemmas
import Morph.Specs.ExecutionMachine.Spec

/-!
# Worked examples: the two β-rules compute the same term

`Morph/Semantics.lean`'s `app_lam` uses `substAll args.reverse body`; the CEK
machine uses `subst' 0 body v`. These examples compute both and check they agree.
-/

namespace Morph.Specs.MachineRelation

open Morph.Syntax Morph.Core Morph.Semantics

/-- **The two β-rules compute the same term.** The left is what the CEK machine's
β-step produces; the right is what `Morph/Semantics.lean`'s `app_lam` reaches
(`args = [3]`, `n = 1`, hence `args.reverse = [3]`). -/
example : subst' 0 (.bvar 0) (.lit (.int 3)) = substAll [(.lit (.int 3))] (.bvar 0) :=
  (substAll_single 0 (.lit (.int 3)) (.bvar 0)).symm

/-- And both compute the argument, as β-reduction should. -/
example : subst' 0 (.bvar 0) (.lit (.int 3)) = .lit (.int 3) := by
  simp [subst', liftUnder, lift]

/-- The theorem, applied at offset 0. -/
example : substAll [(.lit (.int 3))] (.bvar 0) = .lit (.int 3) := by
  simp [substAll', subst', liftUnder, lift]

/-- And at a non-zero offset, which is what happens under a binder — the case a
weaker "offset 0 only" statement would miss. -/
example (e : Expr) : substAll' 1 [(.lit (.int 3))] e = subst' 1 e (.lit (.int 3)) :=
  substAll_single 1 (.lit (.int 3)) e

/-- Under a lambda, both raise the offset by the arity and still agree. -/
example : substAll' 0 [.lit (.int 3)] (.lam 1 (.bvar 1)) =
    subst' 0 (.lam 1 (.bvar 1)) (.lit (.int 3)) :=
  substAll_single 0 (.lit (.int 3)) (.lam 1 (.bvar 1))

/-! ### The step-level bridge (loop 47) -/

/-- The shipped β-rule at one argument lands on the machine's substitution. -/
example (σ : Store) (body v : Expr) :
    Step σ (.app (.lam 1 body) [v]) σ (subst body v) :=
  Step.app_lam_one

/-- Concretely: `(λx. x) 3 → 3` in the shipped relation. -/
example :
    Step Store.empty (.app (.lam 1 (.bvar 0)) [.lit (.int 3)]) Store.empty
      (.lit (.int 3)) := by
  have h := Step.app_lam_one (σ := Store.empty) (body := .bvar 0) (v := .lit (.int 3))
  simpa [subst, subst', liftUnder, lift] using h

/-- The same, phrased with the arity as a variable and the equation `n = 1`. -/
example (σ : Store) (n : Nat) (body v : Expr) (hn : n = 1) :
    Step σ (.app (.lam n body) [v]) σ (subst body v) :=
  Step.app_lam_of_length_one hn

end Morph.Specs.MachineRelation
