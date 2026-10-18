/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ExecutionMachine.Spec

/-!
# Worked examples: the machine, computed

`step` is a total function, so every state has a next state and the machine can
never be stuck. These examples compute the steps.
-/

namespace Morph.Specs.ExecutionMachine

open Morph.Syntax Morph.Specs.SubstTheory Morph.Core

/-- A literal is already a machine value. -/
example : (step ⟨.lit (.int 7), [], []⟩).ctrl = .lit (.int 7) := rfl

/-- The final state of a literal program reads its denotation off the state. -/
example : (⟨.lit (.int 7), [], []⟩ : State).final = some (.int 7) := rfl

/-- A closed lambda is a final state: its value is the closure. -/
example : (⟨.lam 1 (.bvar 0), [], []⟩ : State).final = some (.closure (.bvar 0) 1) := rfl

/-- **The β-step is capture-avoiding.** Applying a closed function to any
argument yields the same function — the binder equation moves the substitution
under the binder, and loop 5's no-capture theorem then leaves the body untouched.
The same two lemmas, applied by hand. -/
example (w : Expr) : subst' 0 (.lam 1 (.bvar 0)) w = .lam 1 (.bvar 0) :=
  beta_identity (.bvar 0) w (by simp [Scoped])

/-- And the machine's β-rule uses exactly that substitution. -/
example : (step ⟨.app (.lam 1 (.bvar 0)) [.lit (.int 3)],
    [], [Frame.arg (.lam 1 (.bvar 0)) [("y", .int 3)] "y"]⟩).ctrl
    = subst' 0 (.bvar 0) (.lit (.int 3)) := rfl

/-- Iteration is fuel-bounded, not `partial`: fuel 0 returns the state itself. -/
example : run 0 ⟨.lit (.int 1), [], []⟩ = ⟨.lit (.int 1), [], []⟩ := rfl

example : (run 3 ⟨.lit (.int 1), [], []⟩).ctrl = .lit (.int 1) := rfl

end Morph.Specs.ExecutionMachine
