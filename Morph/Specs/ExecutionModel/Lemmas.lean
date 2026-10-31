/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ExecutionModel.Spec

namespace Morph.Specs.ExecutionModel

/-!
## Lemmas

Lemmas for the ExecutionModel specification.
This module will contain proofs about evaluation order,
step semantics, and execution properties.
-/

theorem nat_add_comm (m n : Nat) : m + n = n + m := Nat.add_comm m n

theorem nat_mul_zero (n : Nat) : n * 0 = 0 := Nat.mul_zero n

theorem nat_zero_mul (n : Nat) : 0 * n = 0 := Nat.zero_mul n

/-! ## Depth re-audit (loop 91): substitution, environment, and step facts -/

/-- Substituting into a value is the identity. -/
theorem subst_val (v : Value) (x : String) (w : Value) :
    subst (.val v) x w = .val v := rfl

/-- Substituting for the variable itself yields the value. -/
theorem subst_var_hit (x : String) (v : Value) :
    subst (.var x) x v = .val v := by simp [subst]

/-- Substituting for a different variable leaves it alone. -/
theorem subst_var_miss :
    subst (.var "y") "x" (.vInt 1) = .var "y" := rfl

/-- A shadowing binder blocks substitution. -/
theorem subst_lam_shadow (x : String) (body : Expr) (v : Value) :
    subst (.lam x body) x v = .lam x body := by simp [subst]

/-- A shadowing `let` blocks substitution in its body but not its bound term. -/
theorem subst_letE_shadow (x : String) (e1 e2 : Expr) (v : Value) :
    subst (.letE x e1 e2) x v = .letE x (subst e1 x v) e2 := by
  simp [subst]

/-- Lookup finds the binding. -/
theorem lookup_hit (v : Value) :
    Env.lookup [("x", v)] "x" = some v := rfl

/-- Lookup misses anything unbound. -/
theorem lookup_miss (v : Value) :
    Env.lookup [("x", v)] "y" = none := rfl

/-- Extending shadows: the newest binding wins. -/
theorem extend_shadows (v w : Value) :
    Env.lookup (Env.extend [("x", v)] "x" w) "x" = some w := rfl

/-- Only `stuck` is non-terminal. -/
theorem isTerminal_normal (v : Value) :
    StepResult.isTerminal (.normal v) = true := rfl

theorem isTerminal_error (m : String) :
    StepResult.isTerminal (.error m) = true := rfl

theorem isTerminal_stuck (e : Expr) :
    StepResult.isTerminal (.stuck e) = false := rfl

/-- Counting normals in a trace. -/
theorem normalCount_example :
    Trace.normalCount [.normal .vUnit, .stuck (.val .vUnit), .normal (.vInt 1)]
      = 2 := rfl

theorem normalCount_empty : Trace.normalCount [] = 0 := rfl

end Morph.Specs.ExecutionModel
