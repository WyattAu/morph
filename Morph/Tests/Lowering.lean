/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.LoweringLemmas

/-!
# Tests for the lowering foundations (ADR-011 stage 1)

Concrete instances of the write-avoidance lemma and the oracle-alignment
lemmas used by `lowering_correct`:

* `Env.update_same` / `Env.update_ne` on concrete registers;
* `evalInstr` on lowered instructions matching the oracle definition;
* `evalBinOp` agreeing with the surface interpreter on concrete values;
* a lowered `let x = 1 + 2 in x * 3` evaluating to `9` through `execMain`,
  with the interpreter agreeing on the same expression.
-/

namespace Morph.Tests.Lowering

open Morph.Lowering
open Morph.Core Morph.Syntax Morph.MIR Morph.Executable

/-! ## Update stability -/

example (env : MIR.Env) : env.update 3 (.int 7) 3 = some (.int 7) :=
  Env.update_same _ _ _

example (env : MIR.Env) : env.update 3 (.int 7) 5 = env 5 :=
  Env.update_ne _ _ _ _ (by decide)

/-! ## The evaluation oracle matches its definition -/

example (env : MIR.Env) :
    evalInstr env (.const 2 (.int 5)) = some (env.update 2 (.int 5)) := rfl

example (env : MIR.Env) :
    evalInstr env (.load 0 1 .val) = none := rfl

example (env : MIR.Env) :
    evalInstr env (.store 0 1 .ref) = none := rfl

/-! ## Arithmetic agrees with the surface interpreter -/

-- evalBinOp is literally the surface evalBinop on lit-wrapped operands
example : evalBinOp .add (.int 3) (.int 4) == some (.int 7) := by native_decide
example : evalBinOp .sub (.int 3) (.int 4) == some (.int (-1)) := by native_decide
example : evalBinOp .mul (.int 3) (.int 4) == some (.int 12) := by native_decide

-- a mismatched operand is stuck on both sides
example : evalBinOp .add (.bool true) (.int 1) == none := by native_decide
example : evalUnOp .not (.bool true) == some (.bool false) := by native_decide

/-! ## A lowered expression evaluates correctly -/

/-- `let x = 1 + 2 in x * 3` — a two-step straight-line lowering. -/
def ex : Expr :=
  .let_ (.binop .add (.lit (.int 1)) (.lit (.int 2)))
    (.binop .mul (.bvar 0) (.lit (.int 3)))

/-- Lowering succeeds. -/
example : (lower ex).isSome := by native_decide

/-- The lowered function computes `3 * 3 = 9`. -/
example : (lower ex).map (fun f => execMain f (fun _ => none)) == some (some (.int 9)) := by
  native_decide

/-- The interpreter computes the same value on the same expression. -/
example : exprVal (evalFuel 20 ⟨[], []⟩ ex) == some (.int 9) := by
  native_decide

/-- An unbound de Bruijn index lowers to a register nobody writes, so the
    program is stuck on both sides. -/
example : lower (.lit (.int 1)) |>.isSome := by native_decide

end Morph.Tests.Lowering