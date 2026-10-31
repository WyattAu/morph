/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIR

/-!
# Tests for HIR→MIR lowering (Sprints 11/13)

Concrete instances exercising the straight-line lowering and its
correctness statements:

* `1 + 2` lowers to two `const`s and a `binop` with the exact registers;
* `let x = 1 + 2; x` lowers to a `some` function whose `WF` check passes;
* assignment threads the new register through the environment;
* `break`/`whileLoop` leave the straight-line fragment (`none`).
-/

namespace Morph.Tests.HIRToMIR

open Morph.HIRToMIR
open Morph.HIR
open Morph.MIR
open Morph.Core (Typ Value Operator)

/-! ## Expression lowering: exact shape -/

/-- `1 + 2` at the HIR level. -/
def eAdd : HIR.Expr :=
  .binop .add (.lit (.int 1)) (.lit (.int 2))

/-- Literals allocate in order; the `binop` takes the next register. -/
example : lowerExpr [] 0 eAdd =
    some (2, [.const 0 (.int 1), .const 1 (.int 2),
      .binop 2 .add 0 1 .intType], 3) := by rfl

/-- An unbound variable reads nothing: `none`, not a stuck register. -/
example : lowerExpr [] 0 (.var ⟨0, "x"⟩) = none := by rfl

/-! ## Statement lowering: exact program shape -/

/-- `let x = 1 + 2; x`. -/
def progLetAdd : HIR.Program :=
  { stmts :=
    [.varDecl ⟨0, "x"⟩ .intType eAdd,
     .exprStmt (.var ⟨0, "x"⟩)] }

/-- The whole program lowers to one block returning register 3 (register `0`
is the pre-emitted `unit`, user code allocates from `1`). -/
example : lowerProgram progLetAdd =
    some ⟨"main", [],
      [⟨0, [.const 0 .unit, .const 1 (.int 1), .const 2 (.int 2),
        .binop 3 .add 1 2 .intType], .return_ 3⟩],
      0, .unitType⟩ := by rfl

/-- ...which is a well-formed function. -/
example : (match lowerProgram progLetAdd with
  | some f => WF f
  | none => false) = true := by decide

/-! ## Assignment threads the new register -/

/-- `let x = 1; x = 2; x` evaluates to `2`. -/
def progAssign : HIR.Program :=
  { stmts :=
    [.varDecl ⟨0, "x"⟩ .intType (.lit (.int 1)),
     .assign ⟨0, "x"⟩ (.lit (.int 2)),
     .exprStmt (.var ⟨0, "x"⟩)] }

example : (lowerProgram progAssign).isSome = true := by decide

example : (match lowerProgram progAssign with
  | some f => WF f
  | none => false) = true := by decide

/-! ## Control flow leaves the straight-line fragment -/

/-- `break` has no straight-line lowering. -/
example : lowerStmts [] 1 0 [.break] = none := by rfl

/-- `whileLoop` has no straight-line lowering. -/
example : lowerStmts [] 1 0 [.whileLoop (.lit (.bool true)) [.nop]] = none := by
  rfl

end Morph.Tests.HIRToMIR
