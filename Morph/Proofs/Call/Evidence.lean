/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRFunc
import Morph.Frontend.HIRInterp

/-!
# Call-fragment evidence (Stage C item C8, end-to-end pin)

Loop 186. One concrete two-function program through the whole C8 slice,
closed by computation — the pin the design proposal's step 4 calls for,
before any general C8c theorem:

- `addProg`: `add(a, b) = a + b` plus a `main` that returns `add(1, 2)`.
- the callee body is call-free (`FuncOk`, by `native_decide`);
- `lowerCallProg` produces exactly the expected two-function MIR program
  (the `"main"` entry plus the single-block `"add"`), by `native_decide`;
- the HIR oracle (`runHIRStmts` with `add` bound to its `lam` in the
  environment) returns `3`, by `rfl` — the Branch-leaf idiom for oracle
  runs (`runHIRProgram ... = ... := rfl`), with the environment written
  out since `returnStmt` leaves it unchanged;
- the MIR executor (`execFuncCall` on the lowered `"main"`) returns `3`,
  by `native_decide` — the same `.bind ... == some v` shape as the Branch
  `execFuncFrom` pins.

The two `3`s are the agreement, pinned before it is proved. `main` calls
in return position (not bare `exprStmt`), since a bare call statement is
refused: the oracle keeps the return value as the statement value while
`MIR.call` with `dst = none` would discard it.
-/

namespace Morph.Proofs.Call

open Morph.HIR Morph.Core Morph.HIRFunc Morph.Frontend.HIRInterp Morph.MIR
  Morph.Frontend.HIREval

/-- Callee name, shared by the HIR `app` and the lowered `MIR.call`. -/
def addId : HIR.Id := ⟨0, "add"⟩

/-- `add(a, b) = a + b`: straight-line, call-free. -/
def addFunc : Morph.HIRFunc.Func :=
  ⟨addId, [⟨1, "a"⟩, ⟨2, "b"⟩],
    .binop .add (.var ⟨1, "a"⟩) (.var ⟨2, "b"⟩)⟩

/-- The pin program: `main` returns `add(1, 2)`. -/
def addProg : Morph.HIRFunc.CallProg :=
  ⟨[addFunc],
    [.returnStmt (.app addId [.lit (.int 1), .lit (.int 2)])]⟩

/-- The callee body is call-free. -/
example : FuncOk addFunc := by
  unfold FuncOk
  native_decide

/-- The lowered callee: parameters on registers 1–2, single block. -/
def addMIR : MIR.Func :=
  ⟨"add", [(1, .unitType), (2, .unitType)],
    [⟨0, [.const 0 .unit, .binop 3 .add 1 2 .intType], .return_ 3⟩],
    0, .unitType⟩

/-- The lowered entry: constants for the actuals, one `.call`, return. -/
def addMainMIR : MIR.Func :=
  ⟨"main", [],
    [⟨0, [.const 0 .unit, .const 1 (.int 1), .const 2 (.int 2),
      .call (some 3) "add" [1, 2]], .return_ 3⟩],
    0, .unitType⟩

/-- `lowerCallProg` produces exactly the two-function program. -/
example : lowerCallProg addProg == some ⟨[addMainMIR, addMIR]⟩ := by
  native_decide

/-- The HIR oracle: `add` bound to its `lam`, the call returns `3`. -/
example : (runHIRStmts 256
    [(addId, .lam [⟨1, "a"⟩, ⟨2, "b"⟩]
      (.binop .add (.var ⟨1, "a"⟩) (.var ⟨2, "b"⟩)))]
    [.returnStmt (.app addId [.lit (.int 1), .lit (.int 2)])]
    (.value (.lit .unit))).1 = .returned (.lit (.int 3)) := by
  rfl

/-- The MIR executor on the lowered entry returns `3`. -/
example : (lowerCallProg addProg).bind (fun p =>
    p.funcs[0]?.bind fun f =>
      execFuncCall p 5 f ⟨fun _ => none, Store.empty⟩) ==
    some (.int 3) := by
  native_decide

end Morph.Proofs.Call
