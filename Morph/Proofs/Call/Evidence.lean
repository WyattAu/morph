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
      .call (some 3) "add" [2, 1]], .return_ 3⟩],
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

/-! ## The other call positions

The return-position pin never touches the `varDecl`/`assign`-over-`.app`
arms (register threading through `lowerArgs` plus the fresh destination,
and `updAssoc` re-pointing). These two programs pin them the same way:
golden, oracle, executor. -/

/-- A second use-site id, shared by the two programs below. -/
def xId : HIR.Id := ⟨3, "x"⟩

/-- The callee as an environment value (what `app` looks up). -/
def addLam : HIR.Expr :=
  .lam [⟨1, "a"⟩, ⟨2, "b"⟩] addFunc.body

/-- `varDecl`-call: bind the result, add ten. -/
def addVarProg : Morph.HIRFunc.CallProg :=
  ⟨[addFunc],
    [.varDecl xId .intType (.app addId [.lit (.int 1), .lit (.int 2)]),
     .returnStmt (.binop .add (.var xId) (.lit (.int 10)))]⟩

/-- The `varDecl`-call entry: the call writes register 3, which the
trailing addition reads. -/
def addVarMainMIR : MIR.Func :=
  ⟨"main", [],
    [⟨0, [.const 0 .unit, .const 1 (.int 1), .const 2 (.int 2),
      .call (some 3) "add" [2, 1], .const 4 (.int 10),
      .binop 5 .add 3 4 .intType], .return_ 5⟩],
    0, .unitType⟩

example : lowerCallProg addVarProg == some ⟨[addVarMainMIR, addMIR]⟩ := by
  native_decide

example : (runHIRStmts 256 [(addId, addLam)]
    [.varDecl xId .intType (.app addId [.lit (.int 1), .lit (.int 2)]),
     .returnStmt (.binop .add (.var xId) (.lit (.int 10)))]
    (.value (.lit .unit))).1 = .returned (.lit (.int 13)) := by
  rfl

example : (lowerCallProg addVarProg).bind (fun p =>
    p.funcs[0]?.bind fun f =>
      execFuncCall p 5 f ⟨fun _ => none, Store.empty⟩) ==
    some (.int 13) := by
  native_decide

/-- `assign`-call: declare, rebind through the call, read back. -/
def addAssignProg : Morph.HIRFunc.CallProg :=
  ⟨[addFunc],
    [.varDecl xId .intType (.lit (.int 0)),
     .assign xId (.app addId [.lit (.int 3), .lit (.int 4)]),
     .returnStmt (.var xId)]⟩

/-- The `assign`-call entry: the call writes register 4 over the initial 0. -/
def addAssignMainMIR : MIR.Func :=
  ⟨"main", [],
    [⟨0, [.const 0 .unit, .const 1 (.int 0), .const 2 (.int 3),
      .const 3 (.int 4), .call (some 4) "add" [3, 2]], .return_ 4⟩],
    0, .unitType⟩

example : lowerCallProg addAssignProg == some ⟨[addAssignMainMIR, addMIR]⟩ := by
  native_decide

example : (runHIRStmts 256 [(addId, addLam)]
    [.varDecl xId .intType (.lit (.int 0)),
     .assign xId (.app addId [.lit (.int 3), .lit (.int 4)]),
     .returnStmt (.var xId)]
    (.value (.lit .unit))).1 = .returned (.lit (.int 7)) := by
  rfl

example : (lowerCallProg addAssignProg).bind (fun p =>
    p.funcs[0]?.bind fun f =>
      execFuncCall p 5 f ⟨fun _ => none, Store.empty⟩) ==
    some (.int 7) := by
  native_decide

/-! ## The guards

The three refusals the fragment promises: arity is checked up front (the
executor would fail it via `bindCallArgs`), unknown names resolve to
`none`, and bare call statements stay refused. -/

/-- Arity mismatch refuses. -/
example : lowerCallProg
    ⟨[addFunc], [.returnStmt (.app addId [.lit (.int 1)])]⟩ == none := by
  native_decide

/-- Unknown function refuses. -/
example : lowerCallProg ⟨[addFunc],
    [.returnStmt (.app ⟨9, "nope"⟩ [.lit (.int 1), .lit (.int 2)])]⟩ ==
    none := by
  native_decide

/-- Bare call statements refuse (the value would be lost). -/
example : lowerCallProg ⟨[addFunc],
    [.exprStmt (.app addId [.lit (.int 1), .lit (.int 2)])]⟩ == none := by
  native_decide

/-! ## Argument order is load-bearing

`add` commutes, so the three pins above cannot tell whether actuals
arrive in order. They do not: HIR params list innermost-first, so the
call delivers them back-to-front (`vs.reverse` in `lowerCallStmts`).
`sub` (outer minus inner) distinguishes the orders — with actuals in
call order the executor would compute `3 - 5` where the oracle computes
`5 - 3`. -/

/-- Callee name and parameter ids (`i` innermost, `o` outermost). -/
def subId : HIR.Id := ⟨4, "sub"⟩

/-- `sub(o, i) = o - i`: straight-line, call-free, non-commutative. -/
def subFunc : Morph.HIRFunc.Func :=
  ⟨subId, [⟨6, "i"⟩, ⟨5, "o"⟩],
    .binop .sub (.var ⟨5, "o"⟩) (.var ⟨6, "i"⟩)⟩

/-- The callee as an environment value. -/
def subLam : HIR.Expr :=
  .lam [⟨6, "i"⟩, ⟨5, "o"⟩] subFunc.body

/-- The pin program: `main` returns `sub(5, 3)`. -/
def subProg : Morph.HIRFunc.CallProg :=
  ⟨[subFunc],
    [.returnStmt (.app subId [.lit (.int 5), .lit (.int 3)])]⟩

/-- The lowered callee: `i` on register 1, `o` on register 2. -/
def subMIR : MIR.Func :=
  ⟨"sub", [(1, .unitType), (2, .unitType)],
    [⟨0, [.const 0 .unit, .binop 3 .sub 2 1 .intType], .return_ 3⟩],
    0, .unitType⟩

/-- The lowered entry: actuals delivered back-to-front. -/
def subMainMIR : MIR.Func :=
  ⟨"main", [],
    [⟨0, [.const 0 .unit, .const 1 (.int 5), .const 2 (.int 3),
      .call (some 3) "sub" [2, 1]], .return_ 3⟩],
    0, .unitType⟩

example : lowerCallProg subProg == some ⟨[subMainMIR, subMIR]⟩ := by
  native_decide

example : (runHIRStmts 256 [(subId, subLam)]
    [.returnStmt (.app subId [.lit (.int 5), .lit (.int 3)])]
    (.value (.lit .unit))).1 = .returned (.lit (.int 2)) := by
  rfl

example : (lowerCallProg subProg).bind (fun p =>
    p.funcs[0]?.bind fun f =>
      execFuncCall p 5 f ⟨fun _ => none, Store.empty⟩) ==
    some (.int 2) := by
  native_decide

end Morph.Proofs.Call
