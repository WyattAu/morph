/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.MIR

/-!
# Tests for the MIR data types (ADR-011 §1)

Concrete instances exercising the well-formedness checks and the pure
evaluation oracle of `Morph.MIR`:

* `x + y` with two params: `WF` holds;
* use-before-def inside a block: `wfBlockUse` rejects it;
* a `branch` CFG: `WFCFG` accepts it;
* a value defined in one block and used in another: rejected — this documents
  the SINGLE-BLOCK assumption of `wfBlockUse` (cross-block use rules come
  with the phi/dominance work of ADR-011 stage 3);
* `evalInstr` on the pure instructions (`const`/`copy`/`unop`/`binop`).
-/

namespace Morph.Tests.MIR

open Morph.MIR
open Morph.Core (Typ Capability Value)

/-! ## WF: the `x + y` example -/

/-- Block list for `fAdd`: one block, one binop, return. -/
def fAddBlocks : List Block :=
  [{ id := 0
     instrs := [.binop 2 .add 0 1 Typ.intType]
     terminator := .return_ 2 }]

/-- `fAdd(x, y) = x + y`: two params, one block, one binop, return. -/
def fAdd : Func where
  name := "add"
  params := [(0, Typ.intType), (1, Typ.intType)]
  blocks := fAddBlocks
  entry := 0
  retType := Typ.intType

example : WF fAdd = true := by decide
example : WFCFG fAdd = true := by decide
example : WFParams fAdd = true := by decide
example : wfBlockUse [0, 1] fAdd.blocks.head! = true := by decide
example : defsOf fAdd.blocks.head! = [2] := by decide
example : usesOf fAdd.blocks.head!.instrs.head! = [0, 1] := by decide

/-! ## Use-before-def inside one block is rejected -/

/-- Block list for `fUseBeforeDef`: the binop uses value 3, which is neither a
param nor defined earlier. -/
def fUseBeforeDefBlocks : List Block :=
  [{ id := 0
     instrs := [.binop 2 .add 3 0 Typ.intType]
     terminator := .return_ 2 }]

/-- Function using an undefined value inside its (only) block. -/
def fUseBeforeDef : Func where
  name := "bad"
  params := [(0, Typ.intType)]
  blocks := fUseBeforeDefBlocks
  entry := 0
  retType := Typ.intType

example : wfBlockUse [0] fUseBeforeDef.blocks.head! = false := by decide
example : WF fUseBeforeDef = false := by decide

/-! ## CFG shape: `branch` passes WFCFG -/

/-- Block list for `fMax`: cond / then / else, both arms jump to the join
point which returns `x`. -/
def fMaxBlocks : List Block :=
  [⟨0, [.binop 1 .gt 0 2 Typ.intType, .const 2 (.int 0)], .branch 1 1 2⟩,
   ⟨1, [], .goto 3⟩,
   ⟨2, [], .goto 3⟩,
   ⟨3, [], .return_ 0⟩]

/-- `x > 0 ? x : 0` shape — exercises `branch`/`goto` targets. -/
def fMax : Func where
  name := "max"
  params := [(0, Typ.intType)]
  blocks := fMaxBlocks
  entry := 0
  retType := Typ.intType

example : WFCFG fMax = true := by decide
example : blockTargets fMax.blocks[2]!.terminator = [3] := by decide
example : blockTargets fMax.blocks[0]!.terminator = [1, 2] := by decide

/-- Block list for `fDanglingTarget`: branch target 9 does not exist. -/
def fDanglingTargetBlocks : List Block :=
  [{ id := 0
     instrs := []
     terminator := .branch 0 1 9 }]

/-- A branch to a nonexistent block fails `WFCFG`. -/
def fDanglingTarget : Func where
  name := "dangling"
  params := [(0, Typ.boolType)]
  blocks := fDanglingTargetBlocks
  entry := 0
  retType := Typ.unitType

example : WFCFG fDanglingTarget = false := by decide

/-- Duplicate parameter ids fail `WFParams`. -/
def fDupParams : Func where
  name := "dup"
  params := [(0, Typ.intType), (0, Typ.intType)]
  blocks :=
    [{ id := 0
       instrs := []
       terminator := .return_ 0 }]
  entry := 0
  retType := Typ.intType

example : WFParams fDupParams = false := by decide

/-! ## The single-block assumption

Value 2 is defined in block 0 and used (without a phi) in block 1. Each block
individually passes `wfBlockUse` against *its own* defs, so block 1 fails:
cross-block use is unsound to accept before the phi/dominance machinery of
ADR-011 stage 3 exists. -/

/-- Block list for `fCrossBlock`: block 0 defines value 2; block 1 uses it
without a phi. -/
def fCrossBlockBlocks : List Block :=
  [⟨0, [.const 2 (.int 1)], .goto 1⟩,
   ⟨1, [.binop 3 .add 0 2 Typ.intType], .return_ 3⟩]

/-- Cross-block use without a phi — rejected under the single-block rule. -/
def fCrossBlock : Func where
  name := "cross"
  params := [(0, Typ.intType)]
  blocks := fCrossBlockBlocks
  entry := 0
  retType := Typ.intType

example : wfBlockUse [0] fCrossBlock.blocks[0]! = true := by decide
example : wfBlockUse [0] fCrossBlock.blocks[1]! = false := by decide
example : WF fCrossBlock = false := by decide

/-! ## Evaluation oracle (pure instructions) -/

/-- Env with 0 ↦ 5, 1 ↦ 7. -/
def env0 : Env := fun
  | 0 => some (.int 5)
  | 1 => some (.int 7)
  | _ => none

/-- Extract the value bound to `x` after evaluating `i` in `env`, or `none`
if the instruction is a stub or `x` is unbound. -/
def evalTo (env : Env) (i : Instr) (x : ValId) : Option Value :=
  match evalInstr env i with
  | some env' => env' x
  | none => none

-- const defines its destination
example : evalTo env0 (.const 2 (.int 5)) 2 == some (.int 5) := by
  native_decide

-- copy moves the value
example : evalTo env0 (.copy 2 1) 2 == some (.int 7) := by
  native_decide

-- binop delegates to the surface oracle: 5 + 7 = 12
example : evalTo env0 (.binop 2 .add 0 1 Typ.intType) 2 == some (.int 12) := by
  native_decide

-- type mismatch: .not on an int is stuck, so the env is unchanged
example : evalTo env0 (.unop 2 .not 1 Typ.boolType) 2 == none := by
  native_decide

example : evalTo (fun _ => some (.bool true)) (.unop 2 .not 0 Typ.boolType) 2
    == some (.bool false) := by
  native_decide

-- unop notb on ints: ~5 = -6
example : evalTo env0 (.unop 2 .notb 0 Typ.intType) 2 == some (.int (-6)) := by
  native_decide

-- type mismatch: adding bools is stuck, so binop yields none
example : evalTo (fun _ => some (.bool true))
    (.binop 2 .add 0 1 Typ.intType) 2 == none := by
  native_decide

-- memory and call instructions are none-stubs for now
example : evalInstr env0 (.load 2 0 Capability.val) = none := by rfl
example : evalInstr env0 (.store 0 1 Capability.val) = none := by rfl
example : evalInstr env0 (.alloc 2 Capability.iso Typ.intType) = none := by rfl
example : evalInstr env0 (.free 0) = none := by rfl
example : evalInstr env0 (.call none "f" [0]) = none := by rfl
example : evalInstr env0 (.call (some 2) "f" [0]) = none := by rfl

-- evalBinOp / evalUnOp directly
example : evalBinOp .mul (.int 6) (.int 7) == some (.int 42) := by
  native_decide
example : evalUnOp .notb (.int 0) == some (.int (-1)) := by native_decide

/-! ## Edge-aware execution (Stage C item C1)

`execInstrsFull`/`execFunc` are unchanged and still stall on `phi`. The
`...From` executors take the incoming block, which is what a merge block needs.
The diamond below is the smallest program where a *wrong* phi rule is
observable: the two arms write different registers, and the join block carries
one phi per edge into the same destination, so a merge that fired *every* phi
rather than only the incoming edge's would return 20 in both runs.
-/

/-- `cond ? 10 : 20` as a diamond: block 0 branches on value 0, blocks 1/2 set
registers 4/5, block 3 merges them into 2 by phi. -/
def fDiamondBlocks : List Block :=
  [⟨0, [.const 0 (.bool true)], .branch 0 1 2⟩,
   ⟨1, [.const 4 (.int 10)], .goto 3⟩,
   ⟨2, [.const 5 (.int 20)], .goto 3⟩,
   ⟨3, [.phi 2 1 4, .phi 2 2 5], .return_ 2⟩]

def fDiamond : Func where
  name := "diamond"
  params := []
  blocks := fDiamondBlocks
  entry := 0
  retType := Typ.intType

/-- The true arm wins: `10`. -/
example : execFuncFrom 3 fDiamond ⟨fun _ => none, Store.empty⟩ == some (.int 10) := by
  native_decide

/-- Flip the condition (`const 0 (.bool false)`) and the false arm's phi fires. -/
def fDiamondFalse : Func :=
  { fDiamond with
    blocks := [⟨0, [.const 0 (.bool false)], .branch 0 1 2⟩,
               ⟨1, [.const 4 (.int 10)], .goto 3⟩,
               ⟨2, [.const 5 (.int 20)], .goto 3⟩,
               ⟨3, [.phi 2 1 4, .phi 2 2 5], .return_ 2⟩] }

example : execFuncFrom 3 fDiamondFalse ⟨fun _ => none, Store.empty⟩ == some (.int 20) := by
  native_decide

/-- The same program under the edge-blind executor stalls at the merge, which is
why C1 had to come before any `if` lowering. -/
example : execFunc 4 fDiamond ⟨fun _ => none, Store.empty⟩ == none := by
  native_decide

/-- Entry-block phis never fire: value 7 is never defined, and `prev = none`
skips the phi instead of stalling on it. -/
def fEntryPhi : Func where
  name := "entryPhi"
  params := []
  blocks := [⟨0, [.phi 1 0 7, .const 2 (.int 42)], .return_ 2⟩]
  entry := 0
  retType := Typ.intType

example : execFuncFrom 1 fEntryPhi ⟨fun _ => none, Store.empty⟩ == some (.int 42) := by
  native_decide

example : execFuncFrom 1 fEntryPhi ⟨fun _ => none, Store.empty⟩ != none := by
  native_decide

end Morph.Tests.MIR
