/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifBlocks
import Morph.ClifLower
import Morph.HIRToMIRBranch

/-!
# Stage C items C4b/C5: encoding a MIR CFG into the CLIF block model

`docs/STAGEC-SCOPE.md` §4.3. `Morph/ClifLower.lean`'s `blockEncode` turns one
straight-line MIR block into a one-block CLIF function. This file is the CFG
analogue: `encodeFunc` turns a whole MIR function into `Morph.Clif.Cfg.Func`,
with the three pieces of Stage C's target surface:

- **`phi` becomes a block parameter.** A block's leading phis are removed from
  its instruction list and become its `params`, in order. The register the phi
  defined is therefore bound on entry by the edge, not written by an
  instruction — which is what C4b's phi↔argument lemma will be about.
- **A terminator's edge carries arguments.** Each edge passes the `src` of every
  phi in the target that names the source block as its predecessor, in the
  target's parameter order (`edgeArgs`). That is the only place the two arms of
  an `if` can differ on the same target.
- **Phis must lead.** `splitPhis` stops at the first non-phi, and `instrEncode`
  refuses a `.phi`, so a phi in the middle of a block fails the encoding instead
  of being silently dropped or treated as a copy.

The prologue is dropped exactly as `emitBlock` drops it: `lowerProgramCFG` (and
`lowerProgram`) prefix the entry body with `.const 0 .unit`, and register 0 is
unit-valued so no instruction reads it. `stripPrologue` removes it from the
entry block only; a `.const 0 (.int _)` is a real definition and is left alone.

## What this file does and does not prove

It is the encoder plus evidence. The four `native_decide` facts run real
lowerings (`Morph/HIRToMIRBranch.lean`'s `ifProg`, `ifProgFalse`, `ifThenAdd`)
through `Cfg.run` — HIR statement list → lowerer → CLIF block model → value —
and two refusals (a `switch`, a non-leading phi). The general statement, that
*any* MIR run through the edge-aware executor is reproduced by the encoded
function, is C4b; it needs a block-level MIR trace relation and a fuel bound, and
it is not claimed here.
-/

open Morph.Core
open Morph.MIR (ValId)

namespace Morph.Clif
namespace Cfg

/-- A leading `phi` in a MIR block, in the form the lowering produces:
`dst` is defined by the edge from `pred` out of `src`. -/
structure Phi where
  dst : ValId
  pred : Morph.MIR.BlockId
  src : ValId
  deriving Repr, BEq

/-- Read a `phi` instruction, `none` for anything else. -/
def phiInfo : Morph.MIR.Instr → Option Phi
  | .phi dst pred src => some ⟨dst, pred, src⟩
  | _ => none

/-- The leading run of `phi` instructions, and the rest of the block. Stops at
the first non-phi; a phi after that point is not part of the returned run and
will be refused by the encoder. -/
def splitPhis : List Morph.MIR.Instr → List Phi × List Morph.MIR.Instr
  | [] => ([], [])
  | i :: is =>
    match phiInfo i with
    | some p =>
      let rest := splitPhis is
      (p :: rest.1, rest.2)
    | none => ([], i :: is)

/-- The leading phis of the block with the given label, if the block exists. -/
def targetPhis (f : Morph.MIR.Func) (id : Morph.MIR.BlockId) : Option (List Phi) :=
  (f.blocks.find? (fun b => b.id == id)).map (fun b => (splitPhis b.instrs).1)

/-- The join's parameters: the destinations of the leading phis, in order of
first appearance, without repeats. The lowering emits one phi per *predecessor*
with the same destination (`phi vm bThen v1`, `phi vm bElse v2`), which is MIR's
form; CLIF has one parameter per merged value, fed by a different argument on
each edge. Merging by destination is what turns the first into the second. -/
def paramsOf (phis : List Phi) : List ValId :=
  phis.foldl (fun acc p => if acc.elem p.dst then acc else acc ++ [p.dst]) []

/-- No destination is defined twice for the same predecessor. Two phis for one
edge would make the edge's argument ambiguous, so the encoder refuses instead of
picking the first one. -/
def noDupPairs (phis : List Phi) : Bool :=
  phis.all fun p =>
    (phis.filter (fun q => q.dst == p.dst && q.pred == p.pred)).length == 1

/-- The arguments an edge into `target` passes, coming from `pred`: for each of
the join's parameters, the `src` of the phi that names `pred` for it. A
parameter with no phi for this edge fails the encoding — the edge would have no
value to pass, and emitting fewer arguments would defer a lowering bug to a
runtime arity mismatch. -/
def edgeArgs (f : Morph.MIR.Func) (target pred : Morph.MIR.BlockId) : Option (List Reg) := do
  let ps ← targetPhis f target
  (paramsOf ps).mapM fun d =>
    (ps.find? (fun p => p.dst == d && p.pred == pred)).map (fun p => p.src)

/-- Encode a MIR terminator. `switch` is refused (scope §3: no MIR-level oracle
for it; `matchStmt` will lower to branches first). -/
def encodeTerm (f : Morph.MIR.Func) (b : Morph.MIR.Block) : Option Term :=
  match b.terminator with
  | .return_ src => some (.ret src)
  | .goto t => (edgeArgs f t b.id).map fun args => .jump t args
  | .branch c tt ff => do
    let ttArgs ← edgeArgs f tt b.id
    let ffArgs ← edgeArgs f ff b.id
    some (.brif c tt ttArgs ff ffArgs)
  | .switch _ _ _ => none

/-- Drop the unit prologue from a block, if it has one. -/
def stripPrologue (b : Morph.MIR.Block) : Morph.MIR.Block :=
  match b.instrs with
  | .const 0 .unit :: rest => { b with instrs := rest }
  | _ => b

/-- Encode one MIR block: leading phis become parameters, the rest is
straight-line, and the terminator supplies each edge's arguments. -/
def encodeBlock (f : Morph.MIR.Func) (b : Morph.MIR.Block) : Option Block := do
  let phis := (splitPhis b.instrs).1
  if !noDupPairs phis then none
  else
    let is ← instrEncodes (splitPhis b.instrs).2
    let t ← encodeTerm f b
    some ⟨b.id, paramsOf phis, is, t⟩

/-- Encode a MIR function into the CLIF block model, dropping the unit prologue
from the entry block (as `emitBlock` does for the single-block emitter). -/
def encodeFunc (f : Morph.MIR.Func) : Option Func := do
  let bs ← f.blocks.mapM fun b =>
    encodeBlock f (if b.id == f.entry then stripPrologue b else b)
  some ⟨bs, f.entry⟩

/-! ## Evidence on real lowerings

`runLowered` is the whole pipeline below the HIR oracle: statement list →
`lowerProgramCFG` → `encodeFunc` → `Cfg.run`. The conditions are **computed**
(`1 < 2`), not literals: a literal boolean lowers to `.const (.bool b)`, which
`instrEncodes` refuses because the CLIF subset has no boolean constant
(`Morph/ClifEmit.lean` lists it with division and `copy`). That narrowing is
pinned below as a refusal rather than left to prose — the HIR and MIR paths
handle literal conditions, the codegen path does not yet.

Each pair of programs differs in exactly one constructor and expects different
values, so an edge that passed the wrong argument list fails at least one. -/

/-- Lower, encode, run. -/
def runLowered (prog : HIR.Program) (fuel : Nat) : Option Value :=
  (Morph.HIRToMIRCorrect.lowerProgramCFG prog).bind fun f =>
    (encodeFunc f).bind fun cf => run fuel cf

open Morph.HIRToMIRCorrect
open Morph.HIR

/-- `if 1 < 2 { 10 } else { 20 }`. -/
def ifLtProg : HIR.Program :=
  ⟨[.ifStmt (.binop .lt (.lit (.int 1)) (.lit (.int 2)))
      [.exprStmt (.lit (.int 10))] [.exprStmt (.lit (.int 20))]]⟩

/-- The true arm's value survives lowering, encoding, and the block model. -/
example : (runLowered ifLtProg 6 == some (.int 10)) = true := by native_decide

/-- `if 2 < 1 { 10 } else { 20 }`: the same shape, the other edge. -/
def ifLtProgFalse : HIR.Program :=
  ⟨[.ifStmt (.binop .lt (.lit (.int 2)) (.lit (.int 1)))
      [.exprStmt (.lit (.int 10))] [.exprStmt (.lit (.int 20))]]⟩

example : (runLowered ifLtProgFalse 6 == some (.int 20)) = true := by native_decide

/-- A statement after the `if` lives in the join block, so running it is what
shows the phi's parameter really carried the arm's value. -/
def ifLtThenAdd : HIR.Program :=
  ⟨[.ifStmt (.binop .lt (.lit (.int 1)) (.lit (.int 2)))
      [.exprStmt (.lit (.int 10))] [.exprStmt (.lit (.int 20))],
    .exprStmt (.binop .add (.lit (.int 0)) (.lit (.int 5)))]⟩

example : (runLowered ifLtThenAdd 6 == some (.int 5)) = true := by native_decide

/-- A literal boolean condition is refused at encoding: `.const (.bool true)`
has no CLIF instruction in the subset. This is the narrowing named above, not a
lowering bug — `execFuncFrom` runs the same program. -/
example : (runLowered Morph.HIRToMIRCorrect.ifProg 6 == none) = true := by
  native_decide

/-- `switch` is refused rather than given an encoding. -/
def switchFunc : Morph.MIR.Func :=
  ⟨"main", [], [⟨0, [], .switch 0 [] 1⟩, ⟨1, [], .return_ 0⟩], 0, .unitType⟩

example : (encodeFunc switchFunc == none) = true := by native_decide

/-- A phi that does not lead its block is refused: it would have no edge to take
its value from. -/
def latePhiFunc : Morph.MIR.Func :=
  ⟨"main", [], [⟨0, [.const 0 (.int 1), .phi 1 0 0], .return_ 0⟩], 0, .unitType⟩

example : (encodeFunc latePhiFunc == none) = true := by native_decide

end Cfg
end Morph.Clif
