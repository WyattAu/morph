/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore

/-!
# Stage C: the `if` fragment and its CFG lowering

`docs/STAGEC-SCOPE.md` items C2a/C2b. Two pieces:

**The fragment** (`BranchStmts`, `BranchStep`, `ArmStmts`). Stage A's
`StraightStmts` (`Morph/HIRToMIRCore.lean`) is the hypothesis of
`compile_total`, so adding an `ifStmt` constructor to it would make that
theorem's `if`-case an unproved obligation the moment the constructor exists —
the tree would stop being green between C2 and C3. This file instead defines the
Stage C fragment as a *new* predicate that strictly contains the straight-line
one (`straightStmts_to_branch`). `compile_total` keeps its exact statement and
its exact proof; C3's theorem takes `BranchStmts`, and its `if`-free instances
are recovered through the embedding.

Three deliberate shape choices:

- **Statement steps are a separate relation.** `BranchStep` holds the
  per-statement conditions; `BranchStmts` holds the list structure. `ifStmt` is
  then an extra *side* condition instead of a new arm inside an existing
  induction, which is what keeps the existing `StraightStmts` inductions
  untouched.
- **`returnStmt` is terminal here too.** `runStmts` stops at a `return` and
  `lowerStmts` never lowers the tail, so `BranchStmts` does not constrain that
  tail either. This is exactly why `returnStmt` is a `BranchStmts` constructor
  rather than a `BranchStep`: a terminal shape is not a step.
- **Arms have their own grammar** (`ArmStmts`): an arm may evaluate expressions,
  nest `if`s, and `return`, but it may **not** declare or assign
  (`varDecl`/`assign`). An arm that rebinds changes the register file, and the
  join point would then need one phi *per merged binding*, not just the value
  phi. That is C2c; until it exists the lowering must refuse such arms, and this
  grammar is where it refuses them (`lowerStmtsCFG` returns `none` inside an
  arm, exactly like `lowerExpr` does outside the expression fragment).

**The lowering** (`lowerStmtsCFG`, `lowerProgramCFG`). Blocks are produced by a
worker that fills one caller-owned block and returns the rest:

    entry:  <condition instructions>   branch vc, then, else
    then:   <arm>                      goto join        (or `return`, if the arm returned)
    else:   <arm>                      goto join
    join:   phi vm then v_then
            phi vm else v_else
            <rest of the statement list, in the join block>
            return vm

`cont` decides what a completed statement list does: `none` returns the
accumulated value (the program body), `some b` jumps to the join block (an arm,
or the rest of a body after a nested `if`). `arm` is the flag that makes an arm
refuse to bind. One supply counter is threaded through both arms, so the two
sides cannot allocate the same register.

Nothing here proves anything about the lowering; C3 is that theorem. What this
file does provide, at compile time, is that the lowering produces the shapes the
proof will be written against, and that the executor runs them.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR

/-! ## The statement grammars -/

/-- Statement lists an `if` arm may contain: no `varDecl`, no `assign` (see the
module note). `return` is allowed and is terminal, like everywhere else. -/
inductive ArmStmts (budget : Nat) : List HIR.Stmt → Prop where
  | nil : ArmStmts budget []
  | exprStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → ArmStmts budget rest →
      ArmStmts budget (.exprStmt e :: rest)
  | nop (rest : List HIR.Stmt) : ArmStmts budget rest → ArmStmts budget (.nop :: rest)
  | ifStmt (c : HIR.Expr) (th el : List HIR.Stmt) (rest : List HIR.Stmt) :
      IsStraight c → SLWeight c < budget →
      ArmStmts budget th → ArmStmts budget el → ArmStmts budget rest →
      ArmStmts budget (.ifStmt c th el :: rest)
  | returnStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → ArmStmts budget (.returnStmt e :: rest)

/-! `BranchStep` and `BranchStmts` are mutually recursive: an `if`'s arms are
statement lists. (Doc comments inside a `mutual` block break its layout in this
toolchain, hence the section comment here.) -/
mutual

inductive BranchStep (budget : Nat) : HIR.Stmt → Prop where
  | exprStmt (e : HIR.Expr) :
      IsStraight e → SLWeight e < budget → BranchStep budget (.exprStmt e)
  | varDecl (id : HIR.Id) (τ : Typ) (init : HIR.Expr) :
      IsStraight init → SLWeight init < budget → BranchStep budget (.varDecl id τ init)
  | assign (id : HIR.Id) (e : HIR.Expr) :
      IsStraight e → SLWeight e < budget → BranchStep budget (.assign id e)
  | nop : BranchStep budget .nop
  | ifStmt (c : HIR.Expr) (th el : List HIR.Stmt) :
      IsStraight c → SLWeight c < budget →
      ArmStmts budget th → ArmStmts budget el →
      BranchStep budget (.ifStmt c th el)

inductive BranchStmts (budget : Nat) : List HIR.Stmt → Prop where
  | nil : BranchStmts budget []
  | cons {s : HIR.Stmt} {rest : List HIR.Stmt} :
      BranchStep budget s → BranchStmts budget rest → BranchStmts budget (s :: rest)
  | returnStmt (e : HIR.Expr) (rest : List HIR.Stmt) :
      IsStraight e → SLWeight e < budget → BranchStmts budget (.returnStmt e :: rest)

end

/-! ## Stage C does not shrink Stage A -/

/-- Every straight-line program is a Stage C program: the new fragment is a
superset, so C3's theorem covers Stage A's programs rather than replacing them. -/
theorem straightStmts_to_branch {budget : Nat} :
    ∀ {ss : List HIR.Stmt}, StraightStmts budget ss → BranchStmts budget ss
  | _, .nil => .nil
  | _, .exprStmt e rest h1 h2 h3 =>
      .cons (.exprStmt e h1 h2) (straightStmts_to_branch h3)
  | _, .varDecl id τ init rest h1 h2 h3 =>
      .cons (.varDecl id τ init h1 h2) (straightStmts_to_branch h3)
  | _, .assign id e rest h1 h2 h3 =>
      .cons (.assign id e h1 h2) (straightStmts_to_branch h3)
  | _, .returnStmt e rest h1 h2 => .returnStmt e rest h1 h2
  | _, .nop rest h => .cons .nop (straightStmts_to_branch h)

/-! ## The lowering -/

/-- The block a worker was asked to fill, plus every block it produced beyond
that one. `instrs`/`term` are the filled block's body; `blocks` are the others in
*forward emission order* — `lowerProgramCFG` reverses them for printing, and the
last element is the block that holds the list's completed terminator, which is
what the `if` case needs as a phi predecessor. -/
structure Lowered where
  /-- Instructions of the caller-owned block. -/
  instrs : List Instr
  /-- Terminator of the caller-owned block. -/
  term   : Terminator
  /-- Other blocks, forward emission order (last = the list's exit block). -/
  blocks : List Block
  /-- The statement list's value (the runner's accumulator). -/
  val    : ValId
  /-- The register file after the list. -/
  ρ      : List (HIR.Id × ValId)
  /-- Next free register. -/
  supply : Nat
  /-- Next free block id. -/
  next   : MIR.BlockId
  deriving Repr

/-- Lower a statement list into block `bId`.

- `cont = none`: a completed list returns its value (the program body).
- `cont = some b`: a completed list jumps to `b` (an arm, or a body tail).
- `arm = true`: binding statements are refused (see `ArmStmts`).

Block ids: `bId` is the caller's; the two arms take `nextB`/`nextB + 1`, the join
takes `nextB + 2`, and lowering continues from `nextB + 3`. -/
def lowerStmtsCFG (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (arm : Bool) (ρ : List (HIR.Id × ValId)) (supply : Nat) (nextB : MIR.BlockId)
    (lastVal : ValId) : List HIR.Stmt → Option Lowered
  | [] =>
      some ⟨[], (match cont with | none => .return_ lastVal | some t => .goto t),
            [], lastVal, ρ, supply, nextB⟩
  | .nop :: rest => lowerStmtsCFG bId cont arm ρ supply nextB lastVal rest
  | .exprStmt e :: rest => do
      let (v, ie, s1) ← lowerExpr ρ supply e
      let L ← lowerStmtsCFG bId cont arm ρ s1 nextB v rest
      some { L with instrs := ie ++ L.instrs }
  | .varDecl id _τ init :: rest =>
      match arm with
      | true => none
      | false => do
          let (vb, ib, s1) ← lowerExpr ρ supply init
          let L ← lowerStmtsCFG bId cont arm ((id, vb) :: ρ) s1 nextB lastVal rest
          some { L with instrs := ib ++ L.instrs }
  | .assign id e :: rest =>
      match arm with
      | true => none
      | false => do
          let (v, ie, s1) ← lowerExpr ρ supply e
          let L ← lowerStmtsCFG bId cont arm (updAssoc ρ id v) s1 nextB lastVal rest
          some { L with instrs := ie ++ L.instrs }
  | .returnStmt e :: _ => do
      let (v, ie, s1) ← lowerExpr ρ supply e
      some ⟨ie, .return_ v, [], v, ρ, s1, nextB⟩
  | .ifStmt c th el :: rest => do
      let (vc, ic, s1) ← lowerExpr ρ supply c
      let bThen := nextB
      let bElse := nextB + 1
      let bJoin := nextB + 2
      let Lt ← lowerStmtsCFG bThen (some bJoin) true ρ s1 (nextB + 3) lastVal th
      let Le ← lowerStmtsCFG bElse (some bJoin) true ρ Lt.supply Lt.next lastVal el
      -- The merged value: one phi per incoming edge, both writing `vm`. The
      -- edge's *source* is the block that jumps to the join, which is the arm's
      -- own block only when the arm emitted none of its own. An arm holding a
      -- nested `if` ends in that `if`'s join, and that block is the predecessor
      -- — using `bThen` there would name a block whose terminator branches into
      -- the arm's first block instead, so the phi would never fire and the join
      -- would return an unbound register (found in loop 161 by encoding
      -- `if (1 < 2) { if (3 < 4) { 7 } else { 8 } } else { 9 }`).
      let thenExit := (Lt.blocks.getLast?.map (fun b => b.id)).getD bThen
      let elseExit := (Le.blocks.getLast?.map (fun b => b.id)).getD bElse
      let vm := Le.supply
      let phis : List Instr :=
        [.phi vm thenExit Lt.val, .phi vm elseExit Le.val]
      let Lr ← lowerStmtsCFG bJoin cont arm ρ (vm + 1) Le.next vm rest
      some { instrs := ic
             term := .branch vc bThen bElse
             blocks := Lt.blocks ++ [⟨bThen, Lt.instrs, Lt.term⟩]
                       ++ Le.blocks ++ [⟨bElse, Le.instrs, Le.term⟩]
                       ++ Lr.blocks ++ [⟨bJoin, phis ++ Lr.instrs, Lr.term⟩]
             val := Lr.val
             ρ := Lr.ρ
             supply := Lr.supply
             next := Lr.next }
  | _ :: _ => none

/-- Lower a program to a MIR CFG. Register 0 is the unit prologue (as in
`lowerProgram`), block 0 is the entry, and the arms' blocks start at 1. -/
def lowerProgramCFG (prog : HIR.Program) : Option Func := do
  let L ← lowerStmtsCFG 0 none false [] 1 1 0 prog.stmts
  some ⟨"main", [], ⟨0, [.const 0 .unit] ++ L.instrs, L.term⟩ :: L.blocks.reverse,
    0, .unitType⟩

/-! ## The boundary is real

The four facts below are the ones an auditor would ask for: `if` is in, nesting
is in, `while` is out, and a binding arm is out (until C2c). -/

/-- A two-arm `return` program is in the fragment. -/
example :
    BranchStmts 256
      [.ifStmt (.lit (.bool true)) [.returnStmt (.lit (.int 1))]
        [.returnStmt (.lit (.int 2))]] :=
  .cons (.ifStmt (.lit (.bool true)) _ _
    (.lit _) (by simp [SLWeight])
    (.returnStmt _ _ (.lit _) (by simp [SLWeight]))
    (.returnStmt _ _ (.lit _) (by simp [SLWeight]))) .nil

/-- Nested `if`s: the arms are fragments in their own right. -/
example :
    BranchStmts 256
      [.ifStmt (.lit (.bool true))
        [.ifStmt (.lit (.bool false)) [.nop] []]
        []] :=
  .cons (.ifStmt (.lit (.bool true)) _ _
    (.lit _) (by simp [SLWeight])
    (.ifStmt (.lit (.bool false)) _ _ _
      (.lit _) (by simp [SLWeight]) (.nop [] .nil) .nil .nil)
    .nil) .nil

/-- `while` is outside the fragment: `BranchStep` has no arm for it, and the
`returnStmt` shape cannot unify with a `whileLoop`. -/
example : ¬ BranchStmts 256 [.whileLoop (.lit (.bool true)) []] := by
  intro h
  cases h with
  | cons hs _ => cases hs

/-- A binding `if` arm is outside the fragment: `ArmStmts` has no `varDecl`. -/
example : ¬ ArmStmts 256 [.varDecl ⟨0, "x"⟩ Typ.intType (.lit (.int 1))] := by
  intro h
  cases h

/-! ## The lowered CFG runs

These are evidence, not the theorem: the same expression in both arms would pass
even if the phi rule were wrong, so the arms deliberately differ, and the
condition appears in both truth values. -/

/-- `if true { 10 } else { 20 }`. -/
def ifProg : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool true)) [.exprStmt (.lit (.int 10))]
      [.exprStmt (.lit (.int 20))]]⟩

/-- The lowered program is a five-block CFG (entry, then, else, join) plus the
prologue register. -/
example : (lowerProgramCFG ifProg).map (fun f => f.blocks.length) = some 4 := by
  native_decide

/-- The true arm's value reaches the return. -/
example :
    (lowerProgramCFG ifProg).bind (fun f => execFuncFrom 3 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 10) := by
  native_decide

/-- Flipping the condition takes the other arm — the same program, one
constructor different. -/
def ifProgFalse : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool false)) [.exprStmt (.lit (.int 10))]
      [.exprStmt (.lit (.int 20))]]⟩

example :
    (lowerProgramCFG ifProgFalse).bind
        (fun f => execFuncFrom 3 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 20) := by
  native_decide

/-- The join block really merges: the value returned comes out of the phi, so a
program that uses the `if`'s value after it (`if c { 10 } else { 20 }` then `+ 5`)
evaluates 15. -/
def ifThenAdd : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool true)) [.exprStmt (.lit (.int 10))]
      [.exprStmt (.lit (.int 20))],
    .exprStmt (.binop .add (.lit (.int 0)) (.lit (.int 5)))]⟩

/-- The second statement lowers into the join block, and `runStmts`' accumulator
rule (`acc.replace`) is what makes its value the *last* expression's: 5. The
`if`'s phi is still executed (block 3 begins with it) — the value it merges is
just not the result. -/
example :
    (lowerProgramCFG ifThenAdd).bind
        (fun f => execFuncFrom 3 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 5) := by
  native_decide

/-! ## Nested arms: the phi's predecessor

The edge into a join comes from the block that actually jumps there. A flat arm
is one block, so that block is the arm's entry; an arm holding a nested `if`
ends in that `if`'s join instead. Naming the arm's entry unconditionally left the
outer phi unfired, so the join returned an unbound register — a lowering bug
found in loop 161 by trying to *encode* the program, not by any test that ran
the flat shape. These two are the regression tests. -/

/-- An `if` in the then-arm: the outer join takes its value from the inner
join's edge, so the outer phi must name that block. -/
def nestedThenProg : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool true))
      [.ifStmt (.lit (.bool false)) [.exprStmt (.lit (.int 7))]
        [.exprStmt (.lit (.int 8))]]
      [.exprStmt (.lit (.int 9))]]⟩

example :
    (lowerProgramCFG nestedThenProg).bind
        (fun f => execFuncFrom 6 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 8) := by
  native_decide

/-- The same shape in the else-arm, so the fix is not specific to one edge. -/
def nestedElseProg : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool false))
      [.exprStmt (.lit (.int 9))]
      [.ifStmt (.lit (.bool true)) [.exprStmt (.lit (.int 7))]
        [.exprStmt (.lit (.int 8))]]]⟩

example :
    (lowerProgramCFG nestedElseProg).bind
        (fun f => execFuncFrom 6 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 7) := by
  native_decide

end Morph.HIRToMIRCorrect
