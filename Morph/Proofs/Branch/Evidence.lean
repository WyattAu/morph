/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRBranch

/-!
# Stage C evidence: end-to-end program pins (C7 spine)

Terminal leaf: `def` + `example` pairs that apply `lowerProgramCFG_correct`
to concrete programs. Nothing in the proof monolith depends on these names,
so they live here and import `Morph.HIRToMIRBranch` back. New pins go in
this file, not in the monolith.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Carried register through the back edge: `x` is 0 on entry, the loop takes
the back edge once (`0 < 1`), then exits when the carried `5` fails the test. -/
def whileCarryProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .whileLoop (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
      [.assign ⟨0, "x"⟩ (.lit (.int 5))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- End-to-end carried-register loop (C7): the second concrete application of
the program corollary, and the first to take the back edge — the header phi
re-reads the carried `x`, unlike the `break` pin which never loops back. The
body assigns a literal, so the `VarFree` side condition holds; the oracle run
is by `rfl` (two header evaluations, one body). -/
example : ∃ f, lowerProgramCFG whileCarryProg = some f ∧
    execFuncFrom (blockBound 1024 whileCarryProg.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some (.int 5) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp
    ((by native_decide : (lowerProgramCFG whileCarryProg).isSome = true))
  refine ⟨f, hf, ?_⟩
  have hfrag : BranchStmts 256 whileCarryProg.stmts :=
    .cons (.varDecl _ _ _ (.lit _) (by simp [SLWeight]))
      (.cons (.whileStmt _ _
        (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
        (by simp [SLWeight])
        (.assign _ _ _ (.lit _) (by simp [SLWeight]) .nil (.lit _)))
      (.cons (.exprStmt _ (.var _) (by simp [SLWeight])) .nil))
  have hrun : runHIRProgram whileCarryProg = .value (.lit (.int 5)) := by
    rfl
  exact lowerProgramCFG_correct 256 whileCarryProg f ⟨[]⟩ hf hfrag (.int 5) hrun

/-- Loop-body `if` on the back-edge path: the header reads the carried `x`,
the body branches on the same carried `x` (true edge on the first pass),
then assigns the exit constant after the join and loops back. Arms are
binding-free (`exprStmt` discards differing so the value phi matters) with
`ArmNoBreak`, so this exercises `LoopStmts.ifStmt` — the non-break
loop-body arm gate — rather than the `break` pin above. -/
def whileIfBodyProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .whileLoop (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
      [.ifStmt (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
        [.exprStmt (.lit (.int 10))] [.exprStmt (.lit (.int 20))],
       .assign ⟨0, "x"⟩ (.lit (.int 5))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- End-to-end loop-body `if` (C7): the third concrete application of the
program corollary, and the first to run an `if` inside a taken back edge.
Lowering success is by `isSome`/`native_decide`, the fragment witness
supplies the `ArmStmts`/`ArmNoBreak`/`VarFree` obligations (arms differ so
the value phi is load-bearing), and the oracle run is by `rfl`. -/
example : ∃ f, lowerProgramCFG whileIfBodyProg = some f ∧
    execFuncFrom (blockBound 1024 whileIfBodyProg.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some (.int 5) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp
    ((by native_decide : (lowerProgramCFG whileIfBodyProg).isSome = true))
  refine ⟨f, hf, ?_⟩
  have hfrag : BranchStmts 256 whileIfBodyProg.stmts :=
    .cons (.varDecl _ _ _ (.lit _) (by simp [SLWeight]))
      (.cons (.whileStmt _ _
        (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
        (by simp [SLWeight])
        (.ifStmt _ _ _ _
          (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
          (by simp [SLWeight])
          (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
          (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
          (.assign _ _ _ (.lit _) (by simp [SLWeight]) .nil (.lit _))
          (.exprStmt _ _ .nil)
          (.exprStmt _ _ .nil)))
      (.cons (.exprStmt _ (.var _) (by simp [SLWeight])) .nil))
  have hrun : runHIRProgram whileIfBodyProg = .value (.lit (.int 5)) := by
    rfl
  exact lowerProgramCFG_correct 256 whileIfBodyProg f ⟨[]⟩ hf hfrag (.int 5) hrun

/-- Break-via-`if` inside a loop body: the taken arm holds a `break` while
the other arm is a binding-free discard, and the `if` tail is empty (hence
trivially both `LoopStmts` and `ArmStmts`). This exercises
`LoopStmts.ifStmtBreak` — the arm-`break` gate the previous back-edge pin
(`LoopStmts.ifStmt` + `ArmNoBreak`) deliberately avoided — with the break
edge taken on the first pass so the loop exits with `x = 0`. -/
def whileIfBreakProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .whileLoop (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
      [.ifStmt (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
        [.break] [.exprStmt (.lit (.int 20))]],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- End-to-end break-via-`if` (C7): the fourth concrete application of the
program corollary, and the first to take an arm `break` out of a loop body.
Lowering success is by `isSome`/`native_decide`, the fragment witness
supplies the `ArmStmts` obligations (the taken arm is
`.breakStmt .nil`, the tail is empty on both sides), and the oracle run
is by `rfl`. -/
example : ∃ f, lowerProgramCFG whileIfBreakProg = some f ∧
    execFuncFrom (blockBound 1024 whileIfBreakProg.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some (.int 0) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp
    ((by native_decide : (lowerProgramCFG whileIfBreakProg).isSome = true))
  refine ⟨f, hf, ?_⟩
  have hfrag : BranchStmts 256 whileIfBreakProg.stmts :=
    .cons (.varDecl _ _ _ (.lit _) (by simp [SLWeight]))
      (.cons (.whileStmt _ _
        (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
        (by simp [SLWeight])
        (.ifStmtBreak _ _ _ _
          (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
          (by simp [SLWeight])
          (.breakStmt _ .nil)
          (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
          .nil
          .nil))
      (.cons (.exprStmt _ (.var _) (by simp [SLWeight])) .nil))
  have hrun : runHIRProgram whileIfBreakProg = .value (.lit (.int 0)) := by
    rfl
  exact lowerProgramCFG_correct 256 whileIfBreakProg f ⟨[]⟩ hf hfrag (.int 0) hrun

/-- `continue`-via-`if` inside a loop body: progress (`x = 5`) runs before
the branch, then the `if` takes its `continue` arm on the `false` edge
(`5 < 1` is false) and exits on the next header test. Both arms are
break-free (`continue` is allowed by `ArmNoBreak`), so this exercises
`LoopStmts.ifStmt` with an arm `continue` — the last member of the
arm-leave-loop family (`break` pinned above, fall-through pinned before). -/
def whileContinueProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .whileLoop (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
      [.assign ⟨0, "x"⟩ (.lit (.int 5)),
       .ifStmt (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
        [.exprStmt (.lit (.int 20))] [.continue]],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- End-to-end `continue`-via-`if` (C7): the fifth concrete application of
the program corollary. Lowering by `isSome`/`native_decide`, fragment
witness supplies `ArmStmts`/`ArmNoBreak` (taken arm is
`.continueStmt .nil`), oracle run by `rfl`. -/
example : ∃ f, lowerProgramCFG whileContinueProg = some f ∧
    execFuncFrom (blockBound 1024 whileContinueProg.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some (.int 5) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp
    ((by native_decide : (lowerProgramCFG whileContinueProg).isSome = true))
  refine ⟨f, hf, ?_⟩
  have hfrag : BranchStmts 256 whileContinueProg.stmts :=
    .cons (.varDecl _ _ _ (.lit _) (by simp [SLWeight]))
      (.cons (.whileStmt _ _
        (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
        (by simp [SLWeight])
        (.assign _ _ _ (.lit _) (by simp [SLWeight])
          (.ifStmt _ _ _ _
            (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
            (by simp [SLWeight])
            (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
            (.continueStmt _ .nil)
            .nil
            (.exprStmt _ _ .nil)
            (.continueStmt _ .nil))
          (.lit _)))
      (.cons (.exprStmt _ (.var _) (by simp [SLWeight])) .nil))
  have hrun : runHIRProgram whileContinueProg = .value (.lit (.int 5)) := by
    rfl
  exact lowerProgramCFG_correct 256 whileContinueProg f ⟨[]⟩ hf hfrag (.int 5) hrun

/-- Arm-`break` with a real tail: the taken `break` arm skips the
binding-free tail (`exprStmt 30`) while the static exit env still mentions
only carried registers. This exercises `LoopStmts.ifStmtBreak` with a
non-empty `rest` satisfying both `LoopStmts` and `ArmStmts`, rather than
the empty-tail pin above. First pass breaks with `x = 0`. -/
def whileIfBreakTailProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .whileLoop (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
      [.ifStmt (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
        [.break] [.exprStmt (.lit (.int 20))],
       .exprStmt (.lit (.int 30))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- End-to-end arm-`break` with tail (C7): the sixth concrete application
of the program corollary. Lowering by `isSome`/`native_decide`, fragment
witness supplies the `ArmStmts` arms plus the shared binding-free tail on
both the `LoopStmts` and `ArmStmts` sides, oracle run by `rfl`. -/
example : ∃ f, lowerProgramCFG whileIfBreakTailProg = some f ∧
    execFuncFrom (blockBound 1024 whileIfBreakTailProg.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some (.int 0) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp
    ((by native_decide : (lowerProgramCFG whileIfBreakTailProg).isSome = true))
  refine ⟨f, hf, ?_⟩
  have hfrag : BranchStmts 256 whileIfBreakTailProg.stmts :=
    .cons (.varDecl _ _ _ (.lit _) (by simp [SLWeight]))
      (.cons (.whileStmt _ _
        (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
        (by simp [SLWeight])
        (.ifStmtBreak _ _ _ _
          (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
          (by simp [SLWeight])
          (.breakStmt _ .nil)
          (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
          (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
          (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)))
      (.cons (.exprStmt _ (.var _) (by simp [SLWeight])) .nil))
  have hrun : runHIRProgram whileIfBreakTailProg = .value (.lit (.int 0)) := by
    rfl
  exact lowerProgramCFG_correct 256 whileIfBreakTailProg f ⟨[]⟩ hf hfrag (.int 0) hrun

/-- Nested `if` inside a loop-body arm: the taken outer arm holds an inner
`if` over a literal, so both the `ArmStmts` and `ArmNoBreak` predicates
recurse one level deeper. The outer `else` stays a binding-free discard
and the post-join tail assigns the exit constant. First pass takes
outer-true/inner-true, assigns `5`, then exits. -/
def whileNestedIfProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .whileLoop (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
      [.ifStmt (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 1)))
        [.ifStmt (.lit (.bool true))
          [.exprStmt (.lit (.int 10))] [.exprStmt (.lit (.int 11))]]
        [.exprStmt (.lit (.int 20))],
       .assign ⟨0, "x"⟩ (.lit (.int 5))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- End-to-end nested-`if` arm (C7): the seventh concrete application of
the program corollary. Lowering by `isSome`/`native_decide`, the fragment
witness nests `ArmStmts.ifStmt`/`ArmNoBreak.ifStmt` one level, oracle run
by `rfl`. -/
example : ∃ f, lowerProgramCFG whileNestedIfProg = some f ∧
    execFuncFrom (blockBound 1024 whileNestedIfProg.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some (.int 5) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp
    ((by native_decide : (lowerProgramCFG whileNestedIfProg).isSome = true))
  refine ⟨f, hf, ?_⟩
  have hfrag : BranchStmts 256 whileNestedIfProg.stmts :=
    .cons (.varDecl _ _ _ (.lit _) (by simp [SLWeight]))
      (.cons (.whileStmt _ _
        (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
        (by simp [SLWeight])
        (.ifStmt _ _ _ _
          (.binop _ _ _ (by simp [toBinOp]) (.var _) (.lit _))
          (by simp [SLWeight])
          (.ifStmt _ _ _ _ (.lit _) (by simp [SLWeight])
            (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
            (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
            .nil)
          (.exprStmt _ _ (.lit _) (by simp [SLWeight]) .nil)
          (.assign _ _ _ (.lit _) (by simp [SLWeight]) .nil (.lit _))
          (.ifStmt _ _ _ _
            (.exprStmt _ _ .nil) (.exprStmt _ _ .nil) .nil)
          (.exprStmt _ _ .nil)))
      (.cons (.exprStmt _ (.var _) (by simp [SLWeight])) .nil))
  have hrun : runHIRProgram whileNestedIfProg = .value (.lit (.int 5)) := by
    rfl
  exact lowerProgramCFG_correct 256 whileNestedIfProg f ⟨[]⟩ hf hfrag (.int 5) hrun


/- These are evidence, not the theorem: the same expression in both arms would pass
even if the phi rule were wrong, so the arms deliberately differ, and the
condition appears in both truth values. -/

/-- `if true { 10 } else { 20 }`. -/
def ifProg : HIR.Program :=
  ⟨[.ifStmt (.lit (.bool true)) [.exprStmt (.lit (.int 10))]
      [.exprStmt (.lit (.int 20))]]⟩

/-- The lowered program is a four-block CFG (entry, then, else, join) plus the
prologue register. -/
example : (lowerProgramCFG ifProg).map (fun f => f.blocks.length) = some 4 := by
  native_decide

/-- `blockBound` agrees with the CFG the lowering produced: the entry block plus
the `if`'s three. This is the arithmetic C3 will cite instead of a literal. -/
example : blockBound 8 ifProg.stmts = 4 := by
  native_decide

/-- A program with no `if` is one block, whatever its length. -/
example :
    blockBound 8 [.exprStmt (.lit (.int 1)), .exprStmt (.lit (.int 2))] = 1 := by
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
/-! ## Binding arms: the merge join (C2c evidence)

The merge path (`mergeIds` non-empty) only fires when an id bound *before*
the `if` is rebound inside an arm: the join carries one `mkMergePhis` phi
per rebound id plus the value phi. A fresh `varDecl` inside an arm is not
in the pre-branch env, so it takes the old join verbatim. These pins cover
the merge join: `x` is declared before, assigned in each arm, and read
after. -/

/-- Binding-arm `if`, true edge: `x` is 10 after the join. -/
def bindIfAssignProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .ifStmt (.lit (.bool true)) [.assign ⟨0, "x"⟩ (.lit (.int 10))]
      [.assign ⟨0, "x"⟩ (.lit (.int 20))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- Same program, false edge: `x` is 20 after the join. -/
def bindIfAssignFalseProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .ifStmt (.lit (.bool false)) [.assign ⟨0, "x"⟩ (.lit (.int 10))]
      [.assign ⟨0, "x"⟩ (.lit (.int 20))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- Four blocks, like the binding-free `if`: the merge phi lives in the join. -/
example : (lowerProgramCFG bindIfAssignProg).map (fun f => f.blocks.length) =
    some 4 := by
  native_decide

/-- The bound agrees: entry plus the `if`'s three. -/
example : blockBound 8 bindIfAssignProg.stmts = 4 := by
  native_decide

/-- The true arm's assignment reaches the trailing read. -/
example :
    (lowerProgramCFG bindIfAssignProg).bind
        (fun f => execFuncFrom 4 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 10) := by
  native_decide

/-- The false arm's assignment reaches the trailing read. -/
example :
    (lowerProgramCFG bindIfAssignFalseProg).bind
        (fun f => execFuncFrom 4 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 20) := by
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

/-- The bound counts the nested arm, and only the deeper of the two: 1 (entry)
+ 3 (outer `if`) + 3 (inner `if`, in the then-arm). This is the case a flat
"three per statement" bound would get wrong. -/
example : blockBound 8 nestedThenProg.stmts = 7 := by
  native_decide

/-! ## Loops: the header re-reads the carried registers

A loop body that counts (`x = x + 1` while `x < 2`) only terminates because the
header's condition reads the carried register, not the entry value — lowering
the condition in the pre-loop env froze `x` at 0 and spun until fuel ran out
(loop 181). These two pin the fix. -/

/-- Count to two: declare, loop while below two, read back. -/
def whileCountProg : HIR.Program :=
  ⟨[.varDecl ⟨0, "x"⟩ .intType (.lit (.int 0)),
    .whileLoop (.binop .lt (.var ⟨0, "x"⟩) (.lit (.int 2)))
      [.assign ⟨0, "x"⟩ (.binop .add (.var ⟨0, "x"⟩) (.lit (.int 1)))],
    .exprStmt (.var ⟨0, "x"⟩)]⟩

/-- Four blocks: entry, body, header, exit (plus the prologue register). -/
example : (lowerProgramCFG whileCountProg).map (fun f => f.blocks.length) =
    some 4 := by
  native_decide

/-- The bound charges one body traversal per oracle-fuel unit: 1 (entry) +
(2 + 0) * (8 + 1) (the loop) + 0 (the trailing read). -/
example : blockBound 8 whileCountProg.stmts = 19 := by
  native_decide

/-- The counter reaches 2 — and the bound fuel suffices to run it there. -/
example :
    (lowerProgramCFG whileCountProg).bind
        (fun f => execFuncFrom 19 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 2) := by
  native_decide

/-- `break` leaves the loop: an infinite condition still returns. -/
def whileBreakProg : HIR.Program :=
  ⟨[.whileLoop (.lit (.bool true)) [.break],
    .exprStmt (.lit (.int 5))]⟩

example :
    (lowerProgramCFG whileBreakProg).bind
        (fun f => execFuncFrom 5 f ⟨fun _ => none, Store.empty⟩)
      == some (.int 5) := by
  native_decide

/-- End-to-end loop correctness (C7): the `break` program through the program
corollary. This is the first concrete application of the C7 chain — a manual
fragment witness (the body is one `break`, so no `VarFree` obligation), the
oracle run by `rfl` (the loop breaks on its first iteration), and
`lowerProgramCFG_correct` closing it at `blockBound 1024` fuel. -/
example : ∃ f, lowerProgramCFG whileBreakProg = some f ∧
    execFuncFrom (blockBound 1024 whileBreakProg.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some (.int 5) := by
  have hexec : (lowerProgramCFG whileBreakProg).bind
      (fun f => execFuncFrom 5 f ⟨fun _ => none, Store.empty⟩) ==
      some (.int 5) := by
    native_decide
  have hsome : (lowerProgramCFG whileBreakProg).isSome := by
    cases h : lowerProgramCFG whileBreakProg with
    | none => simp [h] at hexec
    | some f => rfl
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨f, hf, ?_⟩
  have hfrag : BranchStmts 256 whileBreakProg.stmts :=
    .cons (.whileStmt _ _ (.lit _) (by simp [SLWeight]) (.breakStmt [] .nil))
      (.cons (.exprStmt _ (.lit _) (by simp [SLWeight])) .nil)
  have hrun : runHIRProgram whileBreakProg = .value (.lit (.int 5)) := by
    rfl
  exact lowerProgramCFG_correct 256 whileBreakProg f ⟨[]⟩ hf hfrag (.int 5) hrun

end Morph.HIRToMIRCorrect
