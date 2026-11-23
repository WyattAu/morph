/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal
import Morph.Proofs.Branch.Merge
import Morph.Proofs.Branch.Fragments
import Morph.Proofs.Branch.Fuel
import Morph.Proofs.Branch.LoopAlloc
import Morph.Proofs.Branch.Assembly
import Morph.Proofs.Branch.Equations
import Morph.HIRToMIRLower
import Morph.Proofs.Branch.Infra
import Morph.Proofs.Branch.ArmTotal
import Morph.Proofs.Branch.ArmBroke
import Morph.Proofs.Branch.ArmContinued
import Morph.Proofs.Branch.LoopBodyRun
import Morph.Proofs.Branch.Oracle
import Morph.Proofs.Branch.BindArm
import Morph.Proofs.Branch.LoopLookup
import Morph.Proofs.Branch.Spine
import Morph.Proofs.Branch.WhileLoop
import Morph.Proofs.Branch.Total
import Morph.Proofs.Branch.IfTotal
import Morph.Proofs.Branch.TopLevel

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
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-! ## The statement grammars: now in `Morph.Proofs.Branch.Fragments` -/

/- The fragment leaf holds `VarFree`, `ArmStmts`, `BindArmStmts`
(Phase A), `ArmStmts_to_BindArmStmts`, `ArmNoBreak`,
`HFlow_replace_ne_broke`, `ArmNoBreak_run`, the
`BranchStep`/`BranchStmts` mutual block, `LoopStmts`,
`straightStmts_to_branch`, and `LoopStmts_to_BranchStmts`
(L0 proof crate: `Core`/`Total` only). This module imports it back. -/

/-! ## Fuel: now in `Morph.Proofs.Branch.Fuel` -/

/- The fuel leaf holds `armBlockBound`, `blockBound`, and the `eq_def`
rewrite lemmas plus the cons/elim helpers (L0 proof crate: `Core`/`Total`
only). This module imports it back. -/

/-! ## Loop helpers (C7a): now in `Morph.Proofs.Branch.LoopAlloc` -/

/- The loop-allocation leaf holds `assignedIds`, `dedupIds`, `LoopInfo`,
`carryCopies`, `mkCarried` plus growth proofs, and `mkHeaderPhis`
(L0 proof crate: `Core`/`Total` only). This module imports it back. -/

/-! ## Arm-merge helpers (C2c groundwork): now in `Morph.Proofs.Branch.Merge` -/

/- The merge leaf holds `mergeIds`, `rhoLookup_some_of_mem`,
`mergeIds_mem_lookup`, `mkMergePhis`, `mkMergePhis_le`,
`mkMergePhis_growth_fresh`, and `boundIds` (L0 proof crate: `Core`/`Total`
only). This module imports it back; Phase B cites the leaf. -/

/- `mkHeaderPhis` lives in `Morph.Proofs.Branch.LoopAlloc`. -/

/-! ## The lowering: now in `Morph.HIRToMIRLower` -/

/- `Lowered`, `lowerStmtsCFG`, and `lowerProgramCFG` live in
`Morph.HIRToMIRLower` (moved verbatim so the `Equations` leaf can cite the
definitions without importing this proof monolith). This module imports it
back; everything below cites the same names in the same namespace. -/

/-! ## C3 infrastructure: now in `Morph.Proofs.Branch.Infra` -/

/- The growth/freshness/`_inv` families, `BranchStep`/`BranchStmts`/`ArmStmts`
inversions, `execBlockFromIn`/`execInstrsFullFromIn` equations, merge/join
executors, and assembly helpers live in the Infra leaf (moved verbatim).
This module imports it back; the workers below cite those names. -/


/-! ## Arm worker: now in `Morph.Proofs.Branch.ArmTotal` -/

/- The fallthrough arm worker (`lowerStmtsCFG_arm_total`) plus the
carried-register / header-phi executor groundwork live in the ArmTotal leaf
(moved verbatim). This module imports it back; the `broke`/`continued`/
loop-body workers below cite those names. -/


/-! ## Arm execution on `break`: now in `Morph.Proofs.Branch.ArmBroke` -/

/- The arm-`break` worker lives in the ArmBroke leaf (moved verbatim).
This module imports it back; the `continued`/loop-body workers below
cite it for breaking arms. -/



/-! ## Arm execution on `continue`: now in `Morph.Proofs.Branch.ArmContinued` -/

/- The arm-`continue` worker lives in the ArmContinued leaf (moved verbatim).
This module imports it back; the loop-body worker below cites it for
continuing arms. -/


/-! ## Loop-body execution: now in `Morph.Proofs.Branch.LoopBodyRun` -/

/- The C7 spine worker (`lowerStmtsCFG_loopBody_run`) lives in the
LoopBodyRun leaf (moved verbatim). This module imports it back;
everything downstream cites it. -/


/-! ## Oracle facts: now in `Morph.Proofs.Branch.Oracle` -/

/- The interpreter-side facts (`runHIRWhile_*` cases, lookup preservation,
eval literals, bind-arm HIR facts) live in the Oracle leaf (moved verbatim).
This module imports it back; the bind-arm workers below cite those names. -/


/-! ## Binding arms: now in `Morph.Proofs.Branch.BindArm` -/

/- The C2c binding-arm family (`bindArm_rho_agree`, `_inv`, `_fresh`, the
join executors, `bindArm_grows`, `bindArm_total`) lives in the BindArm leaf
(moved verbatim). This module imports it back; everything downstream cites
those names. -/


/-! ## Loop-body lookup preservation: now in `Morph.Proofs.Branch.LoopLookup` -/

/- The `LoopBodyLookupAux` section and its followers live in the LoopLookup
leaf (moved verbatim). This module imports it back; the spine lemmas below
cite those names. -/


/-! ## Spine: now in `Morph.Proofs.Branch.Spine` -/

/- `spine_P` through `header_loop_correct` live in the Spine leaf (moved
verbatim). This module imports it back; `whileLoop_correct` cites those
names. -/


/-! ## Loop execution core: now in `Morph.Proofs.Branch.WhileLoop` -/

/- `whileLoop_correct` (with its design NOTE) lives in the WhileLoop leaf
(moved verbatim). This module imports it back; `lowerStmtsCFG_total`'s
`whileStmt` case cites exactly that interface. -/


/-! ## The body worker: now in `Morph.Proofs.Branch.Total` -/

/- `lowerStmtsCFG_total` lives in the Total leaf (moved verbatim). This
module imports it back; the binding-arm `if` worker below cites it for
the merged-env tail. -/


/-! ## The binding-arm `if` worker: now in `Morph.Proofs.Branch.IfTotal` -/

/- `lowerStmtsCFG_bindArm_if_total` lives in the IfTotal leaf (moved
verbatim). This module imports it back; the closed top-level wrapper
below discharges its worker contracts via `bindArm_total`. -/


/-! ## Capstone: now in `Morph.Proofs.Branch.TopLevel` -/

/- The closed wrappers, the top-level invariant, and the two program
corollaries live in the TopLevel leaf (moved verbatim). This module
imports it back; the concrete programs below cite those names. -/



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
