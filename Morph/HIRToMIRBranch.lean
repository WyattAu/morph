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
imports it back; the Evidence leaf cites those names. -/



/-! ## Evidence: now in `Morph.Proofs.Branch.Evidence` -/

/- The concrete programs (`ifProg`, `ifProgFalse`, `ifThenAdd`,
`bindIfAssignProg`, `bindIfAssignFalseProg`, `nestedThenProg`,
`nestedElseProg`, `whileCountProg`, `whileBreakProg`) and their
`native_decide` / end-to-end pins live in the Evidence leaf (moved
verbatim). This module imports nothing back; Evidence cites this
module's theorems. -/


end Morph.HIRToMIRCorrect
