/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal
import Morph.Proofs.Branch.Merge
import Morph.Proofs.Branch.LoopAlloc

/-!
# Stage C lowering: `Lowered`, `lowerStmtsCFG`, `lowerProgramCFG`

Home of the CFG lowering definitions, moved verbatim from
`Morph.HIRToMIRBranch` § "The lowering" so the `Morph.Proofs.Branch.Equations`
leaf can state one rewrite equation per constructor without importing the
proof monolith (which would be an import cycle). `Morph.HIRToMIRBranch`
imports this module back; every proof citing `lowerStmtsCFG`,
`lowerProgramCFG`, or `Lowered` is unaffected (same namespace, same names,
same definitional behavior — verify by byte-diff against the extraction
source plus a green tree).
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-! ## The lowering -/

/-- The block a worker was asked to fill, plus every block it produced beyond
that one. `instrs`/`term` are the filled block's body; `blocks` are the others in
*forward emission order* — `lowerProgramCFG` reverses them for printing, and the
last element is the segment's exit block (the join when the tail after an `if`
is block-free, else the tail's own exit), which is what the `if` case needs as
a phi predecessor. -/
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

/-- Back-edge predecessors of a lowered loop body: blocks (other than the
body's exit block) whose terminator jumps back to the header `nextB`.
`mkHeaderPhis` takes these as the trampoline set. Named once (instead of
inlining the `filterMap` at every use) so the lowering body, the equation
leaf, and the worker proofs all cite one constant: the `fun b => match
b.terminator …` closure elaborates its equation-compiler matcher exactly
once, and `rw` matching stays syntactic across modules (an inlined copy in
another module generates a different matcher constant and silently stops
rewriting — loop 185). -/
def backEdgePreds (lb : Lowered) (nextB : MIR.BlockId) : List MIR.BlockId :=
  lb.blocks.filterMap (fun b =>
    match b.terminator with
    | .goto t =>
        if t == nextB &&
            b.id != (lb.blocks.getLast?.map
              fun b => b.id).getD (nextB + 2) then
          some b.id
        else none
    | _ => none)

/-- Lower a statement list into block `bId`.

- `cont = none`: a completed list returns its value (the program body).
- `cont = some b`: a completed list jumps to `b` (an arm, or a body tail).
- `arm = true`: binding statements are refused (see `ArmStmts`).
- `hasVal`: whether a value has been produced on this path. An arm that
  produced none (empty, or `nop`s only) must still deliver the HIR value
  `unit`, so its nil case emits `const unit` instead of passing `lastVal`
  through (which would leak the incoming accumulator — loop 176 found
  `5; if true {} else {}` lowering to `5`). Bodies keep `lastVal`: their
  accumulator flows through. Arms start at `false`; `exprStmt` and a nested
  `if` set it (their value always materializes); `returnStmt` is terminal.

Block ids: `bId` is the caller's; the two arms take `nextB`/`nextB + 1`, the join
takes `nextB + 2`, and lowering continues from `nextB + 3`.

`loop` threads the enclosing loop's context into a loop body (`break`/`continue`
targets plus the carried registers); it is `none` everywhere else — arms,
rests, and the top level. A `while` under `some _` is refused (no nesting,
see the C7a section note). -/
def lowerStmtsCFG (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (arm : Bool) (ρ : List (HIR.Id × ValId)) (supply : Nat) (nextB : MIR.BlockId)
    (lastVal : ValId) (hasVal : Bool) (loop : Option LoopInfo := none) :
    List HIR.Stmt → Option Lowered
  | [] =>
      match arm, hasVal with
      | true, false =>
          some ⟨[.const supply .unit],
                (match cont with | none => .return_ supply | some t => .goto t),
                [], supply, ρ, supply + 1, nextB⟩
      | _, _ =>
          some ⟨[], (match cont with | none => .return_ lastVal | some t => .goto t),
                [], lastVal, ρ, supply, nextB⟩
  | .nop :: rest => lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal loop rest
  -- Match form, not `do`: `simp only [lowerStmtsCFG]` plus `simp only []`
  -- reduce these exactly as in Stage A (`lowerStmts`), while `do`-notation
  -- `Bind.bind` needs full `simp`, which also normalizes the block assembly
  -- (`[T] ++ X` to `T :: X`) and breaks the syntactic match the C3 invariant
  -- proofs rely on. Everything is inlined (no `let`) so `rw` finds the
  -- recursive calls syntactically.
  | .exprStmt e :: rest =>
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerStmtsCFG bId cont arm ρ s1 nextB v true loop rest with
          | some L => some { L with instrs := ie ++ L.instrs }
          | none => none
      | none => none
  | .varDecl id _τ init :: rest =>
      match arm with
      | true =>
          -- Phase B (C2c): top-level arms (`loop = none`) may bind; the join
          -- merges via `mergeIds`/`mkMergePhis`. Loop-body arms
          -- (`loop = some _`) still refuse, guarding the loop workers.
          match loop with
          | some _ => none
          | none =>
          match lowerExpr ρ supply init with
          | some (vb, ib, s1) =>
              match lowerStmtsCFG bId cont arm ((id, vb) :: ρ) s1 nextB lastVal true loop rest with
              | some L => some { L with instrs := ib ++ L.instrs }
              | none => none
          | none => none
      | false =>
          match loop with
          | some _ => none
          | none =>
          match lowerExpr ρ supply init with
          | some (vb, ib, s1) =>
              match lowerStmtsCFG bId cont arm ((id, vb) :: ρ) s1 nextB lastVal true loop rest with
              | some L => some { L with instrs := ib ++ L.instrs }
              | none => none
          | none => none
  | .assign id e :: rest =>
      match arm with
      | true =>
          -- Phase B (C2c): top-level arms (`loop = none`) may bind; the join
          -- merges via `mergeIds`/`mkMergePhis`. Loop-body arms
          -- (`loop = some _`) still refuse, guarding the loop workers.
          match loop with
          | some _ => none
          | none =>
          match lowerExpr ρ supply e with
          | some (v, ie, s1) =>
              match lowerStmtsCFG bId cont arm (updAssoc ρ id v) s1 nextB lastVal true loop rest with
              | some L => some { L with instrs := ie ++ L.instrs }
              | none => none
          | none => none
      | false =>
          match lowerExpr ρ supply e with
          | some (v, ie, s1) =>
              match lowerStmtsCFG bId cont arm (updAssoc ρ id v) s1 nextB lastVal true loop rest with
              | some L => some { L with instrs := ie ++ L.instrs }
              | none => none
          | none => none
  | .returnStmt e :: _ =>
      match lowerExpr ρ supply e with
      | some (v, ie, s1) => some ⟨ie, .return_ v, [], v, ρ, s1, nextB⟩
      | none => none
  -- The merged value: one phi per incoming edge, both writing `vm`
  -- (`Le.supply`). The edge's *source* is the block that jumps to the join,
  -- which is the arm's own block only when the arm emitted none of its own.
  -- An arm holding a nested `if` ends in that `if`'s join, and that block is
  -- the predecessor — using the arm's own block there would name a block
  -- whose terminator branches into the arm's first block instead, so the phi
  -- would never fire and the join would return an unbound register (found in
  -- loop 161 by encoding `if (1 < 2) { if (3 < 4) { 7 } else { 8 } } else { 9 }`).
  | .ifStmt c th el :: rest =>
      match lowerExpr ρ supply c with
      | none => none
      | some (vc, ic, s1) =>
          match lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3) lastVal false loop th with
          | none => none
          | some lt =>
              match lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ lt.supply lt.next lastVal false loop el with
              | none => none
              | some le =>
                  -- Phase B (C2c): when either arm rebinds, the join merges
                  -- every rebound id via `mergeIds`/`mkMergePhis` and lowers
                  -- the tail under the merged env. Binding-free arms (every
                  -- `ArmStmts` arm, including all loop-body arms) have an
                  -- empty merge set, so they take the old join verbatim —
                  -- the C3 workers discharge `mergeIds ρ lt.ρ le.ρ = []` via
                  -- `arm_rho` and continue on the old path.
                  match mergeIds ρ lt.ρ le.ρ with
                  | [] =>
                      match lowerStmtsCFG (nextB + 2) cont arm ρ (le.supply + 1) le.next le.supply true loop rest with
                      | none => none
                      | some lr =>
                          some { instrs := ic
                                 term := .branch vc nextB (nextB + 1)
                                 blocks := lt.blocks ++ [⟨nextB, lt.instrs, lt.term⟩]
                                           ++ le.blocks ++ [⟨nextB + 1, le.instrs, le.term⟩]
                                           ++ [⟨nextB + 2,
                                               [.phi le.supply ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) lt.val,
                                                .phi le.supply ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1)) le.val] ++ lr.instrs,
                                               lr.term⟩] ++ lr.blocks
                                 val := lr.val
                                 ρ := lr.ρ
                                 supply := lr.supply
                                 -- `lr.next + 1`, not `lr.next`: the join block itself
                                 -- carries id `nextB + 2`, and `rest` may allocate
                                 -- nothing (so `lr.next` can equal `nextB + 2`). The
                                 -- invariant needs every produced id strictly below
                                 -- `L.next`, and nesting needs the outer ids to start
                                 -- strictly above the inner ones, so the high-water
                                 -- mark must clear the join id even when `rest` is empty.
                                 next := lr.next + 1 }
                  | mids =>
                          match mkMergePhis ρ lt.ρ le.ρ (le.supply + 1)
                              ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB)
                              ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1))
                              mids with
                          | none => none
                          | some (mphis, s2, ρm) =>
                              match lowerStmtsCFG (nextB + 2) cont arm ρm s2 le.next le.supply true loop rest with
                              | none => none
                              | some lr =>
                                  some { instrs := ic
                                         term := .branch vc nextB (nextB + 1)
                                         blocks := lt.blocks ++ [⟨nextB, lt.instrs, lt.term⟩]
                                                   ++ le.blocks ++ [⟨nextB + 1, le.instrs, le.term⟩]
                                                   ++ [⟨nextB + 2,
                                                       [.phi le.supply ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) lt.val,
                                                        .phi le.supply ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1)) le.val] ++ mphis ++ lr.instrs,
                                                       lr.term⟩] ++ lr.blocks
                                         val := lr.val
                                         ρ := lr.ρ
                                         supply := lr.supply
                                         next := lr.next + 1 }
  -- `break`/`continue` need their loop's targets; outside a loop they refuse
  -- (the previous catch-all behavior). `continue` snapshots the carried
  -- registers first, so the header sees the current env under fixed names.
  | .break :: _ =>
      match loop with
      | none => none
      | some info =>
          match carryCopies ρ info.carried with
          | none => none
          | some copies =>
              some ⟨copies, .goto info.exit, [], lastVal, ρ, supply, nextB⟩
  | .continue :: _ =>
      match loop with
      | none => none
      | some info =>
          match carryCopies ρ info.carried with
          | none => none
          | some copies =>
              some ⟨copies, .goto info.header, [], lastVal, ρ, supply, nextB⟩
  -- A loop is entry (goto header), header (carried phis, cond, branch to body
  -- or exit), body (falls back to the header, `break` exits), exit (the rest
  -- runs with the loop's unit value). No nesting: under `some _` this is `none`.
  -- The condition lowers in the body-entry env `ρb`, not `ρ`: the header
  -- re-evaluates it every iteration, when each carried id already lives in its
  -- carried register. Lowering it in `ρ` would freeze the entry values and
  -- loop forever on any counter. Ids with no pre-loop binding need no phi
  -- (assigning them is a no-op on both sides), so they are filtered out.
  | .whileLoop c body :: rest =>
      match loop with
      | some _ => none
      | none =>
          match mkCarried ρ supply
              ((dedupIds (assignedIds body)).filterMap
                (fun id => (rhoLookup ρ id).map (fun _ => id))) with
          | none => none
          | some (carried, sA, ρb) =>
              match lowerExpr ρb sA c with
              | none => none
              | some (vc, ic, s1) =>
                  match lowerStmtsCFG (nextB + 2) (some nextB) false ρb (s1 + 1)
                      (nextB + 3) s1 true
                      (loop := some ⟨nextB, nextB + 1, carried⟩) body with
                  | none => none
                  | some lb =>
                      match lowerStmtsCFG (nextB + 1) cont arm ρb
                          (lb.supply + 1) lb.next lb.supply true loop rest with
                      | none => none
                      | some lr =>
                          match mkHeaderPhis ρ bId carried
                              ((lb.blocks.getLast?.map fun b => b.id).getD
                                (nextB + 2))
                              lb.ρ
                              (backEdgePreds lb nextB) with
                          | none => none
                          | some phis =>
                              some { instrs := []
                                     term := .goto nextB
                                     blocks := lb.blocks ++
                                               [⟨nextB + 2,
                                                 .const s1 .unit :: lb.instrs,
                                                 lb.term⟩] ++
                                               [⟨nextB,
                                                 phis ++ ic,
                                                 .branch vc (nextB + 2)
                                                   (nextB + 1)⟩] ++
                                               [⟨nextB + 1,
                                                 .const lb.supply .unit ::
                                                   lr.instrs,
                                                 lr.term⟩] ++ lr.blocks
                                     val := lr.val
                                     ρ := lr.ρ
                                     supply := lr.supply
                                     next := lr.next }
  | _ :: _ => none

/-- Lower a program to a MIR CFG. Register 0 is the unit prologue (as in
`lowerProgram`), block 0 is the entry, and the arms' blocks start at 1. -/
def lowerProgramCFG (prog : HIR.Program) : Option Func := do
  let L ← lowerStmtsCFG 0 none false [] 1 1 0 false none prog.stmts
  some ⟨"main", [], ⟨0, .const 0 .unit :: L.instrs, L.term⟩ :: L.blocks.reverse,
    0, .unitType⟩

end Morph.HIRToMIRCorrect
