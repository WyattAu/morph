/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal

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

/-! ## Fuel: one computable budget for the whole stage (scope §4.4)

C3's theorem cannot carry a literal fuel constant. `if` costs three blocks (its
condition block, the taken arm, the join) and C7's loops cost a block per
iteration, so a constant chosen for `if` is wrong for `while` and every later
statement in the stage would have to repair it. `blockBound` is that budget,
stated once.

It takes the oracle's own step fuel as well as the statement list. That
parameter is **inert** for the fragment that exists today — an `if` traverses a
fixed number of blocks whatever the oracle's fuel — and C7's `whileLoop` case is
where it stops being inert, because an iteration consumes oracle fuel and the
block budget must be allowed to depend on it. Taking it now is the same move as
the program parameter on `MIR.execFuncIn`: the *statement* survives, even the
part of it that is currently vacuous.
-/

/-- Extra blocks a statement list adds beyond the one it starts in. An `if` adds
three: its condition block, the taken arm, and the join. Nested `if`s inside an
arm add to that arm's own count, and only one arm is traversed, so the arms are
combined with `max`. Statements that stay inside their block add nothing. -/
def armBlockBound (fuel : Nat) : List HIR.Stmt → Nat
  | [] => 0
  | s :: rest =>
      match s with
      | .ifStmt _ th el =>
          3 + max (armBlockBound fuel th) (armBlockBound fuel el)
            + armBlockBound fuel rest
      | _ => armBlockBound fuel rest

/-- Block budget for a body: the entry block plus whatever branching adds.
C3, C4b and C7 state their executor fuel as `blockBound fuelH stmts` rather than
a literal, so the arithmetic lives here instead of in every theorem. -/
def blockBound (fuel : Nat) (stmts : List HIR.Stmt) : Nat :=
  1 + armBlockBound fuel stmts

-- `HIR.Stmt` and `HIR.Expr` are mutually recursive, so recursion through an
-- arm is not structural: the equations below are `armBlockBound.eq_def`'s
-- branches, not `rfl`-reductions. Downstream proofs should rewrite with these
-- lemmas (they are `[simp]`), never with the definition name.

@[simp] theorem armBlockBound_nil (fuel : Nat) : armBlockBound fuel [] = 0 := by
  rw [armBlockBound.eq_def]

@[simp] theorem armBlockBound_if (fuel : Nat) (c : HIR.Expr)
    (th el rest : List HIR.Stmt) :
    armBlockBound fuel (.ifStmt c th el :: rest) =
      3 + max (armBlockBound fuel th) (armBlockBound fuel el)
        + armBlockBound fuel rest := by
  rw [armBlockBound.eq_def]

/-- A statement that is not an `if` stays inside the block it starts in, so it
adds no blocks to the list's bound. -/
theorem armBlockBound_cons_not_if (fuel : Nat) {s : HIR.Stmt}
    {rest : List HIR.Stmt} (h : ∀ c th el, s ≠ .ifStmt c th el) :
    armBlockBound fuel (s :: rest) = armBlockBound fuel rest := by
  rw [armBlockBound.eq_def]
  cases s with
  | ifStmt c th el => exact absurd rfl (h c th el)
  | _ => rfl

/-- `if`-free statement lists never leave their block, so their budget is one
block. This is the case every Stage A/B program falls into. -/
theorem armBlockBound_eq_zero_of_forall_not_if (fuel : Nat) :
    ∀ {ss : List HIR.Stmt}, (∀ s ∈ ss, ∀ c th el, s ≠ .ifStmt c th el) →
      armBlockBound fuel ss = 0
  | [], _ => armBlockBound_nil fuel
  | s :: rest, h => by
      rw [armBlockBound_cons_not_if fuel (fun c th el => h s (List.mem_cons_self ..) c th el)]
      exact armBlockBound_eq_zero_of_forall_not_if fuel
        (fun s' hs' c th el => h s' (List.mem_cons_of_mem _ hs') c th el)

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
takes `nextB + 2`, and lowering continues from `nextB + 3`. -/
def lowerStmtsCFG (bId : MIR.BlockId) (cont : Option MIR.BlockId)
    (arm : Bool) (ρ : List (HIR.Id × ValId)) (supply : Nat) (nextB : MIR.BlockId)
    (lastVal : ValId) (hasVal : Bool) : List HIR.Stmt → Option Lowered
  | [] =>
      match arm, hasVal with
      | true, false =>
          some ⟨[.const supply .unit],
                (match cont with | none => .return_ supply | some t => .goto t),
                [], supply, ρ, supply + 1, nextB⟩
      | _, _ =>
          some ⟨[], (match cont with | none => .return_ lastVal | some t => .goto t),
                [], lastVal, ρ, supply, nextB⟩
  | .nop :: rest => lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal rest
  -- Match form, not `do`: `simp only [lowerStmtsCFG]` plus `simp only []`
  -- reduce these exactly as in Stage A (`lowerStmts`), while `do`-notation
  -- `Bind.bind` needs full `simp`, which also normalizes the block assembly
  -- (`[T] ++ X` to `T :: X`) and breaks the syntactic match the C3 invariant
  -- proofs rely on. Everything is inlined (no `let`) so `rw` finds the
  -- recursive calls syntactically.
  | .exprStmt e :: rest =>
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerStmtsCFG bId cont arm ρ s1 nextB v true rest with
          | some L => some { L with instrs := ie ++ L.instrs }
          | none => none
      | none => none
  | .varDecl id _τ init :: rest =>
      match arm with
      | true => none
      | false =>
          match lowerExpr ρ supply init with
          | some (vb, ib, s1) =>
              match lowerStmtsCFG bId cont arm ((id, vb) :: ρ) s1 nextB lastVal true rest with
              | some L => some { L with instrs := ib ++ L.instrs }
              | none => none
          | none => none
  | .assign id e :: rest =>
      match arm with
      | true => none
      | false =>
          match lowerExpr ρ supply e with
          | some (v, ie, s1) =>
              match lowerStmtsCFG bId cont arm (updAssoc ρ id v) s1 nextB lastVal true rest with
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
          match lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1 (nextB + 3) lastVal false th with
          | none => none
          | some lt =>
              match lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ lt.supply lt.next lastVal false el with
              | none => none
              | some le =>
                  match lowerStmtsCFG (nextB + 2) cont arm ρ (le.supply + 1) le.next le.supply true rest with
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
  | _ :: _ => none

/-- Lower a program to a MIR CFG. Register 0 is the unit prologue (as in
`lowerProgram`), block 0 is the entry, and the arms' blocks start at 1. -/
def lowerProgramCFG (prog : HIR.Program) : Option Func := do
  let L ← lowerStmtsCFG 0 none false [] 1 1 0 false prog.stmts
  some ⟨"main", [], ⟨0, .const 0 .unit :: L.instrs, L.term⟩ :: L.blocks.reverse,
    0, .unitType⟩

/-! ## C3 infrastructure: the lowering only grows, and block ids are unique

Loop 174. C3's induction runs the lowered blocks, so it needs three facts
about `lowerStmtsCFG`: supply and block ids only grow, every produced block
id lies in `[nextB, L.next)`, and the produced id sets are duplicate-free.
The induction is on the fragment predicates (`BranchStmts`/`ArmStmts`), not
on the statement list — an `if`'s arms are not structural subterms of the
list, but they are subterms of the predicate proof, and `ArmStmts` having no
`varDecl`/`assign` constructor is what discharges the lowering's arm refusal
without an extra contradiction case. -/

/-- Appending duplicate-free id lists with no shared id keeps duplicate-free
ids. The workhorse for the six-part `if` assembly. -/
theorem nodup_concat {l₁ l₂ : List Nat} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a as ih =>
      rw [List.cons_append, List.nodup_cons] at ⊢
      rw [List.nodup_cons] at h₁
      obtain ⟨hnotin, hnod⟩ := h₁
      refine ⟨?_, ih hnod (fun x hx y hy => hd x (List.mem_cons_of_mem _ hx) y hy)⟩
      intro hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hnotin h
      · exact hd _ (List.mem_cons_self ..) _ h rfl

/-- A block list with duplicate-free ids answers `find?` by membership: the
first match is the block itself, because no other block shares its id. -/
theorem findBlock_of_nodup_mem {l : List Block} {b : Block}
    (hnod : (l.map Block.id).Nodup) (hmem : b ∈ l) :
    l.find? (fun b' => b'.id == b.id) = some b := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
      rw [List.map_cons, List.nodup_cons] at hnod
      obtain ⟨hnotin, hnodtl⟩ := hnod
      cases hb : (hd.id == b.id) with
      | true =>
          have hid : hd.id = b.id := by simpa using hb
          have hnotmem : b ∉ tl := fun h => hnotin (List.mem_map.mpr ⟨b, h, hid.symm⟩)
          have heq : hd = b := by
            rcases List.mem_cons.mp hmem with h | h
            · exact h.symm
            · exact absurd h hnotmem
          subst heq
          simp only [List.find?, hb]
      | false =>
          have hmemtl : b ∈ tl := by
            rcases List.mem_cons.mp hmem with h | h
            · exfalso
              have ht := beq_self_eq_true (b.id)
              rw [← h] at hb
              rw [hb] at ht
              exact Bool.false_ne_true ht
            · exact h
          simp only [List.find?, hb]
          exact ih hnodtl hmemtl

private theorem ne_of_lt_nat' {a b : Nat} (h : a < b) : a ≠ b :=
  Nat.ne_of_lt h

private theorem ne_of_gt_nat' {a b : Nat} (h : a > b) : a ≠ b :=
  (Nat.ne_of_lt h).symm

/-- The six block groups of a lowered `if` have pairwise-disjoint id ranges
— arms below their joins, joins below the next call's ids — so the whole
assembly is duplicate-free. Stated on id lists, so the caller never has to
reassociate the block concatenation: the conclusion is definitionally the
pushed-through map. -/
theorem if_assembly_nodup {nextB ltNext leNext lrNext : Nat}
    {A B C : List Block} {thenB elseB joinB : Block}
    (hmnt : nextB + 3 ≤ ltNext) (hmne : ltNext ≤ leNext) (_hmnr : leNext ≤ lrNext)
    (hbndA : ∀ b ∈ A, nextB + 3 ≤ b.id ∧ b.id < ltNext)
    (hbndB : ∀ b ∈ B, ltNext ≤ b.id ∧ b.id < leNext)
    (hbndC : ∀ b ∈ C, leNext ≤ b.id ∧ b.id < lrNext)
    (hthen : thenB.id = nextB) (helse : elseB.id = nextB + 1)
    (hjoin : joinB.id = nextB + 2)
    (hnodA : (A.map Block.id).Nodup) (hnodB : (B.map Block.id).Nodup)
    (hnodC : (C.map Block.id).Nodup) :
    ((A ++ [thenB] ++ B ++ [elseB] ++ [joinB] ++ C).map Block.id).Nodup := by
  have hbA : ∀ x ∈ A.map Block.id, nextB + 3 ≤ x ∧ x < ltNext := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbndA b hb
  have hbB : ∀ x ∈ B.map Block.id, ltNext ≤ x ∧ x < leNext := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbndB b hb
  have hbC : ∀ x ∈ C.map Block.id, leNext ≤ x ∧ x < lrNext := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbndC b hb
  have e1 : ([nextB + 2] ++ C.map Block.id).Nodup :=
    nodup_concat (by simp) hnodC (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨hloC, -⟩ := hbC y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
        (Nat.le_trans (Nat.le_trans hmnt hmne) hloC)))
  have e2 : ([nextB + 1] ++ ([nextB + 2] ++ C.map Block.id)).Nodup :=
    nodup_concat (by simp) e1 (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with rfl | hy
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 1 < 2 from by decide) nextB)
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
          (Nat.le_trans (Nat.le_trans hmnt hmne) hloC)))
  have e3 : (B.map Block.id ++
      ([nextB + 1] ++ ([nextB + 2] ++ C.map Block.id))).Nodup :=
    nodup_concat hnodB e2 (by
      intro x hx y hy
      obtain ⟨hloB, hhiB⟩ := hbB x hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with rfl | rfl | hy
      · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
          (Nat.le_trans hmnt hloB))
      · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
          (Nat.le_trans hmnt hloB))
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiB hloC))
  have e4 : ([nextB] ++ (B.map Block.id ++
      ([nextB + 1] ++ ([nextB + 2] ++ C.map Block.id)))).Nodup :=
    nodup_concat (by simp) e3 (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl | rfl | hy
      · obtain ⟨hloB, -⟩ := hbB y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 0 < 3 from by decide) x)
          (Nat.le_trans hmnt hloB))
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 0 < 1 from by decide) x)
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 0 < 2 from by decide) x)
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 0 < 3 from by decide) x)
          (Nat.le_trans (Nat.le_trans hmnt hmne) hloC)))
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    hthen, helse, hjoin]
  exact nodup_concat hnodA e4 (by
    intro x hx y hy
    obtain ⟨hloA, hhiA⟩ := hbA x hx
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with rfl | hy | rfl | rfl | hy
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 0 < 3 from by decide) y)
        hloA)
    · obtain ⟨hloB, -⟩ := hbB y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiA hloB)
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
        hloA)
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
        hloA)
    · obtain ⟨hloC, -⟩ := hbC y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiA (Nat.le_trans hmne hloC)))

mutual

/-- Master invariant over the straight-line-carrying fragment: supply and
block ids only grow, every produced block id is fresh for the call and
below the returned supply of ids, and the produced ids are duplicate-free.
`arm` is fixed `false`: bindings are allowed and the lowering handles them. -/
theorem lowerStmtsCFG_branch_inv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont false ρ supply nextB lastVal hasVal ss = some L →
      BranchStmts budget ss →
      nextB ≤ L.next ∧ supply ≤ L.supply ∧
        (∀ b ∈ L.blocks, nextB ≤ b.id ∧ b.id < L.next) ∧
        (L.blocks.map Block.id).Nodup := by
  intro bId cont ρ supply nextB lastVal hasVal ss
  induction ss generalizing bId cont ρ supply nextB lastVal hasVal with
  | nil =>
      intro L h hss
      cases hss with
      | nil =>
          simp only [lowerStmtsCFG.eq_def] at h
          simp at h
          subst h
          exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
            List.nodup_nil⟩
  | cons s rest ih =>
      intro L h hss
      cases hss with
      | cons hs hrs =>
          cases hs with
          | exprStmt e hstr _ =>
              simp [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v0, ie, s1⟩ := p
                  rw [he] at h
                  simp at h
                  cases hr : lowerStmtsCFG bId cont false ρ s1 nextB v0 true rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp at h
                      subst h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr hrs
                      exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
          | varDecl id τ init hstr _ =>
              simp [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp at h
                  cases hr : lowerStmtsCFG bId cont false ((id, vb) :: ρ) s1
                      nextB lastVal true rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp at h
                      subst h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr hrs
                      exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
          | assign id e hstr _ =>
              simp [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp at h
                  cases hr : lowerStmtsCFG bId cont false (updAssoc ρ id v) s1
                      nextB lastVal true rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp at h
                      subst h
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                      obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr hrs
                      exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
          | nop =>
              simp [lowerStmtsCFG] at h
              cases hr : lowerStmtsCFG bId cont false ρ supply nextB
                  lastVal hasVal rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp at h
                  subst h
                  obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr hrs
                  exact ⟨hmn, hms, hbnd, hnod⟩
          | ifStmt c th el hstr _ hath hael =>
              -- Peel with `unfold`, never `simp`: full `simp` normalizes the
              -- block assembly (`[T] ++ X` to `T :: X`), breaking the syntactic
              -- match the membership split and `if_assembly_nodup` need.
              simp only [lowerStmtsCFG] at h
              cases heC : lowerExpr ρ supply c with
              | none => rw [heC] at h; simp at h
              | some p =>
                  obtain ⟨vc, ic, s1⟩ := p
                  rw [heC] at h
                  simp only [] at h
                  cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                      (nextB + 3) lastVal false th with
                  | none => rw [ht] at h; simp at h
                  | some lt =>
                      rw [ht] at h
                      simp only [] at h
                      cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                          true ρ lt.supply lt.next lastVal false el with
                      | none => rw [he] at h; simp at h
                      | some le =>
                          rw [he] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) cont false ρ
                              (le.supply + 1) le.next le.supply true rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              obtain rfl := Option.some.inj h
                              dsimp only at ⊢
                              have hs1 : supply ≤ s1 :=
                                lower_mono.1 _ _ _ _ _ _ heC
                              obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ ht hath
                              obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ he
                                  hael
                              obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                                ih _ _ _ _ _ _ _ _ hr hrs
                              refine ⟨by omega, by omega, ?_, ?_⟩
                              · intro b hb
                                simp only [List.mem_append, List.mem_singleton] at hb
                                rcases hb with (((((hb | rfl) | hb) | rfl) | rfl) | hb)
                                · obtain ⟨hlo, hhi⟩ := hbndt b hb
                                  exact ⟨Nat.le_trans (Nat.le_add_right _ _) hlo,
                                    Nat.lt_of_lt_of_le hhi (Nat.le_trans hmne
                                      (Nat.le_trans hmnr (Nat.le_succ _)))⟩
                                · exact ⟨Nat.le_refl _,
                                    Nat.lt_of_le_of_lt (Nat.le_trans
                                      (Nat.le_trans (Nat.le_trans
                                        (Nat.le_add_right _ _) hmnt) hmne) hmnr)
                                      (Nat.lt_succ_self _)⟩
                                · obtain ⟨hlo, hhi⟩ := hbnde b hb
                                  exact ⟨Nat.le_trans (Nat.le_trans
                                      (Nat.le_add_right _ _) hmnt) hlo,
                                    Nat.lt_of_lt_of_le hhi (Nat.le_trans hmnr
                                      (Nat.le_succ _))⟩
                                · exact ⟨Nat.le_succ _,
                                    Nat.lt_of_le_of_lt (Nat.le_trans
                                      (Nat.le_trans (Nat.le_trans
                                        (Nat.le_trans (Nat.le_succ _)
                                          (Nat.le_succ _)) hmnt) hmne) hmnr)
                                      (Nat.lt_succ_self _)⟩
                                · exact ⟨Nat.le_add_right _ _,
                                    Nat.lt_of_le_of_lt (Nat.le_trans
                                      (Nat.le_trans (Nat.le_trans
                                        (Nat.le_succ _) hmnt) hmne) hmnr)
                                      (Nat.lt_succ_self _)⟩
                                · obtain ⟨hlo, hhi⟩ := hbndr b hb
                                  exact ⟨Nat.le_trans (Nat.le_trans
                                      (Nat.le_trans (Nat.le_add_right _ _)
                                        hmnt) hmne) hlo,
                                    Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                              · exact if_assembly_nodup (A := lt.blocks)
                                  (B := le.blocks) (C := lr.blocks)
                                  (thenB := ⟨nextB, lt.instrs, lt.term⟩)
                                  (elseB := ⟨nextB + 1, le.instrs, le.term⟩)
                                  (joinB := ⟨nextB + 2,
                                    [Instr.phi le.supply ((lt.blocks.getLast?.map
                                      (fun b => b.id)).getD nextB) lt.val,
                                     Instr.phi le.supply ((le.blocks.getLast?.map
                                      (fun b => b.id)).getD (nextB + 1)) le.val] ++
                                      lr.instrs,
                                    lr.term⟩)
                                  hmnt hmne hmnr hbndt hbnde hbndr
                                  rfl rfl rfl hnodt hnode hnodr
      | returnStmt e _ hstr _ =>
          simp [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp at h
              subst h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              exact ⟨Nat.le_refl _, hs1, fun b hb => by simp at hb,
                List.nodup_nil⟩

/-- Same invariant for arms: `arm` is fixed `true`, so the lowering never
takes a binding branch and `ArmStmts` has no such constructor to match. -/
theorem lowerStmtsCFG_arm_inv (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal ss = some L →
      ArmStmts budget ss →
      nextB ≤ L.next ∧ supply ≤ L.supply ∧
        (∀ b ∈ L.blocks, nextB ≤ b.id ∧ b.id < L.next) ∧
        (L.blocks.map Block.id).Nodup := by
  intro bId cont ρ supply nextB lastVal hasVal ss L h hss
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal L with
  | nil =>
      simp only [lowerStmtsCFG.eq_def] at h
      cases hv : hasVal with
      | true =>
          simp only [hv] at h
          simp at h
          subst h
          exact ⟨Nat.le_refl _, Nat.le_refl _, fun b hb => by simp at hb,
            List.nodup_nil⟩
      | false =>
          simp only [hv] at h
          simp at h
          subst h
          -- The valueless arm emits `const unit` into a fresh register.
          exact ⟨Nat.le_refl _, Nat.le_succ _, fun b hb => by simp at hb,
            List.nodup_nil⟩
  | exprStmt e rest hstr _ hrs ih =>
      simp [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp at h
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v0 true rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp at h
              subst h
              have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
              obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr
              exact ⟨hmn, Nat.le_trans hs1 hms, hbnd, hnod⟩
  | nop rest hrs ih =>
      simp [lowerStmtsCFG] at h
      cases hr : lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal rest with
      | none => rw [hr] at h; simp at h          | some q =>
              rw [hr] at h
              simp at h
              subst h
              obtain ⟨hmn, hms, hbnd, hnod⟩ := ih _ _ _ _ _ _ _ _ hr
              exact ⟨hmn, hms, hbnd, hnod⟩
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      simp only [lowerStmtsCFG] at h
      cases heC : lowerExpr ρ supply c with
      | none => rw [heC] at h; simp at h
      | some p =>
          obtain ⟨vc, ic, s1⟩ := p
          rw [heC] at h
          simp only [] at h
          cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
              (nextB + 3) lastVal false th with
          | none => rw [ht] at h; simp at h
          | some lt =>
              rw [ht] at h
              simp only [] at h
              cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                  lt.supply lt.next lastVal false el with
              | none => rw [he] at h; simp at h
              | some le =>
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                      (le.supply + 1) le.next le.supply true rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      dsimp only at ⊢
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                      obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                        iht _ _ _ _ _ _ _ _ ht
                      obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                        ihe _ _ _ _ _ _ _ _ he
                      obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                        ihr _ _ _ _ _ _ _ _ hr
                      refine ⟨by omega, by omega, ?_, ?_⟩
                      · intro b hb
                        simp only [List.mem_append, List.mem_singleton] at hb
                        rcases hb with (((((hb | rfl) | hb) | rfl) | rfl) | hb)
                        · obtain ⟨hlo, hhi⟩ := hbndt b hb
                          exact ⟨Nat.le_trans (Nat.le_add_right _ _) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_trans hmne
                              (Nat.le_trans hmnr (Nat.le_succ _)))⟩
                        · exact ⟨Nat.le_refl _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_add_right _ _) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · obtain ⟨hlo, hhi⟩ := hbnde b hb
                          exact ⟨Nat.le_trans (Nat.le_trans
                              (Nat.le_add_right _ _) hmnt) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_trans hmnr
                              (Nat.le_succ _))⟩
                        · exact ⟨Nat.le_succ _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_trans (Nat.le_succ _)
                                  (Nat.le_succ _)) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · exact ⟨Nat.le_add_right _ _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_succ _) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
                        · obtain ⟨hlo, hhi⟩ := hbndr b hb
                          exact ⟨Nat.le_trans (Nat.le_trans
                              (Nat.le_trans (Nat.le_add_right _ _)
                                hmnt) hmne) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                      · exact if_assembly_nodup (A := lt.blocks)
                          (B := le.blocks) (C := lr.blocks)
                          (thenB := ⟨nextB, lt.instrs, lt.term⟩)
                          (elseB := ⟨nextB + 1, le.instrs, le.term⟩)
                          (joinB := ⟨nextB + 2,
                            [Instr.phi le.supply ((lt.blocks.getLast?.map
                              (fun b => b.id)).getD nextB) lt.val,
                             Instr.phi le.supply ((le.blocks.getLast?.map
                              (fun b => b.id)).getD (nextB + 1)) le.val] ++
                              lr.instrs,
                            lr.term⟩)
                          hmnt hmne hmnr hbndt hbnde hbndr
                          rfl rfl rfl hnodt hnode hnodr
  | returnStmt e rest hstr _ =>
      simp [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp at h
          subst h
          have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
          exact ⟨Nat.le_refl _, hs1, fun b hb => by simp at hb,
            List.nodup_nil⟩

end

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

/-! ## C3 worker helpers: inversions, one-block steps, phi pairs

Loop 175. The worker induction (next) mirrors `lowerStmts_total`: list
induction for the body, predicate induction for the arms, expression steps
via `lower_total.1`, environment preservation via `RelEnv_exec`. What is new
is block dispatch, so these helpers isolate it: projection-style inversions
(the `StraightStmts_*` idiom — `cases` on the predicate never touches the
locals the worker still needs), one-block unfold equations for each
terminator, the join's phi pair firing on the taken edge, and the bridge
from edge-aware execution back to `execInstrsFull` for phi-free expression
code. -/

theorem BranchStep_exprStmt {budget : Nat} {e : HIR.Expr}
    (h : BranchStep budget (.exprStmt e)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | exprStmt _ hs hb => exact ⟨hs, hb⟩

theorem BranchStep_varDecl {budget : Nat} {id : HIR.Id} {τ : Typ}
    {init : HIR.Expr} (h : BranchStep budget (.varDecl id τ init)) :
    IsStraight init ∧ SLWeight init < budget := by
  cases h with
  | varDecl _ _ _ hs hb => exact ⟨hs, hb⟩

theorem BranchStep_assign {budget : Nat} {id : HIR.Id} {e : HIR.Expr}
    (h : BranchStep budget (.assign id e)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | assign _ _ hs hb => exact ⟨hs, hb⟩

theorem BranchStep_if {budget : Nat} {c : HIR.Expr} {th el : List HIR.Stmt}
    (h : BranchStep budget (.ifStmt c th el)) :
    IsStraight c ∧ SLWeight c < budget ∧
      ArmStmts budget th ∧ ArmStmts budget el := by
  cases h with
  | ifStmt _ _ _ hs hb ht he => exact ⟨hs, hb, ht, he⟩

theorem BranchStmts_exprStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : BranchStmts budget (.exprStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget ∧ BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      obtain ⟨hstr, hb⟩ := BranchStep_exprStmt hs
      exact ⟨hstr, hb, hrs⟩

theorem BranchStmts_varDecl {budget : Nat} {id : HIR.Id} {τ : Typ}
    {init : HIR.Expr} {rest : List HIR.Stmt}
    (h : BranchStmts budget (.varDecl id τ init :: rest)) :
    IsStraight init ∧ SLWeight init < budget ∧ BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      obtain ⟨hstr, hb⟩ := BranchStep_varDecl hs
      exact ⟨hstr, hb, hrs⟩

theorem BranchStmts_assign {budget : Nat} {id : HIR.Id} {e : HIR.Expr}
    {rest : List HIR.Stmt} (h : BranchStmts budget (.assign id e :: rest)) :
    IsStraight e ∧ SLWeight e < budget ∧ BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      obtain ⟨hstr, hb⟩ := BranchStep_assign hs
      exact ⟨hstr, hb, hrs⟩

theorem BranchStmts_nop {budget : Nat} {rest : List HIR.Stmt}
    (h : BranchStmts budget (.nop :: rest)) : BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      cases hs with
      | nop => exact hrs

theorem BranchStmts_returnStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : BranchStmts budget (.returnStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | cons hs _ => cases hs
  | returnStmt _ _ hs hb => exact ⟨hs, hb⟩

theorem BranchStmts_if {budget : Nat} {c : HIR.Expr} {th el rest : List HIR.Stmt}
    (h : BranchStmts budget (.ifStmt c th el :: rest)) :
    IsStraight c ∧ SLWeight c < budget ∧
      ArmStmts budget th ∧ ArmStmts budget el ∧ BranchStmts budget rest := by
  cases h with
  | cons hs hrs =>
      obtain ⟨hstr, hb, ht, he⟩ := BranchStep_if hs
      exact ⟨hstr, hb, ht, he, hrs⟩

theorem ArmStmts_exprStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : ArmStmts budget (.exprStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget ∧ ArmStmts budget rest := by
  cases h with
  | exprStmt _ _ hs hb hr => exact ⟨hs, hb, hr⟩

theorem ArmStmts_nop {budget : Nat} {rest : List HIR.Stmt}
    (h : ArmStmts budget (.nop :: rest)) : ArmStmts budget rest := by
  cases h with
  | nop _ hr => exact hr

theorem ArmStmts_if {budget : Nat} {c : HIR.Expr} {th el rest : List HIR.Stmt}
    (h : ArmStmts budget (.ifStmt c th el :: rest)) :
    IsStraight c ∧ SLWeight c < budget ∧
      ArmStmts budget th ∧ ArmStmts budget el ∧ ArmStmts budget rest := by
  cases h with
  | ifStmt _ _ _ _ hs hb ht he hr => exact ⟨hs, hb, ht, he, hr⟩

theorem ArmStmts_returnStmt {budget : Nat} {e : HIR.Expr} {rest : List HIR.Stmt}
    (h : ArmStmts budget (.returnStmt e :: rest)) :
    IsStraight e ∧ SLWeight e < budget := by
  cases h with
  | returnStmt _ _ hs hb => exact ⟨hs, hb⟩

/-- One block, `return` terminator: run the instructions, read the register. -/
theorem execBlockFromIn_return (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId) (is : List Instr) (v : ValId)
    (fenv fenv' : FullEnv)
    (hexec : execInstrsFullFromIn prog prev fenv is = some fenv') :
    execBlockFromIn prog (F + 1) f prev ⟨id, is, .return_ v⟩ fenv =
      fenv'.env v := by
  have hstep : execBlockFromIn prog (F + 1) f prev ⟨id, is, .return_ v⟩ fenv =
      (match execInstrsFullFromIn prog prev fenv is with
       | none => none
       | some fenv' => fenv'.env v) := rfl
  rw [hstep, hexec]

/-- One block, `goto` terminator: run the instructions, continue at the target
with the block as the predecessor edge. -/
theorem execBlockFromIn_goto (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId) (is : List Instr)
    (t : MIR.BlockId) (fenv fenv' : FullEnv) (b' : Block)
    (hexec : execInstrsFullFromIn prog prev fenv is = some fenv')
    (hfind : findBlock f t = some b') :
    execBlockFromIn prog (F + 1) f prev ⟨id, is, .goto t⟩ fenv =
      execBlockFromIn prog F f (some id) b' fenv' := by
  have hstep : execBlockFromIn prog (F + 1) f prev ⟨id, is, .goto t⟩ fenv =
      (match execInstrsFullFromIn prog prev fenv is with
       | none => none
       | some fenv' =>
           match findBlock f t with
           | some b' => execBlockFromIn prog F f (some id) b' fenv'
           | none => none) := rfl
  rw [hstep, hexec, hfind]

/-- Replacing an entry block's instruction prefix with its result: when the
prefix runs to `fenv1`, the block runs the same as the suffix block from
`fenv1`. The worker uses it to peel expression code (`ie`) off the front of
an entry block, leaving the rest segment's entry for the induction
hypothesis. -/
theorem execBlockFromIn_instrs_prefix (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId)
    (pre suf : List Instr) (t : Terminator) (fenv fenv1 : FullEnv)
    (happ : execInstrsFullFromIn prog prev fenv (pre ++ suf) =
      execInstrsFullFromIn prog prev fenv1 suf) :
    execBlockFromIn prog (F + 1) f prev ⟨id, pre ++ suf, t⟩ fenv =
      execBlockFromIn prog (F + 1) f prev ⟨id, suf, t⟩ fenv1 := by
  simp only [execBlockFromIn, happ]

/-- One block, `branch` terminator, condition true: continue at `t`. -/
theorem execBlockFromIn_branch_true (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId) (is : List Instr)
    (c : ValId) (t e : MIR.BlockId) (fenv fenv' : FullEnv) (b' : Block)
    (hexec : execInstrsFullFromIn prog prev fenv is = some fenv')
    (hbool : fenv'.boolOf c = some true)
    (hfind : findBlock f t = some b') :
    execBlockFromIn prog (F + 1) f prev ⟨id, is, .branch c t e⟩ fenv =
      execBlockFromIn prog F f (some id) b' fenv' := by
  have hstep : execBlockFromIn prog (F + 1) f prev ⟨id, is, .branch c t e⟩ fenv =
      (match execInstrsFullFromIn prog prev fenv is with
       | none => none
       | some fenv' =>
           match fenv'.boolOf c with
           | some true =>
               match findBlock f t with
               | some b' => execBlockFromIn prog F f (some id) b' fenv'
               | none => none
           | some false =>
               match findBlock f e with
               | some b' => execBlockFromIn prog F f (some id) b' fenv'
               | none => none
           | none => none) := rfl
  rw [hstep, hexec]
  simp only [hbool, hfind]

/-- One block, `branch` terminator, condition false: continue at `e`. -/
theorem execBlockFromIn_branch_false (prog : Program) (F : Nat) (f : Func)
    (prev : Option MIR.BlockId) (id : MIR.BlockId) (is : List Instr)
    (c : ValId) (t e : MIR.BlockId) (fenv fenv' : FullEnv) (b' : Block)
    (hexec : execInstrsFullFromIn prog prev fenv is = some fenv')
    (hbool : fenv'.boolOf c = some false)
    (hfind : findBlock f e = some b') :
    execBlockFromIn prog (F + 1) f prev ⟨id, is, .branch c t e⟩ fenv =
      execBlockFromIn prog F f (some id) b' fenv' := by
  have hstep : execBlockFromIn prog (F + 1) f prev ⟨id, is, .branch c t e⟩ fenv =
      (match execInstrsFullFromIn prog prev fenv is with
       | none => none
       | some fenv' =>
           match fenv'.boolOf c with
           | some true =>
               match findBlock f t with
               | some b' => execBlockFromIn prog F f (some id) b' fenv'
               | none => none
           | some false =>
               match findBlock f e with
               | some b' => execBlockFromIn prog F f (some id) b' fenv'
               | none => none
           | none => none) := rfl
  rw [hstep, hexec]
  simp only [hbool, hfind]

/-- The join's phi pair on the taken edge: arriving from `p` fires the
`p`-phi, skips the other edge's phi, and runs the rest of the block with the
merged register bound. The miss side needs the edges distinct, which the
worker has from the exit-id ranges. -/
theorem execInstrsFullFromIn_phis_hit (prog : Program) (p : MIR.BlockId)
    (fenv : FullEnv) (vm : ValId) (te ee : MIR.BlockId) (tv ev : ValId)
    (ris : List Instr) (wv : Value)
    (hte : te = p) (hne : ee ≠ p) (hsrc : fenv.env tv = some wv) :
    execInstrsFullFromIn prog (some p) fenv
        ([.phi vm te tv, .phi vm ee ev] ++ ris) =
      execInstrsFullFromIn prog (some p)
        ⟨fenv.env.update vm wv, fenv.store⟩ ris := by
  simp only [List.cons_append, List.nil_append]
  rw [execInstrsFullFromIn_eq, execInstrsFullFromIn_eq,
    execInstrsFullFrom_phi_hit _ _ _ _ _ _ hte, hsrc]
  simp only [execInstrsFullFrom_phi_miss _ _ _ _ _ _ hne]

/-- A pure instruction is never a phi: the worker feeds this to the bridge
below for every expression-emitted instruction. -/
theorem IsPure_not_phi {i : Instr} (h : IsPure i) (dst : ValId)
    (pred : MIR.BlockId) (src : ValId) : i ≠ .phi dst pred src := by
  cases h with
  | const _ _ => simp
  | copy _ _ => simp
  | unop _ _ _ _ => simp
  | binop _ _ _ _ _ => simp

/-- Edge-aware execution agrees with straight-line execution on phi-free
instruction lists: the program parameter is inert (that is
`execInstrsFullFromIn_eq`) and the edge parameter only matters to phis. The
worker uses it to run `lowerExpr` code inside blocks via `lower_total.1`. -/
theorem execInstrsFullFromIn_of_noPhi (prog : Program) (prev : Option MIR.BlockId)
    (fenv : FullEnv) (is : List Instr)
    (h : ∀ dst pred src, .phi dst pred src ∉ is) :
    execInstrsFullFromIn prog prev fenv is = execInstrsFull fenv is := by
  rw [execInstrsFullFromIn_eq]
  induction is generalizing fenv with
  | nil => rfl
  | cons i rest ih =>
      have hhead : ∀ dst pred src, i ≠ .phi dst pred src := by
        intro dst pred src hphi
        exact h dst pred src (hphi ▸ List.mem_cons_self)
      rw [execInstrsFullFrom_nonphi prev fenv hhead]
      cases he : evalInstrFull fenv i with
      | none => simp only [execInstrsFull, he]
      | some fenv' =>
          simp only [execInstrsFull, he]
          exact ih fenv'
            (fun d p s hm => h d p s (List.mem_cons_of_mem _ hm))

/-- A boolean register reads back through `boolOf`. -/
theorem boolOf_of_lit (fenv : FullEnv) (c : ValId) (b : Bool)
    (h : fenv.env c = some (Value.bool b)) : fenv.boolOf c = some b := by
  simp only [FullEnv.boolOf, h]

/-- Edge-aware execution splits over instruction append: run the prefix,
then run the suffix from the resulting environment. The worker uses it to
separate expression code (run env-explicitly via `lower_total.1`) from the
rest of an entry block. -/
theorem execInstrsFullFrom_append (prev : Option MIR.BlockId) (fenv : FullEnv)
    (l₁ l₂ : List Instr) :
    execInstrsFullFrom prev fenv (l₁ ++ l₂) =
      match execInstrsFullFrom prev fenv l₁ with
      | none => none
      | some fenv1 => execInstrsFullFrom prev fenv1 l₂ := by
  induction l₁ generalizing fenv with
  | nil => simp [execInstrsFullFrom]
  | cons i rest ih =>
      by_cases hi : ∃ dst pred src, i = .phi dst pred src
      · obtain ⟨dst, pred, src, rfl⟩ := hi
        cases prev with
        | none =>
            simp only [List.cons_append]
            rw [execInstrsFullFrom_phi_none, execInstrsFullFrom_phi_none, ih]
        | some p =>
            by_cases hp : pred = p
            · cases hsrc : fenv.env src with
              | none =>
                  have h1 : execInstrsFullFrom (some p) fenv
                      (.phi dst pred src :: (rest ++ l₂)) = none := by
                    rw [execInstrsFullFrom_phi_hit _ _ _ _ _ _ hp, hsrc]
                  have h2 : execInstrsFullFrom (some p) fenv
                      (.phi dst pred src :: rest) = none := by
                    rw [execInstrsFullFrom_phi_hit _ _ _ _ _ _ hp, hsrc]
                  simp only [List.cons_append]
                  rw [h1, h2]
              | some v =>
                  have h1 : execInstrsFullFrom (some p) fenv
                      (.phi dst pred src :: (rest ++ l₂)) =
                      execInstrsFullFrom (some p)
                        ⟨fenv.env.update dst v, fenv.store⟩ (rest ++ l₂) := by
                    rw [execInstrsFullFrom_phi_hit _ _ _ _ _ _ hp, hsrc]
                  have h2 : execInstrsFullFrom (some p) fenv
                      (.phi dst pred src :: rest) =
                      execInstrsFullFrom (some p)
                        ⟨fenv.env.update dst v, fenv.store⟩ rest := by
                    rw [execInstrsFullFrom_phi_hit _ _ _ _ _ _ hp, hsrc]
                  simp only [List.cons_append]
                  rw [h1, h2, ih]
            · have h1 : execInstrsFullFrom (some p) fenv
                    (.phi dst pred src :: (rest ++ l₂)) =
                    execInstrsFullFrom (some p) fenv (rest ++ l₂) :=
                execInstrsFullFrom_phi_miss _ _ _ _ _ _ hp
              have h2 : execInstrsFullFrom (some p) fenv
                    (.phi dst pred src :: rest) =
                    execInstrsFullFrom (some p) fenv rest :=
                execInstrsFullFrom_phi_miss _ _ _ _ _ _ hp
              simp only [List.cons_append]
              rw [h1, h2, ih]
      · have hnp : ∀ dst pred src, i ≠ .phi dst pred src :=
          fun d p s h => hi ⟨d, p, s, h⟩
        simp only [List.cons_append]
        rw [execInstrsFullFrom_nonphi prev fenv hnp]
        cases he : evalInstrFull fenv i with
        | none =>
            have h1 : execInstrsFullFrom prev fenv (i :: rest) = none := by
              rw [execInstrsFullFrom_nonphi prev fenv hnp, he]
            rw [h1]
        | some fenv' =>
            have h1 : execInstrsFullFrom prev fenv (i :: rest) =
                execInstrsFullFrom prev fenv' rest := by
              rw [execInstrsFullFrom_nonphi prev fenv hnp, he]
            rw [h1]
            simp only [ih]

/-- Program-aware execution splits too: the program parameter is inert. -/
theorem execInstrsFullFromIn_append (prog : Program)
    (prev : Option MIR.BlockId) (fenv : FullEnv) (l₁ l₂ : List Instr) :
    execInstrsFullFromIn prog prev fenv (l₁ ++ l₂) =
      match execInstrsFullFromIn prog prev fenv l₁ with
      | none => none
      | some fenv1 => execInstrsFullFromIn prog prev fenv1 l₂ := by
  simp only [execInstrsFullFromIn_eq, execInstrsFullFrom_append]

/-- A lowered entry block never starts with a phi: `L.instrs` is expression
code (`lower_isPure`), and phis only appear in join blocks, which live in
`L.blocks`. The worker uses it to run entry instructions edge-blind via
`execInstrsFullFromIn_of_noPhi`. The induction is on the list, not the
fragment predicates: `L.instrs` depends only on the spine (never on arms),
so the `if` case needs no induction hypothesis. -/
theorem lowerStmtsCFG_instrs_pure :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (arm : Bool)
      (ρ : List (HIR.Id × ValId)) (supply nextB : Nat) (lastVal : ValId)
      (hasVal : Bool) (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont arm ρ supply nextB lastVal hasVal ss = some L →
      ∀ i ∈ L.instrs, IsPure i := by
  intro bId cont arm ρ supply nextB lastVal hasVal ss
  induction ss generalizing bId cont arm ρ supply nextB lastVal hasVal with
  | nil =>
      intro L h i hi
      cases arm with
      | true =>
          cases hasVal with
          | false =>
              simp only [lowerStmtsCFG.eq_def] at h
              obtain rfl := Option.some.inj h
              dsimp only at hi
              simp only [List.mem_singleton] at hi
              subst hi
              exact IsPure.const _ _
          | true =>
              simp only [lowerStmtsCFG.eq_def] at h
              obtain rfl := Option.some.inj h
              dsimp only at hi
              simp at hi
      | false =>
          simp only [lowerStmtsCFG.eq_def] at h
          obtain rfl := Option.some.inj h
          dsimp only at hi
          simp at hi
  | cons s rest ih =>
      cases s with
      | exprStmt e =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v0, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              cases hr : lowerStmtsCFG bId cont arm ρ s1 nextB v0 true rest with
              | none => rw [hr] at h; simp at h
              | some q =>
                  rw [hr] at h
                  simp only [] at h
                  obtain rfl := Option.some.inj h
                  simp only [List.mem_append] at hi
                  rcases hi with hi | hi
                  · exact lower_isPure.1 _ _ _ _ _ _ he _ hi
                  · exact ih _ _ _ _ _ _ _ _ _ hr _ hi
      | varDecl id τ init =>
          intro L h i hi
          cases arm with
          | true =>
              simp only [lowerStmtsCFG] at h
              simp at h
          | false =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId cont false ((id, vb) :: ρ) s1
                      nextB lastVal true rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      simp only [List.mem_append] at hi
                      rcases hi with hi | hi
                      · exact lower_isPure.1 _ _ _ _ _ _ he _ hi
                      · exact ih _ _ _ _ _ _ _ _ _ hr _ hi
      | assign id e =>
          intro L h i hi
          cases arm with
          | true =>
              simp only [lowerStmtsCFG] at h
              simp at h
          | false =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId cont false (updAssoc ρ id v)
                      s1 nextB lastVal true rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      simp only [List.mem_append] at hi
                      rcases hi with hi | hi
                      · exact lower_isPure.1 _ _ _ _ _ _ he _ hi
                      · exact ih _ _ _ _ _ _ _ _ _ hr _ hi
      | nop =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases hr : lowerStmtsCFG bId cont arm ρ supply nextB lastVal
              hasVal rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              obtain rfl := Option.some.inj h
              exact ih _ _ _ _ _ _ _ _ _ hr _ hi
      | ifStmt c th el =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases heC : lowerExpr ρ supply c with
          | none => rw [heC] at h; simp at h
          | some p =>
              obtain ⟨vc, ic, s1⟩ := p
              rw [heC] at h
              simp only [] at h
              cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                  (nextB + 3) lastVal false th with
              | none => rw [ht] at h; simp at h
              | some lt =>
                  rw [ht] at h
                  simp only [] at h
                  cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                      lt.supply lt.next lastVal false el with
                  | none => rw [he] at h; simp at h
                  | some le =>
                      rw [he] at h
                      simp only [] at h
                      cases hr : lowerStmtsCFG (nextB + 2) cont arm ρ
                          (le.supply + 1) le.next le.supply true rest with
                      | none => rw [hr] at h; simp at h
                      | some lr =>
                          rw [hr] at h
                          simp only [] at h
                          obtain rfl := Option.some.inj h
                          exact lower_isPure.1 _ _ _ _ _ _ heC _ hi
      | returnStmt e =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              exact lower_isPure.1 _ _ _ _ _ _ he _ hi
      | «break» =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          simp at h
      | «continue» =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          simp at h
      | whileLoop _ _ =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          simp at h
      | matchStmt _ _ =>
          intro L h i hi
          simp only [lowerStmtsCFG] at h
          simp at h

/-- Membership in the six-part `if` assembly, by part. The worker feeds
these to `hsub`/`findBlock_of_nodup_mem` without re-counting the append
nesting at every call site. -/
theorem if_asm_mem_of_lt {lt le lr : List Block} {T E J : Block} {b : Block}
    (h : b ∈ lt) : b ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ h))))

theorem if_asm_mem_then {lt le lr : List Block} {T E J : Block} :
    T ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (by simp)))))

theorem if_asm_mem_of_le {lt le lr : List Block} {T E J : Block} {b : Block}
    (h : b ∈ le) : b ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h)))

theorem if_asm_mem_else {lt le lr : List Block} {T E J : Block} :
    E ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (by simp)))

theorem if_asm_mem_join {lt le lr : List Block} {T E J : Block} :
    J ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_left _ (List.mem_append_right _ (by simp))

theorem if_asm_mem_of_lr {lt le lr : List Block} {T E J : Block} {b : Block}
    (h : b ∈ lr) : b ∈ lt ++ [T] ++ le ++ [E] ++ [J] ++ lr :=
  List.mem_append_right _ h

/-- Arm lowering never rebinds: `ρ` flows through unchanged (there is no
`updAssoc` in `arm` mode — `varDecl`/`assign` lower to `none`). The worker
needs it to transport the arm's `RelEnv` into the rest segment. -/
theorem lowerStmtsCFG_arm_rho (budget : Nat) :
    ∀ (bId : MIR.BlockId) (cont : Option MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId cont true ρ supply nextB lastVal hasVal ss = some L →
      ArmStmts budget ss →
      L.ρ = ρ := by
  intro bId cont ρ supply nextB lastVal hasVal ss L h hss
  induction hss generalizing bId cont ρ supply nextB lastVal hasVal L with
  | nil =>
      simp only [lowerStmtsCFG.eq_def] at h
      cases hv : hasVal with
      | true =>
          simp only [hv] at h
          obtain rfl := Option.some.inj h
          rfl
      | false =>
          simp only [hv] at h
          obtain rfl := Option.some.inj h
          rfl
  | exprStmt e rest hstr _ hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v0, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          cases hr : lowerStmtsCFG bId cont true ρ s1 nextB v0 true rest with
          | none => rw [hr] at h; simp at h
          | some q =>
              rw [hr] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              show q.ρ = ρ
              exact ih _ _ _ _ _ _ _ _ hr
  | nop rest hrs ih =>
      simp only [lowerStmtsCFG] at h
      cases hr : lowerStmtsCFG bId cont true ρ supply nextB lastVal
          hasVal rest with
      | none => rw [hr] at h; simp at h
      | some q =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          show q.ρ = ρ
          exact ih _ _ _ _ _ _ _ _ hr
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      simp only [lowerStmtsCFG] at h
      cases heC : lowerExpr ρ supply c with
      | none => rw [heC] at h; simp at h
      | some p =>
          obtain ⟨vc, ic, s1⟩ := p
          rw [heC] at h
          simp only [] at h
          cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
              (nextB + 3) lastVal false th with
          | none => rw [ht] at h; simp at h
          | some lt =>
              rw [ht] at h
              simp only [] at h
              cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                  lt.supply lt.next lastVal false el with
              | none => rw [he] at h; simp at h
              | some le =>
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) cont true ρ
                      (le.supply + 1) le.next le.supply true rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      show lr.ρ = ρ
                      exact ihr _ _ _ _ _ _ _ _ hr
  | returnStmt e rest hstr _ =>
      simp only [lowerStmtsCFG] at h
      cases he : lowerExpr ρ supply e with
      | none => rw [he] at h; simp at h
      | some p =>
          obtain ⟨v, ie, s1⟩ := p
          rw [he] at h
          simp only [] at h
          obtain rfl := Option.some.inj h
          rfl

/-- A block whose instructions are phi-free runs the same from any
predecessor edge: the program parameter is inert on non-phis
(`execInstrsFullFromIn_eq`) and the terminator dispatch never consults the
edge. The worker uses it to align the rest segment's entry (reached from
the arm's exit) with the induction hypothesis (stated from the rest's own
exit). -/
theorem execBlockFromIn_prev_irrelevant_of_noPhi (prog : Program) (F : Nat)
    (f : Func) (prev1 prev2 : Option MIR.BlockId) (b : Block)
    (fenv : FullEnv)
    (h : ∀ dst pred src, .phi dst pred src ∉ b.instrs) :
    execBlockFromIn prog F f prev1 b fenv =
      execBlockFromIn prog F f prev2 b fenv := by
  cases F with
  | zero => rfl
  | succ F' =>
      have h1 : ∀ (p : Option MIR.BlockId),
          execInstrsFullFromIn prog p fenv b.instrs =
            execInstrsFull fenv b.instrs :=
        fun p => execInstrsFullFromIn_of_noPhi prog p fenv b.instrs h
      simp only [execBlockFromIn, h1]

/-- The assembly's exit is the tail's exit: with `[J]` emitted before
`lr.blocks`, `getLast?` finds the tail's last block (or `J` itself when the
tail is block-free, whose id is the join). The worker rewrites its goal
with this to meet the rest segment's induction hypothesis. -/
theorem if_assembly_exit {lt le lr : List Block} {T E J : Block}
    {bId nextJoin : MIR.BlockId}
    (hJ : J.id = nextJoin) :
    (((lt ++ [T] ++ le ++ [E] ++ [J] ++ lr).getLast?.map
      (fun b => b.id)).getD bId) =
    ((lr.getLast?.map (fun b => b.id)).getD nextJoin) := by
  cases hlr : lr with
  | nil =>
      subst hlr
      have hX : (lt ++ [T] ++ le ++ [E] ++ [J]).getLast? = some J :=
        List.getLast?_concat
      rw [List.append_nil, hX]
      show J.id = nextJoin
      exact hJ
  | cons hd tl =>
      have hne : hd :: tl ≠ [] := by simp
      have hsome : (hd :: tl).getLast? = some ((hd :: tl).getLast hne) :=
        (List.getLast?_eq_some_getLast hne).symm
      have h1 : (lt ++ [T] ++ le ++ [E] ++ [J] ++ (hd :: tl)).getLast? =
          (hd :: tl).getLast? := by
        rw [List.getLast?_append, hsome]
        rfl
      rw [h1, hsome]
      simp

/-- `getLast?` only returns members: the worker needs it to place an arm's
exit block inside its id range. -/
theorem getLast?_mem {α : Type} :
    ∀ {l : List α} {a : α}, l.getLast? = some a → a ∈ l
  | [], _ => by
      intro h
      exact absurd h (by simp)
  | hd :: tl, _ => by
      intro h
      have hne : hd :: tl ≠ [] := by simp
      have hg := List.getLast?_eq_some_getLast hne
      rw [hg] at h
      have ha : _ = (hd :: tl).getLast hne := (Option.some.inj h).symm
      rw [ha]
      exact List.getLast_mem hne

/-- Arm worker: executing an arm segment's entry block runs the HIR arm. On
fallthrough the run arrives at the join block with the arm's value in its
register and both environments related; on `return` the entry block itself
returns the value. The conclusion is equational (arrival state
existential, fuel squeezed between the remaining budget and the caller's
`C`) so the caller — the body worker's `if` case — can chain it into the
rest segment without any continuation hypothesis: the join's phis and the
rest are the caller's business, discharged with the exit formula below.

The HIR run is over the arm alone (arms always run from `unit`), so no
append-composition lemma is needed: the caller already inverts the whole
run into arm-run and rest-run. The two `hasVal` premises say exactly when
the register file is known to hold the accumulator: a produced value is
present, and a valueless arm runs from `unit` (loop 176 — this is what
makes the empty-arm equation close). -/
theorem lowerStmtsCFG_arm_total (budget : Nat) :
    ∀ (bId j : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId (some j) true ρ supply nextB lastVal hasVal ss =
        some L →
      ArmStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      (hasVal = false → accH = .unit) →
      (hasVal = true → fenv.env lastVal = some accH) →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv ss (.value (.lit accH)) = (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId)
        (jblock : Block) (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      findBlock f j = some jblock →
      ∀ (fuelB C : Nat), F ≥ blockBound fuelB ss + C →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
        ∃ F' fenv_arr, F' ≤ F ∧ F' ≥ C ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv
            = execBlockFromIn prog F' f
                (some ((L.blocks.getLast?.map (fun b => b.id)).getD bId))
                jblock fenv_arr ∧
          RelEnv henv' L.ρ fenv_arr.env ∧ fenv_arr.env L.val = some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
        execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
          some w_e) := by
  intro bId j ρ supply nextB lastVal hasVal ss L h hss hfresh hlast
  induction hss generalizing bId j ρ supply nextB lastVal hasVal L with
  | nil =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG.eq_def] at h
        cases hv : hasVal with
        | false =>
            simp only [hv] at h
            obtain rfl := Option.some.inj h
            have hbb : blockBound fuelB ([] : List HIR.Stmt) = 1 := by
              simp [blockBound]
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                have h2 : henv = henv' := congrArg Prod.snd hrun
                have hu : u = .lit accH := by
                  rw [← h1] at hout
                  exact (HFlow.value.inj hout).symm
                have hacc : accH = .unit := hval0 hv
                cases F with
                | zero => omega
                | succ F' =>
                    have hnp : ∀ dst pred src,
                        .phi dst pred src ∉ ([.const supply .unit] : List Instr) := by
                      intro d p s hm
                      simp only [List.mem_singleton] at hm
                      exact IsPure_not_phi (IsPure.const _ _)
                        _ _ _ hm.symm
                    have hexec : execInstrsFullFromIn prog prev fenv
                        [.const supply .unit] =
                        some ⟨fenv.env.update supply .unit, fenv.store⟩ := by
                      rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
                      exact execInstrsFull_singleton _ _ _
                        (by simp [evalInstrFull])
                    refine ⟨accH, hu, F',
                      ⟨fenv.env.update supply .unit, fenv.store⟩,
                      Nat.le_succ _, ?_, ?_, ?_, ?_⟩
                    · omega
                    · dsimp only
                      exact execBlockFromIn_goto prog F' f prev bId
                        [.const supply .unit] j fenv _ jblock hexec hfind
                    · rw [← h2]
                      intro id u hlook
                      obtain ⟨w, hlookH, hreg0⟩ := hrel id u hlook
                      have hu2 : u < supply :=
                        hfresh id u (rhoLookup_some_mem ρ id u hlook)
                      have hne : u ≠ supply := Nat.ne_of_lt hu2
                      refine ⟨w, hlookH, ?_⟩
                      have hupd : (fenv.env.update supply .unit) u
                          = fenv.env u := by simp [Env.update, hne]
                      show (fenv.env.update supply .unit) u = some w
                      rw [hupd]
                      exact hreg0
                    · simp [Env.update, hacc]
          | true =>
              simp only [hv] at h
              obtain rfl := Option.some.inj h
              cases fuelH with
              | zero =>
                  have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                      (.value (.lit accH)) = (.stuck, henv) := rfl
                  rw [hz] at hrun
                  have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                  rw [hst] at hout
                  exact absurd hout (by simp)
              | succ fh =>
                  have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                      (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                  rw [hstep] at hrun
                  have h1 : (.value (.lit accH)) = out :=
                    congrArg Prod.fst hrun
                  have h2 : henv = henv' := congrArg Prod.snd hrun
                  have hu : u = .lit accH := by
                    rw [← h1] at hout
                    exact (HFlow.value.inj hout).symm
                  cases F with
                  | zero =>
                      have hbb : blockBound fuelB ([] : List HIR.Stmt)
                          = 1 := by simp [blockBound]
                      omega
                  | succ F' =>
                      refine ⟨accH, hu, F', fenv, Nat.le_succ _, ?_, ?_,
                        ?_, ?_⟩
                      · have hbb : blockBound fuelB ([] : List HIR.Stmt)
                            = 1 := by simp [blockBound]
                        omega
                      · dsimp only
                        exact execBlockFromIn_goto prog F' f prev bId [] j
                          fenv fenv jblock rfl hfind
                      · rw [← h2]; exact hrel
                      · exact hreg hv
      · intro e hout
        simp only [lowerStmtsCFG.eq_def] at h
        cases hv : hasVal with
        | false =>
            simp only [hv] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                rw [← h1] at hout
                exact absurd hout (by simp)
        | true =>
            simp only [hv] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                rw [← h1] at hout
                exact absurd hout (by simp)
  | exprStmt e rest hstr _ hrs ih =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v0, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            cases hr : lowerStmtsCFG bId (some j) true ρ s1 nextB v0 true rest with
            | none => rw [hr] at h; simp at h
            | some Lr =>
                rw [hr] at h
                simp only [] at h
                obtain rfl := Option.some.inj h
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.exprStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv (.exprStmt e :: rest)
                        (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => runHIRStmts fh henv rest (.value v)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                            hregE⟩ :=
                          lower_total.1 ρ supply e v0 ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        rw [hrE] at hrun
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        have hregE' : fenv1.env v0 = some wE := hww ▸ hregE
                        have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                        have hf1 : FreshAbove ρ s1 :=
                          FreshAbove.mono ρ supply s1 hs1 hfresh
                        have hlast1 : v0 < s1 :=
                          lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                        have hrel1 : RelEnv henv ρ fenv1.env :=
                          RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1
                            hrel hfresh hexec1
                        have hnp_ie : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                        have hexec_ie : execInstrsFullFromIn prog prev fenv ie
                            = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp_ie]
                          exact hexec1
                        have happ : execInstrsFullFromIn prog prev fenv
                            (ie ++ Lr.instrs) =
                            execInstrsFullFromIn prog prev fenv1 Lr.instrs := by
                          rw [execInstrsFullFromIn_append, hexec_ie]
                        have hbb : blockBound fuelB (.exprStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)]
                        cases F with
                        | zero =>
                            have h1 : blockBound fuelB rest ≥ 1 := by
                              rw [blockBound]; omega
                            omega
                        | succ F'' =>
                            have hLHS : execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, ie ++ Lr.instrs, Lr.term⟩ fenv =
                                execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, Lr.instrs, Lr.term⟩ fenv1 :=
                                execBlockFromIn_instrs_prefix prog F'' f prev bId ie
                                Lr.instrs Lr.term fenv fenv1 happ
                            have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                              rw [← hbb]; exact hg
                            have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                              fun b hb => hsub b hb
                            obtain ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                                hrel_arr, hreg_arr⟩ :=
                              ((ih bId j ρ s1 nextB v0 true Lr hr hf1
                                hlast1 wE henv fenv1 hrel1
                                (fun hh => absurd hh (by simp)) (fun _ => hregE')
                                fh henv' out hrun prog f prev jblock (F'' + 1)
                                hsub' hnodf hfind fuelB C hg' u).1 hout)
                            exact ⟨w_u, hu, F', fenv_arr, hle, hge,
                              hLHS.trans heq_rest, hrel_arr, hreg_arr⟩
      · intro e_ret hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v0, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            cases hr : lowerStmtsCFG bId (some j) true ρ s1 nextB v0 true rest with
            | none => rw [hr] at h; simp at h
            | some Lr =>
                rw [hr] at h
                simp only [] at h
                obtain rfl := Option.some.inj h
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.exprStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv (.exprStmt e :: rest)
                        (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => runHIRStmts fh henv rest (.value v)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                            hregE⟩ :=
                          lower_total.1 ρ supply e v0 ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        rw [hrE] at hrun
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        have hregE' : fenv1.env v0 = some wE := hww ▸ hregE
                        have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ he
                        have hf1 : FreshAbove ρ s1 :=
                          FreshAbove.mono ρ supply s1 hs1 hfresh
                        have hlast1 : v0 < s1 :=
                          lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                        have hrel1 : RelEnv henv ρ fenv1.env :=
                          RelEnv_exec henv ρ supply e v0 ie s1 he fenv fenv1
                            hrel hfresh hexec1
                        have hnp_ie : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                        have hexec_ie : execInstrsFullFromIn prog prev fenv ie
                            = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp_ie]
                          exact hexec1
                        have happ : execInstrsFullFromIn prog prev fenv
                            (ie ++ Lr.instrs) =
                            execInstrsFullFromIn prog prev fenv1 Lr.instrs := by
                          rw [execInstrsFullFromIn_append, hexec_ie]
                        have hbb : blockBound fuelB (.exprStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)]
                        cases F with
                        | zero =>
                            have h1 : blockBound fuelB rest ≥ 1 := by
                              rw [blockBound]; omega
                            omega
                        | succ F'' =>
                            have hLHS : execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, ie ++ Lr.instrs, Lr.term⟩ fenv =
                                execBlockFromIn prog (F'' + 1) f prev
                                ⟨bId, Lr.instrs, Lr.term⟩ fenv1 :=
                                execBlockFromIn_instrs_prefix prog F'' f prev bId ie
                                Lr.instrs Lr.term fenv fenv1 happ
                            have hg' : F'' + 1 ≥ blockBound fuelB rest + C := by
                              rw [← hbb]; exact hg
                            have hsub' : ∀ b ∈ Lr.blocks, b ∈ f.blocks :=
                              fun b hb => hsub b hb
                            obtain ⟨w_e, hu_e, heq_rest⟩ :=
                              ((ih bId j ρ s1 nextB v0 true Lr hr hf1
                                hlast1 wE henv fenv1 hrel1
                                (fun hh => absurd hh (by simp)) (fun _ => hregE')
                                fh henv' out hrun prog f prev jblock (F'' + 1)
                                hsub' hnodf hfind fuelB C hg' u).2 e_ret hout)
                            exact ⟨w_e, hu_e, hLHS.trans heq_rest⟩
  | nop rest hrs ih =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG] at h
        cases hr : lowerStmtsCFG bId (some j) true ρ supply nextB lastVal
            hasVal rest with
        | none => rw [hr] at h; simp at h
        | some Lr =>
            rw [hr] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv (.nop :: rest)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv (.nop :: rest)
                    (.value (.lit accH)) =
                    runHIRStmts fh henv rest (.value (.lit accH)) := rfl
                rw [hstep] at hrun
                have hbb : blockBound fuelB (.nop :: rest)
                    = blockBound fuelB rest := by
                  rw [blockBound, blockBound,
                    armBlockBound_cons_not_if fuelB
                      (fun c th el h => by cases h)]
                have hg' : F ≥ blockBound fuelB rest + C := by
                  rw [← hbb]; exact hg
                obtain ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                    hrel_arr, hreg_arr⟩ :=
                  ((ih bId j ρ supply nextB lastVal hasVal Lr hr hfresh
                    hlast accH henv fenv hrel hval0 hreg fh henv' out hrun
                    prog f prev jblock F hsub hnodf hfind fuelB C hg'
                    u).1 hout)
                exact ⟨w_u, hu, F', fenv_arr, hle, hge, heq_rest,
                  hrel_arr, hreg_arr⟩
      · intro e_ret hout
        simp only [lowerStmtsCFG] at h
        cases hr : lowerStmtsCFG bId (some j) true ρ supply nextB lastVal
            hasVal rest with
        | none => rw [hr] at h; simp at h
        | some Lr =>
            rw [hr] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv (.nop :: rest)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv (.nop :: rest)
                    (.value (.lit accH)) =
                    runHIRStmts fh henv rest (.value (.lit accH)) := rfl
                rw [hstep] at hrun
                have hbb : blockBound fuelB (.nop :: rest)
                    = blockBound fuelB rest := by
                  rw [blockBound, blockBound,
                    armBlockBound_cons_not_if fuelB
                      (fun c th el h => by cases h)]
                have hg' : F ≥ blockBound fuelB rest + C := by
                  rw [← hbb]; exact hg
                obtain ⟨w_e, hu_e, heq_rest⟩ :=
                  ((ih bId j ρ supply nextB lastVal hasVal Lr hr hfresh
                    hlast accH henv fenv hrel hval0 hreg fh henv' out hrun
                    prog f prev jblock F hsub hnodf hfind fuelB C hg'
                    u).2 e_ret hout)
                exact ⟨w_e, hu_e, heq_rest⟩
  | ifStmt c th el rest hstr _ hath hael hrs iht ihe ihr =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      simp only [lowerStmtsCFG] at h
      cases heC : lowerExpr ρ supply c with
      | none => rw [heC] at h; simp at h
      | some p =>
          obtain ⟨vc, ic, s1⟩ := p
          rw [heC] at h
          simp only [] at h
          cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
              (nextB + 3) lastVal false th with
          | none => rw [ht] at h; simp at h
          | some lt =>
              rw [ht] at h
              simp only [] at h
              cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2)) true ρ
                  lt.supply lt.next lastVal false el with
              | none => rw [he] at h; simp at h
              | some le =>
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG (nextB + 2) (some j) true ρ
                      (le.supply + 1) le.next le.supply true rest with
                  | none => rw [hr] at h; simp at h
                  | some lr =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      dsimp only at hsub ⊢
                      generalize hTdef : ((lt.blocks.getLast?.map
                        (fun b => b.id)).getD nextB) = exitT
                      generalize hEdef : ((le.blocks.getLast?.map
                        (fun b => b.id)).getD (nextB + 1)) = exitE
                      rw [hTdef, hEdef] at hsub
                      have hs1 : supply ≤ s1 := lower_mono.1 _ _ _ _ _ _ heC
                      have hf1 : FreshAbove ρ s1 :=
                        FreshAbove.mono ρ supply s1 hs1 hfresh
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                        lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ ht hath
                      obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                        lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ he hael
                      obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                        lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _ hr hrs
                      have hrho_t : lt.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ ht hath
                      have hrho_e : le.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ he hael
                      have hrho_r : lr.ρ = ρ :=
                        lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _ hr hrs
                      have hbb_if : blockBound fuelB (.ifStmt c th el :: rest) =
                          1 + (3 + max (armBlockBound fuelB th)
                            (armBlockBound fuelB el) +
                            armBlockBound fuelB rest) := by
                        rw [blockBound, armBlockBound_if]
                      have hB1 : blockBound fuelB (.ifStmt c th el :: rest)
                          ≥ 1 := by
                        rw [blockBound]; omega
                      have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                          ∈ f.blocks :=
                        hsub _ if_asm_mem_then
                      have hfindT : findBlock f nextB =
                          some ⟨nextB, lt.instrs, lt.term⟩ :=
                        findBlock_of_nodup_mem hnodf hTmem
                      have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ : Block)
                          ∈ f.blocks :=
                        hsub _ if_asm_mem_else
                      have hfindE : findBlock f (nextB + 1) =
                          some ⟨nextB + 1, le.instrs, le.term⟩ :=
                        findBlock_of_nodup_mem hnodf hEmem
                      have hJmem : (⟨nextB + 2,
                          [.phi le.supply exitT lt.val,
                           .phi le.supply exitE le.val] ++ lr.instrs,
                          lr.term⟩ : Block) ∈ f.blocks :=
                        hsub _ if_asm_mem_join
                      have hfindJ : findBlock f (nextB + 2) =
                          some ⟨nextB + 2,
                            [.phi le.supply exitT lt.val,
                             .phi le.supply exitE le.val] ++ lr.instrs,
                            lr.term⟩ :=
                        findBlock_of_nodup_mem hnodf hJmem
                      -- the two phi edges differ
                      have hne_pe : exitE ≠ exitT := by
                        have hexitT : exitT = nextB ∨
                            ∃ b ∈ lt.blocks, exitT = b.id := by
                          cases hgl : lt.blocks.getLast? with
                          | none =>
                              exact Or.inl (by simp [← hTdef, hgl])
                          | some b =>
                              have hm : b ∈ lt.blocks := getLast?_mem hgl
                              exact Or.inr ⟨b, hm, by simp [← hTdef, hgl]⟩
                        have hexitE : exitE = nextB + 1 ∨
                            ∃ b ∈ le.blocks, exitE = b.id := by
                          cases hgl : le.blocks.getLast? with
                          | none =>
                              exact Or.inl (by simp [← hEdef, hgl])
                          | some b =>
                              have hm : b ∈ le.blocks := getLast?_mem hgl
                              exact Or.inr ⟨b, hm, by simp [← hEdef, hgl]⟩
                        rcases hexitT with hT | ⟨bt, hbt, hT⟩
                        · rcases hexitE with hE | ⟨be, hbe, hE⟩
                          · simp [hT, hE]
                          · obtain ⟨hlo, -⟩ := hbnde be hbe
                            rw [hE, hT]
                            exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega)
                              (Nat.le_trans hmnt hlo))
                        · rcases hexitE with hE | ⟨be, hbe, hE⟩
                          · obtain ⟨hlo, -⟩ := hbndt bt hbt
                            rw [hE, hT]
                            exact Nat.ne_of_lt (Nat.lt_of_le_of_lt
                              (Nat.add_le_add_left (by decide) nextB) hlo)
                          · obtain ⟨-, hhi⟩ := hbndt bt hbt
                            obtain ⟨hlo, -⟩ := hbnde be hbe
                            rw [hE, hT]
                            exact Nat.ne_of_gt
                              (Nat.lt_of_lt_of_le hhi hlo)
                      cases F with
                      | zero =>
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            omega
                          · intro e hout
                            omega
                      | succ F'' =>
                          cases fuelH with
                          | zero =>
                              have hz : runHIRStmts 0 henv
                                  (.ifStmt c th el :: rest)
                                  (.value (.lit accH)) = (.stuck, henv) := rfl
                              rw [hz] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                simp [hst] at hout
                              · intro e hout
                                simp [hst] at hout
                          | succ fh =>
                              have hstep : runHIRStmts (fh + 1) henv
                                  (.ifStmt c th el :: rest)
                                  (.value (.lit accH)) =
                                  (match evalHIR 256 henv c with
                                    | some (.lit (.bool true)) =>
                                      match runHIRStmts fh henv th
                                          (HFlow.value (.lit .unit)) with
                                      | (HFlow.value u, env') =>
                                          runHIRStmts fh env' rest
                                            ((HFlow.value (.lit accH)).replace
                                              u)
                                      | (f, env') => (f, env')
                                    | some (.lit (.bool false)) =>
                                      match runHIRStmts fh henv el
                                          (HFlow.value (.lit .unit)) with
                                      | (HFlow.value u, env') =>
                                          runHIRStmts fh env' rest
                                            ((HFlow.value (.lit accH)).replace
                                              u)
                                      | (f, env') => (f, env')
                                    | _ => (.stuck, henv)) := rfl
                              rw [hstep] at hrun
                              cases hevC : evalHIR 256 henv c with
                              | none =>
                                  rw [hevC] at hrun
                                  have hst : out = .stuck :=
                                    (congrArg Prod.fst hrun).symm
                                  intro u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    simp [hst] at hout
                                  · intro e hout
                                    simp [hst] at hout
                              | some r =>
                                  rw [hevC] at hrun
                                  obtain ⟨⟨w, hrw⟩, fenvC, hexecC, hstoreC,
                                      wC, hrC, hregC⟩ :=
                                    lower_total.1 ρ supply c vc ic s1 heC hstr
                                      hfresh henv fenv hrel 256 r hevC
                                  subst hrw
                                  have hnp_ic : ∀ dst pred src,
                                      .phi dst pred src ∉ ic := by
                                    intro d p s hm
                                    exact IsPure_not_phi
                                      (lower_isPure.1 _ _ _ _ _ _ heC _ hm)
                                      d p s rfl
                                  have hexec_ic : execInstrsFullFromIn prog
                                      prev fenv ic = some fenvC := by
                                    rw [execInstrsFullFromIn_of_noPhi prog prev
                                      fenv _ hnp_ic]
                                    exact hexecC
                                  have hrelC : RelEnv henv ρ fenvC.env :=
                                    RelEnv_exec henv ρ supply c vc ic s1 heC
                                      fenv fenvC hrel hfresh hexecC
                                  cases w with
                                  | bool b =>
                                      cases b with
                                      | true =>
                                          simp only [] at hrun
                                          cases har : runHIRStmts fh henv th
                                              (HFlow.value (.lit .unit)) with
                                          | mk out_arm env_arm =>
                                              rw [har] at hrun
                                              cases out_arm with
                                              | value u_arm =>
                                                  simp only [] at hrun
                                                  have hregCb : fenvC.env vc =
                                                      some (.bool true) := by
                                                    have hww : (.bool true) =
                                                        wC :=
                                                      HIR.Expr.lit.inj hrC
                                                    rw [hww]
                                                    exact hregC
                                                  have hbool : fenvC.boolOf vc =
                                                      some true :=
                                                    boolOf_of_lit fenvC vc true
                                                      hregCb
                                                  have hentry : execBlockFromIn prog
                                                      (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc nextB
                                                        (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog F'' f
                                                        (some bId)
                                                        ⟨nextB, lt.instrs,
                                                          lt.term⟩ fenvC :=
                                                    execBlockFromIn_branch_true
                                                      prog F'' f prev bId ic vc
                                                      nextB (nextB + 1) fenv
                                                      fenvC ⟨nextB, lt.instrs,
                                                        lt.term⟩ hexec_ic hbool
                                                      hfindT
                                                  have hsub_t : ∀ b ∈ lt.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_lt hb)
                                                  have hC'ge : (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB th +
                                                      C) ≥ blockBound fuelB
                                                      rest + C := by
                                                    have hBrest : blockBound
                                                        fuelB rest = 1 +
                                                        armBlockBound fuelB
                                                          rest := rfl
                                                    omega
                                                  have hg_t : F'' ≥ blockBound
                                                      fuelB th + (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB th +
                                                      C) := by
                                                    have hBth : blockBound
                                                        fuelB th = 1 +
                                                        armBlockBound fuelB
                                                          th := rfl
                                                    omega
                                                  obtain ⟨w_arm, hu_arm, F',
                                                      fenv_arr, hle, hge,
                                                      heq_arm, hrel_arm,
                                                      hreg_arr⟩ :=
                                                    ((iht nextB (nextB + 2) ρ s1
                                                      (nextB + 3) lastVal false
                                                      lt ht hf1 hlast1 .unit
                                                      henv fenvC hrelC
                                                      (fun _ => rfl)
                                                      (fun h => absurd h
                                                        (by simp))
                                                      fh env_arm
                                                      (HFlow.value u_arm) har prog f
                                                      (some bId) ⟨nextB + 2,
                                                        [.phi le.supply exitT
                                                          lt.val,
                                                         .phi le.supply exitE
                                                          le.val] ++ lr.instrs,
                                                        lr.term⟩ F'' hsub_t
                                                      hnodf hfindJ fuelB (2 +
                                                      max (armBlockBound
                                                      fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB th +
                                                      C) hg_t u_arm).1 rfl)
                                                  rw [hTdef] at heq_arm
                                                  rw [hrho_t] at hrel_arm
                                                  have hrep : ((HFlow.value
                                                      (.lit accH)).replace
                                                      (.lit w_arm)) =
                                                      HFlow.value
                                                        (.lit w_arm) := rfl
                                                  rw [hu_arm, hrep] at hrun
                                                  have hfrL : FreshAbove ρ
                                                      le.supply :=
                                                    FreshAbove.mono ρ supply
                                                      le.supply (Nat.le_trans
                                                      hs1 (Nat.le_trans hmst
                                                      hmse)) hfresh
                                                  have hrel_m : RelEnv env_arm ρ
                                                      (fenv_arr.env.update
                                                        le.supply
                                                        w_arm) := by
                                                    intro id u hlook
                                                    obtain ⟨w0, hlookH,
                                                      hreg0⟩ := hrel_arm id u
                                                      hlook
                                                    have hu : u < le.supply :=
                                                      hfrL id u
                                                        (rhoLookup_some_mem ρ
                                                          id u hlook)
                                                    have hne : u ≠ le.supply :=
                                                      Nat.ne_of_lt hu
                                                    refine ⟨w0, hlookH, ?_⟩
                                                    have hupd : (fenv_arr.env.update
                                                        le.supply w_arm) u =
                                                        fenv_arr.env u := by
                                                      simp [Env.update, hne]
                                                    show (fenv_arr.env.update
                                                        le.supply w_arm) u =
                                                      some w0
                                                    rw [hupd]
                                                    exact hreg0
                                                  have hreg_m : (⟨fenv_arr.env.update
                                                      le.supply w_arm,
                                                      fenv_arr.store⟩ :
                                                      FullEnv).env le.supply =
                                                      some w_arm := by
                                                    simp [Env.update]
                                                  have hf_r : FreshAbove ρ
                                                      (le.supply + 1) :=
                                                    FreshAbove.mono ρ supply
                                                      (le.supply + 1)
                                                      (Nat.le_trans hs1
                                                      (Nat.le_trans hmst
                                                      (Nat.le_trans hmse
                                                      (Nat.le_succ _))))
                                                      hfresh
                                                  have hlast_r : le.supply <
                                                      le.supply + 1 :=
                                                    Nat.lt_succ_self _
                                                  have hsub_r : ∀ b ∈ lr.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_lr hb)
                                                  cases F' with
                                                  | zero =>
                                                      have hB1r : blockBound
                                                          fuelB rest ≥ 1 := by
                                                        rw [blockBound]; omega
                                                      exact absurd hge (by omega)
                                                  | succ F1 =>
                                                      have happ_J : execInstrsFullFromIn
                                                          prog (some exitT)
                                                          fenv_arr
                                                          ([.phi le.supply
                                                            exitT lt.val,
                                                            .phi le.supply
                                                            exitE le.val] ++
                                                            lr.instrs) =
                                                          execInstrsFullFromIn
                                                            prog (some exitT)
                                                            ⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩
                                                            lr.instrs :=
                                                        execInstrsFullFromIn_phis_hit
                                                          prog exitT fenv_arr
                                                          le.supply exitT exitE
                                                          lt.val le.val
                                                          lr.instrs w_arm rfl
                                                          hne_pe hreg_arr
                                                      have hJeq : execBlockFromIn
                                                          prog (F1 + 1) f
                                                          (some exitT)
                                                          ⟨nextB + 2,
                                                            [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                            lr.term⟩ fenv_arr =
                                                          execBlockFromIn prog
                                                            (F1 + 1) f
                                                            (some exitT)
                                                            ⟨nextB + 2,
                                                              lr.instrs,
                                                              lr.term⟩
                                                            ⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :=
                                                        execBlockFromIn_instrs_prefix
                                                          prog F1 f (some exitT)
                                                          (nextB + 2)
                                                          [.phi le.supply
                                                            exitT lt.val,
                                                            .phi le.supply
                                                            exitE le.val]
                                                          lr.instrs lr.term
                                                          fenv_arr
                                                          ⟨fenv_arr.env.update
                                                            le.supply w_arm,
                                                            fenv_arr.store⟩
                                                          happ_J
                                                      have hg_r : F1 + 1 ≥
                                                          blockBound fuelB
                                                          rest + C :=
                                                        Nat.le_trans hC'ge hge
                                                      intro u
                                                      have hihr := ihr
                                                        (nextB + 2) j ρ
                                                        (le.supply + 1) le.next
                                                        le.supply true lr hr
                                                        hf_r hlast_r w_arm
                                                        env_arm
                                                        ⟨fenv_arr.env.update
                                                          le.supply w_arm,
                                                          fenv_arr.store⟩
                                                        hrel_m
                                                        (fun h => absurd h
                                                          (by simp))
                                                        (fun _ => hreg_m) fh
                                                        henv' out hrun prog f
                                                        (some exitT) jblock
                                                        (F1 + 1) hsub_r hnodf
                                                        hfind fuelB C hg_r u
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        obtain ⟨w_u, hu, F2,
                                                            fenv_arr2, hle2,
                                                            hge2, heq_rest,
                                                            hrel_final,
                                                            hreg_final⟩ :=
                                                          (hihr.1 hout)
                                                        rw [if_assembly_exit
                                                          rfl]
                                                        exact ⟨w_u, hu, F2,
                                                          fenv_arr2,
                                                          Nat.le_trans
                                                            (Nat.le_trans hle2
                                                            hle)
                                                            (Nat.le_succ _),
                                                          hge2,
                                                          hentry.trans
                                                            (heq_arm.trans
                                                            (hJeq.trans
                                                            heq_rest)),
                                                          hrel_final,
                                                          hreg_final⟩
                                                      · intro e_ret hout2
                                                        obtain ⟨w_e, hu_e,
                                                            heq_rest⟩ :=
                                                          (hihr.2 e_ret hout2)
                                                        exact ⟨w_e, hu_e,
                                                          hentry.trans
                                                            (heq_arm.trans
                                                            (hJeq.trans
                                                            heq_rest))⟩
                                              | returned e_arm =>
                                                  simp only [] at hrun
                                                  have hout_r : out =
                                                      .returned e_arm :=
                                                    (congrArg Prod.fst
                                                      hrun).symm
                                                  intro u
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    rw [hout_r] at hout
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    have hret_e : e_ret =
                                                        e_arm :=
                                                      (HFlow.returned.inj
                                                        (hout_r.symm.trans
                                                          hout2)).symm
                                                    have hregCb_r : fenvC.env vc =
                                                        some (.bool true) := by
                                                      have hww : (.bool true) =
                                                          wC :=
                                                        HIR.Expr.lit.inj hrC
                                                      rw [hww]
                                                      exact hregC
                                                    have hbool_r : fenvC.boolOf vc =
                                                        some true :=
                                                      boolOf_of_lit fenvC vc true
                                                        hregCb_r
                                                    have hentry_r : execBlockFromIn
                                                        prog (F'' + 1) f prev
                                                        ⟨bId, ic, .branch vc
                                                          nextB
                                                          (nextB + 1)⟩ fenv =
                                                        execBlockFromIn prog F''
                                                          f (some bId)
                                                          ⟨nextB, lt.instrs,
                                                            lt.term⟩ fenvC :=
                                                      execBlockFromIn_branch_true
                                                        prog F'' f prev bId ic
                                                        vc nextB (nextB + 1)
                                                        fenv fenvC
                                                        ⟨nextB, lt.instrs,
                                                          lt.term⟩ hexec_ic
                                                        hbool_r hfindT
                                                    have hsub_tr : ∀ b ∈ lt.blocks,
                                                        b ∈ f.blocks :=
                                                      fun b hb => hsub _
                                                        (if_asm_mem_of_lt hb)
                                                    have hC'ge_r : (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB th +
                                                        C) ≥ blockBound fuelB
                                                        rest + C := by
                                                      have hBrest : blockBound
                                                          fuelB rest = 1 +
                                                          armBlockBound fuelB
                                                            rest := rfl
                                                      omega
                                                    have hg_tr : F'' ≥ blockBound
                                                        fuelB th + (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB th +
                                                        C) := by
                                                      have hBth : blockBound
                                                          fuelB th = 1 +
                                                          armBlockBound fuelB
                                                            th := rfl
                                                      omega
                                                    obtain ⟨w_e, heq,
                                                        hexec_arm⟩ :=
                                                      ((iht nextB (nextB + 2)
                                                        ρ s1 (nextB + 3)
                                                        lastVal false lt ht
                                                        hf1 hlast1 .unit henv
                                                        fenvC hrelC
                                                        (fun _ => rfl)
                                                        (fun h => absurd h
                                                          (by simp))
                                                        fh env_arm
                                                        (HFlow.returned e_arm)
                                                        har prog f (some bId)
                                                        ⟨nextB + 2,
                                                          [.phi le.supply exitT
                                                            lt.val,
                                                           .phi le.supply exitE
                                                            le.val] ++
                                                          lr.instrs,
                                                          lr.term⟩ F'' hsub_tr
                                                        hnodf hfindJ fuelB (2 +
                                                        max (armBlockBound
                                                        fuelB th)
                                                        (armBlockBound
                                                          fuelB el) +
                                                        armBlockBound fuelB
                                                          rest -
                                                        armBlockBound fuelB th +
                                                        C) hg_tr
                                                        (.lit .unit)).2 e_arm
                                                        rfl)
                                                    exact ⟨w_e, hret_e.trans
                                                      heq, hentry_r.trans
                                                      hexec_arm⟩
                                              | stuck =>
                                                  simp only [] at hrun
                                                  have hout_s : out =
                                                      .stuck :=
                                                    (congrArg Prod.fst
                                                      hrun).symm
                                                  intro u
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    rw [hout_s] at hout
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    rw [hout_s] at hout2
                                                    exact absurd hout2
                                                      (by simp)
                                              | broke =>
                                                  simp only [] at hrun
                                                  have hout_b : out =
                                                      .broke :=
                                                    (congrArg Prod.fst
                                                      hrun).symm
                                                  intro u
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    rw [hout_b] at hout
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    rw [hout_b] at hout2
                                                    exact absurd hout2
                                                      (by simp)
                                              | continued =>
                                                  simp only [] at hrun
                                                  have hout_c : out =
                                                      .continued :=
                                                    (congrArg Prod.fst
                                                      hrun).symm
                                                  intro u
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    rw [hout_c] at hout
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    rw [hout_c] at hout2
                                                    exact absurd hout2
                                                      (by simp)
                                      | false =>
                                          simp only [] at hrun
                                          have hregCb : fenvC.env vc =
                                              some (.bool false) := by
                                            have hww : (.bool false) =
                                                wC :=
                                              HIR.Expr.lit.inj hrC
                                            rw [hww]
                                            exact hregC
                                          have hbool : fenvC.boolOf vc =
                                              some false :=
                                            boolOf_of_lit fenvC vc false
                                              hregCb
                                          have hentry : execBlockFromIn prog
                                              (F'' + 1) f prev
                                              ⟨bId, ic, .branch vc nextB
                                                (nextB + 1)⟩ fenv =
                                              execBlockFromIn prog F'' f
                                                (some bId)
                                                ⟨nextB + 1, le.instrs,
                                                  le.term⟩ fenvC :=
                                            execBlockFromIn_branch_false
                                              prog F'' f prev bId ic vc
                                              nextB (nextB + 1) fenv
                                              fenvC ⟨nextB + 1, le.instrs,
                                                le.term⟩ hexec_ic hbool
                                              hfindE
                                          have hsub_e : ∀ b ∈ le.blocks,
                                              b ∈ f.blocks :=
                                            fun b hb => hsub _
                                              (if_asm_mem_of_le hb)
                                          have hf_e : FreshAbove ρ
                                              lt.supply :=
                                            FreshAbove.mono ρ s1 lt.supply
                                              hmst hf1
                                          have hlast_e : lastVal <
                                              lt.supply :=
                                            Nat.lt_of_lt_of_le hlast1 hmst
                                          have hC'ge : (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB el +
                                              C) ≥ blockBound fuelB
                                              rest + C := by
                                            have hBrest : blockBound
                                                fuelB rest = 1 +
                                                armBlockBound fuelB
                                                  rest := rfl
                                            omega
                                          have hg_e : F'' ≥ blockBound
                                              fuelB el + (2 + max
                                              (armBlockBound fuelB th)
                                              (armBlockBound fuelB el) +
                                              armBlockBound fuelB rest -
                                              armBlockBound fuelB el +
                                              C) := by
                                            have hBel : blockBound
                                                fuelB el = 1 +
                                                armBlockBound fuelB
                                                  el := rfl
                                            omega
                                          cases har : runHIRStmts fh henv el
                                              (HFlow.value (.lit .unit)) with
                                          | mk out_arm env_arm =>
                                              rw [har] at hrun
                                              cases out_arm with
                                              | value u_arm =>
                                                  simp only [] at hrun
                                                  obtain ⟨w_arm, hu_arm, F',
                                                      fenv_arr, hle, hge,
                                                      heq_arm, hrel_arm,
                                                      hreg_arr⟩ :=
                                                    ((ihe (nextB + 1)
                                                      (nextB + 2) ρ lt.supply
                                                      lt.next lastVal false
                                                      le he hf_e hlast_e .unit
                                                      henv fenvC hrelC
                                                      (fun _ => rfl)
                                                      (fun h => absurd h
                                                        (by simp))
                                                      fh env_arm
                                                      (HFlow.value u_arm) har
                                                      prog f (some bId)
                                                      ⟨nextB + 2,
                                                        [.phi le.supply exitT
                                                          lt.val,
                                                         .phi le.supply exitE
                                                          le.val] ++ lr.instrs,
                                                        lr.term⟩ F'' hsub_e
                                                      hnodf hfindJ fuelB (2 +
                                                      max (armBlockBound
                                                      fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el +
                                                      C) hg_e u_arm).1 rfl)
                                                  rw [hEdef] at heq_arm
                                                  rw [hrho_e] at hrel_arm
                                                  have hrep : ((HFlow.value
                                                      (.lit accH)).replace
                                                      (.lit w_arm)) =
                                                      HFlow.value
                                                        (.lit w_arm) := rfl
                                                  rw [hu_arm, hrep] at hrun
                                                  have hfrL : FreshAbove ρ
                                                      le.supply :=
                                                    FreshAbove.mono ρ supply
                                                      le.supply (Nat.le_trans
                                                      hs1 (Nat.le_trans hmst
                                                      hmse)) hfresh
                                                  have hrel_m : RelEnv env_arm
                                                      ρ (fenv_arr.env.update
                                                        le.supply
                                                        w_arm) := by
                                                    intro id u hlook
                                                    obtain ⟨w0, hlookH,
                                                      hreg0⟩ := hrel_arm id u
                                                      hlook
                                                    have hu : u < le.supply :=
                                                      hfrL id u
                                                        (rhoLookup_some_mem ρ
                                                          id u hlook)
                                                    have hne : u ≠ le.supply :=
                                                      Nat.ne_of_lt hu
                                                    refine ⟨w0, hlookH, ?_⟩
                                                    have hupd : (fenv_arr.env.update
                                                        le.supply w_arm) u =
                                                        fenv_arr.env u := by
                                                      simp [Env.update, hne]
                                                    show (fenv_arr.env.update
                                                        le.supply w_arm) u =
                                                      some w0
                                                    rw [hupd]
                                                    exact hreg0
                                                  have hreg_m : (⟨fenv_arr.env.update
                                                      le.supply w_arm,
                                                      fenv_arr.store⟩ :
                                                      FullEnv).env le.supply =
                                                      some w_arm := by
                                                    simp [Env.update]
                                                  have hf_r : FreshAbove ρ
                                                      (le.supply + 1) :=
                                                    FreshAbove.mono ρ supply
                                                      (le.supply + 1)
                                                      (Nat.le_trans hs1
                                                      (Nat.le_trans hmst
                                                      (Nat.le_trans hmse
                                                      (Nat.le_succ _))))
                                                      hfresh
                                                  have hlast_r : le.supply <
                                                      le.supply + 1 :=
                                                    Nat.lt_succ_self _
                                                  have hsub_r : ∀ b ∈ lr.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_lr hb)
                                                  cases F' with
                                                  | zero =>
                                                      have hB1r : blockBound
                                                          fuelB rest ≥ 1 := by
                                                        rw [blockBound]; omega
                                                      exact absurd hge (by omega)
                                                  | succ F1 =>
                                                      have happ_J : execInstrsFullFromIn
                                                          prog (some exitE)
                                                          fenv_arr
                                                          ([.phi le.supply
                                                            exitT lt.val,
                                                            .phi le.supply
                                                            exitE le.val] ++
                                                            lr.instrs) =
                                                          execInstrsFullFromIn
                                                            prog (some exitE)
                                                            ⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩
                                                            lr.instrs := by
                                                        simp only
                                                          [List.cons_append,
                                                          List.nil_append]
                                                        rw [execInstrsFullFromIn_eq,
                                                          execInstrsFullFromIn_eq,
                                                          execInstrsFullFrom_phi_miss
                                                          _ _ _ _ _ _
                                                          (Ne.symm hne_pe),
                                                          execInstrsFullFrom_phi_hit
                                                          _ _ _ _ _ _ rfl,
                                                          hreg_arr]
                                                      have hJeq : execBlockFromIn
                                                          prog (F1 + 1) f
                                                          (some exitE)
                                                          ⟨nextB + 2,
                                                            [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                              lr.term⟩ fenv_arr =
                                                          execBlockFromIn prog
                                                            (F1 + 1) f
                                                            (some exitE)
                                                            ⟨nextB + 2,
                                                              lr.instrs,
                                                              lr.term⟩
                                                            ⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :=
                                                        execBlockFromIn_instrs_prefix
                                                          prog F1 f (some exitE)
                                                          (nextB + 2)
                                                          [.phi le.supply
                                                            exitT lt.val,
                                                            .phi le.supply
                                                            exitE le.val]
                                                          lr.instrs lr.term
                                                          fenv_arr
                                                          ⟨fenv_arr.env.update
                                                            le.supply w_arm,
                                                            fenv_arr.store⟩
                                                          happ_J
                                                      have hg_r : F1 + 1 ≥
                                                          blockBound fuelB
                                                          rest + C :=
                                                        Nat.le_trans hC'ge
                                                          hge
                                                      intro u
                                                      have hihr := ihr
                                                        (nextB + 2) j ρ
                                                        (le.supply + 1) le.next
                                                        le.supply true lr hr
                                                        hf_r hlast_r w_arm
                                                        env_arm
                                                        ⟨fenv_arr.env.update
                                                          le.supply w_arm,
                                                          fenv_arr.store⟩
                                                        hrel_m
                                                        (fun h => absurd h
                                                          (by simp))
                                                        (fun _ => hreg_m) fh
                                                        henv' out hrun prog f
                                                        (some exitE) jblock
                                                        (F1 + 1) hsub_r hnodf
                                                        hfind fuelB C hg_r u
                                                      refine ⟨?_, ?_⟩
                                                      · intro hout
                                                        obtain ⟨w_u, hu, F2,
                                                            fenv_arr2, hle2,
                                                            hge2, heq_rest,
                                                            hrel_final,
                                                            hreg_final⟩ :=
                                                          (hihr.1 hout)
                                                        rw [if_assembly_exit
                                                          rfl]
                                                        exact ⟨w_u, hu, F2,
                                                          fenv_arr2,
                                                          Nat.le_trans
                                                            (Nat.le_trans hle2
                                                            hle)
                                                            (Nat.le_succ _),
                                                          hge2,
                                                          hentry.trans
                                                            (heq_arm.trans
                                                            (hJeq.trans
                                                            heq_rest)),
                                                          hrel_final,
                                                          hreg_final⟩
                                                      · intro e_ret hout2
                                                        obtain ⟨w_e, hu_e,
                                                            heq_rest⟩ :=
                                                          (hihr.2 e_ret hout2)
                                                        exact ⟨w_e, hu_e,
                                                          hentry.trans
                                                            (heq_arm.trans
                                                            (hJeq.trans
                                                            heq_rest))⟩
                                              | returned e_arm =>
                                                  simp only [] at hrun
                                                  have hout_r : out =
                                                      .returned e_arm :=
                                                    (congrArg Prod.fst
                                                      hrun).symm
                                                  intro u
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    rw [hout_r] at hout
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    have hret_e : e_ret =
                                                        e_arm :=
                                                      (HFlow.returned.inj
                                                        (hout_r.symm.trans
                                                          hout2)).symm
                                                    have hregCb_r : fenvC.env
                                                        vc =
                                                        some
                                                        (.bool false) := by
                                                      have hww : (.bool false) =
                                                          wC :=
                                                        HIR.Expr.lit.inj hrC
                                                      rw [hww]
                                                      exact hregC
                                                    have hbool_r : fenvC.boolOf
                                                        vc = some false :=
                                                      boolOf_of_lit fenvC vc
                                                        false hregCb_r
                                                    have hentry_r : execBlockFromIn
                                                        prog (F'' + 1) f prev
                                                        ⟨bId, ic, .branch vc
                                                          nextB
                                                          (nextB + 1)⟩ fenv =
                                                        execBlockFromIn prog F''
                                                          f (some bId)
                                                          ⟨nextB + 1,
                                                            le.instrs,
                                                            le.term⟩ fenvC :=
                                                      execBlockFromIn_branch_false
                                                        prog F'' f prev bId ic
                                                        vc nextB (nextB + 1)
                                                        fenv fenvC
                                                        ⟨nextB + 1, le.instrs,
                                                          le.term⟩ hexec_ic
                                                        hbool_r hfindE
                                                    have hC'ge_r : (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB el +
                                                        C) ≥ blockBound fuelB
                                                        rest + C := by
                                                      have hBrest : blockBound
                                                          fuelB rest = 1 +
                                                          armBlockBound fuelB
                                                            rest := rfl
                                                      omega
                                                    have hg_er : F'' ≥ blockBound
                                                        fuelB el + (2 + max
                                                        (armBlockBound fuelB th)
                                                        (armBlockBound fuelB el) +
                                                        armBlockBound fuelB rest -
                                                        armBlockBound fuelB el +
                                                        C) := by
                                                      have hBel : blockBound
                                                          fuelB el = 1 +
                                                          armBlockBound fuelB
                                                            el := rfl
                                                      omega
                                                    obtain ⟨w_e, heq,
                                                        hexec_arm⟩ :=
                                                      ((ihe (nextB + 1)
                                                        (nextB + 2) ρ lt.supply
                                                        lt.next lastVal false
                                                        le he hf_e hlast_e
                                                        .unit henv fenvC hrelC
                                                        (fun _ => rfl)
                                                        (fun h => absurd h
                                                          (by simp))
                                                        fh env_arm
                                                        (HFlow.returned e_arm)
                                                        har prog f (some bId)
                                                        ⟨nextB + 2,
                                                          [.phi le.supply exitT
                                                            lt.val,
                                                           .phi le.supply exitE
                                                            le.val] ++
                                                          lr.instrs,
                                                          lr.term⟩ F'' hsub_e
                                                        hnodf hfindJ fuelB (2 +
                                                        max (armBlockBound
                                                        fuelB th)
                                                        (armBlockBound
                                                          fuelB el) +
                                                        armBlockBound fuelB
                                                          rest -
                                                        armBlockBound fuelB el +
                                                        C) hg_er
                                                        (.lit .unit)).2 e_arm
                                                        rfl)
                                                    exact ⟨w_e, hret_e.trans
                                                      heq, hentry_r.trans
                                                      hexec_arm⟩
                                              | stuck =>
                                                  simp only [] at hrun
                                                  have hout_s : out =
                                                      .stuck :=
                                                    (congrArg Prod.fst
                                                      hrun).symm
                                                  intro u
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    rw [hout_s] at hout
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    rw [hout_s] at hout2
                                                    exact absurd hout2
                                                      (by simp)
                                              | broke =>
                                                  simp only [] at hrun
                                                  have hout_b : out =
                                                      .broke :=
                                                    (congrArg Prod.fst
                                                      hrun).symm
                                                  intro u
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    rw [hout_b] at hout
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    rw [hout_b] at hout2
                                                    exact absurd hout2
                                                      (by simp)
                                              | continued =>
                                                  simp only [] at hrun
                                                  have hout_c : out =
                                                      .continued :=
                                                    (congrArg Prod.fst
                                                      hrun).symm
                                                  intro u
                                                  refine ⟨?_, ?_⟩
                                                  · intro hout
                                                    rw [hout_c] at hout
                                                    exact absurd hout (by simp)
                                                  · intro e_ret hout2
                                                    rw [hout_c] at hout2
                                                    exact absurd hout2
                                                      (by simp)
                                  | int _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | string _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | pointer _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | float _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | unit =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | undef =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | some _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | none =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | ok _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | err _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | tuple_ _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | array_ _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | loc _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | closure _ _ =>
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
  | returnStmt e rest hstr _ =>
      intro accH henv fenv hrel hval0 hreg fuelH henv' out hrun prog f prev
        jblock F hsub hnodf hfind fuelB C hg
      intro u
      refine ⟨?_, ?_⟩
      · intro hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv (.returnStmt e :: rest)
                    (.value (.lit accH)) =
                    (match evalHIR 256 henv e with
                      | none => (HFlow.stuck, henv)
                      | some v => (.returned v, henv)) := rfl
                rw [hstep] at hrun
                cases hev : evalHIR 256 henv e with
                | none =>
                    rw [hev] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | some r =>
                    rw [hev] at hrun
                    have hret : out = .returned r := (congrArg Prod.fst hrun).symm
                    rw [hret] at hout
                    exact absurd hout (by simp)
      · intro e_ret hout
        simp only [lowerStmtsCFG] at h
        cases he : lowerExpr ρ supply e with
        | none => rw [he] at h; simp at h
        | some p =>
            obtain ⟨v, ie, s1⟩ := p
            rw [he] at h
            simp only [] at h
            obtain rfl := Option.some.inj h
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv (.returnStmt e :: rest)
                    (.value (.lit accH)) =
                    (match evalHIR 256 henv e with
                      | none => (HFlow.stuck, henv)
                      | some v => (.returned v, henv)) := rfl
                rw [hstep] at hrun
                cases hev : evalHIR 256 henv e with
                | none =>
                    rw [hev] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | some r =>
                    rw [hev] at hrun
                    have hret : out = .returned r := (congrArg Prod.fst hrun).symm
                    rw [hret] at hout
                    obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2, hrE2,
                        hregE⟩ :=
                      lower_total.1 ρ supply e v ie s1 he hstr hfresh
                        henv fenv hrel 256 r hev
                    have hrr : r = e_ret := HFlow.returned.inj hout
                    have heq : e_ret = .lit wE := hrr.symm ▸ hrE
                    have hnp : ∀ dst pred src,
                        .phi dst pred src ∉ ie := by
                      intro d p s hm
                      exact IsPure_not_phi
                        (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                    have hexec : execInstrsFullFromIn prog prev fenv ie
                        = some fenv1 := by
                      rw [execInstrsFullFromIn_of_noPhi prog prev fenv _ hnp]
                      exact hexec1
                    cases F with
                    | zero =>
                        have hbb : blockBound fuelB (.returnStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)]
                        have h1 : blockBound fuelB rest ≥ 1 := by
                          rw [blockBound]; omega
                        omega
                    | succ F' =>
                        refine ⟨wE, heq, ?_⟩
                        have hLHS : execBlockFromIn prog (F' + 1) f prev
                                ⟨bId, ie, .return_ v⟩ fenv =
                                fenv1.env v := by
                          have hret' : execBlockFromIn prog (F' + 1) f prev
                                ⟨bId, ie, .return_ v⟩ fenv =
                              (match execInstrsFullFromIn prog prev fenv ie with
                               | none => (none : Option Value)
                               | some g => g.env v) := rfl
                          rw [hret', hexec]
                        have hww : wE = wE2 :=
                          HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                        rw [hLHS, hww]
                        exact hregE


/-! ## The body worker: closed bodies run to the oracle's value

Loop 179. `lowerStmtsCFG_total` is the body counterpart of the arm worker:
with `cont = none` every path ends in `return_`, so both outcomes conclude
`entry-run = some w` and no join formula is needed. Straight-line steps peel
via `lower_total.1` and the instr-prefix bridge; `if` reuses the arm worker
for both arms and the list IH for the tail; `cont` is fixed to `none`
because only closed programs reach the bridge. -/
theorem lowerStmtsCFG_total (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal ss = some L →
      BranchStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv ss (.value (.lit accH)) = (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId)
        (F : Nat),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (fuelB : Nat), F ≥ blockBound fuelB ss →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog F f prev ⟨bId, L.instrs, L.term⟩ fenv =
            some w_e) := by
  intro bId ρ supply nextB lastVal hasVal ss
  induction ss generalizing bId ρ supply nextB lastVal hasVal with
  | nil =>
      intro L h hss hfresh hlast
      cases hss with
      | nil =>
          intro accH henv fenv hrel hacc fuelH henv' out hrun prog f prev F
            hsub hnodf fuelB hg
          simp only [lowerStmtsCFG] at h
          obtain rfl := Option.some.inj h
          intro u
          refine ⟨?_, ?_⟩
          · intro hout
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout
                exact absurd hout (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have hu : u = .lit accH := by
                  have h1 : (.value (.lit accH)) = out :=
                    congrArg Prod.fst hrun
                  rw [← h1] at hout
                  exact (HFlow.value.inj hout).symm
                refine ⟨accH, hu, ?_⟩
                cases F with
                | zero =>
                    have hbb : blockBound fuelB ([] : List HIR.Stmt) = 1 := by
                      simp [blockBound]
                    omega
                | succ F' =>
                    have hLHS : execBlockFromIn prog (F' + 1) f prev
                        ⟨bId, [], .return_ lastVal⟩ fenv =
                        fenv.env lastVal := rfl
                    rw [hLHS]
                    exact hacc
          · intro e_ret hout2
            cases fuelH with
            | zero =>
                have hz : runHIRStmts 0 henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = (.stuck, henv) := rfl
                rw [hz] at hrun
                have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                rw [hst] at hout2
                exact absurd hout2 (by simp)
            | succ fh =>
                have hstep : runHIRStmts (fh + 1) henv ([] : List HIR.Stmt)
                    (.value (.lit accH)) = ((.value (.lit accH)), henv) := rfl
                rw [hstep] at hrun
                have h1 : (.value (.lit accH)) = out :=
                  congrArg Prod.fst hrun
                rw [← h1] at hout2
                exact absurd hout2 (by simp)
  | cons s rest ih =>
      intro L h hss hfresh hlast
      cases hss with
      | cons hs hrs =>
          cases hs with
          | exprStmt e hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId none false ρ s1 nextB v true
                      rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      have hbb : blockBound fuelB (.exprStmt e :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      have hf1 : FreshAbove ρ s1 :=
                        FreshAbove.mono ρ supply s1 hs1 hfresh
                      have hva : v < s1 :=
                        lower_result_lt.1 ρ supply e v ie s1 he hfresh
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv (.exprStmt e :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.exprStmt e :: rest) (.value (.lit accH)) =
                              (match evalHIR 256 henv e with
                                | none => (HFlow.stuck, henv)
                                | some v => runHIRStmts fh henv rest
                                    (.value v)) := rfl
                          rw [hstep] at hrun
                          cases hev : evalHIR 256 henv e with
                          | none =>
                              rw [hev] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply e v ie s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply e v ie s1 he fenv
                                  fenv1 hrel hfresh hexec1
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ie := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ie = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ie ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ie ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ie q.instrs q.term fenv fenv1
                                      happ
                                  have hww : wE = wE2 :=
                                    HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                                  intro u
                                  have hihr := ih bId ρ s1 nextB v true q hr
                                    hrs hf1 hva wE henv fenv1 hrel1
                                    (hww ▸ hregE) fh henv' out hrun prog f
                                    prev (F' + 1) hsub hnodf fuelB hg' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | varDecl id τ init hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply init with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨vb, ib, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId none false ((id, vb) :: ρ) s1
                      nextB lastVal true rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      have hva : vb < s1 :=
                        lower_result_lt.1 ρ supply init vb ib s1 he hfresh
                      have hf1 : FreshAbove ((id, vb) :: ρ) s1 := by
                        intro j u hmem
                        rcases List.mem_cons.mp hmem with heq | hmem
                        · cases heq
                          exact hva
                        · exact Nat.lt_of_lt_of_le (hfresh j u hmem) hs1
                      have hbb : blockBound fuelB (.varDecl id τ init :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv
                              (.varDecl id τ init :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.varDecl id τ init :: rest)
                              (.value (.lit accH)) =
                              (match evalHIR 256 henv init with
                                | none => (HFlow.stuck, henv)
                                | some v => runHIRStmts fh ((id, v) :: henv)
                                    rest (.value (.lit accH))) := rfl
                          rw [hstep] at hrun
                          cases hev : evalHIR 256 henv init with
                          | none =>
                              rw [hev] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply init vb ib s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              have hww : wE = wE2 :=
                                HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply init vb ib s1 he
                                  fenv fenv1 hrel hfresh hexec1
                              have hrel2 : RelEnv ((id, .lit wE) :: henv)
                                  ((id, vb) :: ρ) fenv1.env := by
                                intro j u hlook
                                by_cases hid : id = j
                                · subst hid
                                  have hu : u = vb := by
                                    have hh : rhoLookup ((id, vb) :: ρ) id =
                                        some vb :=
                                      rhoLookup_cons_head id vb ρ
                                    rw [hh] at hlook
                                    exact (Option.some.inj hlook).symm
                                  subst hu
                                  have hhead : lookupHEnv
                                      ((id, .lit wE) :: henv) id =
                                      some (.lit wE) := by
                                    simp [lookupHEnv]
                                  exact ⟨wE, hhead, hww ▸ hregE⟩
                                · have hlook' : rhoLookup ρ j = some u := by
                                    rw [rhoLookup_cons_ne hid] at hlook
                                    exact hlook
                                  obtain ⟨w', hlookH, hreg⟩ :=
                                    hrel1 j u hlook'
                                  have hlookH' : lookupHEnv
                                      ((id, .lit wE) :: henv) j =
                                      some (.lit w') := by
                                    rw [lookupHEnv_cons_ne hid]
                                    exact hlookH
                                  exact ⟨w', hlookH', hreg⟩
                              have hacc1 : fenv1.env lastVal = some accH := by
                                rw [lower_preserv_regs ρ supply init vb ib
                                  s1 he fenv fenv1 hexec1 lastVal hlast]
                                exact hacc
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ib := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ib = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ib ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ib ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ib q.instrs q.term fenv fenv1
                                      happ
                                  intro u
                                  have hihr := ih bId ((id, vb) :: ρ) s1
                                    nextB lastVal true q hr hrs hf1 hlast1
                                    accH ((id, .lit wE) :: henv) fenv1 hrel2
                                    hacc1 fh henv' out hrun prog f prev
                                    (F' + 1) hsub hnodf fuelB hg' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | assign id e hstr _ =>
              simp only [lowerStmtsCFG] at h
              cases he : lowerExpr ρ supply e with
              | none => rw [he] at h; simp at h
              | some p =>
                  obtain ⟨v0, ie, s1⟩ := p
                  rw [he] at h
                  simp only [] at h
                  cases hr : lowerStmtsCFG bId none false (updAssoc ρ id v0)
                      s1 nextB lastVal true rest with
                  | none => rw [hr] at h; simp at h
                  | some q =>
                      rw [hr] at h
                      simp only [] at h
                      obtain rfl := Option.some.inj h
                      intro accH henv fenv hrel hacc fuelH henv' out hrun
                        prog f prev F hsub hnodf fuelB hg
                      have hs1 : supply ≤ s1 :=
                        lower_mono.1 _ _ _ _ _ _ he
                      have hlast1 : lastVal < s1 :=
                        Nat.lt_of_lt_of_le hlast hs1
                      have hva : v0 < s1 :=
                        lower_result_lt.1 ρ supply e v0 ie s1 he hfresh
                      have hf1 : FreshAbove (updAssoc ρ id v0) s1 := by
                        intro j u hmem
                        rcases updAssoc_mem ρ id v0 j u hmem with ⟨-, hwu⟩ |
                          hmem
                        · rw [hwu]
                          exact hva
                        · exact Nat.lt_of_lt_of_le (hfresh j u hmem) hs1
                      have hbb : blockBound fuelB (.assign id e :: rest)
                          = blockBound fuelB rest := by
                        rw [blockBound, blockBound,
                          armBlockBound_cons_not_if fuelB
                            (fun c th el h => by cases h)]
                      have hg' : F ≥ blockBound fuelB rest := by
                        rw [← hbb]; exact hg
                      cases fuelH with
                      | zero =>
                          have hz : runHIRStmts 0 henv (.assign id e :: rest)
                              (.value (.lit accH)) = (.stuck, henv) := rfl
                          rw [hz] at hrun
                          have hst : out = .stuck :=
                            (congrArg Prod.fst hrun).symm
                          intro u
                          refine ⟨?_, ?_⟩
                          · intro hout
                            rw [hst] at hout
                            exact absurd hout (by simp)
                          · intro e_ret hout2
                            rw [hst] at hout2
                            exact absurd hout2 (by simp)
                      | succ fh =>
                          have hstep : runHIRStmts (fh + 1) henv
                              (.assign id e :: rest)
                              (.value (.lit accH)) =
                              (match evalHIR 256 henv e with
                                | none => (HFlow.stuck, henv)
                                | some v => runHIRStmts fh
                                    (updateHEnv henv id v) rest
                                    (.value (.lit accH))) := rfl
                          rw [hstep] at hrun
                          cases hev : evalHIR 256 henv e with
                          | none =>
                              rw [hev] at hrun
                              have hst : out = .stuck :=
                                (congrArg Prod.fst hrun).symm
                              intro u
                              refine ⟨?_, ?_⟩
                              · intro hout
                                rw [hst] at hout
                                exact absurd hout (by simp)
                              · intro e_ret hout2
                                rw [hst] at hout2
                                exact absurd hout2 (by simp)
                          | some r =>
                              rw [hev] at hrun
                              obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1,
                                  wE2, hrE2, hregE⟩ :=
                                lower_total.1 ρ supply e v0 ie s1 he hstr
                                  hfresh henv fenv hrel 256 r hev
                              have hww : wE = wE2 :=
                                HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                              rw [hrE] at hrun
                              have hrel1 : RelEnv henv ρ fenv1.env :=
                                RelEnv_exec henv ρ supply e v0 ie s1 he fenv
                                  fenv1 hrel hfresh hexec1
                              have hrel2 : RelEnv
                                  (updateHEnv henv id (.lit wE))
                                  (updAssoc ρ id v0) fenv1.env :=
                                RelEnv_update ρ henv fenv1.env id v0 wE
                                  hrel1 (hww ▸ hregE)
                              have hacc1 : fenv1.env lastVal = some accH := by
                                rw [lower_preserv_regs ρ supply e v0 ie s1
                                  he fenv fenv1 hexec1 lastVal hlast]
                                exact hacc
                              have hnp : ∀ dst pred src,
                                  .phi dst pred src ∉ ie := by
                                intro d p s hm
                                exact IsPure_not_phi
                                  (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s
                                  rfl
                              have hexec : execInstrsFullFromIn prog prev
                                  fenv ie = some fenv1 := by
                                rw [execInstrsFullFromIn_of_noPhi prog prev
                                  fenv _ hnp]
                                exact hexec1
                              have happ : execInstrsFullFromIn prog prev
                                  fenv (ie ++ q.instrs) =
                                  execInstrsFullFromIn prog prev fenv1
                                    q.instrs := by
                                rw [execInstrsFullFromIn_append, hexec]
                              cases F with
                              | zero =>
                                  have h1 : blockBound fuelB rest ≥ 1 := by
                                    rw [blockBound]; omega
                                  omega
                              | succ F' =>
                                  have hpeel : execBlockFromIn prog (F' + 1)
                                      f prev ⟨bId, ie ++ q.instrs, q.term⟩
                                      fenv = execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, q.instrs, q.term⟩
                                      fenv1 :=
                                    execBlockFromIn_instrs_prefix prog F' f
                                      prev bId ie q.instrs q.term fenv fenv1
                                      happ
                                  intro u
                                  have hihr := ih bId (updAssoc ρ id v0) s1
                                    nextB lastVal true q hr hrs hf1 hlast1
                                    accH (updateHEnv henv id (.lit wE))
                                    fenv1 hrel2 hacc1 fh henv' out hrun prog
                                    f prev (F' + 1) hsub hnodf fuelB hg' u
                                  refine ⟨?_, ?_⟩
                                  · intro hout
                                    obtain ⟨w_u, hu, heq_rest⟩ := hihr.1 hout
                                    exact ⟨w_u, hu, hpeel.trans heq_rest⟩
                                  · intro e_ret hout2
                                    obtain ⟨w_e, hu_e, heq_rest⟩ :=
                                      hihr.2 e_ret hout2
                                    exact ⟨w_e, hu_e, hpeel.trans heq_rest⟩
          | nop =>
              simp only [lowerStmtsCFG] at h
              intro accH henv fenv hrel hacc fuelH henv' out hrun prog f
                prev F hsub hnodf fuelB hg
              have hbb : blockBound fuelB (Morph.HIR.Stmt.nop :: rest)
                  = blockBound fuelB rest := by
                rw [blockBound, blockBound,
                  armBlockBound_cons_not_if fuelB
                    (fun c th el h => by cases h)]
              have hg' : F ≥ blockBound fuelB rest := by
                rw [← hbb]; exact hg
              cases fuelH with
              | zero =>
                  have hz : runHIRStmts 0 henv
                      (Morph.HIR.Stmt.nop :: rest)
                      (.value (.lit accH)) = (.stuck, henv) := rfl
                  rw [hz] at hrun
                  have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                  intro u
                  refine ⟨?_, ?_⟩
                  · intro hout
                    rw [hst] at hout
                    exact absurd hout (by simp)
                  · intro e_ret hout2
                    rw [hst] at hout2
                    exact absurd hout2 (by simp)
              | succ fh =>
                  have hstep : runHIRStmts (fh + 1) henv
                      (Morph.HIR.Stmt.nop :: rest) (.value (.lit accH)) =
                      runHIRStmts fh henv rest (.value (.lit accH)) := rfl
                  rw [hstep] at hrun
                  intro u
                  exact ih bId ρ supply nextB lastVal hasVal L h hrs hfresh
                    hlast accH henv fenv hrel hacc fh henv' out hrun prog f
                    prev F hsub hnodf fuelB hg' u
          | ifStmt c th el hstr _ hath hael =>
              simp only [lowerStmtsCFG] at h
              cases heC : lowerExpr ρ supply c with
              | none => rw [heC] at h; simp at h
              | some p =>
                  obtain ⟨vc, ic, s1⟩ := p
                  rw [heC] at h
                  simp only [] at h
                  cases ht : lowerStmtsCFG nextB (some (nextB + 2)) true ρ s1
                      (nextB + 3) lastVal false th with
                  | none => rw [ht] at h; simp at h
                  | some lt =>
                      rw [ht] at h
                      simp only [] at h
                      cases he : lowerStmtsCFG (nextB + 1) (some (nextB + 2))
                          true ρ lt.supply lt.next lastVal false el with
                      | none => rw [he] at h; simp at h
                      | some le =>
                          rw [he] at h
                          simp only [] at h
                          cases hr : lowerStmtsCFG (nextB + 2) none false ρ
                              (le.supply + 1) le.next le.supply true rest with
                          | none => rw [hr] at h; simp at h
                          | some lr =>
                              rw [hr] at h
                              simp only [] at h
                              obtain rfl := Option.some.inj h
                              intro accH henv fenv hrel hacc fuelH henv' out
                                hrun prog f prev F hsub hnodf fuelB hg
                              dsimp only at hsub ⊢
                              generalize hTdef : ((lt.blocks.getLast?.map
                                (fun b => b.id)).getD nextB) = exitT
                              generalize hEdef : ((le.blocks.getLast?.map
                                (fun b => b.id)).getD (nextB + 1)) = exitE
                              rw [hTdef, hEdef] at hsub
                              have hs1 : supply ≤ s1 :=
                                lower_mono.1 _ _ _ _ _ _ heC
                              have hf1 : FreshAbove ρ s1 :=
                                FreshAbove.mono ρ supply s1 hs1 hfresh
                              have hlast1 : lastVal < s1 :=
                                Nat.lt_of_lt_of_le hlast hs1
                              obtain ⟨hmnt, hmst, hbndt, hnodt⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _
                                  ht hath
                              obtain ⟨hmne, hmse, hbnde, hnode⟩ :=
                                lowerStmtsCFG_arm_inv budget _ _ _ _ _ _ _ _ _
                                  he hael
                              obtain ⟨hmnr, hmsr, hbndr, hnodr⟩ :=
                                lowerStmtsCFG_branch_inv budget _ _ _ _ _ _ _
                                  _ _ hr hrs
                              have hrho_t : lt.ρ = ρ :=
                                lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _
                                  ht hath
                              have hrho_e : le.ρ = ρ :=
                                lowerStmtsCFG_arm_rho budget _ _ _ _ _ _ _ _ _
                                  he hael
                              have hbb_if : blockBound fuelB
                                  (.ifStmt c th el :: rest) =
                                  1 + (3 + max (armBlockBound fuelB th)
                                    (armBlockBound fuelB el) +
                                    armBlockBound fuelB rest) := by
                                rw [blockBound, armBlockBound_if]
                              have hB1 : blockBound fuelB
                                  (.ifStmt c th el :: rest) ≥ 1 := by
                                rw [blockBound]; omega
                              have hTmem : (⟨nextB, lt.instrs, lt.term⟩ : Block)
                                  ∈ f.blocks :=
                                hsub _ if_asm_mem_then
                              have hfindT : findBlock f nextB =
                                  some ⟨nextB, lt.instrs, lt.term⟩ :=
                                findBlock_of_nodup_mem hnodf hTmem
                              have hEmem : (⟨nextB + 1, le.instrs, le.term⟩ :
                                  Block) ∈ f.blocks :=
                                hsub _ if_asm_mem_else
                              have hfindE : findBlock f (nextB + 1) =
                                  some ⟨nextB + 1, le.instrs, le.term⟩ :=
                                findBlock_of_nodup_mem hnodf hEmem
                              have hJmem : (⟨nextB + 2,
                                  [.phi le.supply exitT lt.val,
                                   .phi le.supply exitE le.val] ++ lr.instrs,
                                  lr.term⟩ : Block) ∈ f.blocks :=
                                hsub _ if_asm_mem_join
                              have hfindJ : findBlock f (nextB + 2) =
                                  some ⟨nextB + 2,
                                    [.phi le.supply exitT lt.val,
                                     .phi le.supply exitE le.val] ++ lr.instrs,
                                    lr.term⟩ :=
                                findBlock_of_nodup_mem hnodf hJmem
                              have hne_pe : exitE ≠ exitT := by
                                have hexitT : exitT = nextB ∨
                                    ∃ b ∈ lt.blocks, exitT = b.id := by
                                  cases hgl : lt.blocks.getLast? with
                                  | none =>
                                      exact Or.inl (by simp [← hTdef, hgl])
                                  | some b =>
                                      have hm : b ∈ lt.blocks :=
                                        getLast?_mem hgl
                                      exact Or.inr ⟨b, hm, by simp [← hTdef, hgl]⟩
                                have hexitE : exitE = nextB + 1 ∨
                                    ∃ b ∈ le.blocks, exitE = b.id := by
                                  cases hgl : le.blocks.getLast? with
                                  | none =>
                                      exact Or.inl (by simp [← hEdef, hgl])
                                  | some b =>
                                      have hm : b ∈ le.blocks :=
                                        getLast?_mem hgl
                                      exact Or.inr ⟨b, hm, by simp [← hEdef, hgl]⟩
                                rcases hexitT with hT | ⟨bt, hbt, hT⟩
                                · rcases hexitE with hE | ⟨be, hbe, hE⟩
                                  · simp [hT, hE]
                                  · obtain ⟨hlo, -⟩ := hbnde be hbe
                                    rw [hE, hT]
                                    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le
                                      (by omega)
                                      (Nat.le_trans hmnt hlo))
                                · rcases hexitE with hE | ⟨be, hbe, hE⟩
                                  · obtain ⟨hlo, -⟩ := hbndt bt hbt
                                    rw [hE, hT]
                                    exact Nat.ne_of_lt (Nat.lt_of_le_of_lt
                                      (Nat.add_le_add_left (by decide) nextB)
                                      hlo)
                                  · obtain ⟨-, hhi⟩ := hbndt bt hbt
                                    obtain ⟨hlo, -⟩ := hbnde be hbe
                                    rw [hE, hT]
                                    exact Nat.ne_of_gt
                                      (Nat.lt_of_lt_of_le hhi hlo)
                              have hgF : F ≥ 1 + (3 + max (armBlockBound fuelB
                                  th) (armBlockBound fuelB el) +
                                  armBlockBound fuelB rest) := by
                                rw [← hbb_if]; exact hg
                              cases F with
                              | zero => omega
                              | succ F'' =>
                                  cases fuelH with
                                  | zero =>
                                      have hz : runHIRStmts 0 henv
                                          (.ifStmt c th el :: rest)
                                          (.value (.lit accH)) =
                                          (.stuck, henv) := rfl
                                      rw [hz] at hrun
                                      have hst : out = .stuck :=
                                        (congrArg Prod.fst hrun).symm
                                      intro u
                                      refine ⟨?_, ?_⟩
                                      · intro hout
                                        simp [hst] at hout
                                      · intro e hout
                                        simp [hst] at hout
                                  | succ fh =>
                                      have hstep : runHIRStmts (fh + 1) henv
                                          (.ifStmt c th el :: rest)
                                          (.value (.lit accH)) =
                                          (match evalHIR 256 henv c with
                                            | some (.lit (.bool true)) =>
                                              match runHIRStmts fh henv th
                                                  (HFlow.value (.lit .unit)) with
                                              | (HFlow.value u, env') =>
                                                  runHIRStmts fh env' rest
                                                    ((HFlow.value
                                                      (.lit accH)).replace u)
                                              | (f, env') => (f, env')
                                            | some (.lit (.bool false)) =>
                                              match runHIRStmts fh henv el
                                                  (HFlow.value (.lit .unit)) with
                                              | (HFlow.value u, env') =>
                                                  runHIRStmts fh env' rest
                                                    ((HFlow.value
                                                      (.lit accH)).replace u)
                                              | (f, env') => (f, env')
                                            | _ => (.stuck, henv)) := rfl
                                      rw [hstep] at hrun
                                      cases hevC : evalHIR 256 henv c with
                                      | none =>
                                          rw [hevC] at hrun
                                          have hst : out = .stuck :=
                                            (congrArg Prod.fst hrun).symm
                                          intro u
                                          refine ⟨?_, ?_⟩
                                          · intro hout
                                            simp [hst] at hout
                                          · intro e hout
                                            simp [hst] at hout
                                      | some r =>
                                          rw [hevC] at hrun
                                          obtain ⟨⟨w, hrw⟩, fenvC, hexecC,
                                              hstoreC, wC, hrC, hregC⟩ :=
                                            lower_total.1 ρ supply c vc ic s1
                                              heC hstr hfresh henv fenv hrel
                                              256 r hevC
                                          subst hrw
                                          have hnp_ic : ∀ dst pred src,
                                              .phi dst pred src ∉ ic := by
                                            intro d p s hm
                                            exact IsPure_not_phi
                                              (lower_isPure.1 _ _ _ _ _ _ heC
                                                _ hm) d p s rfl
                                          have hexec_ic : execInstrsFullFromIn
                                              prog prev fenv ic =
                                              some fenvC := by
                                            rw [execInstrsFullFromIn_of_noPhi
                                              prog prev fenv _ hnp_ic]
                                            exact hexecC
                                          have hrelC : RelEnv henv ρ
                                              fenvC.env :=
                                            RelEnv_exec henv ρ supply c vc ic
                                              s1 heC fenv fenvC hrel hfresh
                                              hexecC
                                          cases w with
                                          | bool b =>
                                              cases b with
                                              | true =>
                                                  simp only [] at hrun
                                                  cases har : runHIRStmts fh
                                                      henv th (HFlow.value
                                                        (.lit .unit)) with
                                                  | mk out_arm env_arm =>
                                                      rw [har] at hrun
                                                      cases out_arm with
                                                      | value u_arm =>
                                                          simp only [] at hrun
                                                          have hregCb :
                                                              fenvC.env vc =
                                                              some
                                                              (.bool true) := by
                                                            have hww :
                                                                (.bool true) =
                                                                wC :=
                                                              HIR.Expr.lit.inj
                                                                hrC
                                                            rw [hww]
                                                            exact hregC
                                                          have hbool :
                                                              fenvC.boolOf vc =
                                                              some true :=
                                                            boolOf_of_lit fenvC
                                                              vc true hregCb
                                                          have hentry :
                                                              execBlockFromIn
                                                              prog (F'' + 1) f
                                                              prev ⟨bId, ic,
                                                              .branch vc nextB
                                                              (nextB + 1)⟩
                                                              fenv =
                                                              execBlockFromIn
                                                              prog F'' f
                                                              (some bId)
                                                              ⟨nextB, lt.instrs,
                                                              lt.term⟩ fenvC :=
                                                            execBlockFromIn_branch_true
                                                              prog F'' f prev
                                                              bId ic vc nextB
                                                              (nextB + 1) fenv
                                                              fenvC
                                                              ⟨nextB, lt.instrs,
                                                              lt.term⟩ hexec_ic
                                                              hbool hfindT
                                                          have hsub_t : ∀ b ∈
                                                              lt.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lt
                                                              hb)
                                                          have hCtge : (2 + max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) ≥
                                                              blockBound fuelB
                                                              rest := by
                                                            have hBrest :
                                                                blockBound fuelB
                                                                rest = 1 +
                                                                armBlockBound
                                                                fuelB rest :=
                                                              rfl
                                                            omega
                                                          have hg_t : F'' ≥
                                                              blockBound fuelB
                                                              th + (2 + max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) := by
                                                            have hBth :
                                                                blockBound fuelB
                                                                th = 1 +
                                                                armBlockBound
                                                                fuelB th := rfl
                                                            omega
                                                          obtain ⟨w_arm, hu_arm,
                                                              F', fenv_arr, hle,
                                                              hge, heq_arm,
                                                              hrel_arm,
                                                              hreg_arr⟩ :=
                                                            ((lowerStmtsCFG_arm_total
                                                              budget nextB
                                                              (nextB + 2) ρ s1
                                                              (nextB + 3)
                                                              lastVal false th
                                                              lt ht hath hf1
                                                              hlast1 .unit henv
                                                              fenvC hrelC
                                                              (fun _ => rfl)
                                                              (fun h => absurd h
                                                              (by simp))
                                                              fh env_arm
                                                              (HFlow.value
                                                              u_arm) har prog f
                                                              (some bId)
                                                              ⟨nextB + 2,
                                                              [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                              lr.term⟩ F''
                                                              hsub_t hnodf
                                                              hfindJ fuelB (2 +
                                                              max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB th) hg_t
                                                              u_arm).1 rfl)
                                                          rw [hTdef] at heq_arm
                                                          rw [hrho_t] at hrel_arm
                                                          have hrep :
                                                              ((HFlow.value
                                                              (.lit accH)).replace
                                                              (.lit w_arm)) =
                                                              HFlow.value
                                                              (.lit w_arm) :=
                                                            rfl
                                                          rw [hu_arm, hrep] at hrun
                                                          have hfrL : FreshAbove
                                                              ρ le.supply :=
                                                            FreshAbove.mono ρ
                                                              supply le.supply
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              hmse)) hfresh
                                                          have hrel_m : RelEnv
                                                              env_arm ρ
                                                              (fenv_arr.env.update
                                                              le.supply
                                                              w_arm) := by
                                                            intro id u hlook
                                                            obtain ⟨w0, hlookH,
                                                              hreg0⟩ :=
                                                              hrel_arm id u
                                                              hlook
                                                            have hu : u <
                                                                le.supply :=
                                                              hfrL id u
                                                              (rhoLookup_some_mem
                                                              ρ id u hlook)
                                                            have hne : u ≠
                                                                le.supply :=
                                                              Nat.ne_of_lt hu
                                                            refine ⟨w0, hlookH,
                                                              ?_⟩
                                                            have hupd :
                                                                (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                                fenv_arr.env
                                                                u := by
                                                              simp [Env.update,
                                                                hne]
                                                            show (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                              some w0
                                                            rw [hupd]
                                                            exact hreg0
                                                          have hreg_m :
                                                              (⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :
                                                              FullEnv).env
                                                              le.supply =
                                                              some w_arm := by
                                                            simp [Env.update]
                                                          have hf_r : FreshAbove
                                                              ρ (le.supply +
                                                              1) :=
                                                            FreshAbove.mono ρ
                                                              supply
                                                              (le.supply + 1)
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              (Nat.le_trans hmse
                                                              (Nat.le_succ _))))
                                                              hfresh
                                                          have hlast_r :
                                                              le.supply <
                                                              le.supply + 1 :=
                                                            Nat.lt_succ_self _
                                                          have hsub_r : ∀ b ∈
                                                              lr.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lr
                                                              hb)
                                                          cases F' with
                                                          | zero =>
                                                              have hB1r :
                                                                  blockBound
                                                                  fuelB rest ≥
                                                                  1 := by
                                                                rw [blockBound]
                                                                omega
                                                              exact absurd hge
                                                                (by omega)
                                                          | succ F1 =>
                                                              have happ_J :
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitT)
                                                                  fenv_arr
                                                                  ([.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs) =
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitT)
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  lr.instrs :=
                                                                execInstrsFullFromIn_phis_hit
                                                                  prog exitT
                                                                  fenv_arr
                                                                  le.supply
                                                                  exitT exitE
                                                                  lt.val le.val
                                                                  lr.instrs
                                                                  w_arm rfl
                                                                  hne_pe
                                                                  hreg_arr
                                                              have hJeq :
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitT)
                                                                  ⟨nextB + 2,
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  fenv_arr =
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitT)
                                                                  ⟨nextB + 2,
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩ :=
                                                                execBlockFromIn_instrs_prefix
                                                                  prog F1 f
                                                                  (some exitT)
                                                                  (nextB + 2)
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val]
                                                                  lr.instrs
                                                                  lr.term
                                                                  fenv_arr
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  happ_J
                                                              have hg_r : F1 + 1 ≥
                                                                  blockBound
                                                                  fuelB rest :=
                                                                Nat.le_trans hCtge
                                                                  hge
                                                              intro u
                                                              have hihr := ih
                                                                (nextB + 2) ρ
                                                                (le.supply + 1)
                                                                le.next
                                                                le.supply true
                                                                lr hr hrs hf_r
                                                                hlast_r w_arm
                                                                env_arm
                                                                ⟨fenv_arr.env.update
                                                                le.supply w_arm,
                                                                fenv_arr.store⟩
                                                                hrel_m hreg_m fh
                                                                henv' out hrun
                                                                prog f
                                                                (some exitT)
                                                                (F1 + 1) hsub_r
                                                                hnodf fuelB hg_r
                                                                u
                                                              refine ⟨?_, ?_⟩
                                                              · intro hout
                                                                obtain ⟨w_u, hu,
                                                                    heq_rest⟩ :=
                                                                  hihr.1 hout
                                                                exact ⟨w_u, hu,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                              · intro e_ret hout2
                                                                obtain ⟨w_e, hu_e,
                                                                    heq_rest⟩ :=
                                                                  hihr.2 e_ret
                                                                    hout2
                                                                exact ⟨w_e, hu_e,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                      | returned e_arm =>
                                                          simp only [] at hrun
                                                          have hout_r : out =
                                                              .returned e_arm :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_r] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            have hret_e : e_ret =
                                                                e_arm :=
                                                              (HFlow.returned.inj
                                                                (hout_r.symm.trans
                                                                hout2)).symm
                                                            have hregCb_r :
                                                                fenvC.env vc =
                                                                some
                                                                (.bool true) := by
                                                              have hww :
                                                                  (.bool true) =
                                                                  wC :=
                                                                HIR.Expr.lit.inj
                                                                  hrC
                                                              rw [hww]
                                                              exact hregC
                                                            have hbool_r :
                                                                fenvC.boolOf vc =
                                                                some true :=
                                                              boolOf_of_lit
                                                                fenvC vc true
                                                                hregCb_r
                                                            have hentry_r :
                                                                execBlockFromIn
                                                                prog (F'' + 1)
                                                                f prev ⟨bId, ic,
                                                                .branch vc
                                                                nextB
                                                                (nextB + 1)⟩
                                                                fenv =
                                                                execBlockFromIn
                                                                prog F'' f
                                                                (some bId)
                                                                ⟨nextB, lt.instrs,
                                                                lt.term⟩
                                                                fenvC :=
                                                              execBlockFromIn_branch_true
                                                                prog F'' f prev
                                                                bId ic vc nextB
                                                                (nextB + 1)
                                                                fenv fenvC
                                                                ⟨nextB,
                                                                lt.instrs,
                                                                lt.term⟩
                                                                hexec_ic
                                                                hbool_r hfindT
                                                            have hsub_tr : ∀ b ∈
                                                                lt.blocks,
                                                                b ∈ f.blocks :=
                                                              fun b hb => hsub _
                                                                (if_asm_mem_of_lt
                                                                hb)
                                                            have hCtge_r : (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) ≥
                                                                blockBound fuelB
                                                                rest := by
                                                              have hBrest :
                                                                  blockBound
                                                                  fuelB rest =
                                                                  1 +
                                                                  armBlockBound
                                                                  fuelB rest :=
                                                                rfl
                                                              omega
                                                            have hg_tr : F'' ≥
                                                                blockBound fuelB
                                                                th + (2 + max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) := by
                                                              have hBth :
                                                                  blockBound
                                                                  fuelB th = 1 +
                                                                  armBlockBound
                                                                  fuelB th :=
                                                                rfl
                                                              omega
                                                            obtain ⟨w_e, heq,
                                                                hexec_arm⟩ :=
                                                              ((lowerStmtsCFG_arm_total
                                                                budget nextB
                                                                (nextB + 2) ρ s1
                                                                (nextB + 3)
                                                                lastVal false th
                                                                lt ht hath hf1
                                                                hlast1 .unit henv
                                                                fenvC hrelC
                                                                (fun _ => rfl)
                                                                (fun h => absurd h
                                                                (by simp))
                                                                fh env_arm
                                                                (HFlow.returned
                                                                e_arm)
                                                                har prog f
                                                                (some bId)
                                                                ⟨nextB + 2,
                                                                [.phi le.supply
                                                                exitT lt.val,
                                                                .phi le.supply
                                                                exitE le.val] ++
                                                                lr.instrs,
                                                                lr.term⟩ F''
                                                                hsub_tr hnodf
                                                                hfindJ fuelB (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB th) hg_tr
                                                                (.lit .unit)).2
                                                                e_arm rfl)
                                                            exact ⟨w_e,
                                                              hret_e.trans heq,
                                                              hentry_r.trans
                                                              hexec_arm⟩
                                                      | stuck =>
                                                          simp only [] at hrun
                                                          have hout_s : out =
                                                              .stuck :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_s] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_s] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | broke =>
                                                          simp only [] at hrun
                                                          have hout_b : out =
                                                              .broke :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_b] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_b] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | continued =>
                                                          simp only [] at hrun
                                                          have hout_c : out =
                                                              .continued :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_c] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_c] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                              | false =>
                                                  simp only [] at hrun
                                                  have hregCb : fenvC.env vc =
                                                      some (.bool false) := by
                                                    have hww : (.bool false) =
                                                        wC :=
                                                      HIR.Expr.lit.inj hrC
                                                    rw [hww]
                                                    exact hregC
                                                  have hbool : fenvC.boolOf vc =
                                                      some false :=
                                                    boolOf_of_lit fenvC vc false
                                                      hregCb
                                                  have hentry : execBlockFromIn
                                                      prog (F'' + 1) f prev
                                                      ⟨bId, ic, .branch vc
                                                      nextB (nextB + 1)⟩ fenv =
                                                      execBlockFromIn prog F'' f
                                                        (some bId)
                                                        ⟨nextB + 1, le.instrs,
                                                        le.term⟩ fenvC :=
                                                    execBlockFromIn_branch_false
                                                      prog F'' f prev bId ic vc
                                                      nextB (nextB + 1) fenv
                                                      fenvC
                                                      ⟨nextB + 1, le.instrs,
                                                      le.term⟩ hexec_ic hbool
                                                      hfindE
                                                  have hsub_e : ∀ b ∈ le.blocks,
                                                      b ∈ f.blocks :=
                                                    fun b hb => hsub _
                                                      (if_asm_mem_of_le hb)
                                                  have hf_e : FreshAbove ρ
                                                      lt.supply :=
                                                    FreshAbove.mono ρ s1
                                                      lt.supply hmst hf1
                                                  have hlast_e : lastVal <
                                                      lt.supply :=
                                                    Nat.lt_of_lt_of_le hlast1
                                                      hmst
                                                  have hCege : (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el) ≥
                                                      blockBound fuelB rest := by
                                                    have hBrest : blockBound
                                                        fuelB rest = 1 +
                                                        armBlockBound fuelB
                                                          rest := rfl
                                                    omega
                                                  have hg_e : F'' ≥ blockBound
                                                      fuelB el + (2 + max
                                                      (armBlockBound fuelB th)
                                                      (armBlockBound fuelB el) +
                                                      armBlockBound fuelB rest -
                                                      armBlockBound fuelB el) := by
                                                    have hBel : blockBound
                                                        fuelB el = 1 +
                                                        armBlockBound fuelB
                                                          el := rfl
                                                    omega
                                                  cases har : runHIRStmts fh
                                                      henv el (HFlow.value
                                                        (.lit .unit)) with
                                                  | mk out_arm env_arm =>
                                                      rw [har] at hrun
                                                      cases out_arm with
                                                      | value u_arm =>
                                                          simp only [] at hrun
                                                          obtain ⟨w_arm, hu_arm,
                                                              F', fenv_arr, hle,
                                                              hge, heq_arm,
                                                              hrel_arm,
                                                              hreg_arr⟩ :=
                                                            ((lowerStmtsCFG_arm_total
                                                              budget (nextB + 1)
                                                              (nextB + 2) ρ
                                                              lt.supply lt.next
                                                              lastVal false el
                                                              le he hael hf_e
                                                              hlast_e .unit henv
                                                              fenvC hrelC
                                                              (fun _ => rfl)
                                                              (fun h => absurd h
                                                              (by simp))
                                                              fh env_arm
                                                              (HFlow.value
                                                              u_arm) har prog f
                                                              (some bId)
                                                              ⟨nextB + 2,
                                                              [.phi le.supply
                                                              exitT lt.val,
                                                              .phi le.supply
                                                              exitE le.val] ++
                                                              lr.instrs,
                                                              lr.term⟩ F''
                                                              hsub_e hnodf
                                                              hfindJ fuelB (2 +
                                                              max
                                                              (armBlockBound
                                                              fuelB th)
                                                              (armBlockBound
                                                              fuelB el) +
                                                              armBlockBound
                                                              fuelB rest -
                                                              armBlockBound
                                                              fuelB el) hg_e
                                                              u_arm).1 rfl)
                                                          rw [hEdef] at heq_arm
                                                          rw [hrho_e] at hrel_arm
                                                          have hrep :
                                                              ((HFlow.value
                                                              (.lit accH)).replace
                                                              (.lit w_arm)) =
                                                              HFlow.value
                                                              (.lit w_arm) :=
                                                            rfl
                                                          rw [hu_arm, hrep] at hrun
                                                          have hfrL : FreshAbove
                                                              ρ le.supply :=
                                                            FreshAbove.mono ρ
                                                              supply le.supply
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              hmse)) hfresh
                                                          have hrel_m : RelEnv
                                                              env_arm ρ
                                                              (fenv_arr.env.update
                                                              le.supply
                                                              w_arm) := by
                                                            intro id u hlook
                                                            obtain ⟨w0, hlookH,
                                                              hreg0⟩ :=
                                                              hrel_arm id u
                                                              hlook
                                                            have hu : u <
                                                                le.supply :=
                                                              hfrL id u
                                                              (rhoLookup_some_mem
                                                              ρ id u hlook)
                                                            have hne : u ≠
                                                                le.supply :=
                                                              Nat.ne_of_lt hu
                                                            refine ⟨w0, hlookH,
                                                              ?_⟩
                                                            have hupd :
                                                                (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                                fenv_arr.env
                                                                u := by
                                                              simp [Env.update,
                                                                hne]
                                                            show (fenv_arr.env.update
                                                                le.supply
                                                                w_arm) u =
                                                              some w0
                                                            rw [hupd]
                                                            exact hreg0
                                                          have hreg_m :
                                                              (⟨fenv_arr.env.update
                                                              le.supply w_arm,
                                                              fenv_arr.store⟩ :
                                                              FullEnv).env
                                                              le.supply =
                                                              some w_arm := by
                                                            simp [Env.update]
                                                          have hf_r : FreshAbove
                                                              ρ (le.supply +
                                                              1) :=
                                                            FreshAbove.mono ρ
                                                              supply
                                                              (le.supply + 1)
                                                              (Nat.le_trans hs1
                                                              (Nat.le_trans hmst
                                                              (Nat.le_trans hmse
                                                              (Nat.le_succ _))))
                                                              hfresh
                                                          have hlast_r :
                                                              le.supply <
                                                              le.supply + 1 :=
                                                            Nat.lt_succ_self _
                                                          have hsub_r : ∀ b ∈
                                                              lr.blocks,
                                                              b ∈ f.blocks :=
                                                            fun b hb => hsub _
                                                              (if_asm_mem_of_lr
                                                              hb)
                                                          cases F' with
                                                          | zero =>
                                                              have hB1r :
                                                                  blockBound
                                                                  fuelB rest ≥
                                                                  1 := by
                                                                rw [blockBound]
                                                                omega
                                                              exact absurd hge
                                                                (by omega)
                                                          | succ F1 =>
                                                              have happ_J :
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitE)
                                                                  fenv_arr
                                                                  ([.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs) =
                                                                  execInstrsFullFromIn
                                                                  prog
                                                                  (some exitE)
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  lr.instrs := by
                                                                simp only
                                                                  [List.cons_append,
                                                                  List.nil_append]
                                                                rw [execInstrsFullFromIn_eq,
                                                                  execInstrsFullFromIn_eq,
                                                                  execInstrsFullFrom_phi_miss
                                                                  _ _ _ _ _ _
                                                                  (Ne.symm
                                                                  hne_pe),
                                                                  execInstrsFullFrom_phi_hit
                                                                  _ _ _ _ _ _
                                                                  rfl,
                                                                  hreg_arr]
                                                              have hJeq :
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitE)
                                                                  ⟨nextB + 2,
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val] ++
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  fenv_arr =
                                                                  execBlockFromIn
                                                                  prog (F1 + 1)
                                                                  f (some exitE)
                                                                  ⟨nextB + 2,
                                                                  lr.instrs,
                                                                  lr.term⟩
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩ :=
                                                                execBlockFromIn_instrs_prefix
                                                                  prog F1 f
                                                                  (some exitE)
                                                                  (nextB + 2)
                                                                  [.phi
                                                                  le.supply
                                                                  exitT lt.val,
                                                                  .phi le.supply
                                                                  exitE le.val]
                                                                  lr.instrs
                                                                  lr.term
                                                                  fenv_arr
                                                                  ⟨fenv_arr.env.update
                                                                  le.supply
                                                                  w_arm,
                                                                  fenv_arr.store⟩
                                                                  happ_J
                                                              have hg_r : F1 + 1 ≥
                                                                  blockBound
                                                                  fuelB rest :=
                                                                Nat.le_trans hCege
                                                                  hge
                                                              intro u
                                                              have hihr := ih
                                                                (nextB + 2) ρ
                                                                (le.supply + 1)
                                                                le.next
                                                                le.supply true
                                                                lr hr hrs hf_r
                                                                hlast_r w_arm
                                                                env_arm
                                                                ⟨fenv_arr.env.update
                                                                le.supply w_arm,
                                                                fenv_arr.store⟩
                                                                hrel_m hreg_m fh
                                                                henv' out hrun
                                                                prog f
                                                                (some exitE)
                                                                (F1 + 1) hsub_r
                                                                hnodf fuelB hg_r
                                                                u
                                                              refine ⟨?_, ?_⟩
                                                              · intro hout
                                                                obtain ⟨w_u, hu,
                                                                    heq_rest⟩ :=
                                                                  hihr.1 hout
                                                                exact ⟨w_u, hu,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                              · intro e_ret hout2
                                                                obtain ⟨w_e, hu_e,
                                                                    heq_rest⟩ :=
                                                                  hihr.2 e_ret
                                                                    hout2
                                                                exact ⟨w_e, hu_e,
                                                                  hentry.trans
                                                                  (heq_arm.trans
                                                                  (hJeq.trans
                                                                  heq_rest))⟩
                                                      | returned e_arm =>
                                                          simp only [] at hrun
                                                          have hout_r : out =
                                                              .returned e_arm :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_r] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            have hret_e : e_ret =
                                                                e_arm :=
                                                              (HFlow.returned.inj
                                                                (hout_r.symm.trans
                                                                hout2)).symm
                                                            have hregCb_r :
                                                                fenvC.env vc =
                                                                some
                                                                (.bool false) := by
                                                              have hww :
                                                                  (.bool false) =
                                                                  wC :=
                                                                HIR.Expr.lit.inj
                                                                  hrC
                                                              rw [hww]
                                                              exact hregC
                                                            have hbool_r :
                                                                fenvC.boolOf vc =
                                                                some false :=
                                                              boolOf_of_lit
                                                                fenvC vc false
                                                                hregCb_r
                                                            have hentry_r :
                                                                execBlockFromIn
                                                                prog (F'' + 1)
                                                                f prev ⟨bId, ic,
                                                                .branch vc
                                                                nextB
                                                                (nextB + 1)⟩
                                                                fenv =
                                                                execBlockFromIn
                                                                prog F'' f
                                                                (some bId)
                                                                ⟨nextB + 1,
                                                                le.instrs,
                                                                le.term⟩
                                                                fenvC :=
                                                              execBlockFromIn_branch_false
                                                                prog F'' f prev
                                                                bId ic vc nextB
                                                                (nextB + 1)
                                                                fenv fenvC
                                                                ⟨nextB + 1,
                                                                le.instrs,
                                                                le.term⟩
                                                                hexec_ic
                                                                hbool_r hfindE
                                                            have hsub_er : ∀ b ∈
                                                                le.blocks,
                                                                b ∈ f.blocks :=
                                                              fun b hb => hsub _
                                                                (if_asm_mem_of_le
                                                                hb)
                                                            have hCege_r : (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) ≥
                                                                blockBound fuelB
                                                                rest := by
                                                              have hBrest :
                                                                  blockBound
                                                                  fuelB rest =
                                                                  1 +
                                                                  armBlockBound
                                                                  fuelB rest :=
                                                                rfl
                                                              omega
                                                            have hg_er : F'' ≥
                                                                blockBound fuelB
                                                                el + (2 + max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) := by
                                                              have hBel :
                                                                  blockBound
                                                                  fuelB el = 1 +
                                                                  armBlockBound
                                                                  fuelB el :=
                                                                rfl
                                                              omega
                                                            obtain ⟨w_e, heq,
                                                                hexec_arm⟩ :=
                                                              ((lowerStmtsCFG_arm_total
                                                                budget (nextB + 1)
                                                                (nextB + 2) ρ
                                                                lt.supply lt.next
                                                                lastVal false el
                                                                le he hael hf_e
                                                                hlast_e .unit
                                                                henv fenvC hrelC
                                                                (fun _ => rfl)
                                                                (fun h => absurd h
                                                                (by simp))
                                                                fh env_arm
                                                                (HFlow.returned
                                                                e_arm)
                                                                har prog f
                                                                (some bId)
                                                                ⟨nextB + 2,
                                                                [.phi le.supply
                                                                exitT lt.val,
                                                                .phi le.supply
                                                                exitE le.val] ++
                                                                lr.instrs,
                                                                lr.term⟩ F''
                                                                hsub_er hnodf
                                                                hfindJ fuelB (2 +
                                                                max
                                                                (armBlockBound
                                                                fuelB th)
                                                                (armBlockBound
                                                                fuelB el) +
                                                                armBlockBound
                                                                fuelB rest -
                                                                armBlockBound
                                                                fuelB el) hg_er
                                                                (.lit .unit)).2
                                                                e_arm rfl)
                                                            exact ⟨w_e,
                                                              hret_e.trans heq,
                                                              hentry_r.trans
                                                              hexec_arm⟩
                                                      | stuck =>
                                                          simp only [] at hrun
                                                          have hout_s : out =
                                                              .stuck :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_s] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_s] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | broke =>
                                                          simp only [] at hrun
                                                          have hout_b : out =
                                                              .broke :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_b] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_b] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                                      | continued =>
                                                          simp only [] at hrun
                                                          have hout_c : out =
                                                              .continued :=
                                                            (congrArg Prod.fst
                                                              hrun).symm
                                                          intro u
                                                          refine ⟨?_, ?_⟩
                                                          · intro hout
                                                            rw [hout_c] at hout
                                                            exact absurd hout
                                                              (by simp)
                                                          · intro e_ret hout2
                                                            rw [hout_c] at hout2
                                                            exact absurd hout2
                                                              (by simp)
                                          | int _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | string _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | pointer _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | float _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | unit =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | undef =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | some _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | none =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | ok _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | err _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | tuple_ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | array_ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | loc _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
                                          | closure _ _ =>
                                              have hst : out = .stuck :=
                                                (congrArg Prod.fst hrun).symm
                                              intro u
                                              refine ⟨?_, ?_⟩
                                              · intro hout
                                                simp [hst] at hout
                                              · intro e hout
                                                simp [hst] at hout
      | returnStmt e rest hstr _ =>
          intro accH henv fenv hrel hacc fuelH henv' out hrun prog f prev F
            hsub hnodf fuelB hg
          simp only [lowerStmtsCFG] at h
          cases he : lowerExpr ρ supply e with
          | none => rw [he] at h; simp at h
          | some p =>
              obtain ⟨v, ie, s1⟩ := p
              rw [he] at h
              simp only [] at h
              obtain rfl := Option.some.inj h
              intro u
              refine ⟨?_, ?_⟩
              · intro hout
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout
                    exact absurd hout (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.returnStmt e :: rest) (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => (.returned v, henv)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck :=
                          (congrArg Prod.fst hrun).symm
                        rw [hst] at hout
                        exact absurd hout (by simp)
                    | some r =>
                        rw [hev] at hrun
                        have hret : out = .returned r :=
                          (congrArg Prod.fst hrun).symm
                        rw [hret] at hout
                        exact absurd hout (by simp)
              · intro e_ret hout2
                cases fuelH with
                | zero =>
                    have hz : runHIRStmts 0 henv (.returnStmt e :: rest)
                        (.value (.lit accH)) = (.stuck, henv) := rfl
                    rw [hz] at hrun
                    have hst : out = .stuck := (congrArg Prod.fst hrun).symm
                    rw [hst] at hout2
                    exact absurd hout2 (by simp)
                | succ fh =>
                    have hstep : runHIRStmts (fh + 1) henv
                        (.returnStmt e :: rest) (.value (.lit accH)) =
                        (match evalHIR 256 henv e with
                          | none => (HFlow.stuck, henv)
                          | some v => (.returned v, henv)) := rfl
                    rw [hstep] at hrun
                    cases hev : evalHIR 256 henv e with
                    | none =>
                        rw [hev] at hrun
                        have hst : out = .stuck :=
                          (congrArg Prod.fst hrun).symm
                        rw [hst] at hout2
                        exact absurd hout2 (by simp)
                    | some r =>
                        rw [hev] at hrun
                        have hret : out = .returned r :=
                          (congrArg Prod.fst hrun).symm
                        rw [hret] at hout2
                        obtain ⟨⟨wE, hrE⟩, fenv1, hexec1, hstore1, wE2,
                            hrE2, hregE⟩ :=
                          lower_total.1 ρ supply e v ie s1 he hstr hfresh
                            henv fenv hrel 256 r hev
                        have hrr : r = e_ret := HFlow.returned.inj hout2
                        have heq : e_ret = .lit wE := hrr.symm ▸ hrE
                        have hnp : ∀ dst pred src,
                            .phi dst pred src ∉ ie := by
                          intro d p s hm
                          exact IsPure_not_phi
                            (lower_isPure.1 _ _ _ _ _ _ he _ hm) d p s rfl
                        have hexec : execInstrsFullFromIn prog prev fenv ie
                            = some fenv1 := by
                          rw [execInstrsFullFromIn_of_noPhi prog prev fenv _
                            hnp]
                          exact hexec1
                        have hbb : blockBound fuelB (.returnStmt e :: rest)
                            = blockBound fuelB rest := by
                          rw [blockBound, blockBound,
                            armBlockBound_cons_not_if fuelB
                              (fun c th el h => by cases h)]
                        have h1 : blockBound fuelB rest ≥ 1 := by
                          rw [blockBound]; omega
                        cases F with
                        | zero => omega
                        | succ F' =>
                            refine ⟨wE, heq, ?_⟩
                            have hLHS : execBlockFromIn prog (F' + 1) f prev
                                    ⟨bId, ie, .return_ v⟩ fenv =
                                    fenv1.env v := by
                              have hret' : execBlockFromIn prog (F' + 1) f
                                      prev ⟨bId, ie, .return_ v⟩ fenv =
                                  (match execInstrsFullFromIn prog prev fenv
                                      ie with
                                   | none => (none : Option Value)
                                   | some g => g.env v) := rfl
                              rw [hret', hexec]
                            have hww : wE = wE2 :=
                              HIR.Expr.lit.inj (hrE.symm.trans hrE2)
                            rw [hLHS, hww]
                            exact hregE

/-! ## §4.4: the fuel bound, and closed programs

Loop 180. The worker leaves `F` and `fuelB` free; the bridge only needs one
instantiation: `F := blockBound fuelH ss` with `fuelB := fuelH`, closed by
`Nat.le_refl`. C7 cites this corollary, never the worker. -/
theorem lowerStmtsCFG_total_bound (budget : Nat) :
    ∀ (bId : MIR.BlockId) (ρ : List (HIR.Id × ValId))
      (supply nextB : Nat) (lastVal : ValId) (hasVal : Bool)
      (ss : List HIR.Stmt) (L : Lowered),
      lowerStmtsCFG bId none false ρ supply nextB lastVal hasVal ss = some L →
      BranchStmts budget ss →
      FreshAbove ρ supply → lastVal < supply →
      ∀ (accH : Value) (henv : HEnv) (fenv : FullEnv),
      RelEnv henv ρ fenv.env →
      fenv.env lastVal = some accH →
      ∀ (fuelH : Nat) (henv' : HEnv) (out : HFlow),
      runHIRStmts fuelH henv ss (.value (.lit accH)) = (out, henv') →
      ∀ (prog : Program) (f : Func) (prev : Option MIR.BlockId),
      (∀ b ∈ L.blocks, b ∈ f.blocks) →
      (f.blocks.map Block.id).Nodup →
      ∀ (u : HIR.Expr),
      (out = .value u →
        ∃ w_u, u = .lit w_u ∧
          execBlockFromIn prog (blockBound fuelH ss) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_u) ∧
      (∀ (e : HIR.Expr), out = .returned e →
        ∃ w_e, e = .lit w_e ∧
          execBlockFromIn prog (blockBound fuelH ss) f prev
            ⟨bId, L.instrs, L.term⟩ fenv = some w_e) := by
  intro bId ρ supply nextB lastVal hasVal ss L h hss hfresh hlast
    accH henv fenv hrel hacc fuelH henv' out hrun prog f prev hsub hnodf u
  exact lowerStmtsCFG_total budget bId ρ supply nextB lastVal hasVal ss L
    h hss hfresh hlast accH henv fenv hrel hacc fuelH henv' out hrun prog f
    prev (blockBound fuelH ss) hsub hnodf fuelH
    (Nat.le_refl (blockBound fuelH ss)) u

/-- Top corollary (C3 exit): a closed lowered program runs the oracle's value.
C7 cites this: HIR success (`runHIRProgram = value`) is MIR success
(`execFuncFrom = some`), with executor fuel `blockBound 1024`. The entry
block's `const 0 unit` prologue peels first (supply starts at 1, so register
0 is free); the worker then runs from `L.instrs`. Succeed-direction only:
C7 must not contrapose this for failure. -/
theorem lowerProgramCFG_correct (budget : Nat) (prog : HIR.Program)
    (f : Func) (progM : Program) (hlower : lowerProgramCFG prog = some f)
    (hss : BranchStmts budget prog.stmts) (w : Value)
    (hrun : runHIRProgram prog = .value (.lit w)) :
    execFuncFrom (blockBound 1024 prog.stmts) f
      ⟨fun _ => none, Store.empty⟩ = some w := by
  unfold lowerProgramCFG at hlower
  cases hc : lowerStmtsCFG 0 none false [] 1 1 0 false prog.stmts with
  | none =>
      simp [hc] at hlower
  | some L =>
      simp [hc] at hlower
      obtain rfl := hlower
      obtain ⟨hmn, hms, hbnd, hnodr⟩ :=
        lowerStmtsCFG_branch_inv budget 0 none [] 1 1 0 false prog.stmts L
          hc hss
      have hsub : ∀ b ∈ L.blocks, b ∈ (⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks := by
        intro b hb
        exact List.Mem.tail _ (List.mem_reverse.mpr hb)
      have hrev : ∀ (l : List Block), (l.map Block.id).Nodup →
          (l.reverse.map Block.id).Nodup := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons b rest ih =>
            intro h
            rw [List.map_cons, List.nodup_cons] at h
            obtain ⟨hnotin, hnod⟩ := h
            have ihr := ih hnod
            rw [List.reverse_cons, List.map_append, List.map_singleton,
              List.nodup_append]
            refine ⟨ihr, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
            intro a ha x hx
            simp only [List.mem_singleton] at hx
            subst hx
            intro hcon
            have ha' : a ∈ rest.map Block.id := by
              obtain ⟨c, hc_mem, hc_id⟩ := List.mem_map.mp ha
              exact List.mem_map.mpr
                ⟨c, List.mem_reverse.mp hc_mem, hc_id⟩
            exact hnotin (hcon ▸ ha')
      have hmap0 : (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id) =
          0 :: L.blocks.reverse.map Block.id := rfl
      have hnodf : (((⟨"main", [],
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ : Func).blocks).map
          Block.id).Nodup := by
        show (((⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
          L.blocks.reverse).map Block.id).Nodup
        rw [hmap0]
        refine List.nodup_cons.mpr ⟨?_, hrev _ hnodr⟩
        intro hm
        obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hm
        obtain ⟨hlo, -⟩ := hbnd b (List.mem_reverse.mp hb)
        rw [hbid] at hlo
        exact absurd hlo (by decide)
      have hmem_entry : (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ∈
          (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse :=
        List.Mem.head _
      have hfind_entry : findBlock
          ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) ::
            L.blocks.reverse, 0, .unitType⟩ 0 =
          some (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block) :=
        findBlock_of_nodup_mem hnodf hmem_entry
      cases hp : runHIRStmts 1024 [] prog.stmts (.value (.lit .unit)) with
      | mk out henv' =>
          have hout : out = .value (.lit w) := by
            have h1 : (runHIRStmts 1024 [] prog.stmts
                (.value (.lit .unit))).1 = .value (.lit w) := hrun
            rw [hp] at h1
            simp only [] at h1
            exact h1
          have hfresh : FreshAbove ([] : List (HIR.Id × ValId)) 1 := by
            intro j u hmem
            exact absurd hmem (by simp)
          have hrel : RelEnv ([] : HEnv) []
              (Env.update (fun _ => none) 0 .unit) := by
            intro id u hlook
            exact absurd hlook (by simp [rhoLookup])
          have hacc : Env.update (fun _ => none : Morph.MIR.Env) 0 .unit 0 =
              some .unit := by
            simp [Env.update]
          have hexec0 : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              [.const 0 .unit] =
              some (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                Store.empty⟩ : FullEnv) := rfl
          have happ : execInstrsFullFromIn progM none
              ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩
              ([.const 0 .unit] ++ L.instrs) =
              execInstrsFullFromIn progM none
                (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                  Store.empty⟩ : FullEnv) L.instrs := by
            rw [execInstrsFullFromIn_append, hexec0]
          cases hF : blockBound 1024 prog.stmts with
          | zero =>
              have h1 : blockBound 1024 prog.stmts ≥ 1 := by
                rw [blockBound]; omega
              omega
          | succ F' =>
              have hpeel : execBlockFromIn progM (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none
                  (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    ⟨0, L.instrs, L.term⟩
                    (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                      Store.empty⟩ : FullEnv) :=
                execBlockFromIn_instrs_prefix progM F'
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩ none 0
                  [.const 0 .unit] L.instrs L.term _ _ happ
              have hrunF : execFuncFrom (F' + 1)
                  ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                    Block) :: L.blocks.reverse, 0, .unitType⟩
                  ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ =
                  execBlockFromIn progM (F' + 1)
                    ⟨"main", [], (⟨0, .const 0 .unit :: L.instrs, L.term⟩ :
                      Block) :: L.blocks.reverse, 0, .unitType⟩ none
                    (⟨0, .const 0 .unit :: L.instrs, L.term⟩ : Block)
                    ⟨(fun _ => none : Morph.MIR.Env), Store.empty⟩ := by
                rw [execFuncFrom_eq _ _ _ _ hfind_entry,
                  ← execBlockFromIn_eq]
              obtain ⟨w_u, hu, heq⟩ :=
                (lowerStmtsCFG_total_bound budget 0 [] 1 1 0 false prog.stmts
                  L hc hss hfresh (by decide) .unit []
                  (⟨Env.update (fun _ => none : Morph.MIR.Env) 0 .unit,
                    Store.empty⟩ : FullEnv) hrel hacc 1024 henv'
                  out hp progM _ none hsub hnodf (.lit w)).1 hout
              have hw : w = w_u := HIR.Expr.lit.inj hu
              subst hw
              rw [hF] at heq
              exact hrunF.trans (hpeel.trans heq)

/-! ## The lowered CFG runs

These are evidence, not the theorem: the same expression in both arms would pass
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

end Morph.HIRToMIRCorrect
