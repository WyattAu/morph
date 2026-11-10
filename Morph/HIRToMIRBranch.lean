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
                                       ++ lr.blocks ++ [⟨nextB + 2,
                                           [.phi le.supply ((lt.blocks.getLast?.map (fun b => b.id)).getD nextB) lt.val,
                                            .phi le.supply ((le.blocks.getLast?.map (fun b => b.id)).getD (nextB + 1)) le.val] ++ lr.instrs,
                                           lr.term⟩]
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
  some ⟨"main", [], ⟨0, [.const 0 .unit] ++ L.instrs, L.term⟩ :: L.blocks.reverse,
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
    ((A ++ [thenB] ++ B ++ [elseB] ++ C ++ [joinB]).map Block.id).Nodup := by
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
  have e1 : (C.map Block.id ++ [nextB + 2]).Nodup :=
    nodup_concat hnodC (by simp) (by
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      obtain ⟨hloC, -⟩ := hbC x hx
      exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
        (Nat.le_trans (Nat.le_trans hmnt hmne) hloC)))
  have e2 : ([nextB + 1] ++ (C.map Block.id ++ [nextB + 2])).Nodup :=
    nodup_concat (by simp) e1 (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
          (Nat.le_trans (Nat.le_trans hmnt hmne) hloC))
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 1 < 2 from by decide) nextB))
  have e3 : (B.map Block.id ++
      ([nextB + 1] ++ (C.map Block.id ++ [nextB + 2]))).Nodup :=
    nodup_concat hnodB e2 (by
      intro x hx y hy
      obtain ⟨hloB, hhiB⟩ := hbB x hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with rfl | hy | rfl
      · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
          (Nat.le_trans hmnt hloB))
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiB hloC)
      · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
          (Nat.le_trans hmnt hloB)))
  have e4 : ([nextB] ++ (B.map Block.id ++
      ([nextB + 1] ++ (C.map Block.id ++ [nextB + 2])))).Nodup :=
    nodup_concat (by simp) e3 (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl | hy | rfl
      · obtain ⟨hloB, -⟩ := hbB y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 0 < 3 from by decide) x)
          (Nat.le_trans hmnt hloB))
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 0 < 1 from by decide) x)
      · obtain ⟨hloC, -⟩ := hbC y hy
        exact ne_of_lt_nat' (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (show 0 < 3 from by decide) x)
          (Nat.le_trans (Nat.le_trans hmnt hmne) hloC))
      · exact ne_of_lt_nat'
          (Nat.add_lt_add_left (show 0 < 2 from by decide) x))
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    hthen, helse, hjoin]
  exact nodup_concat hnodA e4 (by
    intro x hx y hy
    obtain ⟨hloA, hhiA⟩ := hbA x hx
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with rfl | hy | rfl | hy | rfl
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 0 < 3 from by decide) y)
        hloA)
    · obtain ⟨hloB, -⟩ := hbB y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiA hloB)
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 1 < 3 from by decide) nextB)
        hloA)
    · obtain ⟨hloC, -⟩ := hbC y hy
      exact ne_of_lt_nat' (Nat.lt_of_lt_of_le hhiA (Nat.le_trans hmne hloC))
    · exact ne_of_gt_nat' (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (show 2 < 3 from by decide) nextB)
        hloA))

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
                                rcases hb with ((((hb | rfl) | hb) | rfl) | hb) | rfl
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
                                · obtain ⟨hlo, hhi⟩ := hbndr b hb
                                  exact ⟨Nat.le_trans (Nat.le_trans
                                      (Nat.le_trans (Nat.le_add_right _ _)
                                        hmnt) hmne) hlo,
                                    Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                                · exact ⟨Nat.le_add_right _ _,
                                    Nat.lt_of_le_of_lt (Nat.le_trans
                                      (Nat.le_trans (Nat.le_trans
                                        (Nat.le_succ _) hmnt) hmne) hmnr)
                                      (Nat.lt_succ_self _)⟩
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
                        rcases hb with ((((hb | rfl) | hb) | rfl) | hb) | rfl
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
                        · obtain ⟨hlo, hhi⟩ := hbndr b hb
                          exact ⟨Nat.le_trans (Nat.le_trans
                              (Nat.le_trans (Nat.le_add_right _ _)
                                hmnt) hmne) hlo,
                            Nat.lt_of_lt_of_le hhi (Nat.le_succ _)⟩
                        · exact ⟨Nat.le_add_right _ _,
                            Nat.lt_of_le_of_lt (Nat.le_trans
                              (Nat.le_trans (Nat.le_trans
                                (Nat.le_succ _) hmnt) hmne) hmnr)
                              (Nat.lt_succ_self _)⟩
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
