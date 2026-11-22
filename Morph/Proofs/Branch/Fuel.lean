/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal

/-!
# Proof crate `Fuel` (L0 leaf): one computable block budget

Estate-style leaf: depends on `Core`/`Total` only, never on
`Morph.HIRToMIRBranch` or another leaf. `Morph.HIRToMIRBranch` imports this
module back; the tree stays green between cuts.

Provenance (statements unchanged, proofs verbatim): `armBlockBound`,
`blockBound`, `armBlockBound_nil`/`_if`/`_while`, `armBlockBound_cons_not_if`,
`armBlockBound_eq_zero_of_forall_not_if` — extracted from
`Morph/HIRToMIRBranch.lean` § "Fuel: one computable budget for the whole
stage (scope §4.4)".

C3's theorem cannot carry a literal fuel constant. `if` costs three blocks
(its condition block, the taken arm, the join) and C7's loops cost a block
per iteration, so a constant chosen for `if` is wrong for `while` and every
later statement in the stage would have to repair it. `blockBound` is that
budget, stated once.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

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
      | .whileLoop _ body =>
          -- C7: a loop body runs once per oracle-fuel unit (header plus its
          -- own entry and extras), so the bound multiplies by `fuel + 1`.
          -- C7c validates the traversal against this number.
          (2 + armBlockBound fuel body) * (fuel + 1)
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

@[simp] theorem armBlockBound_while (fuel : Nat) (c : HIR.Expr)
    (body rest : List HIR.Stmt) :
    armBlockBound fuel (.whileLoop c body :: rest) =
      (2 + armBlockBound fuel body) * (fuel + 1)
        + armBlockBound fuel rest := by
  rw [armBlockBound.eq_def]

/-- A statement that is neither an `if` nor a `while` stays inside the block
it starts in, so it adds no blocks to the list's bound. -/
theorem armBlockBound_cons_not_if (fuel : Nat) {s : HIR.Stmt}
    {rest : List HIR.Stmt} (h : ∀ c th el, s ≠ .ifStmt c th el)
    (hw : ∀ c body, s ≠ .whileLoop c body) :
    armBlockBound fuel (s :: rest) = armBlockBound fuel rest := by
  rw [armBlockBound.eq_def]
  cases s with
  | ifStmt c th el => exact absurd rfl (h c th el)
  | whileLoop c body => exact absurd rfl (hw c body)
  | _ => rfl

/-- `if`- and `while`-free statement lists never leave their block, so their
budget is one block. This is the case every Stage A/B program falls into. -/
theorem armBlockBound_eq_zero_of_forall_not_if (fuel : Nat) :
    ∀ {ss : List HIR.Stmt}, (∀ s ∈ ss, ∀ c th el, s ≠ .ifStmt c th el) →
      (∀ s ∈ ss, ∀ c body, s ≠ .whileLoop c body) →
      armBlockBound fuel ss = 0
  | [], _, _ => armBlockBound_nil fuel
  | s :: rest, h, hw => by
      rw [armBlockBound_cons_not_if fuel
        (fun c th el => h s (List.mem_cons_self ..) c th el)
        (fun c body => hw s (List.mem_cons_self ..) c body)]
      exact armBlockBound_eq_zero_of_forall_not_if fuel
        (fun s' hs' c th el => h s' (List.mem_cons_of_mem _ hs') c th el)
        (fun s' hs' c body => hw s' (List.mem_cons_of_mem _ hs') c body)

end Morph.HIRToMIRCorrect
