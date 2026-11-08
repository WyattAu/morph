/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore

/-!
# Stage C statement fragment: `if`-statements

`docs/STAGEC-SCOPE.md` items C2/C3. Stage A's `StraightStmts`
(`Morph/HIRToMIRCore.lean`) is the hypothesis of `compile_total`, so adding an
`ifStmt` constructor to it would make that theorem's `if`-case an unproved
obligation the moment the constructor exists — the tree would stop being green
between C2 and C3. This file instead defines the Stage C fragment as a *new*
predicate, `BranchStmts`, which strictly contains the straight-line one
(`straightStmts_to_branch`). `compile_total` keeps its exact statement and its
exact proof; C3's theorem takes `BranchStmts`, and its `if`-free instances are
recovered through the embedding.

Three deliberate shape choices:

- **Statement steps are a separate relation.** `BranchStep` holds the
  per-statement conditions; `BranchStmts` holds the list structure. `ifStmt` is
  then an extra *side* condition (two sub-lists, recursively well-formed)
  instead of a new arm inside an existing induction, which is what keeps the
  existing `StraightStmts` inductions untouched.
- **`returnStmt` is terminal here too.** `runStmts` stops at a `return` and
  `lowerStmts` never lowers the tail, so `BranchStmts` does not constrain that
  tail either. This is exactly why `returnStmt` is a `BranchStmts` constructor
  rather than a `BranchStep`: a terminal shape is not a step.
- **The expression conditions are Stage A's, not new ones.** `IsStraight` and
  `SLWeight` are imported, so the expression bridge is shared.

Not in the fragment (each is a later item, and their absence is the contract):
`whileLoop`, `doWhile`, `matchStmt`, `break`, `continue`.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR

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
      BranchStmts budget th → BranchStmts budget el →
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

/-! ## The boundary is real

The three facts below are the ones an auditor would ask for: `if` is in,
nesting is in (so the arms' recursive structure is not decoration), and `while`
is out. -/

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
    (.cons (.ifStmt (.lit (.bool false)) _ _
      (.lit _) (by simp [SLWeight]) (.cons .nop .nil) .nil) .nil)
    .nil) .nil

/-- `while` is outside the fragment: `BranchStep` has no arm for it, and the
`returnStmts` shape cannot unify with a `whileLoop`, so `cases` closes both. -/
example : ¬ BranchStmts 256 [.whileLoop (.lit (.bool true)) []] := by
  intro h
  cases h with
  | cons hs _ => cases hs

end Morph.HIRToMIRCorrect
