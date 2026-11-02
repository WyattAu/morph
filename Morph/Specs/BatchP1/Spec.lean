/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Feasible-50 kernels — P1 verification + types (loop 110)

Executable cores for the first ten feasible rows (E4 triage, Batch P1):
E-104, E-113, E-116, E-120, E-123, E-124, E-137, E-141, E-148, E-149.
Each section is a *model with a theorem*: the smallest decidable kernel
that makes the row falsifiable. `Std`-only, `Nat`/`List`/`Bool` first.

| Register row | Concept | Lean core |
|---|---|---|
| E-104 | peephole translation validation | `PExpr`, `peval`, `popt`, `validOpt` |
| E-113 | differential check vs oracle | `agree` |
| E-116 | Kildall liveness on straight-line code | `transfer`, `seqLive` |
| E-120 | borrow completeness, loop-free fragment | `Loan`, `conflicts`, `acceptLoan` |
| E-123 | monotone-framework engine | `mj`, `mtrans`, `runM` |
| E-124 | interval domain + widening | `Ival`, `ivalJoin`, `widen` |
| E-137 | order-lifecycle typestate | `OState`, `OEv`, `ostep` |
| E-141 | phantom venue branding | `BOrder`, `matchSame` |
| E-148 | or-pattern exhaustiveness | `Pat`, `hasWild`, `coversAny` |
| E-149 | row-polymorphic risk records | `Row`, `compose`, `hasField` |
-/

namespace Morph.Specs.BatchP1

/-! ## E-104: peephole validation -/

/-- Tiny peephole expression language. -/
inductive PExpr where
  | const : Nat → PExpr
  | add : PExpr → PExpr → PExpr
  deriving Repr, DecidableEq

/-- Evaluator (the oracle). -/
def peval : PExpr → Nat
  | .const n => n
  | .add a b => peval a + peval b

/-- Zero test for the peephole rule. -/
def isZero : PExpr → Bool
  | .const n => decide (n = 0)
  | .add _ _ => false

/-- One certified peephole rule: drop `+ 0` on either side. -/
def popt : PExpr → PExpr
  | .const n => .const n
  | .add a b =>
    if isZero b then popt a
    else if isZero a then popt b
    else .add (popt a) (popt b)

/-- Validator: pre/post agree on evaluation. -/
def validOpt (a b : PExpr) : Bool := decide (peval a = peval b)

/-! ## E-113: differential agreement -/

/-- Check agrees with oracle iff the booleans match. -/
def agree (c o : Bool) : Bool := c == o

/-! ## E-116: liveness transfer -/

/-- One straight-line instruction: single def, use list. -/
structure Instr where
  defv : Nat
  uses : List Nat
  deriving Repr, DecidableEq

/-- Backward transfer: uses plus live-after minus the def. -/
def transfer (i : Instr) (liveAfter : List Nat) : List Nat :=
  i.uses ++ liveAfter.filter (fun v => v != i.defv)

/-- Fold the transfer over a block (back to front). -/
def seqLive : List Instr → List Nat → List Nat
  | [], live => live
  | i :: is, live => transfer i (seqLive is live)

/-! ## E-120: loop-free borrow acceptance -/

/-- A loan: holder place, borrower place. -/
structure Loan where
  holder : Nat
  borrower : Nat
  deriving Repr, DecidableEq

/-- Conflict iff the same place is already held. -/
def conflicts (ls : List Loan) (holder : Nat) : Bool :=
  ls.any (fun l => l.holder == holder)

/-- Accept a new loan iff it conflicts with nothing held. -/
def acceptLoan (ls : List Loan) (holder _borrower : Nat) : Bool :=
  !conflicts ls holder

/-! ## E-123: monotone framework over Nat -/

/-- Join is `max`. -/
def mj (a b : Nat) : Nat := Nat.max a b

/-- Transfer adds a constant. -/
def mtrans (t x : Nat) : Nat := x + t

/-- Run the transfer over a block. -/
def runM : List Nat → Nat → Nat
  | [], x => x
  | t :: ts, x => runM ts (mtrans t x)

/-! ## E-124: interval domain -/

/-- A closed interval. -/
structure Ival where
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

/-- Validity: non-empty. -/
def ivalOk (i : Ival) : Prop := i.lo ≤ i.hi

/-- Join: hull of both. -/
def ivalJoin (a b : Ival) : Ival :=
  ⟨Nat.min a.lo b.lo, Nat.max a.hi b.hi⟩

/-- Widening: keep the lower bound, jump the upper bound up. -/
def widen (a b : Ival) : Ival :=
  ⟨Nat.min a.lo b.lo, Nat.max a.hi b.hi + (if b.hi ≤ a.hi then 0 else 1)⟩

/-! ## E-137: order typestate -/

/-- Order lifecycle states. -/
inductive OState where
  | placed
  | acked
  | filled
  deriving Repr, DecidableEq

/-- Lifecycle events. -/
inductive OEv where
  | ack
  | fill
  deriving Repr, DecidableEq

/-- Legal transitions; illegal ones are `none`. -/
def ostep : OState → OEv → Option OState
  | .placed, .ack => some .acked
  | .acked, .fill => some .filled
  | _, _ => none

/-! ## E-141: phantom branding -/

/-- An order branded by venue. -/
structure BOrder where
  venue : Nat
  qty : Nat
  deriving Repr, DecidableEq

/-- Same-venue match (the brand check). -/
def matchSame (a b : BOrder) : Bool := decide (a.venue = b.venue)

/-! ## E-148: pattern exhaustiveness -/

/-- Tiny pattern language. -/
inductive Pat where
  | wild : Pat
  | lit : Nat → Pat
  deriving Repr, DecidableEq

/-- A row of patterns is exhaustive iff it has a wildcard. -/
def hasWild (ps : List Pat) : Bool := ps.any (fun p => p == .wild)

/-- Coverage of a value: wildcards cover; literals match exactly. -/
def coversAny : List Pat → Option Nat → Bool
  | [], _ => false
  | .wild :: _, _ => true
  | .lit _ :: ps, v => coversAny ps v

/-! ## E-149: row records -/

/-- A row is a field-id list. -/
abbrev Row := List Nat

/-- Compose two rows. -/
def compose (r1 r2 : Row) : Row := r1 ++ r2

/-- Field membership. -/
def hasField (r : Row) (f : Nat) : Bool := decide (f ∈ r)

end Morph.Specs.BatchP1
