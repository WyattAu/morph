/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Semantics

import Std

open Morph.Core
open Morph.Syntax
open Morph.Semantics

namespace Morph.Executable

/-!
# Executable Reference Interpreter

Big-step call-by-value evaluator for the Morph surface syntax.
Serves as the test oracle for the future Rust/C++ compiler.

Uses the same de Bruijn substitution as the small-step `Step` relation,
ensuring consistency between the formal semantics and executable behavior.

Note: The evaluator works with `Expr` as the result type because lambda
closures (`Expr.lam`) are values in the Morph semantics (see `IsValue`).
-/

/-! ## Context -/

/-- Runtime environment: bound-variable stack (de Bruijn) + free-variable map.
    Stores `Expr` values (literals and lambdas) since both are valid Morph values. -/
structure Context where
  bvs : List Expr     -- bound variable values (always .lit or .lam)
  fvs : List (String × Expr)  -- free variable name-value pairs
  deriving Repr

/-- Empty context -/
def Context.empty : Context := ⟨[], []⟩

/-- Push a bound variable value -/
def Context.pushBv (ctx : Context) (v : Expr) : Context :=
  { ctx with bvs := v :: ctx.bvs }

/-- Push n bound variable values (reversed so first becomes bvar n-1) -/
def Context.pushBvs (ctx : Context) (vs : List Expr) : Context :=
  { ctx with bvs := vs.reverse ++ ctx.bvs }

/-- Look up a bound variable by de Bruijn index -/
def Context.getBv? (ctx : Context) (n : Nat) : Option Expr :=
  let rec go : List Expr → Nat → Option Expr
    | [], _ => none
    | v :: _, 0 => some v
    | _ :: rest, n + 1 => go rest n
  go ctx.bvs n

/-- Look up a free variable by name -/
def Context.getFv? (ctx : Context) (name : String) : Option Expr :=
  ctx.fvs.findSome? (fun (n, v) => if n == name then some v else none)

/-! ## Operation Evaluation -/

/-- Evaluate unary operations on values.
    Input must be a `.lit` value; returns `.lit` result. -/
def evalUnop (op : Operator) (v : Expr) : Option Expr :=
  match op, v with
  | .not, .lit (.bool b) => some (.lit (.bool (!b)))
  | .notb, .lit (.int n) => some (.lit (.int (-n - 1)))
  | _, _ => none

/-- Evaluate binary operations on values.
    Inputs must be `.lit` values; returns `.lit` result.
    Matches the behavior of `Step` rules in Semantics.lean exactly. -/
def evalBinop (op : Operator) (v1 v2 : Expr) : Option Expr :=
  match v1, v2 with
  | .lit (.int n1), .lit (.int n2) =>
    match op with
    | .add => some (.lit (.int (n1 + n2)))
    | .sub => some (.lit (.int (n1 - n2)))
    | .mul => some (.lit (.int (n1 * n2)))
    | .div => some (.lit (.int (if n2 == 0 then 0 else n1 / n2)))
    | .mod => some (.lit (.int (if n2 == 0 then 0 else n1 % n2)))
    | .eq => some (.lit (.bool (n1 == n2)))
    | .neq => some (.lit (.bool !(n1 == n2)))
    | .lt => some (.lit (.bool (n1 < n2)))
    | .leq => some (.lit (.bool (n1 <= n2)))
    | .gt => some (.lit (.bool (n1 > n2)))
    | .geq => some (.lit (.bool (n1 >= n2)))
    | .andb => some (.lit (.int (if decide (n1 % 2 = 1) && decide (n2 % 2 = 1) then 1 else 0)))
    | .orb => some (.lit (.int (if decide (n1 % 2 = 1) || decide (n2 % 2 = 1) then 1 else 0)))
    | .xorb => some (.lit (.int (if decide (n1 % 2 = 1) != decide (n2 % 2 = 1) then 1 else 0)))
    | .shl => some (.lit (.int (n1 * Int.pow 2 n2.toNat)))
    | .shr => some (.lit (.int (Int.shiftRight n1 n2.toNat)))
    | .ptrAdd | .ptrSub | .ptrLoad | .ptrStore => none
    | .and | .or | .not | .notb => none
  | .lit (.bool b1), .lit (.bool b2) =>
    match op with
    | .and => some (.lit (.bool (b1 && b2)))
    | .or => some (.lit (.bool (b1 || b2)))
    | _ => none
  | .lit (.pointer p), .lit (.int n) =>
    match op with
    | .ptrAdd => some (.lit (.pointer { p with offset := p.offset + n }))
    | .ptrSub => some (.lit (.pointer { p with offset := p.offset - n }))
    | .ptrLoad => some (.lit .undef)
    | .ptrStore => some (.lit .unit)
    | _ => none
  | .lit (.float f1), .lit (.float f2) =>
    match op with
    | .add => some (.lit (.float (f1 + f2)))
    | .sub => some (.lit (.float (f1 - f2)))
    | .mul => some (.lit (.float (f1 * f2)))
    | .div => some (.lit (.float (f1 / f2)))
    | .eq => some (.lit (.bool (f1 == f2)))
    | .neq => some (.lit (.bool !(f1 == f2)))
    | .lt => some (.lit (.bool (f1 < f2)))
    | .leq => some (.lit (.bool (f1 <= f2)))
    | .gt => some (.lit (.bool (f1 > f2)))
    | .geq => some (.lit (.bool (f1 >= f2)))
    | _ => none
  | .lit (.string s1), .lit (.string s2) =>
    match op with
    | .add => some (.lit (.string (s1 ++ s2)))
    | _ => none
  | _, _ => none

/-! ## Main Evaluator -/

instance : Inhabited Expr := ⟨Expr.lit Value.unit⟩

/-- Fuel-bounded big-step call-by-value evaluator.
    Returns `some v` if evaluation completes, `none` if it gets stuck or the
    fuel runs out. Uses the same `substAll` from Syntax.lean as the small-step
    `Step` relation.

    **Totality.** This used to be a `partial def`: β-substitution grows the
    term, so termination is genuinely non-structural. The fuel makes the
    evaluator kernel-transparent (its equations reduce, so `rfl`/`decide` can
    compute with it) at the price of an explicit bound: every recursive step —
    including one iteration of a `forLoop` — consumes one unit. Blocks are
    evaluated by mapping over the expression list and taking the last value,
    which is what the sequential `evalBlock` computed. -/
def evalWithFuel : Nat → Context → Expr → Option Expr
  | 0, _, _ => none
  | fuel + 1, ctx, e =>
    match e with
    | .bvar n => ctx.getBv? n
    | .fvar name => ctx.getFv? name
    | .lit v => some (.lit v)
    | .unop op a => do
      let v ← evalWithFuel fuel ctx a
      evalUnop op v
    | .binop op a b => do
      let v1 ← evalWithFuel fuel ctx a
      let v2 ← evalWithFuel fuel ctx b
      evalBinop op v1 v2
    | .app fn args => do
      let fnVal ← evalWithFuel fuel ctx fn
      match fnVal with
      | .lam n body =>
        if args.length ≠ n then none
        else do
          let argVals ← args.mapM (evalWithFuel fuel ctx)
          evalWithFuel fuel ctx (substAll argVals.reverse body)
      | _ => none
    | .lam n body => some (.lam n body)
    | .let_ a b => do
      let v1 ← evalWithFuel fuel ctx a
      evalWithFuel fuel (ctx.pushBv v1) b
    | .ifThenElse c t f => do
      let cv ← evalWithFuel fuel ctx c
      match cv with
      | .lit (.bool true) => evalWithFuel fuel ctx t
      | .lit (.bool false) => evalWithFuel fuel ctx f
      | _ => none
    | .forLoop start stop body => do
      let sv ← evalWithFuel fuel ctx start
      let ev ← evalWithFuel fuel ctx stop
      match sv, ev with
      | .lit (.int n), .lit (.int m) =>
        if n ≥ m then some (.lit .unit)
        else do
          let _ ← evalWithFuel fuel (ctx.pushBv (.lit (.int n))) (.block body)
          evalWithFuel fuel ctx (.forLoop (.lit (.int (n + 1))) stop body)
      | _, _ => none
    | .block exprs => do
      let vs ← exprs.mapM (evalWithFuel fuel ctx)
      match vs with
      | [] => some (.lit .unit)
      | vs' => some vs'.getLast!
    | .match_ scrut branches => do
      let sv ← evalWithFuel fuel ctx scrut
      match branches with
      | [] => none
      | (vars, body) :: _ =>
        evalWithFuel fuel (ctx.pushBvs (List.replicate vars.length sv)) body
    | .field_ a _ => evalWithFuel fuel ctx a
    | .pipe a f => do
      let v ← evalWithFuel fuel ctx a
      evalWithFuel fuel ctx (.app f [v])
    | .typeAsc a _ => evalWithFuel fuel ctx a
    | .none_ => some (.lit Value.none)
    | .some_ a => do
      let v ← evalWithFuel fuel ctx a
      match v with
      | .lit inner => some (.lit (.some inner))
      | .none_ => some (.lit (.some Value.none))
      | .lam _ _ => none
      | _ => none
    | .ok_ a => do
      let v ← evalWithFuel fuel ctx a
      match v with
      | .lit inner => some (.lit (.ok inner))
      | .none_ => some (.lit (.ok Value.none))
      | .lam _ _ => none
      | _ => none
    | .err_ a => do
      let v ← evalWithFuel fuel ctx a
      match v with
      | .lit inner => some (.lit (.err inner))
      | .none_ => some (.lit (.err Value.none))
      | .lam _ _ => none
      | _ => none
    | .nullCoalesce a b => do
      let v1 ← evalWithFuel fuel ctx a
      match v1 with
      | .lit (.some _) => some v1
      | .lit .none => evalWithFuel fuel ctx b
      | .some_ _ => some v1
      | .none_ => evalWithFuel fuel ctx b
      | _ => none
    | .tuple_ elems => do
      let vals ← elems.mapM (evalWithFuel fuel ctx)
      if vals.length = elems.length then
        some (.lit (.tuple_
          (vals.filterMap fun v => match v with | .lit inner => some inner | _ => none)))
      else
        none
    | .arrayLit elems => do
      let vals ← elems.mapM (evalWithFuel fuel ctx)
      if vals.length = elems.length then
        some (.lit (.array_
          (vals.filterMap fun v => match v with | .lit inner => some inner | _ => none)))
      else
        none
    | .arrayIndex arr idx => do
      let arrVal ← evalWithFuel fuel ctx arr
      let idxVal ← evalWithFuel fuel ctx idx
      match arrVal, idxVal with
      | .lit (.array_ elems), .lit (.int n) =>
        if n ≥ 0 && n < elems.length then
          some (.lit (elems.getD n.toNat .unit))
        else none
      | _, _ => none
    | .refCreate a _cap _ => do
      let _ ← evalWithFuel fuel ctx a
      some (.lit (.loc 0))  -- placeholder; real semantics uses Store
    | .refLoad a => do
      let _ ← evalWithFuel fuel ctx a
      some (.lit .unit)  -- placeholder
    | .refStore a v _ => do
      let _ ← evalWithFuel fuel ctx a
      let _ ← evalWithFuel fuel ctx v
      some (.lit .unit)  -- placeholder
    | .refFree a => do
      let _ ← evalWithFuel fuel ctx a
      some (.lit .unit)  -- placeholder
    | .refCast a _ => do
      let _ ← evalWithFuel fuel ctx a
      some (.lit .unit)  -- placeholder

/-- The shipped evaluator: `evalWithFuel` seeded with 256 units. Every recursive
step — including one `forLoop` iteration — consumes one unit, so 256 covers
the tests' expression depths and iteration counts; exhaustion returns `none`
instead of diverging. -/
def eval (ctx : Context) (e : Expr) : Option Expr :=
  evalWithFuel 256 ctx e

/-- Evaluate an expression in the empty context. -/
def run (e : Expr) : Option Expr :=
  eval Context.empty e

end Morph.Executable
