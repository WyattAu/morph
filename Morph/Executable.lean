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

/-- Big-step call-by-value evaluator.
    Returns `some v` if evaluation completes, `none` if it gets stuck.
    Uses the same `substAll` from Syntax.lean as the small-step `Step` relation. -/
partial def eval (ctx : Context) : Expr → Option Expr
  | .bvar n => ctx.getBv? n
  | .fvar name => ctx.getFv? name
  | .lit v => some (.lit v)
  | .unop op e => do
    let v ← eval ctx e
    evalUnop op v
  | .binop op e1 e2 => do
    let v1 ← eval ctx e1
    let v2 ← eval ctx e2
    evalBinop op v1 v2
  | .app fn args => do
    let fnVal ← eval ctx fn
    match fnVal with
    | .lam n body =>
      if args.length ≠ n then none
      else do
        let argVals ← args.mapM (eval ctx)
        let body' := substAll argVals.reverse body
        eval ctx body'
    | _ => none
  | .lam n body => some (.lam n body)
  | .let_ e1 e2 => do
    let v1 ← eval ctx e1
    eval (ctx.pushBv v1) e2
  | .ifThenElse c t f => do
    let cv ← eval ctx c
    match cv with
    | .lit (.bool true) => eval ctx t
    | .lit (.bool false) => eval ctx f
    | _ => none
  | .forLoop start stop body => do
    let s ← eval ctx start
    let e ← eval ctx stop
    match s, e with
    | .lit (.int s), .lit (.int e) =>
      loop ctx s e body
    | _, _ => none
  | .block exprs => evalBlock ctx exprs
  | .match_ scrut branches => do
    let sv ← eval ctx scrut
    evalMatch ctx sv branches
  | .field_ e _ => eval ctx e
  | .pipe e f => do
    let v ← eval ctx e
    eval ctx (.app f [v])
  | .typeAsc e _ => eval ctx e
  | .none_ => some (.lit Value.none)
  | .some_ e => do
    let v ← eval ctx e
    match v with
    | .lit inner => some (.lit (.some inner))
    | .none_ => some (.lit (.some Value.none))
    | .lam _ _ => none
    | _ => none
  | .ok_ e => do
    let v ← eval ctx e
    match v with
    | .lit inner => some (.lit (.ok inner))
    | .none_ => some (.lit (.ok Value.none))
    | .lam _ _ => none
    | _ => none
   | .err_ e => do
     let v ← eval ctx e
     match v with
     | .lit inner => some (.lit (.err inner))
     | .none_ => some (.lit (.err Value.none))
     | .lam _ _ => none
     | _ => none
   | .nullCoalesce e1 e2 => do
     let v1 ← eval ctx e1
     match v1 with
     | .lit (.some _) => some v1
     | .lit .none => eval ctx e2
     | .some_ _ => some v1
     | .none_ => eval ctx e2
     | _ => none
   | .tuple_ elems => do
      let vals ← elems.mapM (eval ctx)
      if vals.length = elems.length then
        some (.lit (.tuple_ (vals.filterMap fun v => match v with | .lit inner => some inner | _ => none)))
      else
        none
   | .arrayLit elems => do
      let vals ← elems.mapM (eval ctx)
      if vals.length = elems.length then
        some (.lit (.array_ (vals.filterMap fun v => match v with | .lit inner => some inner | _ => none)))
      else
        none
   | .arrayIndex arr idx => do
      let arrVal ← eval ctx arr
      let idxVal ← eval ctx idx
      match arrVal, idxVal with
      | .lit (.array_ elems), .lit (.int n) =>
        if n ≥ 0 && n < elems.length then
          some (.lit (elems.getD n.toNat .unit))
        else none
      | _, _ => none
   | .refCreate e _cap _ => do
      let _ ← eval ctx e
      some (.lit (.loc 0))  -- placeholder; real semantics uses Store
   | .refLoad e => do
      let _ ← eval ctx e
      some (.lit .unit)  -- placeholder
   | .refStore e v _ => do
      let _ ← eval ctx e
      let _ ← eval ctx v
      some (.lit .unit)  -- placeholder
   | .refFree e => do
      let _ ← eval ctx e
      some (.lit .unit)  -- placeholder
   | .refCast e _ => do
      let _ ← eval ctx e
      some (.lit .unit)  -- placeholder
  where
  evalBlock (ctx : Context) : List Expr → Option Expr
    | [] => some (.lit .unit)
    | [e] => eval ctx e
    | e :: rest => do
      let _ ← eval ctx e
      evalBlock ctx rest

  loop (ctx : Context) (n m : Int) (body : List Expr) : Option Expr :=
    if n >= m then some (.lit .unit)
    else do
      let _ ← evalBlock (ctx.pushBv (.lit (.int n))) body
      loop ctx (n + 1) m body

  evalMatch (ctx : Context) (sv : Expr) : List (List String × Expr) → Option Expr
    | [] => none
    | (vars, body) :: _ =>
      let ctx' := ctx.pushBvs (List.replicate vars.length sv)
      eval ctx' body

/-- Evaluate an expression in the empty context. -/
def run (e : Expr) : Option Expr :=
  eval Context.empty e

end Morph.Executable
