/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax

namespace Morph.Semantics

open Morph.Core
open Morph.Syntax

/-!
# Small-Step Operational Semantics

Defines the `Step : Expr → Expr → Prop` relation and the `IsValue : Expr → Prop` predicate
for the Morph surface syntax (`Morph.Syntax.Expr`).

This semantics is call-by-value: arguments are evaluated before function application.
-/

/-! ## Value Predicate -/

inductive IsValue : Expr → Prop where
  | lit : ∀ v, IsValue (.lit v)
  | lam : ∀ xs body, IsValue (.lam xs body)

/-! ## Operator Classifications -/

def isArithOp (op : Operator) : Prop :=
  match op with
  | .add | .sub | .mul | .div | .mod => True
  | _ => False

def isCompOp (op : Operator) : Prop :=
  match op with
  | .eq | .neq | .lt | .leq | .gt | .geq => True
  | _ => False

def isLogicOp (op : Operator) : Prop :=
  match op with
  | .and | .or => True
  | _ => False

def isBitwiseOp (op : Operator) : Prop :=
  match op with
  | .andb | .orb | .xorb | .shl | .shr => True
  | _ => False

/-! ## Evaluation Helpers -/

def evalArithOp : Operator → Int → Int → Option Int
  | .add, n1, n2 => some (n1 + n2)
  | .sub, n1, n2 => some (n1 - n2)
  | .mul, n1, n2 => some (n1 * n2)
  | .div, _, 0   => none
  | .div, n1, n2 => some (n1 / n2)
  | .mod, _, 0   => none
  | .mod, n1, n2 => some (n1 % n2)
  | _,    _,   _ => none

def evalCompOp : Operator → Int → Int → Bool
  | .eq,  n1, n2 => n1 == n2
  | .neq, n1, n2 => !(n1 == n2)
  | .lt,  n1, n2 => n1 < n2
  | .leq, n1, n2 => n1 <= n2
  | .gt,  n1, n2 => n1 > n2
  | .geq, n1, n2 => n1 >= n2
  | _,    _,   _ => false

def evalLogicOp : Operator → Bool → Bool → Option Bool
  | .and, b1, b2 => some (b1 && b2)
  | .or,  b1, b2 => some (b1 || b2)
  | _,    _,   _ => none

def evalBitwiseOp : Operator → Int → Int → Option Int
  | .andb, n1, n2 => some (if decide (n1 % 2 = 1) && decide (n2 % 2 = 1) then 1 else 0)
  | .orb,  n1, n2 => some (if decide (n1 % 2 = 1) || decide (n2 % 2 = 1) then 1 else 0)
  | .xorb, n1, n2 => some (if decide (n1 % 2 = 1) != decide (n2 % 2 = 1) then 1 else 0)
  | .shl,  n1, n2 => some (n1 * Int.pow 2 n2.toNat)
  | .shr,  n1, n2 => some (Int.shiftRight n1 n2.toNat)
  | _,     _,   _ => none

/-! ## Substitution -/

def subst (e : Expr) (x : String) (v : Expr) : Expr :=
  match e with
  | .var id => if id.name == x then v else .var id
  | .lit _ => e
  | .unop op e1 => .unop op (subst e1 x v)
  | .binop op e1 e2 => .binop op (subst e1 x v) (subst e2 x v)
  | .app fn args => .app (subst fn x v) (args.map (fun e => subst e x v))
  | .lam xs body =>
    if xs.any (fun id => id.name == x) then .lam xs body
    else .lam xs (subst body x v)
  | .let id e1 e2 =>
    let e1' := subst e1 x v
    if id.name == x then .let id e1' e2
    else .let id e1' (subst e2 x v)
  | .ifThenElse c t f =>
    .ifThenElse (subst c x v) (subst t x v) (subst f x v)
  | .forLoop id s e body =>
    let s' := subst s x v
    let e' := subst e x v
    if id.name == x then .forLoop id s' e' body
    else .forLoop id s' e' (body.map (fun e => subst e x v))
  | .block exprs =>
    .block (exprs.map (fun e => subst e x v))

def substList (es : List Expr) (x : String) (v : Expr) : List Expr :=
  es.map (fun e => subst e x v)

def substAll (body : Expr) (xs : List Id) (vs : List Expr) : Expr :=
  match xs, vs with
  | [], [] => body
  | x :: xs', v :: vs' => substAll (subst body x.name v) xs' vs'
  | _, _ => body

/-! ## Small-Step Relation -/

inductive Step : Expr → Expr → Prop where
  /- ## Binary Operations -/

  | binop_left : ∀ op e1 e1' e2,
      Step e1 e1' →
      Step (.binop op e1 e2) (.binop op e1' e2)

  | binop_right : ∀ op v1 e2 e2',
      IsValue (.lit v1) → Step e2 e2' →
      Step (.binop op (.lit v1) e2) (.binop op (.lit v1) e2')

  | binop_arith : ∀ op n1 n2 r,
      isArithOp op →
      evalArithOp op n1 n2 = some r →
      Step (.binop op (.lit (.int n1)) (.lit (.int n2))) (.lit (.int r))

  | binop_comp : ∀ op n1 n2,
      isCompOp op →
      Step (.binop op (.lit (.int n1)) (.lit (.int n2)))
        (.lit (.bool (evalCompOp op n1 n2)))

  | binop_logic : ∀ op b1 b2 r,
      isLogicOp op → evalLogicOp op b1 b2 = some r →
      Step (.binop op (.lit (.bool b1)) (.lit (.bool b2))) (.lit (.bool r))

  | binop_bitwise : ∀ op n1 n2 r,
      isBitwiseOp op →
      evalBitwiseOp op n1 n2 = some r →
      Step (.binop op (.lit (.int n1)) (.lit (.int n2))) (.lit (.int r))

  /- ## Unary Operations -/

  | unop_step : ∀ op e e',
      Step e e' → Step (.unop op e) (.unop op e')

  | unop_not : ∀ b,
      Step (.unop .not (.lit (.bool b))) (.lit (.bool (!b)))

  | unop_notb : ∀ n,
      Step (.unop .notb (.lit (.int n))) (.lit (.int (-n - 1)))

  /- ## Conditionals -/

  | if_cond : ∀ c c' t f,
      Step c c' → Step (.ifThenElse c t f) (.ifThenElse c' t f)

  | if_true : ∀ t f,
      Step (.ifThenElse (.lit (.bool true)) t f) t

  | if_false : ∀ t f,
      Step (.ifThenElse (.lit (.bool false)) t f) f

  /- ## Let Binding -/

  | let_step : ∀ id e1 e1' e2,
      Step e1 e1' → Step (.let id e1 e2) (.let id e1' e2)

  | let_subst : ∀ id e1 e2,
      IsValue e1 →
      Step (.let id e1 e2) (subst e2 id.name e1)

  /- ## For Loops -/

  | for_start : ∀ id s s' e body,
      Step s s' → Step (.forLoop id s e body) (.forLoop id s' e body)

  | for_end : ∀ id s e e' body,
      IsValue (.lit s) → Step e e' →
      Step (.forLoop id (.lit s) e body) (.forLoop id (.lit s) e' body)

  | for_exec : ∀ id n m body,
      n < m →
      Step (.forLoop id (.lit (.int n)) (.lit (.int m)) body)
        (.let id (.lit (.int n))
          (.block (body ++ [.forLoop id (.lit (.int (n + 1))) (.lit (.int m)) body])))

  | for_done : ∀ id n m body,
      n ≥ m →
      Step (.forLoop id (.lit (.int n)) (.lit (.int m)) body) (.lit .unit)

  /- ## Blocks -/

  | block_head : ∀ e e' rest,
      Step e e' → Step (.block (e :: rest)) (.block (e' :: rest))

  | block_singleton : ∀ v,
      IsValue (.lit v) → Step (.block [.lit v]) (.lit v)


  | block_lam_singleton : ∀ xs body,
      Step (.block [.lam xs body]) (.lam xs body)

  | block_pop : ∀ e head rest,
      IsValue e → Step (.block (e :: head :: rest)) (.block (head :: rest))

  | binop_div_zero : ∀ n1,
      Step (.binop .div (.lit (.int n1)) (.lit (.int 0))) (.lit (.int 0))

  | binop_mod_zero : ∀ n1,
      Step (.binop .mod (.lit (.int n1)) (.lit (.int 0))) (.lit (.int 0))
  /- ## Function Application -/

  | app_fn : ∀ fn fn' args,
      Step fn fn' →
      Step (.app fn args) (.app fn' args)

  | app_arg : ∀ fn a a' rest,
      IsValue fn → Step a a' →
      Step (.app fn (a :: rest)) (.app fn (a' :: rest))

  | app_lam : ∀ xs body args,
      args.length = xs.length →
      Step (.app (.lam xs body) args) (substAll body xs args)


end Morph.Semantics
