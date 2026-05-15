/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax

namespace Morph.Semantics

open Morph.Core
open Morph.Syntax

/-!
# Small-Step Operational Semantics (de Bruijn)

Defines the `Step : Expr → Expr → Prop` relation and the `IsValue : Expr → Prop` predicate
for the Morph surface syntax with de Bruijn indices.

This semantics is call-by-value: arguments are evaluated before function application.
-/

/-! ## Value Predicate -/

inductive IsValue : Expr → Prop where
  | lit : ∀ v, IsValue (.lit v)
  | lam : ∀ n body, IsValue (.lam n body)

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

  /- ## Let Binding

  `let_` binds the initializer's value at de Bruijn index 0 in the body.
  No binder name is needed — substitution is capture-avoiding by construction.
  -/

  | let_step : ∀ e1 e1' e2,
      Step e1 e1' → Step (.let_ e1 e2) (.let_ e1' e2)

  | let_subst : ∀ e1 e2,
      IsValue e1 →
      Step (.let_ e1 e2) (subst e2 e1)

  /- ## For Loops

  `forLoop` binds the iterator at de Bruijn index 0 in the body.
  No binder name is needed.
  -/

  | for_start : ∀ s s' e body,
      Step s s' → Step (.forLoop s e body) (.forLoop s' e body)

  | for_end : ∀ s e e' body,
      IsValue (.lit s) → Step e e' →
      Step (.forLoop (.lit s) e body) (.forLoop (.lit s) e' body)

  | for_exec : ∀ n m body,
      n < m →
      Step (.forLoop (.lit (.int n)) (.lit (.int m)) body)
        (.let_ (.lit (.int n))
          (.block (body ++ [.forLoop (.lit (.int (n + 1))) (.lit (.int m)) body])))

  | for_done : ∀ n m body,
      n ≥ m →
      Step (.forLoop (.lit (.int n)) (.lit (.int m)) body) (.lit .unit)

  /- ## Blocks -/

  | block_head : ∀ e e' rest,
      Step e e' → Step (.block (e :: rest)) (.block (e' :: rest))

  | block_singleton : ∀ v,
      IsValue (.lit v) → Step (.block [.lit v]) (.lit v)

  | block_lam_singleton : ∀ n body,
      Step (.block [.lam n body]) (.lam n body)

  | block_pop : ∀ e head rest,
      IsValue e → Step (.block (e :: head :: rest)) (.block (head :: rest))

  | binop_div_zero : ∀ n1,
      Step (.binop .div (.lit (.int n1)) (.lit (.int 0))) (.lit (.int 0))

  | binop_mod_zero : ∀ n1,
      Step (.binop .mod (.lit (.int n1)) (.lit (.int 0))) (.lit (.int 0))

  /- ## Function Application

  When applying `.lam n body` to `args`:
  - `args.reverse` because bvar 0 = last parameter but args[0] = first parameter
  - `substAll body args.reverse` simultaneously substitutes all bound variables
  -/

  | app_fn : ∀ fn fn' args,
      Step fn fn' →
      Step (.app fn args) (.app fn' args)

  | app_arg : ∀ fn a a' rest,
      IsValue fn → Step a a' →
      Step (.app fn (a :: rest)) (.app fn (a' :: rest))

  | app_lam : ∀ n body args,
      args.length = n →
      Step (.app (.lam n body) args) (substAll args.reverse body)


end Morph.Semantics
