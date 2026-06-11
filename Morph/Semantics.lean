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

mutual

inductive IsValue : Expr → Prop where
  | lit : ∀ v, IsValue (.lit v)
  | lam : ∀ n body, IsValue (.lam n body)
  | none_ : IsValue .none_
  | err_ : ∀ e, IsValue e → IsValue (.err_ e)
  | ok_ : ∀ e, IsValue e → IsValue (.ok_ e)
  | some_ : ∀ e, IsValue e → IsValue (.some_ e)
  | tuple_ : ∀ (elems : List Expr) (_hvs : ∀ e ∈ elems, IsValue e), IsValue (.tuple_ elems)
  | array_ : ∀ (elems : List Expr) (_hvs : ∀ e ∈ elems, IsValue e), IsValue (.arrayLit elems)
  | refCreate : ∀ e cap τ, IsValue e → IsValue (.refCreate e cap τ)

end

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

def isPtrArithOp (op : Operator) : Prop :=
  match op with
  | .ptrAdd | .ptrSub => True
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

def evalPtrArithOp : Operator → Pointer → Int → Option Pointer
  | .ptrAdd, p, n => some { p with offset := p.offset + n }
  | .ptrSub, p, n => some { p with offset := p.offset - n }
  | _,        _, _ => none

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

  | binop_ptr_arith : ∀ op p n r,
      isPtrArithOp op →
      evalPtrArithOp op p n = some r →
      Step (.binop op (.lit (.pointer p)) (.lit (.int n))) (.lit (.pointer r))

  | binop_ptr_load : ∀ p,
      Step (.binop .ptrLoad (.lit (.pointer p)) (.lit (.unit))) (.lit (.unit))

  | binop_ptr_store : ∀ p v,
      Step (.binop .ptrStore (.lit (.pointer p)) (.lit v)) (.lit .unit)

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

  /- When executing one iteration of a for-loop, the body appears twice:
     1. In the first copy (under `let_`), the iterator is at index 0 — same context
        as the original forLoop, so no lift needed.
     2. In the recursive forLoop, the body is under BOTH `let_` (adds .intType)
        AND the inner forLoop (adds another .intType). So the body needs `lift 1`
        to shift outer-variable references past the let-binding layer. -/
  | for_exec : ∀ n m body,
      n < m →
      Step (.forLoop (.lit (.int n)) (.lit (.int m)) body)
        (.let_ (.lit (.int n))
          (.block (body ++ [.forLoop (.lit (.int (n + 1))) (.lit (.int m)) (body.map (lift 1))])))

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

  | block_none_singleton :
      Step (.block [.none_]) .none_

  | block_err_singleton : ∀ e,
      IsValue e → Step (.block [.err_ e]) (.err_ e)

  | block_ok_singleton : ∀ e,
      IsValue e → Step (.block [.ok_ e]) (.ok_ e)

  | block_some_singleton : ∀ e,
      IsValue e → Step (.block [.some_ e]) (.some_ e)

  | block_tuple_singleton : ∀ (elems : List Expr) (_hvs : ∀ e ∈ elems, IsValue e),
      Step (.block [.tuple_ elems]) (.tuple_ elems)

  | block_array_singleton : ∀ (elems : List Expr) (_hvs : ∀ e ∈ elems, IsValue e),
      Step (.block [.arrayLit elems]) (.arrayLit elems)

  | block_pop : ∀ e head rest,
      IsValue e → Step (.block (e :: head :: rest)) (.block (head :: rest))

  | block_refCreate_singleton : ∀ e cap τ, IsValue e → Step (.block [.refCreate e cap τ]) (.refCreate e cap τ)
  | block_refLoad_singleton : ∀ e, IsValue e → Step (.block [.refLoad e]) (.refLoad e)
  | block_refStore_singleton : ∀ e v τ, IsValue e → IsValue v → Step (.block [.refStore e v τ]) (.refStore e v τ)
  | block_refFree_singleton : ∀ e, IsValue e → Step (.block [.refFree e]) (.refFree e)

  | binop_string_concat : ∀ s1 s2,
      Step (.binop .add (.lit (.string s1)) (.lit (.string s2))) (.lit (.string (s1 ++ s2)))

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

  /- ## Field Access
  Step the base expression. No final reduction without struct values. -/

  | field_step : ∀ e e' name,
      Step e e' →
      Step (.field_ e name) (.field_ e' name)

  /- ## Pipeline (e |> f) -/

  | pipe_left : ∀ e e' f,
      Step e e' →
      Step (.pipe e f) (.pipe e' f)

  | pipe_right : ∀ v f f',
      IsValue v → Step f f' →
      Step (.pipe v f) (.pipe v f')

  | pipe_done : ∀ v f,
      IsValue v →
      Step (.pipe v f) (.app f [v])

  /- ## Type Ascription (e : τ) -/

  | typeAsc_step : ∀ e e' τ,
      Step e e' →
      Step (.typeAsc e τ) (.typeAsc e' τ)

  | typeAsc_done : ∀ v τ,
      IsValue v →
      Step (.typeAsc v τ) v

  /- ## Option Constructors -/

  | some_step : ∀ e e',
      Step e e' →
      Step (.some_ e) (.some_ e')

  | some_done : ∀ v,
      Step (.some_ (.lit v)) (.lit (.some v))

  | some_none_done :
      Step (.some_ .none_) (.lit (.some Value.none))

  | none_step :
      Step .none_ (.lit Value.none)

  /- ## Result Constructors -/

  | ok_step : ∀ e e',
      Step e e' →
      Step (.ok_ e) (.ok_ e')

  | ok_done : ∀ v,
      Step (.ok_ (.lit v)) (.lit (.ok v))

  | ok_none_done :
      Step (.ok_ .none_) (.lit (.ok Value.none))

  | err_step : ∀ e e',
      Step e e' →
      Step (.err_ e) (.err_ e')

  | err_done : ∀ v,
      Step (.err_ (.lit v)) (.lit (.err v))

  | err_none_done :
      Step (.err_ .none_) (.lit (.err Value.none))

  /- ## Match -/

  | match_scrut_step : ∀ scrut scrut' arms,
      Step scrut scrut' →
      Step (.match_ scrut arms) (.match_ scrut' arms)

  | match_arm : ∀ e vars body rest,
      IsValue e →
      Step (.match_ e ((vars, body) :: rest))
        (substAll (List.replicate vars.length e) body)

  | match_empty : ∀ e,
      IsValue e →
      Step (.match_ e []) (.lit .unit)

  /- ## Null Coalesce (e1 ?? e2) -/

  | null_coalesce_step_e1 : ∀ e1 e1' e2,
      Step e1 e1' →
      Step (.nullCoalesce e1 e2) (.nullCoalesce e1' e2)

  | null_coalesce_some : ∀ v e2,
      Step (.nullCoalesce (.some_ v) e2) (.some_ v)

  | null_coalesce_none : ∀ e2,
      Step (.nullCoalesce .none_ e2) e2

  | null_coalesce_lit_some : ∀ v e2,
      Step (.nullCoalesce (.lit (.some v)) e2) (.lit (.some v))

  | null_coalesce_lit_none : ∀ e2,
      Step (.nullCoalesce (.lit .none) e2) e2

  /- ## Tuple

  Tuples step by evaluating their elements left-to-right.
  `tuple_step_head` steps the first element.
  `tuple_step_rest` skips the first value element and steps the rest. -/

  | tuple_step_head : ∀ head head' rest,
      Step head head' →
      Step (.tuple_ (head :: rest)) (.tuple_ (head' :: rest))

  | tuple_step_rest : ∀ head rest rest',
      IsValue head →
      Step (.tuple_ rest) (.tuple_ rest') →
      Step (.tuple_ (head :: rest)) (.tuple_ (head :: rest'))

  /- ## Array

  Array literals step by evaluating their elements left-to-right (same as tuples).
  Array index steps the array expression first, then the index expression,
  then performs the bounds-checked lookup on the resulting value. -/

  | array_step_head : ∀ head head' rest,
      Step head head' →
      Step (.arrayLit (head :: rest)) (.arrayLit (head' :: rest))

  | array_step_rest : ∀ head rest rest',
      IsValue head →
      Step (.arrayLit rest) (.arrayLit rest') →
      Step (.arrayLit (head :: rest)) (.arrayLit (head :: rest'))

  | array_index_array : ∀ arr arr' idx,
      Step arr arr' →
      Step (.arrayIndex arr idx) (.arrayIndex arr' idx)

  | array_index_idx : ∀ arr idx idx',
      IsValue arr →
      Step idx idx' →
      Step (.arrayIndex arr idx) (.arrayIndex arr idx')

  | array_index_hit : ∀ (elems : List Expr) (hvs : ∀ e ∈ elems, IsValue e) (n : Nat),
      n < elems.length →
      Step (.arrayIndex (.arrayLit elems) (.lit (.int n)))
           (elems.getD n (.lit .unit))

  | array_index_oob : ∀ (elems : List Expr) (hvs : ∀ e ∈ elems, IsValue e) (n : Nat),
      elems.length > 0 →
      n ≥ elems.length →
      Step (.arrayIndex (.arrayLit elems) (.lit (.int n)))
           (elems.getD 0 (.lit .unit))

  | array_index_neg : ∀ (elems : List Expr) (hvs : ∀ e ∈ elems, IsValue e) (n : Nat),
      elems.length > 0 →
      Step (.arrayIndex (.arrayLit elems) (.lit (.int (Int.negSucc n))))
           (elems.getD 0 (.lit .unit))

  /- ## Reference Operations (Store Model, ADR-010)

  Reference operations step through their sub-expressions.
  The "done" rules (allocating, loading, storing, freeing) are deferred
  to the store-carrying Step migration (ADR-010 Phase 2).
  Without a store, these expressions get stuck at fully-evaluated form. -/

  | ref_create_step : ∀ e e' cap τ,
      Step e e' →
      Step (.refCreate e cap τ) (.refCreate e' cap τ)

  | ref_load_step : ∀ e e',
      Step e e' →
      Step (.refLoad e) (.refLoad e')

  | ref_store_step_arr : ∀ e e' v τ,
      Step e e' →
      Step (.refStore e v τ) (.refStore e' v τ)

  | ref_store_step_val : ∀ e e' v τ,
      IsValue e →
      Step v e' →
      Step (.refStore e v τ) (.refStore e e' τ)

  | ref_free_step : ∀ e e',
      Step e e' →
      Step (.refFree e) (.refFree e')

  /- ## Reference Operations — Evaluation on Fully-Evaluated Arguments (Storeless)

  When sub-expressions are fully evaluated, reference operations can proceed
  without a store by directly reducing. These rules replace the previous design
  where refLoad/refStore/refFree were considered "stuck values." -/

  | ref_load_eval : ∀ e cap τ,
      IsValue e →
      Step (.refLoad (.refCreate e cap τ)) e

  | ref_store_eval : ∀ e v cap τ,
      IsValue e → IsValue v → cap ≠ .val →
      Step (.refStore (.refCreate e cap τ) v τ) (.lit .unit)

  | ref_free_eval : ∀ e τ,
      IsValue e →
      Step (.refFree (.refCreate e .iso τ)) (.lit .unit)

end Morph.Semantics
