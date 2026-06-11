/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Store

namespace Morph.Semantics

open Morph.Core
open Morph.Syntax

/-!
# Small-Step Operational Semantics (de Bruijn)

Defines the `Step : Store → Expr → Store → Expr → Prop` relation and the `IsValue : Expr → Prop` predicate
for the Morph surface syntax with de Bruijn indices.

This semantics is call-by-value: arguments are evaluated before function application.
The store is threaded through all rules (unchanged in Phase 1a).
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

inductive Step : Store → Expr → Store → Expr → Prop where
  /- ## Binary Operations -/

  | binop_left : ∀ σ op e1 e1' e2,
      Step σ e1 σ e1' →
      Step σ (.binop op e1 e2) σ (.binop op e1' e2)

  | binop_right : ∀ σ op v1 e2 e2',
      IsValue (.lit v1) → Step σ e2 σ e2' →
      Step σ (.binop op (.lit v1) e2) σ (.binop op (.lit v1) e2')

  | binop_arith : ∀ σ op n1 n2 r,
      isArithOp op →
      evalArithOp op n1 n2 = some r →
      Step σ (.binop op (.lit (.int n1)) (.lit (.int n2))) σ (.lit (.int r))

  | binop_comp : ∀ σ op n1 n2,
      isCompOp op →
      Step σ (.binop op (.lit (.int n1)) (.lit (.int n2)))
        σ (.lit (.bool (evalCompOp op n1 n2)))

  | binop_logic : ∀ σ op b1 b2 r,
      isLogicOp op → evalLogicOp op b1 b2 = some r →
      Step σ (.binop op (.lit (.bool b1)) (.lit (.bool b2))) σ (.lit (.bool r))

  | binop_bitwise : ∀ σ op n1 n2 r,
      isBitwiseOp op →
      evalBitwiseOp op n1 n2 = some r →
      Step σ (.binop op (.lit (.int n1)) (.lit (.int n2))) σ (.lit (.int r))

  | binop_ptr_arith : ∀ σ op p n r,
      isPtrArithOp op →
      evalPtrArithOp op p n = some r →
      Step σ (.binop op (.lit (.pointer p)) (.lit (.int n))) σ (.lit (.pointer r))

  | binop_ptr_load : ∀ σ p,
      Step σ (.binop .ptrLoad (.lit (.pointer p)) (.lit (.unit))) σ (.lit (.unit))

  | binop_ptr_store : ∀ σ p v,
      Step σ (.binop .ptrStore (.lit (.pointer p)) (.lit v)) σ (.lit .unit)

  /- ## Unary Operations -/

  | unop_step : ∀ σ op e e',
      Step σ e σ e' → Step σ (.unop op e) σ (.unop op e')

  | unop_not : ∀ σ b,
      Step σ (.unop .not (.lit (.bool b))) σ (.lit (.bool (!b)))

  | unop_notb : ∀ σ n,
      Step σ (.unop .notb (.lit (.int n))) σ (.lit (.int (-n - 1)))

  /- ## Conditionals -/

  | if_cond : ∀ σ c c' t f,
      Step σ c σ c' → Step σ (.ifThenElse c t f) σ (.ifThenElse c' t f)

  | if_true : ∀ σ t f,
      Step σ (.ifThenElse (.lit (.bool true)) t f) σ t

  | if_false : ∀ σ t f,
      Step σ (.ifThenElse (.lit (.bool false)) t f) σ f

  /- ## Let Binding

  `let_` binds the initializer's value at de Bruijn index 0 in the body.
  No binder name is needed — substitution is capture-avoiding by construction.
  -/

  | let_step : ∀ σ e1 e1' e2,
      Step σ e1 σ e1' → Step σ (.let_ e1 e2) σ (.let_ e1' e2)

  | let_subst : ∀ σ e1 e2,
      IsValue e1 →
      Step σ (.let_ e1 e2) σ (subst e2 e1)

  /- ## For Loops

  `forLoop` binds the iterator at de Bruijn index 0 in the body.
  No binder name is needed.
  -/

  | for_start : ∀ σ s s' e body,
      Step σ s σ s' → Step σ (.forLoop s e body) σ (.forLoop s' e body)

  | for_end : ∀ σ s e e' body,
      IsValue (.lit s) → Step σ e σ e' →
      Step σ (.forLoop (.lit s) e body) σ (.forLoop (.lit s) e' body)

  /- When executing one iteration of a for-loop, the body appears twice:
     1. In the first copy (under `let_`), the iterator is at index 0 — same context
        as the original forLoop, so no lift needed.
     2. In the recursive forLoop, the body is under BOTH `let_` (adds .intType)
        AND the inner forLoop (adds another .intType). So the body needs `lift 1`
        to shift outer-variable references past the let-binding layer. -/
  | for_exec : ∀ σ n m body,
      n < m →
      Step σ (.forLoop (.lit (.int n)) (.lit (.int m)) body)
        σ (.let_ (.lit (.int n))
          (.block (body ++ [.forLoop (.lit (.int (n + 1))) (.lit (.int m)) (body.map (lift 1))])))

  | for_done : ∀ σ n m body,
      n ≥ m →
      Step σ (.forLoop (.lit (.int n)) (.lit (.int m)) body) σ (.lit .unit)

  /- ## Blocks -/

  | block_head : ∀ σ e e' rest,
      Step σ e σ e' → Step σ (.block (e :: rest)) σ (.block (e' :: rest))

  | block_singleton : ∀ σ v,
      IsValue (.lit v) → Step σ (.block [.lit v]) σ (.lit v)

  | block_lam_singleton : ∀ σ n body,
      Step σ (.block [.lam n body]) σ (.lam n body)

  | block_none_singleton : ∀ σ,
      Step σ (.block [.none_]) σ .none_

  | block_err_singleton : ∀ σ e,
      IsValue e → Step σ (.block [.err_ e]) σ (.err_ e)

  | block_ok_singleton : ∀ σ e,
      IsValue e → Step σ (.block [.ok_ e]) σ (.ok_ e)

  | block_some_singleton : ∀ σ e,
      IsValue e → Step σ (.block [.some_ e]) σ (.some_ e)

  | block_tuple_singleton : ∀ σ (elems : List Expr) (_hvs : ∀ e ∈ elems, IsValue e),
      Step σ (.block [.tuple_ elems]) σ (.tuple_ elems)

  | block_array_singleton : ∀ σ (elems : List Expr) (_hvs : ∀ e ∈ elems, IsValue e),
      Step σ (.block [.arrayLit elems]) σ (.arrayLit elems)

  | block_pop : ∀ σ e head rest,
      IsValue e → Step σ (.block (e :: head :: rest)) σ (.block (head :: rest))

  | block_refCreate_singleton : ∀ σ e cap τ, IsValue e → Step σ (.block [.refCreate e cap τ]) σ (.refCreate e cap τ)
  | block_refLoad_singleton : ∀ σ e, IsValue e → Step σ (.block [.refLoad e]) σ (.refLoad e)
  | block_refStore_singleton : ∀ σ e v τ, IsValue e → IsValue v → Step σ (.block [.refStore e v τ]) σ (.refStore e v τ)
  | block_refFree_singleton : ∀ σ e, IsValue e → Step σ (.block [.refFree e]) σ (.refFree e)

  | binop_string_concat : ∀ σ s1 s2,
      Step σ (.binop .add (.lit (.string s1)) (.lit (.string s2))) σ (.lit (.string (s1 ++ s2)))

  | binop_div_zero : ∀ σ n1,
      Step σ (.binop .div (.lit (.int n1)) (.lit (.int 0))) σ (.lit (.int 0))

  | binop_mod_zero : ∀ σ n1,
      Step σ (.binop .mod (.lit (.int n1)) (.lit (.int 0))) σ (.lit (.int 0))

  /- ## Function Application

  When applying `.lam n body` to `args`:
  - `args.reverse` because bvar 0 = last parameter but args[0] = first parameter
  - `substAll body args.reverse` simultaneously substitutes all bound variables
  -/

  | app_fn : ∀ σ fn fn' args,
      Step σ fn σ fn' →
      Step σ (.app fn args) σ (.app fn' args)

  | app_arg : ∀ σ fn a a' rest,
      IsValue fn → Step σ a σ a' →
      Step σ (.app fn (a :: rest)) σ (.app fn (a' :: rest))

  | app_lam : ∀ σ n body args,
      args.length = n →
      Step σ (.app (.lam n body) args) σ (substAll args.reverse body)

  /- ## Field Access
  Step the base expression. No final reduction without struct values. -/

  | field_step : ∀ σ e e' name,
      Step σ e σ e' →
      Step σ (.field_ e name) σ (.field_ e' name)

  /- ## Pipeline (e |> f) -/

  | pipe_left : ∀ σ e e' f,
      Step σ e σ e' →
      Step σ (.pipe e f) σ (.pipe e' f)

  | pipe_right : ∀ σ v f f',
      IsValue v → Step σ f σ f' →
      Step σ (.pipe v f) σ (.pipe v f')

  | pipe_done : ∀ σ v f,
      IsValue v →
      Step σ (.pipe v f) σ (.app f [v])

  /- ## Type Ascription (e : τ) -/

  | typeAsc_step : ∀ σ e e' τ,
      Step σ e σ e' →
      Step σ (.typeAsc e τ) σ (.typeAsc e' τ)

  | typeAsc_done : ∀ σ v τ,
      IsValue v →
      Step σ (.typeAsc v τ) σ v

  /- ## Option Constructors -/

  | some_step : ∀ σ e e',
      Step σ e σ e' →
      Step σ (.some_ e) σ (.some_ e')

  | some_done : ∀ σ v,
      Step σ (.some_ (.lit v)) σ (.lit (.some v))

  | some_none_done : ∀ σ,
      Step σ (.some_ .none_) σ (.lit (.some Value.none))

  | none_step : ∀ σ,
      Step σ .none_ σ (.lit Value.none)

  /- ## Result Constructors -/

  | ok_step : ∀ σ e e',
      Step σ e σ e' →
      Step σ (.ok_ e) σ (.ok_ e')

  | ok_done : ∀ σ v,
      Step σ (.ok_ (.lit v)) σ (.lit (.ok v))

  | ok_none_done : ∀ σ,
      Step σ (.ok_ .none_) σ (.lit (.ok Value.none))

  | err_step : ∀ σ e e',
      Step σ e σ e' →
      Step σ (.err_ e) σ (.err_ e')

  | err_done : ∀ σ v,
      Step σ (.err_ (.lit v)) σ (.lit (.err v))

  | err_none_done : ∀ σ,
      Step σ (.err_ .none_) σ (.lit (.err Value.none))

  /- ## Match -/

  | match_scrut_step : ∀ σ scrut scrut' arms,
      Step σ scrut σ scrut' →
      Step σ (.match_ scrut arms) σ (.match_ scrut' arms)

  | match_arm : ∀ σ e vars body rest,
      IsValue e →
      Step σ (.match_ e ((vars, body) :: rest))
        σ (substAll (List.replicate vars.length e) body)

  | match_empty : ∀ σ e,
      IsValue e →
      Step σ (.match_ e []) σ (.lit .unit)

  /- ## Null Coalesce (e1 ?? e2) -/

  | null_coalesce_step_e1 : ∀ σ e1 e1' e2,
      Step σ e1 σ e1' →
      Step σ (.nullCoalesce e1 e2) σ (.nullCoalesce e1' e2)

  | null_coalesce_some : ∀ σ v e2,
      Step σ (.nullCoalesce (.some_ v) e2) σ (.some_ v)

  | null_coalesce_none : ∀ σ e2,
      Step σ (.nullCoalesce .none_ e2) σ e2

  | null_coalesce_lit_some : ∀ σ v e2,
      Step σ (.nullCoalesce (.lit (.some v)) e2) σ (.lit (.some v))

  | null_coalesce_lit_none : ∀ σ e2,
      Step σ (.nullCoalesce (.lit .none) e2) σ e2

  /- ## Tuple

  Tuples step by evaluating their elements left-to-right.
  `tuple_step_head` steps the first element.
  `tuple_step_rest` skips the first value element and steps the rest. -/

  | tuple_step_head : ∀ σ head head' rest,
      Step σ head σ head' →
      Step σ (.tuple_ (head :: rest)) σ (.tuple_ (head' :: rest))

  | tuple_step_rest : ∀ σ head rest rest',
      IsValue head →
      Step σ (.tuple_ rest) σ (.tuple_ rest') →
      Step σ (.tuple_ (head :: rest)) σ (.tuple_ (head :: rest'))

  /- ## Array

  Array literals step by evaluating their elements left-to-right (same as tuples).
  Array index steps the array expression first, then the index expression,
  then performs the bounds-checked lookup on the resulting value. -/

  | array_step_head : ∀ σ head head' rest,
      Step σ head σ head' →
      Step σ (.arrayLit (head :: rest)) σ (.arrayLit (head' :: rest))

  | array_step_rest : ∀ σ head rest rest',
      IsValue head →
      Step σ (.arrayLit rest) σ (.arrayLit rest') →
      Step σ (.arrayLit (head :: rest)) σ (.arrayLit (head :: rest'))

  | array_index_array : ∀ σ arr arr' idx,
      Step σ arr σ arr' →
      Step σ (.arrayIndex arr idx) σ (.arrayIndex arr' idx)

  | array_index_idx : ∀ σ arr idx idx',
      IsValue arr →
      Step σ idx σ idx' →
      Step σ (.arrayIndex arr idx) σ (.arrayIndex arr idx')

  | array_index_hit : ∀ σ (elems : List Expr) (hvs : ∀ e ∈ elems, IsValue e) (n : Nat),
      n < elems.length →
      Step σ (.arrayIndex (.arrayLit elems) (.lit (.int n)))
           σ (elems.getD n (.lit .unit))

  | array_index_oob : ∀ σ (elems : List Expr) (hvs : ∀ e ∈ elems, IsValue e) (n : Nat),
      elems.length > 0 →
      n ≥ elems.length →
      Step σ (.arrayIndex (.arrayLit elems) (.lit (.int n)))
           σ (elems.getD 0 (.lit .unit))

  | array_index_neg : ∀ σ (elems : List Expr) (hvs : ∀ e ∈ elems, IsValue e) (n : Nat),
      elems.length > 0 →
      Step σ (.arrayIndex (.arrayLit elems) (.lit (.int (Int.negSucc n))))
           σ (elems.getD 0 (.lit .unit))

  /- ## Reference Operations (Store Model, ADR-010)

  Reference operations step through their sub-expressions.
  The "done" rules (allocating, loading, storing, freeing) are deferred
  to the store-carrying Step migration (ADR-010 Phase 2).
  Without a store, these expressions get stuck at fully-evaluated form. -/

  | ref_create_step : ∀ σ e e' cap τ,
      Step σ e σ e' →
      Step σ (.refCreate e cap τ) σ (.refCreate e' cap τ)

  | ref_load_step : ∀ σ e e',
      Step σ e σ e' →
      Step σ (.refLoad e) σ (.refLoad e')

  | ref_store_step_arr : ∀ σ e e' v τ,
      Step σ e σ e' →
      Step σ (.refStore e v τ) σ (.refStore e' v τ)

  | ref_store_step_val : ∀ σ e e' v τ,
      IsValue e →
      Step σ v σ e' →
      Step σ (.refStore e v τ) σ (.refStore e e' τ)

  | ref_free_step : ∀ σ e e',
      Step σ e σ e' →
      Step σ (.refFree e) σ (.refFree e')

  /- ## Reference Operations — Evaluation on Fully-Evaluated Arguments (Storeless)

  When sub-expressions are fully evaluated, reference operations can proceed
  without a store by directly reducing. These rules replace the previous design
  where refLoad/refStore/refFree were considered "stuck values." -/

  | ref_load_eval : ∀ σ e cap τ,
      IsValue e →
      Step σ (.refLoad (.refCreate e cap τ)) σ e

  | ref_store_eval : ∀ σ e v cap τ,
      IsValue e → IsValue v → cap ≠ .val →
      Step σ (.refStore (.refCreate e cap τ) v τ) σ (.lit .unit)

  | ref_free_eval : ∀ σ e τ,
      IsValue e →
      Step σ (.refFree (.refCreate e .iso τ)) σ (.lit .unit)

end Morph.Semantics
