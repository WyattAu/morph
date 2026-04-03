/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Morph.Specs.TypeSystem

namespace Morph.Proofs.TypeSoundness

open Morph.Core
open Morph.Syntax
open Morph.Semantics
open Step
open Morph.Specs.TypeSystem
open HasType

private theorem HasTypeAll_cons_head {Gamma : TypEnv} {e : Expr} {es : List Expr}
    {tau : Typ} {taus : List Typ} (h : HasTypeAll Gamma (e :: es) (tau :: taus)) : HasType Gamma e tau := by
  cases h with | cons _ _ _ _ _ hE _ => exact hE

private theorem HasTypeAll_cons_tail {Gamma : TypEnv} {e : Expr} {es : List Expr}
    {tau : Typ} {taus : List Typ} (h : HasTypeAll Gamma (e :: es) (tau :: taus)) : HasTypeAll Gamma es taus := by
  cases h with | cons _ _ _ _ _ _ hRest => exact hRest

private theorem HasTypeAll_nil_types {Gamma : TypEnv} {taus : List Typ} :
    HasTypeAll Gamma [] taus -> taus = [] := by
  intro h; cases h with | nil _ => rfl

private theorem append_singleton_ne_nil (taus : List Typ) (tau : Typ) : taus ++ [tau] <> [] := by
  intro h
  cases taus with
  | nil => exact List.noConfusion h
  | cons _ _ => exact List.noConfusion h

private theorem HasTypeAll_length (Gamma : TypEnv) (es : List Expr) (taus : List Typ) :
    HasTypeAll Gamma es taus -> es.length = taus.length := by
  intro h; cases h with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => sorry

private theorem sem_isArithOp_not_spec_isCompOp (op : Operator) :
    Morph.Semantics.isArithOp op -> ¬ (Morph.Specs.TypeSystem.isCompOp op) := by
  intro ha hc
  cases op <;> simp [Morph.Semantics.isArithOp, Morph.Specs.TypeSystem.isCompOp] at * <;> contradiction

private theorem sem_isCompOp_not_spec_isArithOp (op : Operator) :
    Morph.Semantics.isCompOp op -> ¬ (Morph.Specs.TypeSystem.isArithOp op) := by
  intro hc ha
  cases op <;> simp [Morph.Semantics.isCompOp, Morph.Specs.TypeSystem.isArithOp] at * <;> contradiction

private theorem sem_isBitwiseOp_not_spec_isCompOp (op : Operator) :
    Morph.Semantics.isBitwiseOp op -> ¬ (Morph.Specs.TypeSystem.isCompOp op) := by
  intro hb hc
  cases op <;> simp [Morph.Semantics.isBitwiseOp, Morph.Specs.TypeSystem.isCompOp] at * <;> contradiction

private theorem sem_isCompOp_not_spec_isBitwiseOp (op : Operator) :
    Morph.Semantics.isCompOp op -> ¬ (Morph.Specs.TypeSystem.isBitwiseOp op) := by
  intro hc hb
  cases op <;> simp [Morph.Semantics.isCompOp, Morph.Specs.TypeSystem.isBitwiseOp] at * <;> contradiction

private theorem lookupTyp_extend_eq (Gamma : TypEnv) (x : String) (tau : Typ) :
    lookupTyp (extendTypEnv Gamma x tau) x = some tau := by
  unfold extendTypEnv lookupTyp
  simp only [List.find?_cons, List.map, Prod.fst, Prod.snd]
  split <;> simp_all

private theorem lookupTyp_extend_ne (Gamma : TypEnv) (x y : String) (tau : Typ) (hNe : x != y) :
    lookupTyp (extendTypEnv Gamma x tau) y = lookupTyp Gamma y := by
  unfold extendTypEnv lookupTyp
  simp only [List.find?_cons, List.map, Prod.fst, Prod.snd]
  split
  · next h => exact absurd hNe sorry
  · next _ _ => rfl

private theorem subst_preserves_type (Gamma : TypEnv) (e : Expr) (x : String) (v : Expr) (tau1 tau : Typ)
    (hE : HasType (extendTypEnv Gamma x tau1) e tau)
    (hV : HasType Gamma v tau1) : HasType Gamma (subst e x v) tau := by
  induction hE with
  | var_type _ id' tau' hLookup =>
    exact if h : id'.name == x then
      have : tau' = tau1 := by
        have := lookupTyp_extend_eq Gamma x tau1
        have : id'.name = x := sorry
        rw [this] at hLookup
        injection (this.trans hLookup) with heq
        exact heq
        hV
    else
      have := lookupTyp_extend_ne Gamma x id'.name tau1 (fun h => hNe (show id'.name <> x from sorry))
      have hLookup2 : lookupTyp Gamma id'.name = some tau' := this.symm.trans hLookup
      HasType.var_type Gamma id' tau' hLookup2
  | lit_int _ n => HasType.lit_int Gamma n
  | lit_bool _ b => HasType.lit_bool Gamma b
  | lit_string _ s => HasType.lit_string Gamma s
  | lit_unit => HasType.lit_unit Gamma
  | lit_pointer _ p => HasType.lit_pointer Gamma p
  | unop_not _ e' hE' =>
    HasType.unop_not Gamma (subst e' x v) (subst_preserves_type e' x v tau1 Typ.boolType hE' hV)
  | unop_notb _ e' hE' =>
    HasType.unop_notb Gamma (subst e' x v) (subst_preserves_type e' x v tau1 Typ.intType hE' hV)
  | binop_arith _ op e1 e2 hArith hE1 hE2 =>
    HasType.binop_arith Gamma op (subst e1 x v) (subst e2 x v) hArith
      (subst_preserves_type e1 x v tau1 Typ.intType hE1 hV)
      (subst_preserves_type e2 x v tau1 Typ.intType hE2 hV)
  | binop_comp _ op e1 e2 hComp hE1 hE2 =>
    HasType.binop_comp Gamma op (subst e1 x v) (subst e2 x v) hComp
      (subst_preserves_type e1 x v tau1 Typ.intType hE1 hV)
      (subst_preserves_type e2 x v tau1 Typ.intType hE2 hV)
  | binop_logic _ op e1 e2 hLogic hE1 hE2 =>
    HasType.binop_logic Gamma op (subst e1 x v) (subst e2 x v) hLogic
      (subst_preserves_type e1 x v tau1 Typ.boolType hE1 hV)
      (subst_preserves_type e2 x v tau1 Typ.boolType hE2 hV)
  | binop_bitwise _ op e1 e2 hBit hE1 hE2 =>
    HasType.binop_bitwise Gamma op (subst e1 x v) (subst e2 x v) hBit
      (subst_preserves_type e1 x v tau1 Typ.intType hE1 hV)
      (subst_preserves_type e2 x v tau1 Typ.intType hE2 hV)
  | lam_type _ y body tau1' tau2 hBody => sorry
  | app_type _ fn args taus_ret tau_ret hLookup hArgs =>
    have hLookup' : lookupTyp Gamma fn.name = some (Typ.functionType taus_ret tau_ret) := by
      have hNe : fn.name <> x := by
        intro hEq
        have := lookupTyp_extend_eq (extendTypEnv Gamma x tau1) x tau1
        rw [hEq] at this
        rw [hEq] at hLookup
        exact absurd (this.trans hLookup) (fun _ => rfl)
      exact (lookupTyp_extend_ne Gamma x fn.name tau1 hNe).symm.trans hLookup
    HasType.app_type Gamma fn (args.map (fun a => subst a x v)) taus_ret tau_ret hLookup' sorry
  | let_type _ id' e1' e2' tau_a tau_b hE1' hE2' =>
    HasType.let_type Gamma id' (subst e1' x v)
      (if id'.name == x then e2' else subst e2' x v) tau_a tau_b
      (subst_preserves_type e1' x v tau1 tau_a hE1' hV) sorry
  | if_type _ c t f tau' hC hT hF =>
    HasType.if_type Gamma (subst c x v) (subst t x v) (subst f x v) tau'
      (subst_preserves_type c x v tau1 Typ.boolType hC hV)
      (subst_preserves_type t x v tau1 tau' hT hV)
      (subst_preserves_type f x v tau1 tau' hF hV)
  | for_type _ id' s e' body hS hE' hBody => sorry
  | block_type _ exprs taus_b tau_b hAll =>
    HasType.block_type Gamma (exprs.map (fun a => subst a x v)) taus_b tau_b sorry
  | nil => exfalso; exact absurd hE sorry
  | cons _ _ _ _ _ _ _ => exfalso; exact absurd hE sorry

theorem preservation : forall {e e' : Expr} {tau : Typ} {Gamma : TypEnv},
    HasType Gamma e tau -> Step e e' -> HasType Gamma e' tau := by
  intro e e' tau Gamma hType hStep
  cases hStep with
  | binop_left op e1 e1' e2 hStep1 =>
    cases hType with
    | binop_arith _ _ _ _ hArith hE1 hE2 =>
      exact HasType.binop_arith Gamma op e1' e2 hArith (preservation hE1 hStep1) hE2
    | binop_comp _ _ _ _ hComp hE1 hE2 =>
      exact HasType.binop_comp Gamma op e1' e2 hComp (preservation hE1 hStep1) hE2
    | binop_logic _ _ _ _ hLogic hE1 hE2 =>
      exact HasType.binop_logic Gamma op e1' e2 hLogic (preservation hE1 hStep1) hE2
    | binop_bitwise _ _ _ _ hBit hE1 hE2 =>
      exact HasType.binop_bitwise Gamma op e1' e2 hBit (preservation hE1 hStep1) hE2
    | _ => contradiction
  | binop_right op v1 e2 e2' _ hStep2 =>
    cases hType with
    | binop_arith _ _ _ _ hArith hE1 hE2 =>
      exact HasType.binop_arith Gamma op (.lit v1) e2' hArith hE1 (preservation hE2 hStep2)
    | binop_comp _ _ _ _ hComp hE1 hE2 =>
      exact HasType.binop_comp Gamma op (.lit v1) e2' hComp hE1 (preservation hE2 hStep2)
    | binop_logic _ _ _ _ hLogic hE1 hE2 =>
      exact HasType.binop_logic Gamma op (.lit v1) e2' hLogic hE1 (preservation hE2 hStep2)
    | binop_bitwise _ _ _ _ hBit hE1 hE2 =>
      exact HasType.binop_bitwise Gamma op (.lit v1) e2' hBit hE1 (preservation hE2 hStep2)
    | _ => contradiction
  | binop_arith op n1 n2 r hArith _ =>
    cases hType with
    | binop_arith _ _ _ _ _ _ _ => exact HasType.lit_int Gamma r
    | binop_comp _ _ _ _ hComp _ _ => exfalso; exact sem_isArithOp_not_spec_isCompOp op hArith hComp
    | binop_logic _ _ _ _ _ hE1 _ => cases hE1
    | binop_bitwise _ _ _ _ _ _ _ => exact HasType.lit_int Gamma r
    | _ => contradiction
  | binop_comp op n1 n2 hComp =>
    cases hType with
    | binop_arith _ _ _ _ hArith _ _ => exfalso; exact sem_isCompOp_not_spec_isArithOp op hComp hArith
    | binop_comp _ _ _ _ _ _ _ => exact HasType.lit_bool Gamma (Morph.Semantics.evalCompOp op n1 n2)
    | binop_logic _ _ _ _ _ hE1 _ => cases hE1
    | binop_bitwise _ _ _ _ hBit _ _ => exfalso; exact sem_isCompOp_not_spec_isBitwiseOp op hComp hBit
    | _ => contradiction
  | binop_logic _ b1 b2 r _ _ =>
    cases hType with
    | binop_arith _ _ _ _ _ hE1 _ => cases hE1
    | binop_comp _ _ _ _ _ hE1 _ => cases hE1
    | binop_logic _ _ _ _ _ _ _ => exact HasType.lit_bool Gamma r
    | binop_bitwise _ _ _ _ _ hE1 _ => cases hE1
    | _ => contradiction
  | binop_bitwise op n1 n2 r hBit _ =>
    cases hType with
    | binop_arith _ _ _ _ _ _ _ => exact HasType.lit_int Gamma r
    | binop_comp _ _ _ _ hComp _ _ => exfalso; exact sem_isBitwiseOp_not_spec_isCompOp op hBit hComp
    | binop_logic _ _ _ _ _ hE1 _ => cases hE1
    | binop_bitwise _ _ _ _ _ _ _ => exact HasType.lit_int Gamma r
    | _ => contradiction
  | binop_div_zero _ =>
    cases hType with
    | binop_arith _ _ _ _ _ _ _ => exact HasType.lit_int Gamma 0
    | _ => contradiction
  | binop_mod_zero _ =>
    cases hType with
    | binop_arith _ _ _ _ _ _ _ => exact HasType.lit_int Gamma 0
    | _ => contradiction
  | unop_step op e e' hStep1 =>
    cases hType with
    | unop_not _ _ hE =>
      exact HasType.unop_not Gamma e' (preservation hE hStep1)
    | unop_notb _ _ hE =>
      exact HasType.unop_notb Gamma e' (preservation hE hStep1)
    | _ => contradiction
  | unop_not b =>
    cases hType with
    | unop_not _ _ _ => exact HasType.lit_bool Gamma (!b)
    | _ => contradiction
  | unop_notb n =>
    cases hType with
    | unop_notb _ _ _ => exact HasType.lit_int Gamma (-n - 1)
    | _ => contradiction
  | if_cond c c' t f hStep1 =>
    cases hType with
    | if_type _ _ _ _ _ hC hT hF =>
      exact HasType.if_type Gamma c' t f tau (preservation hC hStep1) hT hF
    | _ => contradiction
  | if_true _ _ =>
    cases hType with
    | if_type _ _ _ _ _ _ hT _ => exact hT
    | _ => contradiction
  | if_false _ _ =>
    cases hType with
    | if_type _ _ _ _ _ _ _ hF => exact hF
    | _ => contradiction
  | let_step id e1 e1' e2 hStep1 =>
    cases hType with
    | let_type _ _ _ _ tau1 _ hE1 hE2 =>
      exact HasType.let_type Gamma id e1' e2 tau1 tau (preservation hE1 hStep1) hE2
    | _ => contradiction
  | let_subst id e1 e2 _ =>
    cases hType with
    | let_type _ _ _ _ tau1 _ hE1 hE2 =>
      exact subst_preserves_type Gamma e2 id.name e1 tau1 tau hE2 hE1
    | _ => contradiction
  | for_start id s s' e body hStep1 =>
    cases hType with
    | for_type _ _ _ _ _ hS hE hBody =>
      exact HasType.for_type Gamma id s' e body (preservation hS hStep1) hE hBody
    | _ => contradiction
  | for_end id s e e' body _ hStep2 =>
    cases hType with
    | for_type _ _ _ _ _ hS hE hBody =>
      exact HasType.for_type Gamma id (.lit s) e' body hS (preservation hE hStep2) hBody
    | _ => contradiction
  | for_exec id n m body _ =>
    cases hType with
    | for_type _ _ _ _ _ _ _ hBody =>
      exact HasType.let_type Gamma id (.lit (.int n))
        (.block (body ++ [.forLoop id (.lit (.int (n + 1))) (.lit (.int m)) body]))
        .intType .unitType (HasType.lit_int Gamma n)
        (HasType.block_type (extendTypEnv Gamma id.name .intType)
          (body ++ [.forLoop id (.lit (.int (n + 1))) (.lit (.int m)) body])
          [.unitType] .unitType sorry)
    | _ => contradiction
  | for_done _ _ _ _ _ =>
    cases hType with
    | for_type => exact HasType.lit_unit Gamma
    | _ => contradiction
  | block_head e' e'' rest hStep1 =>
    cases hType with
    | block_type _ _ taus _ hAll =>
      cases taus with
      | nil =>
        exact HasType.block_type Gamma (e'' :: rest) [] tau
          (HasTypeAll.cons Gamma e'' rest tau [] (preservation (HasTypeAll_cons_head hAll) hStep1) (HasTypeAll_cons_tail hAll))
      | cons tau' taus' =>
        exact HasType.block_type Gamma (e'' :: rest) (tau' :: taus') tau
          (HasTypeAll.cons Gamma e'' rest tau' (taus' ++ [tau]) (preservation (HasTypeAll_cons_head hAll) hStep1) (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_singleton v _ =>
    cases hType with
    | block_type _ _ taus _ hAll =>
      cases taus with
      | nil => exact HasTypeAll_cons_head hAll
      | cons _ taus' =>
        exfalso
        exact append_singleton_ne_nil taus' tau (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_lam_singleton xs body =>
    cases hType with
    | block_type _ _ taus _ hAll =>
      cases taus with
      | nil => exact HasTypeAll_cons_head hAll
      | cons _ taus' =>
        exfalso
        exact append_singleton_ne_nil taus' tau (HasTypeAll_nil_types (HasTypeAll_cons_tail hAll))
    | _ => contradiction
  | block_pop e_val head rest _ =>
    cases hType with
    | block_type _ _ taus _ hAll =>
      cases taus with
      | nil =>
        exfalso
        have := HasTypeAll_length Gamma (e_val :: head :: rest) ([] ++ [tau]) hAll
        simp [List.length_append, List.length_cons] at this
        omega
      | cons tau' taus' =>
        exact HasType.block_type Gamma (head :: rest) taus' tau (HasTypeAll_cons_tail hAll)
    | _ => contradiction

end Morph.Proofs.TypeSoundness
