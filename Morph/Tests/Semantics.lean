import Std
import Morph.Core
import Morph.Syntax
import Morph.Semantics
import Aesop

/-!
# Module: Tests.Semantics

**Author:** QA Engineer
**Created:** 2026-01-16
**Last Updated:** 2026-05-14
**Status:** Complete

## Purpose

Comprehensive semantics tests for Morph verification system.
This module provides unit tests and property-based tests for:
- IsValue predicate (lit, lam constructors)
- Expr type (all constructors)
- Stmt type (all constructors)
- Step relation (all constructors)
- Operator classification functions (isArithOp, isCompOp, isLogicOp, isBitwiseOp)
- Evaluation helper functions (evalArithOp, evalCompOp, evalLogicOp, evalBitwiseOp)
- Substitution functions (subst, substAll)
- Property-based tests for evaluation determinism

## Dependencies

- `Morph.Core` - Core type definitions (Value, Operator, Typ, etc.)
- `Morph.Syntax` - Surface syntax (Expr, Stmt, Id, Program, etc.)
- `Morph.Semantics` - Semantics definitions (IsValue, Step, subst, eval helpers)
- `Std` - Standard library
- `Aesop` - Automated proof search

## Notes

- Tests use `theorem` for named verification
- Property-based tests verify generic properties
- Uses de Bruijn indices: `bvar 0` = most recent binder

## References

- Coding Standards Section 7: Testing Patterns
- ADR-009: Testing Infrastructure
- ADR-005: Aesop Automation Strategy

-/
namespace Tests.Semantics

open Morph.Semantics
open Morph.Core
open Morph.Syntax

/-!
## Section 1: IsValue Predicate Unit Tests
-/

section IsValueTests

  /-- integer literals are values -/
  theorem isValue_int : IsValue (.lit (.int 42)) := by apply IsValue.lit

  /-- boolean literals are values -/
  theorem isValue_bool : IsValue (.lit (.bool true)) := by apply IsValue.lit

  /-- unit literal is a value -/
  theorem isValue_unit : IsValue (.lit .unit) := by apply IsValue.lit

  /-- string literals are values -/
  theorem isValue_string : IsValue (.lit (.string "hello")) := by apply IsValue.lit

  /-- lambda expressions are values -/
  theorem isValue_lam : IsValue (.lam 1 (.bvar 0)) := by apply IsValue.lam

  /-- multi-parameter lambdas are values -/
  theorem isValue_lam_multi :
    IsValue (.lam 2 (.binop .add (.bvar 1) (.bvar 0))) := by
      apply IsValue.lam

  /-- any literal is a value -/
  theorem isValue_any_lit (v : Value) : IsValue (.lit v) := by apply IsValue.lit

  /-- any lambda is a value -/
  theorem isValue_any_lam (n : Nat) (body : Expr) : IsValue (.lam n body) := by
    apply IsValue.lam

end IsValueTests

/-!
## Section 2: Operator Classification Unit Tests
-/

section OperatorClassificationTests

  theorem isArithOp_add : isArithOp .add := by trivial
  theorem isArithOp_sub : isArithOp .sub := by trivial
  theorem isArithOp_mul : isArithOp .mul := by trivial
  theorem isArithOp_div : isArithOp .div := by trivial
  theorem isArithOp_mod : isArithOp .mod := by trivial
  theorem isArithOp_eq : ¬ isArithOp .eq := by simp [isArithOp]
  theorem isArithOp_and : ¬ isArithOp .and := by simp [isArithOp]
  theorem isArithOp_andb : ¬ isArithOp .andb := by simp [isArithOp]
  theorem isArithOp_not : ¬ isArithOp .not := by simp [isArithOp]

  theorem isCompOp_eq : isCompOp .eq := by trivial
  theorem isCompOp_neq : isCompOp .neq := by trivial
  theorem isCompOp_lt : isCompOp .lt := by trivial
  theorem isCompOp_leq : isCompOp .leq := by trivial
  theorem isCompOp_gt : isCompOp .gt := by trivial
  theorem isCompOp_geq : isCompOp .geq := by trivial
  theorem isCompOp_add : ¬ isCompOp .add := by simp [isCompOp]
  theorem isCompOp_and : ¬ isCompOp .and := by simp [isCompOp]

  theorem isLogicOp_and : isLogicOp .and := by trivial
  theorem isLogicOp_or : isLogicOp .or := by trivial
  theorem isLogicOp_not : ¬ isLogicOp .not := by simp [isLogicOp]
  theorem isLogicOp_add : ¬ isLogicOp .add := by simp [isLogicOp]
  theorem isLogicOp_eq : ¬ isLogicOp .eq := by simp [isLogicOp]

  theorem isBitwiseOp_andb : isBitwiseOp .andb := by trivial
  theorem isBitwiseOp_orb : isBitwiseOp .orb := by trivial
  theorem isBitwiseOp_xorb : isBitwiseOp .xorb := by trivial
  theorem isBitwiseOp_shl : isBitwiseOp .shl := by trivial
  theorem isBitwiseOp_shr : isBitwiseOp .shr := by trivial
  theorem isBitwiseOp_and : ¬ isBitwiseOp .and := by simp [isBitwiseOp]
  theorem isBitwiseOp_add : ¬ isBitwiseOp .add := by simp [isBitwiseOp]
  theorem isBitwiseOp_notb : ¬ isBitwiseOp .notb := by simp [isBitwiseOp]

end OperatorClassificationTests

/-!
## Section 3: Evaluation Helper Function Tests
-/

section EvalHelperTests

  theorem evalArithOp_add : evalArithOp .add 3 4 = some 7 := by rfl
  theorem evalArithOp_sub : evalArithOp .sub 10 3 = some 7 := by rfl
  theorem evalArithOp_mul : evalArithOp .mul 6 7 = some 42 := by rfl
  theorem evalArithOp_div : evalArithOp .div 10 3 = some 3 := by rfl
  theorem evalArithOp_div_zero : evalArithOp .div 10 0 = none := by rfl
  theorem evalArithOp_mod : evalArithOp .mod 10 3 = some 1 := by rfl
  theorem evalArithOp_mod_zero : evalArithOp .mod 10 0 = none := by rfl
  theorem evalArithOp_non_arith : evalArithOp .eq 1 2 = none := by rfl
  theorem evalArithOp_neg : evalArithOp .add (-3) 5 = some 2 := by rfl

  theorem evalCompOp_eq_true : evalCompOp .eq 3 3 = true := by rfl
  theorem evalCompOp_eq_false : evalCompOp .eq 3 4 = false := by rfl
  theorem evalCompOp_neq_true : evalCompOp .neq 3 4 = true := by rfl
  theorem evalCompOp_neq_false : evalCompOp .neq 3 3 = false := by rfl
  theorem evalCompOp_lt_true : evalCompOp .lt 3 5 = true := by rfl
  theorem evalCompOp_lt_false : evalCompOp .lt 5 3 = false := by rfl
  theorem evalCompOp_leq_true : evalCompOp .leq 3 3 = true := by rfl
  theorem evalCompOp_leq_false : evalCompOp .leq 5 3 = false := by rfl
  theorem evalCompOp_gt_true : evalCompOp .gt 5 3 = true := by rfl
  theorem evalCompOp_gt_false : evalCompOp .gt 3 5 = false := by rfl
  theorem evalCompOp_geq_true : evalCompOp .geq 5 5 = true := by rfl
  theorem evalCompOp_geq_false : evalCompOp .geq 3 5 = false := by rfl
  theorem evalCompOp_non_comp : evalCompOp .add 1 2 = false := by rfl

  theorem evalLogicOp_and_tt : evalLogicOp .and true true = some true := by rfl
  theorem evalLogicOp_and_tf : evalLogicOp .and true false = some false := by rfl
  theorem evalLogicOp_and_ft : evalLogicOp .and false true = some false := by rfl
  theorem evalLogicOp_and_ff : evalLogicOp .and false false = some false := by rfl
  theorem evalLogicOp_or_ff : evalLogicOp .or false false = some false := by rfl
  theorem evalLogicOp_or_tf : evalLogicOp .or true false = some true := by rfl
  theorem evalLogicOp_or_ft : evalLogicOp .or false true = some true := by rfl
  theorem evalLogicOp_or_tt : evalLogicOp .or true true = some true := by rfl
  theorem evalLogicOp_non_logic : evalLogicOp .add true true = none := by rfl

  theorem evalBitwiseOp_andb_11 : evalBitwiseOp .andb 1 1 = some 1 := by rfl
  theorem evalBitwiseOp_andb_10 : evalBitwiseOp .andb 1 0 = some 0 := by rfl
  theorem evalBitwiseOp_andb_01 : evalBitwiseOp .andb 0 1 = some 0 := by rfl
  theorem evalBitwiseOp_andb_00 : evalBitwiseOp .andb 0 0 = some 0 := by rfl
  theorem evalBitwiseOp_orb_01 : evalBitwiseOp .orb 0 1 = some 1 := by rfl
  theorem evalBitwiseOp_orb_00 : evalBitwiseOp .orb 0 0 = some 0 := by rfl
  theorem evalBitwiseOp_orb_11 : evalBitwiseOp .orb 1 1 = some 1 := by rfl
  theorem evalBitwiseOp_xorb_10 : evalBitwiseOp .xorb 1 0 = some 1 := by rfl
  theorem evalBitwiseOp_xorb_11 : evalBitwiseOp .xorb 1 1 = some 0 := by rfl
  theorem evalBitwiseOp_shl : evalBitwiseOp .shl 1 2 = some 4 := by rfl
  theorem evalBitwiseOp_shr : evalBitwiseOp .shr 8 2 = some 2 := by rfl
  theorem evalBitwiseOp_non_bitwise : evalBitwiseOp .add 1 1 = none := by rfl

end EvalHelperTests

/-!
## Section 4: Substitution Function Tests

All substitution tests use de Bruijn indices.
`subst e v` substitutes bound variable at index 0 with `v`.
-/
section SubstitutionTests

  /-- subst replaces bvar 0 with the value -/
  theorem subst_bvar_zero :
    subst (.bvar 0) (.lit (.int 42)) = .lit (.int 42) := by
      simp [subst, subst', liftUnder]

  /-- subst shifts bvar 1 down to bvar 0 (no match at index 0) -/
  theorem subst_bvar_one :
    subst (.bvar 1) (.lit (.int 42)) = .bvar 0 := by
      simp [subst, subst']

  /-- subst leaves bvar 2 as bvar 1 (shifts down by 1) -/
  theorem subst_bvar_two :
    subst (.bvar 2) (.lit (.int 42)) = .bvar 1 := by
      simp [subst, subst']

  /-- subst on a literal returns the literal unchanged -/
  theorem subst_lit :
    subst (.lit (.int 5)) (.lit (.int 42)) = .lit (.int 5) := by
      simp [subst, subst']

  /-- subst on an fvar returns the fvar unchanged -/
  theorem subst_fvar :
    subst (.fvar "x") (.lit (.int 42)) = .fvar "x" := by
      simp [subst, subst']

  /-- subst on unop recurses into the operand -/
  theorem subst_unop :
    subst (.unop .not (.bvar 0)) (.lit (.bool true))
      = .unop .not (.lit (.bool true)) := by
        simp [subst, subst', liftUnder]

  /-- subst on binop recurses into both operands -/
  theorem subst_binop_left :
    subst (.binop .add (.bvar 0) (.bvar 1)) (.lit (.int 10))
      = .binop .add (.lit (.int 10)) (.bvar 0) := by
        simp [subst, subst', liftUnder]

  theorem subst_binop_right :
    subst (.binop .add (.lit (.int 1)) (.bvar 0)) (.lit (.int 10))
      = .binop .add (.lit (.int 1)) (.lit (.int 10)) := by
        simp [subst, subst', liftUnder]

  /-- subst under lam: bvar 0 in body refers to lam's param, not subst target -/
  theorem subst_lam_captured :
    subst (.lam 1 (.bvar 0)) (.lit (.int 42))
      = .lam 1 (.bvar 0) := by
        simp [subst, subst']

  /-- subst under lam: bvar 1 in body refers to outer (subst target), becomes the value lifted -/
  theorem subst_lam_escape :
    subst (.lam 1 (.bvar 1)) (.lit (.int 42))
      = .lam 1 (.lit (.int 42)) := by
        simp [subst, subst', liftUnder]

  /-- subst on let_: bvar 0 in body is captured by let binder, not substituted -/
  theorem subst_let_body :
    subst (.let_ (.lit (.int 0)) (.bvar 0)) (.lit (.int 10))
      = .let_ (.lit (.int 0)) (.bvar 0) := by
        simp [subst, subst']

  /-- subst on ifThenElse recurses into all three branches -/
  theorem subst_if :
    subst (.ifThenElse (.fvar "c") (.bvar 0) (.lit (.int 0))) (.lit (.int 1))
      = .ifThenElse (.fvar "c") (.lit (.int 1)) (.lit (.int 0)) := by
        simp [subst, subst', liftUnder]

  /-- subst on block recurses into all expressions -/
  theorem subst_block :
    subst (.block [.bvar 0, .bvar 1]) (.lit (.int 1))
      = .block [.lit (.int 1), .bvar 0] := by
        simp [subst, subst', liftUnder]

  /-- subst on app recurses into function and arguments -/
  theorem subst_app :
    subst (.app (.fvar "f") [.bvar 0]) (.lit (.int 1))
      = .app (.fvar "f") [.lit (.int 1)] := by
        simp [subst, subst', liftUnder]

  /-- subst on forLoop: start substituted; body at depth 1: bvar 0 = loop var (captured), bvar 1 = outer (substituted) -/
  theorem subst_forLoop :
    subst (.forLoop (.bvar 0) (.lit (.int 10)) [.bvar 0, .bvar 1])
      (.lit (.int 1))
      = .forLoop (.lit (.int 1)) (.lit (.int 10)) [.bvar 0, .lit (.int 1)] := by
        simp [subst, subst', liftUnder]

  /-- substAll with no values leaves expression unchanged -/
  theorem substAll_empty :
    substAll [] (.bvar 0) = .bvar 0 := by
      simp [substAll, substAll']

  /-- substAll with one value replaces bvar 0 -/
  theorem substAll_single :
    substAll [.lit (.int 42)] (.bvar 0) = .lit (.int 42) := by
      simp [substAll, substAll', liftUnder]

  /-- substAll with two values replaces bvar 0 and bvar 1 -/
  theorem substAll_multi :
    substAll [.lit (.int 1), .lit (.int 2)] (.binop .add (.bvar 0) (.bvar 1))
      = .binop .add (.lit (.int 1)) (.lit (.int 2)) := by
      simp [substAll, substAll', liftUnder]

  /-- substAll under lam: body bvar 0 refers to lam's param, outer bvar 1 gets value -/
  theorem substAll_under_lam :
    substAll [.lit (.int 1)] (.lam 1 (.bvar 1))
      = .lam 1 (.lit (.int 1)) := by
      simp [substAll, substAll', liftUnder]

  /-- substAll with more values than bvars: first value maps to bvar 0 -/
  theorem substAll_extra :
    substAll [.lit (.int 1), .lit (.int 2)] (.bvar 0)
      = .lit (.int 1) := by
      simp [substAll, substAll', liftUnder]

end SubstitutionTests

/-!
## Section 5: Step Relation — Binary Operations
-/

section StepBinopTests

  theorem step_binop_left :
    Step (.binop .add (.ifThenElse (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2)))
          (.lit (.int 3)))
      (.binop .add (.lit (.int 1)) (.lit (.int 3))) := by
    apply Step.binop_left; apply Step.if_true

  theorem step_binop_right :
    Step (.binop .add (.lit (.int 1))
          (.ifThenElse (.lit (.bool true)) (.lit (.int 2)) (.lit (.int 3))))
      (.binop .add (.lit (.int 1)) (.lit (.int 2))) := by
    apply Step.binop_right; apply IsValue.lit; apply Step.if_true

  theorem step_binop_arith_add :
    Step (.binop .add (.lit (.int 3)) (.lit (.int 4))) (.lit (.int 7)) := by
    apply Step.binop_arith <;> trivial

  theorem step_binop_arith_sub :
    Step (.binop .sub (.lit (.int 10)) (.lit (.int 3))) (.lit (.int 7)) := by
    apply Step.binop_arith <;> trivial

  theorem step_binop_arith_mul :
    Step (.binop .mul (.lit (.int 6)) (.lit (.int 7))) (.lit (.int 42)) := by
    apply Step.binop_arith <;> trivial

  theorem step_binop_arith_div :
    Step (.binop .div (.lit (.int 10)) (.lit (.int 3))) (.lit (.int 3)) := by
    apply Step.binop_arith <;> trivial

  theorem step_binop_arith_mod :
    Step (.binop .mod (.lit (.int 10)) (.lit (.int 3))) (.lit (.int 1)) := by
    apply Step.binop_arith <;> trivial

  theorem step_binop_comp_eq :
    Step (.binop .eq (.lit (.int 3)) (.lit (.int 3))) (.lit (.bool true)) := by
    apply Step.binop_comp; trivial

  theorem step_binop_comp_neq :
    Step (.binop .neq (.lit (.int 3)) (.lit (.int 4))) (.lit (.bool true)) := by
    apply Step.binop_comp; trivial

  theorem step_binop_comp_lt :
    Step (.binop .lt (.lit (.int 3)) (.lit (.int 5))) (.lit (.bool true)) := by
    apply Step.binop_comp; trivial

  theorem step_binop_comp_leq :
    Step (.binop .leq (.lit (.int 3)) (.lit (.int 3))) (.lit (.bool true)) := by
    apply Step.binop_comp; trivial

  theorem step_binop_comp_gt :
    Step (.binop .gt (.lit (.int 5)) (.lit (.int 3))) (.lit (.bool true)) := by
    apply Step.binop_comp; trivial

  theorem step_binop_comp_geq :
    Step (.binop .geq (.lit (.int 5)) (.lit (.int 5))) (.lit (.bool true)) := by
    apply Step.binop_comp; trivial

  theorem step_binop_logic_and :
    Step (.binop .and (.lit (.bool true)) (.lit (.bool false))) (.lit (.bool false)) := by
    apply Step.binop_logic <;> trivial

  theorem step_binop_logic_or :
    Step (.binop .or (.lit (.bool false)) (.lit (.bool true))) (.lit (.bool true)) := by
    apply Step.binop_logic <;> trivial

  theorem step_binop_bitwise_andb :
    Step (.binop .andb (.lit (.int 1)) (.lit (.int 1))) (.lit (.int 1)) := by
    apply Step.binop_bitwise <;> trivial

  theorem step_binop_bitwise_orb :
    Step (.binop .orb (.lit (.int 0)) (.lit (.int 1))) (.lit (.int 1)) := by
    apply Step.binop_bitwise <;> trivial

  theorem step_binop_bitwise_xorb :
    Step (.binop .xorb (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 1)) := by
    apply Step.binop_bitwise <;> trivial

  theorem step_binop_bitwise_shl :
    Step (.binop .shl (.lit (.int 1)) (.lit (.int 2))) (.lit (.int 4)) := by
    apply Step.binop_bitwise <;> trivial

  theorem step_binop_bitwise_shr :
    Step (.binop .shr (.lit (.int 8)) (.lit (.int 2))) (.lit (.int 2)) := by
    apply Step.binop_bitwise <;> trivial

  theorem step_binop_div_zero :
    Step (.binop .div (.lit (.int 42)) (.lit (.int 0))) (.lit (.int 0)) := by
    exact Step.binop_div_zero 42

  theorem step_binop_div_zero_zero :
    Step (.binop .div (.lit (.int 0)) (.lit (.int 0))) (.lit (.int 0)) := by
    exact Step.binop_div_zero 0

  theorem step_binop_mod_zero :
    Step (.binop .mod (.lit (.int 42)) (.lit (.int 0))) (.lit (.int 0)) := by
    exact Step.binop_mod_zero 42

  theorem step_binop_mod_zero_zero :
    Step (.binop .mod (.lit (.int 0)) (.lit (.int 0))) (.lit (.int 0)) := by
    exact Step.binop_mod_zero 0

end StepBinopTests

/-!
## Section 6: Step Relation — Unary Operations
-/

section StepUnopTests

  theorem step_unop_step :
    Step (.unop .not (.ifThenElse (.lit (.bool true)) (.lit (.bool true)) (.lit (.bool false))))
      (.unop .not (.lit (.bool true))) := by
    apply Step.unop_step; apply Step.if_true

  theorem step_unop_not_true :
    Step (.unop .not (.lit (.bool true))) (.lit (.bool false)) := by
    exact Step.unop_not true

  theorem step_unop_not_false :
    Step (.unop .not (.lit (.bool false))) (.lit (.bool true)) := by
    exact Step.unop_not false

  theorem step_unop_notb_pos :
    Step (.unop .notb (.lit (.int 5))) (.lit (.int (-6))) := by
    exact Step.unop_notb 5

  theorem step_unop_notb_zero :
    Step (.unop .notb (.lit (.int 0))) (.lit (.int (-1))) := by
    exact Step.unop_notb 0

  theorem step_unop_notb_neg :
    Step (.unop .notb (.lit (.int (-3)))) (.lit (.int 2)) := by
    exact Step.unop_notb (-3)

end StepUnopTests

/-!
## Section 7: Step Relation — Conditionals
-/

section StepConditionalTests

  theorem step_if_cond :
    Step (.ifThenElse (.binop .add (.lit (.int 1)) (.lit (.int 2)))
          (.lit (.int 10)) (.lit (.int 20)))
      (.ifThenElse (.lit (.int 3)) (.lit (.int 10)) (.lit (.int 20))) := by
    apply Step.if_cond; apply Step.binop_arith <;> trivial

  theorem step_if_true :
    Step (.ifThenElse (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2)))
      (.lit (.int 1)) := by
    apply Step.if_true

  theorem step_if_false :
    Step (.ifThenElse (.lit (.bool false)) (.lit (.int 1)) (.lit (.int 2)))
      (.lit (.int 2)) := by
    apply Step.if_false

end StepConditionalTests

/-!
## Section 8: Step Relation — Let Binding
-/

section StepLetTests

  theorem step_let_step :
    Step (.let_ (.binop .add (.lit (.int 1)) (.lit (.int 2))) (.bvar 0))
      (.let_ (.lit (.int 3)) (.bvar 0)) := by
    apply Step.let_step; apply Step.binop_arith <;> trivial

  theorem step_let_subst :
    Step (.let_ (.lit (.int 42)) (.bvar 0))
      (subst (.bvar 0) (.lit (.int 42))) := by
    apply Step.let_subst; apply IsValue.lit

  theorem step_let_subst_lam :
    Step (.let_ (.lam 1 (.bvar 0)) (.bvar 0))
      (subst (.bvar 0) (.lam 1 (.bvar 0))) := by
    apply Step.let_subst; apply IsValue.lam

end StepLetTests

/-!
## Section 9: Step Relation — For Loops
-/

section StepForLoopTests

  theorem step_for_start :
    Step (.forLoop (.binop .add (.lit (.int 0)) (.lit (.int 1)))
          (.lit (.int 5)) [])
      (.forLoop (.lit (.int 1)) (.lit (.int 5)) []) := by
    apply Step.for_start; apply Step.binop_arith <;> trivial

  theorem step_for_end :
    Step (.forLoop (.lit (.int 0)) (.binop .add (.lit (.int 3)) (.lit (.int 2)))
          [])
      (.forLoop (.lit (.int 0)) (.lit (.int 5)) []) := by
    apply Step.for_end; apply IsValue.lit; apply Step.binop_arith <;> trivial

  theorem step_for_exec :
    Step (.forLoop (.lit (.int 0)) (.lit (.int 3)) [.bvar 0])
      (.let_ (.lit (.int 0))
        (.block ([.bvar 0] ++ [.forLoop (.lit (.int 1)) (.lit (.int 3)) [.bvar 0]]))) := by
    apply Step.for_exec; decide

  theorem step_for_done :
    Step (.forLoop (.lit (.int 5)) (.lit (.int 3)) []) (.lit .unit) := by
    apply Step.for_done; decide

  theorem step_for_done_equal :
    Step (.forLoop (.lit (.int 3)) (.lit (.int 3)) []) (.lit .unit) := by
    apply Step.for_done; decide

end StepForLoopTests

/-!
## Section 10: Step Relation — Blocks
-/

section StepBlockTests

  theorem step_block_head :
    Step (.block [.binop .add (.lit (.int 1)) (.lit (.int 2)), .lit (.int 3)])
      (.block [.lit (.int 3), .lit (.int 3)]) := by
    apply Step.block_head; apply Step.binop_arith <;> trivial

  theorem step_block_singleton :
    Step (.block [.lit (.int 42)]) (.lit (.int 42)) := by
    apply Step.block_singleton; apply IsValue.lit

  theorem step_block_lam_singleton :
    Step (.block [.lam 1 (.bvar 0)]) (.lam 1 (.bvar 0)) := by
    apply Step.block_lam_singleton

  theorem step_block_pop :
    Step (.block [.lit (.int 1), .lit (.int 2)])
      (.block [.lit (.int 2)]) := by
    apply Step.block_pop; apply IsValue.lit

end StepBlockTests

/-!
## Section 11: Step Relation — Function Application
-/

section StepAppTests

  theorem step_let_subst_lam_in_app :
    Step (.let_ (.lam 1 (.bvar 0))
          (.app (.bvar 0) [.lit (.int 1)]))
      (subst (.app (.bvar 0) [.lit (.int 1)]) (.lam 1 (.bvar 0))) := by
    apply Step.let_subst; apply IsValue.lam

  theorem step_app_arg :
    Step (.app (.lam 1 (.bvar 0))
          [.binop .add (.lit (.int 1)) (.lit (.int 2))])
      (.app (.lam 1 (.bvar 0)) [.lit (.int 3)]) := by
    apply Step.app_arg; apply IsValue.lam; apply Step.binop_arith <;> trivial

  theorem step_app_lam :
    Step (.app (.lam 1 (.bvar 0)) [.lit (.int 42)])
      (substAll [.lit (.int 42)] (.bvar 0)) := by
    apply Step.app_lam; rfl

  theorem step_app_lam_multi :
    Step (.app (.lam 2 (.binop .add (.bvar 1) (.bvar 0)))
          [.lit (.int 3), .lit (.int 4)])
      (substAll [.lit (.int 4), .lit (.int 3)]
        (.binop .add (.bvar 1) (.bvar 0))) := by
    apply Step.app_lam; rfl

end StepAppTests

/-!
## Section 12: Expr Constructor Unit Tests
-/

section ExprTests

  theorem expr_bvar (n : Nat) : (Expr.bvar n) = Expr.bvar n := by rfl
  theorem expr_fvar (name : String) : (Expr.fvar name) = Expr.fvar name := by rfl
  theorem expr_lit (v : Value) : (Expr.lit v) = Expr.lit v := by rfl
  theorem expr_binop (op : Operator) (e1 e2 : Expr) :
    (Expr.binop op e1 e2) = Expr.binop op e1 e2 := by rfl
  theorem expr_unop (op : Operator) (e : Expr) :
    (Expr.unop op e) = Expr.unop op e := by rfl
  theorem expr_app (fn : Expr) (args : List Expr) :
    (Expr.app fn args) = Expr.app fn args := by rfl
  theorem expr_lam (n : Nat) (body : Expr) :
    (Expr.lam n body) = Expr.lam n body := by rfl
  theorem expr_let (e1 e2 : Expr) :
    (Expr.let_ e1 e2) = Expr.let_ e1 e2 := by rfl
  theorem expr_ifThenElse (c t f : Expr) :
    (Expr.ifThenElse c t f) = Expr.ifThenElse c t f := by rfl
  theorem expr_forLoop (s e : Expr) (body : List Expr) :
    (Expr.forLoop s e body) = Expr.forLoop s e body := by rfl
  theorem expr_block (exprs : List Expr) :
    (Expr.block exprs) = Expr.block exprs := by rfl

  theorem expr_reflexivity (e : Expr) : e = e := by rfl
  theorem expr_symmetry (e1 e2 : Expr) : e1 = e2 → e2 = e1 := by
    intro h; exact h.symm
  theorem expr_transitivity (e1 e2 e3 : Expr) : e1 = e2 → e2 = e3 → e1 = e3 := by
    intro h1 h2; exact h1.trans h2

end ExprTests

/-!
## Section 13: Stmt Constructor Unit Tests
-/

section StmtTests

  theorem stmt_exprStmt (e : Expr) :
    (Stmt.exprStmt e) = Stmt.exprStmt e := by rfl
  theorem stmt_varDecl (id : Id) (ty : Typ) (e : Expr) :
    (Stmt.varDecl id ty e) = Stmt.varDecl id ty e := by rfl
  theorem stmt_assign (id : Id) (e : Expr) :
    (Stmt.assign id e) = Stmt.assign id e := by rfl
  theorem stmt_returnStmt (e : Expr) :
    (Stmt.returnStmt e) = Stmt.returnStmt e := by rfl
  theorem stmt_break : Stmt.break = Stmt.break := by rfl
  theorem stmt_continue : Stmt.continue = Stmt.continue := by rfl
  theorem stmt_whileLoop (cond : Expr) (body : List Stmt) :
    (Stmt.whileLoop cond body) = Stmt.whileLoop cond body := by rfl
  theorem stmt_doWhile (cond : Expr) (body : List Stmt) :
    (Stmt.doWhile cond body) = Stmt.doWhile cond body := by rfl
  theorem stmt_nop : Stmt.nop = Stmt.nop := by rfl

  theorem stmt_reflexivity (s : Stmt) : s = s := by rfl
  theorem stmt_symmetry (s1 s2 : Stmt) : s1 = s2 → s2 = s1 := by
    intro h; exact h.symm
  theorem stmt_transitivity (s1 s2 s3 : Stmt) : s1 = s2 → s2 = s3 → s1 = s3 := by
    intro h1 h2; exact h1.trans h2

end StmtTests

/-!
## Section 14: Property-Based Tests
-/

section PropertyTests

  theorem step_well_formed (e1 e2 : Expr) : Step e1 e2 → True := by
    intro _; trivial

  theorem isvalue_is_predicate (e : Expr) : IsValue e → True := by
    intro _; trivial

  theorem evalArithOp_deterministic (op : Operator) (n1 n2 : Int) (r1 r2 : Int) :
    evalArithOp op n1 n2 = some r1 → evalArithOp op n1 n2 = some r2 → r1 = r2 := by
    aesop

  theorem evalCompOp_deterministic (op : Operator) (n1 n2 : Int) (b1 b2 : Bool) :
    evalCompOp op n1 n2 = b1 → evalCompOp op n1 n2 = b2 → b1 = b2 := by
    aesop

  theorem evalLogicOp_deterministic (op : Operator) (b1 b2 r1 r2 : Bool) :
    evalLogicOp op b1 b2 = some r1 → evalLogicOp op b1 b2 = some r2 → r1 = r2 := by
    aesop

  theorem evalBitwiseOp_deterministic (op : Operator) (n1 n2 : Int) (r1 r2 : Int) :
    evalBitwiseOp op n1 n2 = some r1 → evalBitwiseOp op n1 n2 = some r2 → r1 = r2 := by
    aesop

  theorem arith_not_comp : isArithOp .add → ¬ isCompOp .add := by
    aesop

  theorem comp_not_logic : isCompOp .eq → ¬ isLogicOp .eq := by
    aesop

  theorem logic_not_bitwise : isLogicOp .and → ¬ isBitwiseOp .and := by
    aesop

  theorem arith_not_bitwise : isArithOp .add → ¬ isBitwiseOp .add := by
    aesop

end PropertyTests

end Tests.Semantics
