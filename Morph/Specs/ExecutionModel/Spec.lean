/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std
import Morph.Semantics

open Morph.Semantics Morph.Store

/-!
# Execution Model Specification

Operational semantics for the Morph language.
Defines step results, reduction strategies, and evaluation contexts.

## Overview

The execution model formalizes how Morph expressions are reduced to values.
It supports multiple reduction strategies (call-by-value, call-by-name, call-by-need)
and tracks execution via step results (normal, stuck, error).

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Step result | `StepResult` | Done |
| Reduction strategy | `ReductionStrategy` | Done |
| Evaluation context | `EvaluationContext` | Done |

## Known Issues

None.
-/

namespace Morph.Specs.ExecutionModel

/-- A simplified value in the execution model -/
inductive Value where
  | vUnit : Value
  | vInt : Int → Value
  | vBool : Bool → Value
  | vString : String → Value
  deriving Repr, BEq

/-- A simplified expression for operational semantics -/
inductive Expr where
  | val : Value → Expr
  | var : String → Expr
  | app : Expr → Expr → Expr
  | lam : String → Expr → Expr
  | add : Expr → Expr → Expr
  | letE : String → Expr → Expr → Expr
  | ifE : Expr → Expr → Expr → Expr
  | seq : Expr → Expr → Expr
deriving Repr, BEq

/-- Substitution: replace variable `x` with value `v` in expression `e`. -/
def subst (e : Expr) (x : String) (v : Value) : Expr :=
  match e with
  | .val _ => e
  | .var y => if y == x then .val v else e
  | .app e1 e2 => .app (subst e1 x v) (subst e2 x v)
  | .lam y body => if y == x then e else .lam y (subst body x v)
  | .add e1 e2 => .add (subst e1 x v) (subst e2 x v)
  | .letE y e1 e2 => .letE y (subst e1 x v) (if y == x then e2 else subst e2 x v)
  | .ifE c t f => .ifE (subst c x v) (subst t x v) (subst f x v)
  | .seq e1 e2 => .seq (subst e1 x v) (subst e2 x v)

/-- Evaluation contexts: where reduction can occur -/
inductive EvalContext where
  | hole
  | appL : EvalContext → Expr → EvalContext
  | appR : Value → EvalContext → EvalContext
  | addL : EvalContext → Expr → EvalContext
  | addR : Value → EvalContext → EvalContext
  | letE : String → EvalContext → Expr → EvalContext
  | ifE : EvalContext → Expr → Expr → EvalContext
deriving Repr

/-- Result of a single evaluation step -/
inductive StepResult where
  | normal : Value → StepResult
  | stuck : Expr → StepResult
  | error : String → StepResult
  deriving Repr, BEq

/-- Reduction strategy for expression evaluation -/
inductive ReductionStrategy where
  | callByValue : ReductionStrategy
  | callByName : ReductionStrategy
  | callByNeed : ReductionStrategy
  deriving Repr, BEq, Hashable

/-- Environment mapping variable names to values -/
abbrev Env := List (String × Value)

/-- Look up a variable in the environment -/
def Env.lookup (env : Env) (name : String) : Option Value :=
  env.find? (fun (n, _) => n == name) |>.map Prod.snd

/-- Extend the environment with a new binding -/
def Env.extend (env : Env) (name : String) (v : Value) : Env :=
  (name, v) :: env

/-- Evaluation context for context-based reduction -/
structure EvaluationContext where
  strategy : ReductionStrategy
  env : Env
  maxSteps : Nat
  deriving Repr, BEq

/-- A trace of execution steps -/
abbrev Trace := List StepResult

/-- Count the number of normal results in a trace -/
def Trace.normalCount (t : Trace) : Nat :=
  t.filter (fun s => match s with | StepResult.normal _ => true | _ => false) |>.length

/-- Check if a step result is terminal (not stuck) -/
def StepResult.isTerminal (r : StepResult) : Bool :=
  match r with
  | .normal _ => true
  | .error _ => true
  | .stuck _ => false

/-! ## Determinism of the pure binop core (loop 102)

Research basis: Wright & Felleisen, *A Syntactic Approach to Type Soundness*
(Information & Computation 1994) — determinism of a small-step semantics is
proved from value irreducibility plus agreement of the leaf rules. The GA
foundational assumption "all pure expressions have deterministic evaluation
order" (`SPEC_GAPS_AND_BASIS.md`, Foundational Basis §4) is grounded here for
the pure binop core: `binop` over literal operands, the arithmetic fragment
of `spec/concurrency/execution_model_spec.md`.

**Finding (loop 102):** unconditional value-irreducibility is **false** in
the shipped semantics — `none_step` makes `Step σ .none_ σ .none_` hold
reflexively, so the value `.none_` steps (uniquely, hence still
deterministically), and `some_none_done` departs from the value
`.some_ .none_`. The determinism theorem is therefore stated for literal
operands, where irreducibility is provable; extending it to the remaining
values is future work. -/

/-- Every operator kind gets a distinct number: the five binop leaf-rule
families are pairwise disjoint by construction. -/
def opKind : Morph.Core.Operator → Nat
  | .add | .sub | .mul | .div | .mod => 1
  | .eq | .neq | .lt | .leq | .gt | .geq => 2
  | .and | .or => 3
  | .andb | .orb | .xorb | .shl | .shr => 4
  | .ptrAdd | .ptrSub => 5
  | _ => 0

theorem isArithOp_kind (op : Morph.Core.Operator) (h : isArithOp op) :
    opKind op = 1 := by
  cases op <;> simp [isArithOp, opKind] at h ⊢ <;> omega

theorem isCompOp_kind (op : Morph.Core.Operator) (h : isCompOp op) :
    opKind op = 2 := by
  cases op <;> simp [isCompOp, opKind] at h ⊢ <;> omega

theorem isLogicOp_kind (op : Morph.Core.Operator) (h : isLogicOp op) :
    opKind op = 3 := by
  cases op <;> simp [isLogicOp, opKind] at h ⊢ <;> omega

theorem isBitwiseOp_kind (op : Morph.Core.Operator) (h : isBitwiseOp op) :
    opKind op = 4 := by
  cases op <;> simp [isBitwiseOp, opKind] at h ⊢ <;> omega

theorem isPtrArithOp_kind (op : Morph.Core.Operator) (h : isPtrArithOp op) :
    opKind op = 5 := by
  cases op <;> simp [isPtrArithOp, opKind] at h ⊢ <;> omega

/-- **Literals are irreducible.** No step departs from a literal — the first
ingredient of determinism (Wright–Felleisen 1994). -/
theorem lit_irreducible (σ σ' : Morph.Store) (v : Morph.Core.Value)
    (e : Morph.Syntax.Expr) :
    ¬ Step σ (Morph.Syntax.Expr.lit v) σ' e := by
  intro h
  cases h

set_option linter.unusedSimpArgs false in
/-- **One-step determinism of the pure arithmetic core.** For `binop` over
literal operands with an arithmetic operator, at most one leaf rule applies
(the operator families are disjoint; literals are irreducible, so the
congruence rules cannot fire), and it lands in a unique store — pure rules
pass the store through unchanged — and a unique result. The machine-checked
core of the GA assumption "all pure expressions have deterministic
evaluation order". -/
theorem binop_arith_deterministic (σ σ₁ σ₂ : Morph.Store)
    (op : Morph.Core.Operator) (n1 n2 : Int) (r₁ r₂ : Morph.Syntax.Expr)
    (ha : isArithOp op)
    (h₁ : Step σ (Morph.Syntax.Expr.binop op
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int n1))
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int n2))) σ₁ r₁)
    (h₂ : Step σ (Morph.Syntax.Expr.binop op
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int n1))
      (Morph.Syntax.Expr.lit (Morph.Core.Value.int n2))) σ₂ r₂) :
    σ₁ = σ₂ ∧ r₁ = r₂ := by
  cases op <;> cases h₁ <;> cases h₂ <;>
    simp_all [lit_irreducible, isArithOp, isCompOp, isLogicOp, isBitwiseOp,
      isPtrArithOp, isArithOp_kind, isCompOp_kind, isLogicOp_kind,
      isBitwiseOp_kind, isPtrArithOp_kind, evalArithOp, evalCompOp,
      evalLogicOp, evalBitwiseOp, evalPtrArithOp]

end Morph.Specs.ExecutionModel
