/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

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
  deriving Repr, BEq

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

end Morph.Specs.ExecutionModel
