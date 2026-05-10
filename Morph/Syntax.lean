/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
import Morph.Core
open Morph.Core

namespace Morph.Syntax

/-!
# Surface Syntax

**Purpose:** This module defines the surface syntax for the Morph language.
Surface syntax represents the language as written by programmers, before
any transformations or optimizations.

**Key Features:**
- High-level expression constructs (lambda, let, application)
- Rich control flow (for loops, while loops, do-while loops)
- Variable declarations and assignments
- Block expressions for scoping

**Related Files:**
- `Morph/Core.lean` - Core type definitions
- `Morph/HIR.lean` - High-level IR
- `Morph/MIR.lean` - Mid-level IR

-/
/-!
## Id

Identifier for surface syntax constructs.

An identifier consists of:
- `name`: Human-readable name

Identifiers are used for variable names, function names, and labels.
-/
structure Id where
  name : String
  deriving Repr, BEq, Hashable

namespace Id

/-- Get the name of an identifier -/
def getName (id : Id) : String := id.name

end Id

/-!
## Expr

Expression language for surface syntax.

Expressions represent computable values:
- `var id`: Variable reference by identifier
- `lit v`: Literal value
- `unop op e`: Unary operation
- `binop op e1 e2`: Binary operation
- `app fn args`: Function application (fn is an expression, typically a variable or lambda)
- `lam params body`: Lambda abstraction with multiple parameters
- `let id init body`: Let binding (bind id to init in body)
- `ifThenElse cond then else`: Conditional expression
- `forLoop id start end body`: For loop with iterator variable
- `block exprs`: Block expression (sequence of expressions)

This expression language provides high-level abstractions for the Morph language.
-/
inductive Expr : Type where
  | var : Id -> Expr
  | lit : Morph.Core.Value -> Expr
  | unop : Operator -> Expr -> Expr
  | binop : Operator -> Expr -> Expr -> Expr
  | app : Expr -> List Expr -> Expr
  | lam : List Id -> Expr -> Expr
  | let : Id -> Expr -> Expr -> Expr
  | ifThenElse : Expr -> Expr -> Expr -> Expr
  | forLoop : Id -> Expr -> Expr -> List Expr -> Expr
  | block : List Expr -> Expr
 deriving Repr

/-!
## Stmt

Statement language for surface syntax.

Statements represent executable instructions:
- `exprStmt expr`: Expression statement
- `varDecl id ty init`: Variable declaration with type and initializer
- `assign id expr`: Assignment statement
- `returnStmt expr`: Return statement
- `break`: Break from loop
- `continue`: Continue to next loop iteration
- `whileLoop cond body`: While loop statement
- `doWhile cond body`: Do-while loop statement
- `nop`: No-operation statement

This statement language provides control flow constructs for the Morph language.
-/
inductive Stmt : Type where
  | exprStmt : Expr -> Stmt
  | varDecl : Id -> Typ -> Expr -> Stmt
  | assign : Id -> Expr -> Stmt
  | returnStmt : Expr -> Stmt
  | break : Stmt
  | continue : Stmt
  | whileLoop : Expr -> List Stmt -> Stmt
  | doWhile : Expr -> List Stmt -> Stmt
  | nop : Stmt
 deriving Repr
/-!
## Program

Top-level program structure for surface syntax.

A program consists of a list of statements to execute.
-/
structure Program where
  stmts : List Stmt
  deriving Repr

namespace Program

/-- Create an empty program with no statements -/
def empty : Program := ⟨[]⟩

end Program

/-!
## Free Variables

Computes all variable names mentioned in an expression, INCLUDING binder names.
This is used as a freshness predicate: `x ∉ freeVars e` means `x` is not
mentioned anywhere in `e` (neither as a free variable nor as a binder).
-/

def freeVars : Expr → List String
  | .var id => [id.name]
  | .lit _ => []
  | .unop _ e => freeVars e
  | .binop _ e1 e2 => freeVars e1 ++ freeVars e2
  | .app fn args => freeVars fn ++ args.flatMap freeVars
  | .lam params body => (params.map Id.name) ++ freeVars body
  | .let id e1 e2 => freeVars e1 ++ [id.name] ++ freeVars e2
  | .ifThenElse c t f => freeVars c ++ freeVars t ++ freeVars f
  | .forLoop id s e body => freeVars s ++ freeVars e ++ [id.name] ++ body.flatMap freeVars
  | .block exprs => exprs.flatMap freeVars

/-- Compute the truly free variables of an expression (excluding binder names).
    Used for capture-avoidance in substitution. -/
def trulyFreeVars : Expr → List String
  | .var id => [id.name]
  | .lit _ => []
  | .unop _ e => trulyFreeVars e
  | .binop _ e1 e2 => trulyFreeVars e1 ++ trulyFreeVars e2
  | .app fn args => trulyFreeVars fn ++ args.flatMap trulyFreeVars
  | .lam params body =>
    (trulyFreeVars body).filter (fun n => ¬params.any (fun id => id.name == n))
  | .let id e1 e2 =>
    trulyFreeVars e1 ++ (trulyFreeVars e2).filter (fun n => n ≠ id.name)
  | .ifThenElse c t f => trulyFreeVars c ++ trulyFreeVars t ++ trulyFreeVars f
  | .forLoop id s e body =>
    trulyFreeVars s ++ trulyFreeVars e ++
    (body.flatMap trulyFreeVars).filter (fun n => n ≠ id.name)
  | .block exprs => exprs.flatMap trulyFreeVars

end Morph.Syntax
