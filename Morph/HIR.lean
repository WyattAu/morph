/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
import Morph.Core

namespace Morph.HIR

/-!
# High-Level Intermediate Representation (HIR)

**Purpose:** This module defines the High-Level Intermediate Representation for the Morph language.
HIR serves as an intermediate representation between the surface syntax and lower-level IRs.

**Key Features:**
- Pattern matching expressions
- Lambda expressions with multiple parameters
- Let bindings for local variables
- Conditional and loop constructs
- Block expressions for scoping

**Related Files:**
- `Morph/Core.lean` - Core type definitions
- `Morph/Syntax.lean` - Surface syntax
- `Morph/MIR.lean` - Lower-level IR
-/

/-!
## Id

Identifier for HIR constructs.

An identifier consists of:
- `index`: Numeric index for unique identification
- `name`: Human-readable name

This dual representation enables both efficient indexing and readable debugging.
-/
structure Id where
  index : Nat
  name : String
  deriving Repr, BEq, Hashable

namespace Id

/-- Get the numeric index of an identifier -/
def getIndex (id : Id) : Nat := id.index

/-- Get the name of an identifier -/
def getName (id : Id) : String := id.name

end Id

/-!
## Pattern

Pattern matching expressions for HIR.

Patterns can be:
- `lit v`: Match a literal value
- `wildcard`: Match any value (wildcard pattern)
- `var id`: Bind the matched value to a variable

Patterns are used in match expressions for destructuring values.
-/
inductive Pattern : Type where
  | lit : Morph.Core.Value -> Pattern
  | wildcard : Pattern
  | var : Id -> Pattern
 deriving Repr

/-!
## Expr

Expression language for HIR.

Expressions represent computable values:
- `var id`: Variable reference by identifier
- `lit v`: Literal value
- `unop op e`: Unary operation
- `binop op e1 e2`: Binary operation
- `app fn args`: Function application
- `lam params body`: Lambda abstraction with multiple parameters
- `let id init body`: Let binding (bind id to init in body)
- `ifThenElse cond then else`: Conditional expression
- `whileLoop cond body`: While loop expression
- `match scrutinee cases`: Pattern matching expression
- `block exprs`: Block expression (sequence of expressions)
- `infer`: Type inference placeholder

This expression language provides high-level abstractions for the Morph language.
-/
inductive Expr : Type where
  | var : Id -> Expr
  | lit : Morph.Core.Value -> Expr
  | unop : Operator -> Expr -> Expr
  | binop : Operator -> Expr -> Expr -> Expr
  | app : Id -> List Expr -> Expr
  | lam : List Id -> Expr -> Expr
  | let : Id -> Expr -> Expr -> Expr
  | ifThenElse : Expr -> Expr -> Expr -> Expr
  | whileLoop : Expr -> List Expr -> Expr
  | match : Expr -> List (Pattern × Expr) -> Expr
  | block : List Expr -> Expr
  | infer : Expr
 deriving Repr

/-!
## Stmt

Statement language for HIR.

Statements represent executable instructions:
- `exprStmt expr`: Expression statement
- `varDecl id ty init`: Variable declaration with type and initializer
- `assign id expr`: Assignment statement
- `returnStmt expr`: Return statement
- `break`: Break from loop
- `continue`: Continue to next loop iteration
- `whileLoop cond body`: While loop statement
- `nop`: No-operation statement

This statement language provides control flow constructs for HIR.
-/
inductive Stmt : Type where
  | exprStmt : Expr -> Stmt
  | varDecl : Id -> Typ -> Expr -> Stmt
  | assign : Id -> Expr -> Stmt
  | returnStmt : Expr -> Stmt
  | break : Stmt
  | continue : Stmt
  | whileLoop : Expr -> List Stmt -> Stmt
  | nop : Stmt
 deriving Repr

/-!
## Program

Top-level program structure for HIR.

A program consists of a list of statements to execute.
-/
structure Program where
  stmts : List Stmt
  deriving Repr

namespace Program

/-- Create an empty program with no statements -/
def empty : Program := ⟨[]⟩

end Program

end Morph.HIR
