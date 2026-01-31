/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
import Morph.Core

namespace Morph.MIR

/-!
# Mid-Level Intermediate Representation (MIR)

**Purpose:** This module defines the Mid-Level Intermediate Representation for the Morph language.
MIR serves as a lower-level IR that is closer to machine code while maintaining
high-level abstractions for verification.

**Key Features:**
- Basic block structure with terminators
- Explicit memory operations (load, store)
- Pointer arithmetic operations
- SSA-style phi nodes
- Control flow in terminators

**Related Files:**
- `Morph/Core.lean` - Core type definitions
- `Morph/HIR.lean` - High-level IR
- `Morph/Syntax.lean` - Surface syntax
-/

/-!
## Id

Identifier for MIR constructs.

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
## Expr

Expression language for MIR.

Expressions represent computable values:
- `var id`: Variable reference by identifier
- `lit v`: Literal value
- `unop op e`: Unary operation
- `binop op e1 e2`: Binary operation
- `load id`: Load value from memory location
- `store dst src`: Store value from src to dst
- `ptrAdd base offset`: Pointer addition
- `ptrSub base offset`: Pointer subtraction
- `call fn args`: Function call
- `phi args`: Phi node for SSA (Static Single Assignment)

This expression language provides low-level operations for MIR.
-/
inductive Expr : Type where
  | var : Id -> Expr
  | lit : Morph.Core.Value -> Expr
  | unop : Operator -> Expr -> Expr
  | binop : Operator -> Expr -> Expr -> Expr
  | load : Id -> Expr
  | store : Id -> Id -> Expr
  | ptrAdd : Id -> Id -> Expr
  | ptrSub : Id -> Id -> Expr
  | call : Id -> List Id -> Expr
  | phi : List Id -> Expr
 deriving Repr

/-!
## Stmt

Statement language for MIR.

Statements represent executable instructions:
- `exprStmt expr`: Expression statement
- `varDecl id ty init`: Variable declaration with type and initializer
- `assign id expr`: Assignment statement
- `returnStmt expr`: Return statement
- `break`: Break from loop
- `continue`: Continue to next loop iteration
- `whileLoop cond body`: While loop statement
- `nop`: No-operation statement

This statement language provides control flow constructs for MIR.
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
## Terminator

Terminator for basic blocks in MIR.

Terminators define how control flow exits a basic block:
- `ret id`: Return with value from identifier
- `br cond trueBlock falseBlock`: Conditional branch
- `jmp block`: Unconditional jump to block
- `switch id cases`: Switch statement with cases
- `unreachable`: Unreachable code

Terminators are essential for control flow analysis and optimization.
-/
inductive Terminator : Type where
  | ret : Id -> Terminator
  | br : Id -> Morph.Core.BlockId -> Morph.Core.BlockId -> Terminator
  | jmp : Morph.Core.BlockId -> Terminator
  | switch : Id -> List (Morph.Core.BlockId × Option Morph.Core.Value) -> Terminator
  | unreachable : Terminator
 deriving Repr

/-!
## BasicBlock

Basic block structure for MIR.

A basic block consists of:
- `id`: Unique block identifier
- `stmts`: List of statements in the block
- `term`: Terminator that ends the block

Basic blocks are fundamental units of control flow in MIR.
-/
structure BasicBlock where
  id : Morph.Core.BlockId
  stmts : List Stmt
  term : Terminator
 deriving Repr

/-!
## Function

Function definition for MIR.

A function consists of:
- `id`: Function identifier
- `params`: List of parameter identifiers and types
- `retType`: Return type
- `blocks`: List of basic blocks

Functions are the primary unit of compilation in MIR.
-/
structure Function where
  id : Id
  params : List (Id × Typ)
  retType : Typ
  blocks : List BasicBlock

/-!
## Program

Top-level program structure for MIR.

A program consists of a list of functions.
-/
structure Program where
  functions : List Function

namespace Program

/-- Create an empty program with no functions -/
def empty : Program := ⟨[]⟩

end Program

end Morph.MIR
