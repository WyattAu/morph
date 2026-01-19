/- Copyright 2024-2025 The Morph Project Authors
-- SPDX-License-Identifier: Apache-2.0
-/
import Morph.Core

namespace Morph.MIR

structure Id where
  index : Nat
  name : String
deriving Repr, BEq, Hashable

namespace Id
  def getIndex (id : Id) : Nat := id.index
  def getName (id : Id) : String := id.name
end Id

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

inductive Terminator : Type where
  | ret : Id -> Terminator
  | br : Id -> Morph.Core.BlockId -> Morph.Core.BlockId -> Terminator
  | jmp : Morph.Core.BlockId -> Terminator
  | switch : Id -> List (Morph.Core.BlockId × Option Morph.Core.Value) -> Terminator
  | unreachable : Terminator
deriving Repr

structure BasicBlock where
  id : Morph.Core.BlockId
  stmts : List Stmt
  term : Terminator
deriving Repr

structure Function where
  id : Id
  params : List (Id × Typ)
  retType : Typ
  blocks : List BasicBlock

structure Program where
  functions : List Function

namespace Program
  def empty : Program := ⟨[]⟩
end Program

end Morph.MIR
