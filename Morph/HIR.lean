/- Copyright 2024-2025 The Morph Project Authors
-- SPDX-License-Identifier: Apache-2.0
-/
import Morph.Core

namespace Morph.HIR

structure Id where
  index : Nat
  name : String
deriving Repr, BEq, Hashable

namespace Id
  def getIndex (id : Id) : Nat := id.index
  def getName (id : Id) : String := id.name
end Id

inductive Pattern : Type where
  | lit : Morph.Core.Value -> Pattern
  | wildcard : Pattern
  | var : Id -> Pattern
deriving Repr

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

structure Program where
  stmts : List Stmt
deriving Repr

namespace Program
  def empty : Program := ⟨[]⟩
end Program

end Morph.HIR
