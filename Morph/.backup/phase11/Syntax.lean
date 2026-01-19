import Morph.Core

namespace Morph.Syntax

structure Id where
  name : String
deriving Repr, BEq, Hashable

namespace Id
  def getName (id : Id) : String := id.name
end Id

inductive Expr : Type where
  | var : Id -> Expr
  | lit : Morph.Core.Value -> Expr
  | unop : Operator -> Expr -> Expr
  | binop : Operator -> Expr -> Expr -> Expr
  | app : Id -> List Expr -> Expr
  | lam : List Id -> Expr -> Expr
  | let : Id -> Expr -> Expr -> Expr
  | ifThenElse : Expr -> Expr -> Expr -> Expr
  | forLoop : Id -> Expr -> Expr -> List Expr -> Expr
  | block : List Expr -> Expr
deriving Repr

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

structure Program where
  stmts : List Stmt
deriving Repr

namespace Program
  def empty : Program := ⟨[]⟩
end Program

end Morph.Syntax
