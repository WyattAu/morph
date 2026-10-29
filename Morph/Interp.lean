/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Executable

/-!
# The statement interpreter

Loop 74. The expression evaluator (`Morph.Executable`) is total and
kernel-transparent, but it evaluates one expression; a Morph *program* is a
sequence of statements. This module runs `Program`/`Stmt` over the same
evaluator, with statement variables bound by name in the `Context.fvs`
environment — exactly the representation `parseStmt` targets (expression-level
binders keep their de Bruijn scope inside `let .. in` and `fn .. ->`).

The environment threads through everything: a declaration pushes a binding,
an assignment updates the innermost one, and a loop body's environment is the
next iteration's starting environment (which is what makes
`while (i < 5) { let i = i + 1; }` terminate).

Totality: statement-level recursion (including `while` iterations) is bounded
by an explicit fuel that every step consumes; exhaustion is `Flow.stuck`, not
divergence. The driver composes `parseProgram` + `runProgram`.
-/

namespace Morph.Interp

open Morph.Syntax Morph.Executable

/-- The statement machine's outcome. -/
inductive Flow where
  | value : Expr → Flow
  | returned : Expr → Flow
  | broke : Flow
  | continued : Flow
  | stuck : Flow
  deriving Repr, BEq
/-- What one statement sequence did, paired with the final environment. -/
abbrev Ran := Flow × List (String × Expr)


def isStuck : Flow → Bool | .stuck => true | _ => false
def isValue : Flow → Bool | .value _ => true | _ => false

/-- The expression context for the current environment: statement variables
are free-name bindings; the de Bruijn stack is empty at statement level. -/
def ctxOf (env : List (String × Expr)) : Context :=
  { bvs := [], fvs := env }

/-- Replace the innermost binding of `x`. Assignment never introduces a name:
assigning to an undeclared variable leaves the environment unchanged (and the
variable stays stuck on later reads). -/
def updateBinding : List (String × Expr) → String → Expr → List (String × Expr)
  | [], _, _ => []
  | (n, w) :: rest, x, v =>
      if n == x then (n, v) :: rest else (n, w) :: updateBinding rest x v

/-- A loop's own value is unit; remember the sequence's last expression
instead (an expression statement after the loop keeps its value). -/
def Flow.replace : Flow → Expr → Flow
  | .value _, u => .value u
  | f, _ => f

mutual

/-- Run statements to completion. `acc` carries the most recent expression
statement's value, so the sequence's value is its last expression. -/
private def runStmts : Nat → List (String × Expr) → List Stmt → Flow → Ran
  | 0, env, _, _ => (.stuck, env)
  | _ + 1, env, [], acc => (acc, env)
  | fuel + 1, env, .nop :: rest, acc => runStmts fuel env rest acc
  | fuel + 1, env, .exprStmt e :: rest, _ =>
      match eval (ctxOf env) e with
      | none => (.stuck, env)
      | some v => runStmts fuel env rest (.value v)
  | fuel + 1, env, .varDecl x _ init :: rest, acc =>
      match eval (ctxOf env) init with
      | none => (.stuck, env)
      | some v => runStmts fuel ((x.name, v) :: env) rest acc
  | fuel + 1, env, .assign x e :: rest, acc =>
      match eval (ctxOf env) e with
      | none => (.stuck, env)
      | some v => runStmts fuel (updateBinding env x.name v) rest acc
  | fuel + 1, env, .returnStmt e :: _, _ =>
      match eval (ctxOf env) e with
      | none => (.stuck, env)
      | some v => (.returned v, env)
  | _ + 1, env, .break :: _, acc => (.broke, env)
  | _ + 1, env, .continue :: _, acc => (.continued, env)
  | fuel + 1, env, .whileLoop cond body :: rest, acc =>
      match runWhile fuel env cond body with
      | (.value u, env') => runStmts fuel env' rest (acc.replace u)
      | (f, env') => (f, env')
  | fuel + 1, env, .doWhile cond body :: rest, acc =>
      match runDoWhile fuel env cond body with
      | (.value u, env') => runStmts fuel env' rest (acc.replace u)
      | (f, env') => (f, env')

/-- `while (cond) body`: one fuel unit per iteration; the body's final
environment is the next iteration's starting environment. `break` exits the
loop as completed; `continue` starts the next iteration; `return` propagates.
The loop's own value is unit. -/
private def runWhile (fuel : Nat) (env : List (String × Expr)) (cond : Expr)
    (body : List Stmt) : Ran :=
  match fuel with
  | 0 => (.stuck, env)
  | fuel + 1 =>
    match eval (ctxOf env) cond with
    | some (.lit (.bool true)) =>
      match runStmts fuel env body (.value (.lit .unit)) with
      | (.broke, env') => (.value (.lit .unit), env')
      | (.continued, env') => runWhile fuel env' cond body
      | (.value _, env') => runWhile fuel env' cond body
      | (f, env') => (f, env')
    | some (.lit (.bool false)) => (.value (.lit .unit), env)
    | _ => (.stuck, env)

/-- `do body while (cond)`: the body runs at least once. -/
private def runDoWhile (fuel : Nat) (env : List (String × Expr)) (cond : Expr)
    (body : List Stmt) : Ran :=
  match fuel with
  | 0 => (.stuck, env)
  | fuel + 1 =>
    match runStmts fuel env body (.value (.lit .unit)) with
    | (.broke, env') => (.value (.lit .unit), env')
    | (.continued, env') => runWhile fuel env' cond body
    | (.value _, env') =>
        match eval (ctxOf env') cond with
        | some (.lit (.bool true)) => runDoWhile fuel env' cond body
        | some (.lit (.bool false)) => (.value (.lit .unit), env')
        | _ => (.stuck, env')
    | (f, env') => (f, env')

end

/-- Run a whole program: 1024 statement-level fuel units (one per statement,
per `while` iteration), empty starting environment. -/
def runProgram (prog : Program) : Flow :=
  (runStmts 1024 [] prog.stmts (.value (.lit .unit))).1

end Morph.Interp
