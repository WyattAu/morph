/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
import Morph.Core
open Morph.Core

namespace Morph.Syntax

/-!
# Surface Syntax (de Bruijn Indices)

**Purpose:** This module defines the surface syntax for the Morph language
using de Bruijn indices for bound variable representation.

**Key Design Decisions:**
- `bvar (n : Nat)` — bound variable by de Bruijn index (0 = most recent binder)
- `fvar (name : String)` — free variable by name
- `lam (n : Nat) body` — lambda binding n variables (indices 0..n-1)
- `let_ init body` — let binding 1 variable at index 0 (no binder name)
- `forLoop start end body` — for loop binding iterator at index 0 (no binder name)
- `Id` struct preserved for `Stmt.varDecl`/`Stmt.assign`

**Related Files:**
- `Morph/Core.lean` - Core type definitions
- `Morph/Semantics.lean` - Operational semantics with de Bruijn substitution
- `Morph/Specs/TypeSystem/Spec.lean` - Type system with bound-variable context

-/
/-!
## Id

Identifier for surface syntax constructs.

Preserved for use in `Stmt.varDecl` and `Stmt.assign`, which are
imperative constructs that don't participate in the de Bruijn system.
-/
structure Id where
  name : String
  deriving Repr, BEq, Hashable

namespace Id

/-- Get the name of an identifier -/
def getName (id : Id) : String := id.name

end Id

/-!
## Expr (de Bruijn representation)

Expression language using de Bruijn indices for bound variables:

- `bvar n`: Bound variable at de Bruijn index n (0 = most recent binder)
- `fvar name`: Free variable by name
- `lit v`: Literal value
- `unop op e`: Unary operation
- `binop op e1 e2`: Binary operation
- `app fn args`: Function application
- `lam n body`: Lambda binding n variables (de Bruijn indices 0..n-1)
- `let_ init body`: Let binding (binds init's value at index 0 in body)
- `ifThenElse c t f`: Conditional expression
- `forLoop start end body`: For loop (binds iterator at index 0 in body)
- `block exprs`: Block expression (sequence of expressions)
-/
inductive Expr : Type where
  | bvar : Nat → Expr
  | fvar : String → Expr
  | lit : Morph.Core.Value → Expr
  | unop : Operator → Expr → Expr
  | binop : Operator → Expr → Expr → Expr
  | app : Expr → List Expr → Expr
  | lam : Nat → Expr → Expr
  | let_ : Expr → Expr → Expr
  | ifThenElse : Expr → Expr → Expr → Expr
  | forLoop : Expr → Expr → List Expr → Expr
  | block : List Expr → Expr
 deriving Repr

/-!
## Stmt

Statement language for surface syntax.

Statements use `Id` for variable declarations and assignments (imperative constructs).
-/
inductive Stmt : Type where
  | exprStmt : Expr → Stmt
  | varDecl : Id → Typ → Expr → Stmt
  | assign : Id → Expr → Stmt
  | returnStmt : Expr → Stmt
  | break : Stmt
  | continue : Stmt
  | whileLoop : Expr → List Stmt → Stmt
  | doWhile : Expr → List Stmt → Stmt
  | nop : Stmt
 deriving Repr
/-!
## Program

Top-level program structure for surface syntax.
-/
structure Program where
  stmts : List Stmt
  deriving Repr

namespace Program

/-- Create an empty program with no statements -/
def empty : Program := ⟨[]⟩

end Program

/-!
## Lifting (de Bruijn index shifting)

`liftUnder bound k e`: Lift free bound-variable indices in `e` by `k`,
but only for indices ≥ `bound`. Indices < `bound` refer to binders
that have been crossed (internal references) and are left unchanged.

This is the standard de Bruijn lifting operation.
-/
def liftUnder (bound : Nat) (k : Nat) : Expr → Expr
  | .bvar n =>
    if n < bound then .bvar n else .bvar (n + k)
  | .fvar name => .fvar name
  | .lit v => .lit v
  | .unop op e => .unop op (liftUnder bound k e)
  | .binop op e1 e2 => .binop op (liftUnder bound k e1) (liftUnder bound k e2)
  | .app fn args => .app (liftUnder bound k fn) (args.map (liftUnder bound k))
  | .lam n body => .lam n (liftUnder (bound + n) k body)
  | .let_ e1 e2 => .let_ (liftUnder bound k e1) (liftUnder (bound + 1) k e2)
  | .ifThenElse c t f =>
    .ifThenElse (liftUnder bound k c) (liftUnder bound k t) (liftUnder bound k f)
  | .forLoop s e body =>
    .forLoop (liftUnder bound k s) (liftUnder bound k e) (body.map (liftUnder (bound + 1) k))
  | .block exprs => .block (exprs.map (liftUnder bound k))

/-- Lift all free bound-variable indices in `e` by `k`. -/
abbrev lift (k : Nat) (e : Expr) : Expr := liftUnder 0 k e

/-!
## Substitution (de Bruijn)

`subst' bound e v`: Substitute the bound variable at index `bound` with `v`.
When crossing binders, the bound counter is incremented (to track which binder
we're under) and the substitute `v` is lifted.

This is capture-avoiding by construction with de Bruijn indices.
-/
def subst' (bound : Nat) (e : Expr) (v : Expr) : Expr :=
  match e with
  | .bvar n =>
    if n < bound then .bvar n
    else if n = bound then lift bound v
    else .bvar (n - 1)
  | .fvar name => .fvar name
  | .lit v' => .lit v'
  | .unop op e1 => .unop op (subst' bound e1 v)
  | .binop op e1 e2 => .binop op (subst' bound e1 v) (subst' bound e2 v)
  | .app fn args => .app (subst' bound fn v) (args.map (subst' bound · v))
  | .lam n body => .lam n (subst' (bound + n) body v)
  | .let_ e1 e2 => .let_ (subst' bound e1 v) (subst' (bound + 1) e2 v)
  | .ifThenElse c t f =>
    .ifThenElse (subst' bound c v) (subst' bound t v) (subst' bound f v)
  | .forLoop s e body =>
    .forLoop (subst' bound s v) (subst' bound e v) (body.map (subst' (bound + 1) · v))
  | .block exprs => .block (exprs.map (subst' bound · v))

/-- Substitute the bound variable at index 0 with `v`. -/
abbrev subst (e : Expr) (v : Expr) : Expr := subst' 0 e v

/-!
## Simultaneous Substitution

`substAll' k vs e`: Simultaneously substitute bound variables at indices
k, k+1, ..., k+|vs|-1 with the corresponding values from `vs`.

This is NOT sequential (foldl) substitution. Sequential substitution is wrong
because processing later substitutes can shift free bvar indices in earlier
substitutes.

Logic for `.bvar n`:
- If `n < k`: leave as `.bvar n` (shadowed by an outer binder)
- If `n - k < vs.length`: substitute with `lift k vs[n-k]`
- Else: `.bvar (n - vs.length)` (free variable, shifted down)
-/
def substAll' (k : Nat) (vs : List Expr) (e : Expr) : Expr :=
  match e with
  | .bvar n =>
    if n < k then .bvar n
    else if h : n - k < vs.length then
      lift k (vs[n - k])
    else
      .bvar (n - vs.length)
  | .fvar name => .fvar name
  | .lit v => .lit v
  | .unop op e1 => .unop op (substAll' k vs e1)
  | .binop op e1 e2 => .binop op (substAll' k vs e1) (substAll' k vs e2)
  | .app fn args => .app (substAll' k vs fn) (args.map (substAll' k vs))
  | .lam n body => .lam n (substAll' (k + n) vs body)
  | .let_ e1 e2 => .let_ (substAll' k vs e1) (substAll' (k + 1) vs e2)
  | .ifThenElse c t f =>
    .ifThenElse (substAll' k vs c) (substAll' k vs t) (substAll' k vs f)
  | .forLoop s e body =>
    .forLoop (substAll' k vs s) (substAll' k vs e) (body.map (substAll' (k + 1) vs))
  | .block exprs => .block (exprs.map (substAll' k vs))

/-- Simultaneously substitute bound variables at indices 0, 1, ..., |vs|-1. -/
abbrev substAll (vs : List Expr) (e : Expr) : Expr := substAll' 0 vs e

/-!
## Free Variables

Collects all free variable names (from `fvar` constructors) in an expression.
With de Bruijn indices, there is no concept of "truly free" vs "mentioned in binder"
— free variables are simply the `fvar` nodes.
-/
def freeVars : Expr → List String
  | .bvar _ => []
  | .fvar name => [name]
  | .lit _ => []
  | .unop _ e => freeVars e
  | .binop _ e1 e2 => freeVars e1 ++ freeVars e2
  | .app fn args => freeVars fn ++ args.flatMap freeVars
  | .lam _ body => freeVars body
  | .let_ e1 e2 => freeVars e1 ++ freeVars e2
  | .ifThenElse c t f => freeVars c ++ freeVars t ++ freeVars f
  | .forLoop s e body => freeVars s ++ freeVars e ++ body.flatMap freeVars
  | .block exprs => exprs.flatMap freeVars

end Morph.Syntax
