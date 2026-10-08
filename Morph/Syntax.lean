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
- `match_ scrut arms`: Pattern match expression
- `field_ e name`: Field access on struct expression
- `pipe e f`: Pipeline: e |> f
- `typeAsc e τ`: Type ascription
- `some_ e`: Option Some constructor
- `none_`: Option None constructor
- `ok_ e`: Result Ok constructor
- `err_ e`: Result Err constructor
- `nullCoalesce e1 e2`: Null coalescing (e1 ?? e2)
- `tuple_ elems`: Tuple expression
- `arrayLit elems`: Array literal expression
- `arrayIndex arr idx`: Array index expression
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
  | match_ : Expr → List (List String × Expr) → Expr
  | field_ : Expr → String → Expr
  | pipe : Expr → Expr → Expr
  | typeAsc : Expr → Typ → Expr
  | some_ : Expr → Expr
  | none_ : Expr
  | ok_ : Expr → Expr
  | err_ : Expr → Expr
  | nullCoalesce : Expr → Expr → Expr
  | tuple_ : List Expr → Expr
  | arrayLit : List Expr → Expr
  | arrayIndex : Expr → Expr → Expr
  | refCreate : Expr → Capability → Typ → Expr
  | refLoad : Expr → Expr
  | refStore : Expr → Expr → Typ → Expr
  | refFree : Expr → Expr
  deriving Repr, BEq

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
mutual
def liftUnderArms (bound k : Nat) : List (List String × Expr) → List (List String × Expr)
  | [] => []
  | (vars, body) :: rest => (vars, liftUnder (bound + vars.length) k body) :: liftUnderArms bound k rest

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
  | .match_ scrut arms => .match_ (liftUnder bound k scrut) (liftUnderArms bound k arms)
  | .field_ e name => .field_ (liftUnder bound k e) name
  | .pipe e f => .pipe (liftUnder bound k e) (liftUnder bound k f)
  | .typeAsc e ty => .typeAsc (liftUnder bound k e) ty
  | .some_ e => .some_ (liftUnder bound k e)
  | .none_ => .none_
  | .ok_ e => .ok_ (liftUnder bound k e)
  | .err_ e => .err_ (liftUnder bound k e)
  | .nullCoalesce e1 e2 => .nullCoalesce (liftUnder bound k e1) (liftUnder bound k e2)
  | .tuple_ elems => .tuple_ (elems.map (liftUnder bound k))
  | .arrayLit elems => .arrayLit (elems.map (liftUnder bound k))
  | .arrayIndex arr idx => .arrayIndex (liftUnder bound k arr) (liftUnder bound k idx)
  | .refCreate e cap τ => .refCreate (liftUnder bound k e) cap τ
  | .refLoad e => .refLoad (liftUnder bound k e)
  | .refStore e v τ => .refStore (liftUnder bound k e) (liftUnder bound k v) τ
  | .refFree e => .refFree (liftUnder bound k e)
end

/-- Lift all free bound-variable indices in `e` by `k`. -/
abbrev lift (k : Nat) (e : Expr) : Expr := liftUnder 0 k e

/-!
## Substitution (de Bruijn)

`subst' bound e v`: Substitute the bound variable at index `bound` with `v`.
When crossing binders, the bound counter is incremented (to track which binder
we're under) and the substitute `v` is lifted.

This is capture-avoiding by construction with de Bruijn indices.
-/
mutual
def substArms (bound : Nat) (v : Expr) : List (List String × Expr) → List (List String × Expr)
  | [] => []
  | (vars, body) :: rest => (vars, subst' (bound + vars.length) body v) :: substArms bound v rest

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
  | .match_ scrut arms => .match_ (subst' bound scrut v) (substArms bound v arms)
  | .field_ e name => .field_ (subst' bound e v) name
  | .pipe e f => .pipe (subst' bound e v) (subst' bound f v)
  | .typeAsc e ty => .typeAsc (subst' bound e v) ty
  | .some_ e => .some_ (subst' bound e v)
  | .none_ => .none_
  | .ok_ e => .ok_ (subst' bound e v)
  | .err_ e => .err_ (subst' bound e v)
  | .nullCoalesce e1 e2 => .nullCoalesce (subst' bound e1 v) (subst' bound e2 v)
  | .tuple_ elems => .tuple_ (elems.map (fun e => subst' bound e v))
  | .arrayLit elems => .arrayLit (elems.map (fun e => subst' bound e v))
  | .arrayIndex arr idx => .arrayIndex (subst' bound arr v) (subst' bound idx v)
  | .refCreate e cap τ => .refCreate (subst' bound e v) cap τ
  | .refLoad e => .refLoad (subst' bound e v)
  | .refStore e v' τ => .refStore (subst' bound e v) (subst' bound v' v) τ
  | .refFree e => .refFree (subst' bound e v)
end

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
mutual
def substAllArms (k : Nat) (vs : List Expr) : List (List String × Expr) → List (List String × Expr)
  | [] => []
  | (vars, body) :: rest => (vars, substAll' (k + vars.length) vs body) :: substAllArms k vs rest

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
  | .match_ scrut arms => .match_ (substAll' k vs scrut) (substAllArms k vs arms)
  | .field_ e name => .field_ (substAll' k vs e) name
  | .pipe e f => .pipe (substAll' k vs e) (substAll' k vs f)
  | .typeAsc e ty => .typeAsc (substAll' k vs e) ty
  | .some_ e => .some_ (substAll' k vs e)
  | .none_ => .none_
  | .ok_ e => .ok_ (substAll' k vs e)
  | .err_ e => .err_ (substAll' k vs e)
  | .nullCoalesce e1 e2 => .nullCoalesce (substAll' k vs e1) (substAll' k vs e2)
  | .tuple_ elems => .tuple_ (elems.map (fun e => substAll' k vs e))
  | .arrayLit elems => .arrayLit (elems.map (fun e => substAll' k vs e))
  | .arrayIndex arr idx => .arrayIndex (substAll' k vs arr) (substAll' k vs idx)
  | .refCreate e cap τ => .refCreate (substAll' k vs e) cap τ
  | .refLoad e => .refLoad (substAll' k vs e)
  | .refStore e v τ => .refStore (substAll' k vs e) (substAll' k vs v) τ
  | .refFree e => .refFree (substAll' k vs e)
end

/-- Simultaneously substitute bound variables at indices 0, 1, ..., |vs|-1. -/
abbrev substAll (vs : List Expr) (e : Expr) : Expr := substAll' 0 vs e

/-!
## Occurrence Counting (ADR-014)

`countUses e n`: the number of free occurrences of de Bruijn index `n` in `e`.
Occurrences under `k` additional binders count as uses of index `n + k`
(the same index convention as `liftUnder`/`subst'`: entering a binder of
arity `m` shifts the target index by `m`).

The linear arrow's typing rule (ADR-014 stage 1) uses `countUses` to enforce,
syntactically, that every parameter of a `linearFunctionType` is used exactly
once in the body. -/
mutual
def countUsesArms (n : Nat) : List (List String × Expr) → Nat
  | [] => 0
  | (vars, body) :: rest => countUses body (n + vars.length) + countUsesArms n rest

def countUsesList : List Expr → Nat → Nat
  | [], _ => 0
  | e :: rest, n => countUses e n + countUsesList rest n

def countUses : Expr → Nat → Nat
  | .bvar m, n => if m = n then 1 else 0
  | .fvar _, _ => 0
  | .lit _, _ => 0
  | .unop _ e, n => countUses e n
  | .binop _ e1 e2, n => countUses e1 n + countUses e2 n
  | .app fn args, n => countUses fn n + countUsesList args n
  | .lam m body, n => countUses body (n + m)
  | .let_ a b, n => countUses a n + countUses b (n + 1)
  | .ifThenElse c t f, n => countUses c n + countUses t n + countUses f n
  | .forLoop s e body, n => countUses s n + countUses e n + countUsesList body (n + 1)
  | .block exprs, n => countUsesList exprs n
  | .match_ scrut arms, n => countUses scrut n + countUsesArms n arms
  | .field_ e _, n => countUses e n
  | .pipe e f, n => countUses e n + countUses f n
  | .typeAsc e _, n => countUses e n
  | .some_ e, n => countUses e n
  | .none_, _ => 0
  | .ok_ e, n => countUses e n
  | .err_ e, n => countUses e n
  | .nullCoalesce e1 e2, n => countUses e1 n + countUses e2 n
  | .tuple_ elems, n => countUsesList elems n
  | .arrayLit elems, n => countUsesList elems n
  | .arrayIndex arr idx, n => countUses arr n + countUses idx n
  | .refCreate e _ _, n => countUses e n
  | .refLoad e, n => countUses e n
  | .refStore e v _, n => countUses e n + countUses v n
  | .refFree e, n => countUses e n
end

/-!
## Free Variables

Collects all free variable names (from `fvar` constructors) in an expression.
With de Bruijn indices, there is no concept of "truly free" vs "mentioned in binder"
— free variables are simply the `fvar` nodes.
-/
mutual
def freeVarsMatchArms : List (List String × Expr) → List String
  | [] => []
  | (_, body) :: rest => freeVars body ++ freeVarsMatchArms rest

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
  | .match_ scrut arms => freeVars scrut ++ freeVarsMatchArms arms
  | .field_ e _ => freeVars e
  | .pipe e f => freeVars e ++ freeVars f
  | .typeAsc e _ => freeVars e
  | .some_ e => freeVars e
  | .none_ => []
  | .ok_ e => freeVars e
  | .err_ e => freeVars e
  | .nullCoalesce e1 e2 => freeVars e1 ++ freeVars e2
  | .tuple_ elems => List.flatMap freeVars elems
  | .arrayLit elems => List.flatMap freeVars elems
  | .arrayIndex arr idx => freeVars arr ++ freeVars idx
  | .refCreate e _ _ => freeVars e
  | .refLoad e => freeVars e
  | .refStore e v _ => freeVars e ++ freeVars v
  | .refFree e => freeVars e
end

end Morph.Syntax
