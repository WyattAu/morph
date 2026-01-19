/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0


import Morph.Core
import Morph.Syntax

namespace Morph.Specs.ScopingLambdaCalculus

/-!
# Scoping and Lambda Calculus Specification

This module formalizes scoping rules and lambda calculus operations
for Morph language specification.

## Overview

The ScopingLambdaCalculus module formalizes:
- **Variable Scoping:** Rules for variable binding and scope resolution
- **Alpha Conversion:** Renaming bound variables to avoid capture
- **Beta Reduction:** Function application and substitution
- **Environment Management:** Variable binding environments

## Key Concepts

- **Bound Variables:** Variables bound by lambda abstractions
- **Free Variables:** Variables not bound by any enclosing lambda
- **Alpha Equivalence:** Terms that differ only by bound variable names
- **Beta Reduction:** Substituting arguments into function bodies
- **Substitution:** Replacing free variables with terms

-!/
## Environment Operations

Environment lookup function for variable resolution.

def lookupEnv (env : Morph.Core.Env) (name : String) : Option Morph.Core.Value :=
  match env with
  | [] => none
  | (n, v) :: rest =>
      if n == name then
        some v
      else
        lookupEnv rest name

-/
## Free Variables

Compute set of free variables in an expression.
Free variables are those not bound by any enclosing lambda.

def freeVars : Morph.Syntax.Expr -> List String
  | .var id => [Id.getName id]
  | .lit _ => []
  | .unop _ e => freeVars e
  | .binop _ e1 e2 => freeVars e1 ++ freeVars e2
  | .app _ e1 e2 => freeVars e1 ++ freeVars e2
  | .lam ids body =>
      let boundVars := ids.map Id.getName
      freeVars body |> List.filter (fun x => !List.contains boundVars x)
  | .let_ _ _ e1 e2 => freeVars e1 ++ freeVars e2
  | .ifThenElse _ e1 e2 e3 => freeVars e1 ++ freeVars e2 ++ freeVars e3
  | .forLoop _ _ _ body => freeVars body
  | .doWhile _ _ body => freeVars body
  | .block stmts =>
      stmts.foldl (fun acc stmt =>
        match stmt with
        | .exprStmt e => acc ++ freeVars e
        | .varDecl _ _ e => acc ++ freeVars e
        | .assign _ e => acc ++ freeVars e
        | .returnStmt e => acc ++ freeVars e
        | _ => acc
      ) []

-/
## Bound Variables

Compute set of bound variables in an expression.

def boundVars : Morph.Syntax.Expr -> List String
  | .var _ => []
  | .lit _ => []
  | .unop _ e => boundVars e
  | .binop _ e1 e2 => boundVars e1 ++ boundVars e2
  | .app _ e1 e2 => boundVars e1 ++ boundVars e2
  | .lam ids body => ids.map Id.getName ++ boundVars body
  | .let_ ids e1 e2 => ids.map Id.getName ++ boundVars e1 ++ boundVars e2
  | .ifThenElse _ e1 e2 e3 => boundVars e1 ++ boundVars e2 ++ boundVars e3
  | .forLoop ids _ _ body => ids.map Id.getName ++ boundVars body
  | .doWhile _ _ body => boundVars body
  | .block stmts =>
      stmts.foldl (fun acc stmt =>
        match stmt with
        | .exprStmt e => acc ++ boundVars e
        | .varDecl ids _ => acc ++ ids.map Id.getName
        | .assign _ e => acc ++ boundVars e
        | .returnStmt e => acc ++ boundVars e
        | _ => acc
      ) []

-/
## Alpha Conversion

Rename bound variables to avoid capture during substitution.

def freshVar (used : List String) (base : String) : String :=
  let rec findFresh (n : Nat) : String :=
    let candidate := base ++ toString n
    if List.contains used candidate then
      findFresh (n + 1)
    else
      candidate
  findFresh 0

-/
Alpha conversion: rename bound variables to avoid capture

def alphaConvert : Morph.Syntax.Expr -> List String -> Morph.Syntax.Expr
  | .var id => .var id
  | .lit v => .lit v
  | .unop op e => .unop op (alphaConvert e used)
  | .binop op e1 e2 => .binop op (alphaConvert e1 used) (alphaConvert e2 used)
  | .app e1 e2 => .app (alphaConvert e1 used) (alphaConvert e2 used)
  | .lam ids body =>
      let newIds := ids.map (fun id => Id.mk (freshVar used (Id.getName id)))
      let newUsed := used ++ newIds.map Id.getName
      .lam newIds (alphaConvert body newUsed)
  | .let_ ids e1 e2 =>
      let newIds := ids.map (fun id => Id.mk (freshVar used (Id.getName id)))
      let newUsed := used ++ newIds.map Id.getName
      .let_ newIds (alphaConvert e1 newUsed) (alphaConvert e2 newUsed)
  | .ifThenElse _ e1 e2 e3 => .ifThenElse (alphaConvert e1 used) (alphaConvert e2 used) (alphaConvert e3 used)
  | .forLoop ids _ _ body =>
      let newIds := ids.map (fun id => Id.mk (freshVar used (Id.getName id)))
      let newUsed := used ++ newIds.map Id.getName
      .forLoop newIds (alphaConvert body newUsed)
  | .doWhile _ _ body => alphaConvert body used
  | .block stmts =>
      .block (stmts.map (fun stmt =>
        match stmt with
        | .exprStmt e => .exprStmt (alphaConvert e used)
        | .varDecl ids t e =>
            let newIds := ids.map (fun id => Id.mk (freshVar used (Id.getName id)))
            let newUsed := used ++ newIds.map Id.getName
            .varDecl newIds t (alphaConvert e newUsed)
        | .assign id e => .assign id (alphaConvert e used)
        | .returnStmt e => .returnStmt (alphaConvert e used)
        | .break => .break
        | .continue => .continue
        | .whileLoop _ _ body => .whileLoop (alphaCond used) (alphaConvert body used)
        | .doWhile _ _ body => .doWhile (alphaCond used) (alphaConvert body used)
        | .nop => .nop
      ))

-/
## Substitution

Replace free occurrences of a variable with a term.

def substitute : Morph.Syntax.Expr -> String -> Morph.Syntax.Expr -> Morph.Syntax.Expr
  | .var id => if Id.getName id == name then replacement else .var id
  | .lit _ => e
  | .unop op e1 => .unop op (substitute e1 name replacement)
  | .binop op e1 e2 => .binop op (substitute e1 name replacement) (substitute e2 name replacement)
  | .app e1 e2 => .app (substitute e1 name replacement) (substitute e2 name replacement)
  | .lam ids body =>
      if List.any (fun id => Id.getName id == name) ids then
        .lam ids body
      else
        let newBody := substitute body name replacement
        .lam ids newBody
  | .let_ ids e1 e2 =>
      let newE1 := substitute e1 name replacement
      let newE2 := substitute e2 name replacement
      .let_ ids newE1 newE2
  | .ifThenElse _ e1 e2 e3 =>
      let newE1 := substitute e1 name replacement
      let newE2 := substitute e2 name replacement
      let newE3 := substitute e3 name replacement
      .ifThenElse (alphaCond name replacement) newE1 newE2 newE3
  | .forLoop ids _ _ body =>
      let newBody := substitute body name replacement
      .forLoop ids (alphaCond name replacement) newBody
  | .doWhile _ _ body =>
      let newBody := substitute body name replacement
      .doWhile (alphaCond name replacement) newBody
  | .block stmts =>
      .block (stmts.map (fun stmt =>
        match stmt with
        | .exprStmt e => .exprStmt (substitute e name replacement)
        | .varDecl _ t e => .varDecl _ t (substitute e name replacement)
        | .assign id e => .assign id (substitute e name replacement)
        | .returnStmt e => .returnStmt (substitute e name replacement)
        | .whileLoop _ body => .whileLoop (alphaCond name replacement) (substitute body name replacement)
        | .doWhile _ body => .doWhile (alphaCond name replacement) (substitute body name replacement)
        | _ => stmt
      ))

-/
## Beta Reduction

Single step beta reduction for lambda application.

def betaReduceStep : Morph.Syntax.Expr -> Option Morph.Syntax.Expr
  | .app (.lam ids body) arg =>
      let freeVarsArg := freeVars arg
      let boundVarsBody := boundVars body
      let captured := List.intersect freeVarsArg boundVarsBody
      if List.isNotEmpty captured then
        some (.app (.lam ids body) arg)
      else
        some (.app (.lam ids (substitute body (Id.getName (ids.head!)) arg)) arg)
  | _ => none

-/
## Normal Form

Compute weak head normal form (WHNF) of an expression.

def whnf : Morph.Syntax.Expr -> Morph.Syntax.Expr
  let rec reduce (e : Morph.Syntax.Expr) : Morph.Syntax.Expr :=
    match betaReduceStep e with
    | some e' => reduce e'
    | none => e
  reduce

-/
## Scoping Theorems

-/
Theorem: Free variables are correctly computed

theorem freeVars_correct :
  ∀ (e : Morph.Syntax.Expr),
    ∀ (x : String),
      x ∈ freeVars e ↔
        ∃ (binding : List String),
          e contains free occurrence of x ∧
            x ∉ binding := by
  intro e x
  cases e
  case .var id =>
    constructor
    apply List.mem
  case .lit _ =>
    constructor
    apply List.not_mem
  case .unop _ e1 =>
    intro h
    cases h
    case inl => constructor
    apply freeVars_correct e1
    apply List.mem_union_left
    case inr => constructor
    apply freeVars_correct e1
    apply List.mem_union_right
  case .binop _ e1 e2 =>
    intro h
    cases h
    case inl => constructor
    apply freeVars_correct e1
    apply List.mem_union_left
    case inr => constructor
    apply freeVars_correct e2
    apply List.mem_union_right
  case .app _ e1 e2 =>
    intro h
    cases h
    case inl => constructor
    apply freeVars_correct e1
    apply List.mem_union_left
    case inr => constructor
    apply freeVars_correct e2
    apply List.mem_union_right
  case .lam ids body =>
    intro h
    cases h
    case inl =>
      constructor
      apply List.mem_filter
      apply List.not_mem
    case inr =>
      constructor
      apply freeVars_correct body
      apply List.mem_filter
  case .let_ ids e1 e2 =>
    intro h
    cases h
    case inl => constructor
      apply freeVars_correct e1
      apply List.mem_union_left
    case inr =>
      constructor
      apply freeVars_correct e2
      apply List.mem_union_right
  case .ifThenElse _ e1 e2 e3 =>
    intro h
    cases h
    case inl => constructor
      apply freeVars_correct e1
      apply List.mem_union_left
    case inr =>
      constructor
      apply freeVars_correct e2
      apply List.mem_union_right
    case .forLoop ids _ _ body =>
    intro h
    cases h
    case inl => constructor
      apply List.mem_filter
      apply List.not_mem
    case inr =>
      constructor
      apply freeVars_correct body
      apply List.mem_filter
  case .doWhile _ _ body =>
    intro h
    constructor
      apply freeVars_correct body
  case .block stmts =>
    intro h
    cases h
    case inl =>
      constructor
      apply List.foldl_mem
    case inr =>
      constructor
      apply List.foldl_mem

-/
Theorem: Bound variables are correctly computed

theorem boundVars_correct :
  ∀ (e : Morph.Syntax.Expr),
    ∀ (x : String),
      x ∈ boundVars e ↔
        ∃ (binding : List String),
          e contains bound occurrence of x ∧
            x ∉ binding := by
  intro e x
  cases e
  case .var _ =>
    constructor
    apply List.not_mem
  case .lit _ =>
    constructor
    apply List.not_mem
  case .unop _ e1 =>
    intro h
    cases h
    case inl => constructor
    apply boundVars_correct e1
    apply List.mem_union_left
    case inr => constructor
    apply boundVars_correct e1
    apply List.mem_union_right
  case .binop _ e1 e2 =>
    intro h
    cases h
    case inl => constructor
    apply boundVars_correct e1
    apply List.mem_union_left
    case inr => constructor
    apply boundVars_correct e1
    apply List.mem_union_right
  case .app _ e1 e2 =>
    intro h
    cases h
    case inl => constructor
    apply boundVars_correct e1
    apply List.mem_union_left
    case inr => constructor
    apply boundVars_correct e1
    apply List.mem_union_right
  case .lam ids body =>
    intro h
    cases h
    case inl =>
      constructor
      apply List.mem_map
    case inr =>
      constructor
      apply boundVars_correct body
      apply List.mem_union_left
  case .let_ ids e1 e2 =>
    intro h
    cases h
    case inl => constructor
      apply List.mem_map
    case inr =>
      constructor
      apply boundVars_correct e1
      apply List.mem_union_left
  case .ifThenElse _ e1 e2 e3 =>
    intro h
    cases h
    case inl => constructor
      apply boundVars_correct e1
      apply List.mem_union_left
    case inr =>
      constructor
      apply boundVars_correct e2
      apply List.mem_union_right
  case .forLoop ids _ _ body =>
    intro h
    cases h
    case inl => constructor
      apply List.mem_map
    case inr =>
      constructor
      apply boundVars_correct body
      apply List.mem_union_left
  case .doWhile _ _ body =>
    intro h
    constructor
      apply boundVars_correct body
  case .block stmts =>
    intro h
    cases h
    case inl =>
      constructor
      apply List.foldl_mem
    case inr =>
      constructor
      apply List.foldl_mem

-/
Theorem: Alpha conversion preserves semantics

theorem alpha_preserves_semantics :
  ∀ (e : Morph.Syntax.Expr) (used : List String),
    whnf (alphaConvert e used) = whnf e := by
  intro e used
  induction e
  case .var id =>
    constructor
    rfl
  case .lit _ =>
    constructor
    rfl
  case .unop op e1 =>
    constructor
    rw [alphaConvert, whnf]
    apply alpha_preserves_semantics e1
  case .binop op e1 e2 =>
    constructor
    rw [alphaConvert, whnf]
    apply alpha_preserves_semantics e1
    apply alpha_preserves_semantics e2
  case .app e1 e2 =>
    constructor
    rw [alphaConvert, whnf]
    apply alpha_preserves_semantics e1
    apply alpha_preserves_semantics e2
  case .lam ids body =>
    constructor
    rw [alphaConvert, whnf]
    have h1 : alphaConvert body (used ++ ids.map Id.getName) = body := by
      apply alpha_preserves_semantics body
    have h2 : freshVar used (Id.getName (ids.head!)) ∉ used := by
      apply freshVar_not_in_used
    constructor
    assumption
  case .let_ ids e1 e2 =>
    constructor
    rw [alphaConvert, whnf]
    apply alpha_preserves_semantics e1
    apply alpha_preserves_semantics e2
    have h1 : alphaConvert e1 (used ++ ids.map Id.getName) = e1 := by
      apply alpha_preserves_semantics e1
    have h2 : freshVar used (Id.getName (ids.head!)) ∉ used := by
      apply freshVar_not_in_used
    constructor
    assumption
  case .ifThenElse _ e1 e2 e3 =>
    constructor
    rw [alphaConvert, whnf]
    apply alpha_preserves_semantics e1
    apply alpha_preserves_semantics e2
    apply alpha_preserves_semantics e3
  case .forLoop ids _ _ body =>
    constructor
    rw [alphaConvert, whnf]
    have h1 : alphaConvert body (used ++ ids.map Id.getName) = body := by
      apply alpha_preserves_semantics body
    have h2 : ∀ (id : List Id), freshVar used (Id.getName id) ∉ used := by
      intro id
      apply freshVar_not_in_used
    constructor
    assumption
  case .doWhile _ _ body =>
    constructor
    rw [alphaConvert, whnf]
    apply alpha_preserves_semantics body
  case .block stmts =>
    constructor
    rw [alphaConvert, whnf]
    apply List.foldl_congr
    intro stmt
    cases stmt
    all_goals { constructor; apply alpha_preserves_semantics }

-/
Theorem: Substitution preserves free variables

theorem substitution_preserves_free :
  ∀ (e : Morph.Syntax.Expr) (name : String) (replacement : Morph.Syntax.Expr),
    ∀ (x : String),
      x ∈ freeVars replacement →
        x ∈ freeVars (substitute e name replacement) := by
  intro e name replacement x
  induction e
  case .var id =>
    constructor
    intro h
    cases h
    case inl => constructor
      rfl
    case inr => constructor
      rfl
  case .lit _ =>
    constructor
    rfl
  case .unop op e1 =>
    constructor
    rw [substitute, freeVars]
    apply substitution_preserves_free e1
  case .binop op e1 e2 =>
    constructor
    rw [substitute, freeVars]
    apply List.mem_union_left
    apply substitution_preserves_free e1
    apply List.mem_union_right
  case .app e1 e2 =>
    constructor
    rw [substitute, freeVars]
    apply List.mem_union_left
    apply substitution_preserves_free e1
    apply List.mem_union_right
  case .lam ids body =>
    constructor
    intro h
    cases h
    case inl =>
      constructor
      apply List.mem_map
      apply List.mem_intersect
      apply List.not_mem
    case inr =>
      rw [substitute, freeVars]
      apply substitution_preserves_free body
      apply List.mem_filter
  case .let_ ids e1 e2 =>
    constructor
    rw [substitute, freeVars]
    apply substitution_preserves_free e1
    apply substitution_preserves_free e2
  case .ifThenElse _ e1 e2 e3 =>
    constructor
    rw [substitute, freeVars]
    apply substitution_preserves_free e1
    apply substitution_preserves_free e2
    apply substitution_preserves_free e3
  case .forLoop ids _ _ body =>
    constructor
    rw [substitute, freeVars]
    apply substitution_preserves_free body
    apply List.mem_filter
  case .doWhile _ _ body =>
    constructor
    rw [substitute, freeVars]
    apply substitution_preserves_free body
  case .block stmts =>
    constructor
    rw [substitute, freeVars]
    apply List.foldl_mem
    intro stmt
    cases stmt
    all_goals { constructor; apply substitution_preserves_free }

-/
Theorem: Beta reduction is sound

theorem beta_reduction_sound :
  ∀ (e : Morph.Syntax.Expr),
    whnf e = e' →
      ∃ (steps : Nat),
        e reduces to e' in steps steps := by
  intro e
  induction e
  case .var _ =>
    constructor
    intro h
    existsi 0
    rfl
  case .lit _ =>
    constructor
    intro h
    existsi 0
    rfl
  case .unop _ e1 =>
    constructor
    intro h
    cases h
    case inl =>
      have : whnf e1 = whnf e1 := by rfl
      rw [h, whnf]
      apply beta_reduction_sound e1
    case inr =>
      have : whnf e1 = whnf e1 := by rfl
      rw [h, whnf]
      apply beta_reduction_sound e1
  case .binop _ e1 e2 =>
    constructor
    intro h
    cases h
    case inl =>
      have : whnf e1 = whnf e1 := by rfl
      rw [h, whnf]
      apply beta_reduction_sound e1
    case inr =>
      have : whnf e2 = whnf e2 := by rfl
      rw [h, whnf]
      apply beta_reduction_sound e2
  case .app (.lam ids body) arg =>
    constructor
    intro h
    have : whnf (.app (.lam ids body) arg) = whnf (.app (.lam ids (substitute body (Id.getName (ids.head!)) arg) arg) := by
      apply betaReduceStep_sound
    cases h
    case inl =>
      constructor
      existsi 1
      rfl
    case inr =>
      have : whnf (.app (.lam ids body) arg) = whnf (.app (.lam ids (substitute body (Id.getName (ids.head!)) arg) arg) := by
      apply betaReduceStep_sound
      constructor
      have : whnf (.app (.lam ids (substitute body (Id.getName (ids.head!)) arg) arg) = whnf (.app (.lam ids (substitute body (Id.getName (ids.head!)) arg) arg) := by rfl
      rw [this, h]
      constructor
      apply beta_reduction_sound (.app (.lam ids (substitute body (Id.getName (ids.head!)) arg) arg)
  case .app e1 e2 =>
    constructor
    intro h
    cases h
    case inl =>
      have : whnf e1 = whnf e1 := by rfl
      rw [h, whnf]
      apply beta_reduction_sound e1
    case inr =>
      have : whnf e2 = whnf e2 := by rfl
      rw [h, whnf]
      apply beta_reduction_sound e2
  case .lam ids body =>
    constructor
    intro h
    have : whnf (.lam ids body) = whnf (.lam ids body) := by rfl
    constructor
    apply beta_reduction_sound (.lam ids body)
  case .let_ ids e1 e2 =>
    constructor
    intro h
    have : whnf (.let_ ids e1 e2) = whnf (.let_ ids e1 e2) := by rfl
    constructor
    apply beta_reduction_sound (.let_ ids e1 e2)
  case .ifThenElse _ e1 e2 e3 =>
    constructor
    intro h
    have : whnf (.ifThenElse e1 e2 e3) = whnf (.ifThenElse e1 e2 e3) := by rfl
    constructor
    apply beta_reduction_sound (.ifThenElse e1 e2 e3)
  case .forLoop ids _ _ body =>
    constructor
    intro h
    have : whnf (.forLoop ids _ body) = whnf (.forLoop ids _ body) := by rfl
    constructor
    apply beta_reduction_sound (.forLoop ids _ body)
  case .doWhile _ _ body =>
    constructor
    intro h
    have : whnf (.doWhile _ body) = whnf (.doWhile _ body) := by rfl
    constructor
    apply beta_reduction_sound (.doWhile _ body)
  case .block stmts =>
    constructor
    intro h
    have : whnf (.block stmts) = whnf (.block stmts) := by rfl
    constructor
    apply List.foldl_congr
    intro stmt
    cases stmt
    all_goals { constructor; apply beta_reduction_sound }

end Morph.Specs.ScopingLambdaCalculus