/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Syntax
import Morph.HIR

namespace Morph.Frontend.HIRLower

open Morph.Syntax

/-!
# HIR lowering — `Syntax.Expr` to `HIR.Expr` (loop 82)

The roadmap (§6.1) names HIR lowering as the remaining frontend step
after parsing: `Morph.HIR` already defines the target language, but
nothing mapped the surface AST into it. This module is that map, in the
codebase's established partial-lowering discipline (`Lowering.lowerIn`
returns `Option`, rejecting what it cannot represent, rather than
miscompiling it).

**Variable scheme.** Every de Bruijn slot maps to `Id ⟨n, "bv"⟩`, so a
body occurrence and its binder agree by index at every binder (`lam`
params innermost-first, mirroring the parser's `params ++ scope`;
`let_`'s single slot; single-`var_` match arms). Free variables map to
`Id ⟨0, "free:" ++ x⟩` — the prefix keeps them distinct from bound slot
0. `forLoop`'s iterator is anonymous *and* unreachable by name (loop
78b), so there is no HIR name to give it: `forLoop` is rejected.

**Supported fragment** (everything else is `none`): `bvar`/`fvar`/`lit`/
`unop`/`binop`/`lam`/`let_`/`ifThenElse`/`block`, `app` whose function
is a variable (HIR application is call-by-`Id`), and `match_` over
`wild`/`lit_`/`var_` patterns. Rejected: `field_`/`pipe`/`typeAsc`
(no HIR counterpart), `some_`/`none_`/`ok_`/`err_`/`nullCoalesce`
(HIR has no option/result constructors), `tuple_`/`arrayLit`/
`arrayIndex` (HIR has no tuple/array), all `ref*` (HIR has no store),
`forLoop` (above), `app` of a non-variable function, and arms with
`some_`/`ok_`/`err_`/`none_` patterns (HIR patterns are
`lit`/`wildcard`/`var` only).

Semantic preservation against HIR evaluation is named future work: HIR
has no evaluator yet, so there is nothing to preserve *into*. What is
proved here is the contract itself — every supported constructor lowers
to its mirror image, every rejected class lowers to `none` — pinned
both as theorems and as executable tests.
-/

/-- Lower one identifier occurrence to an HIR variable. -/
def toHIRVar : Syntax.Expr → Option HIR.Id
  | .bvar n => some ⟨n, "bv"⟩
  | .fvar x => some ⟨0, "free:" ++ x⟩
  | _ => none

/-- Lower a surface pattern; `none` where HIR patterns stop. -/
def toHIRPat : Syntax.Pattern → Option HIR.Pattern
  | .wild => some .wildcard
  | .var_ _ => some (.var ⟨0, "bv"⟩)
  | .lit_ v => some (.lit v)
  | .some_ _ => none
  | .none_ => none
  | .ok_ _ => none
  | .err_ _ => none

mutual

/-- Lower a surface expression to HIR; `none` outside the fragment above. -/
def toHIR : Syntax.Expr → Option HIR.Expr
  | .bvar n => some (.var ⟨n, "bv"⟩)
  | .fvar x => some (.var ⟨0, "free:" ++ x⟩)
  | .lit v => some (.lit v)
  | .unop op e => toHIR e |>.map (.unop op ·)
  | .binop op a b =>
    match toHIR a, toHIR b with
    | some a', some b' => some (.binop op a' b')
    | _, _ => none
  | .app f args =>
    match toHIRVar f, toHIRList args with
    | some id, some args' => some (.app id args')
    | _, _ => none
  | .lam n body =>
    toHIR body |>.map (.lam ((List.range n).map fun i => ⟨i, "bv"⟩) ·)
  | .let_ init body =>
    match toHIR init, toHIR body with
    | some init', some body' => some (.let ⟨0, "bv"⟩ init' body')
    | _, _ => none
  | .ifThenElse c t f =>
    match toHIR c, toHIR t, toHIR f with
    | some c', some t', some f' => some (.ifThenElse c' t' f')
    | _, _, _ => none
  | .forLoop _ _ _ => none
  | .block es => toHIRList es |>.map .block
  | .match_ scrut arms =>
    match toHIR scrut, toHIRArms arms with
    | some scrut', some arms' => some (.match scrut' arms')
    | _, _ => none
  | .field_ _ _ => none
  | .pipe _ _ => none
  | .typeAsc _ _ => none
  | .some_ _ => none
  | .none_ => none
  | .ok_ _ => none
  | .err_ _ => none
  | .nullCoalesce _ _ => none
  | .tuple_ _ => none
  | .arrayLit _ => none
  | .arrayIndex _ _ => none
  | .refCreate _ _ _ => none
  | .refLoad _ => none
  | .refStore _ _ _ => none
  | .refFree _ => none
  | .refCast _ _ => none

/-- `toHIR` over an expression list; one rejection fails the list. -/
def toHIRList : List Syntax.Expr → Option (List HIR.Expr)
  | [] => some []
  | e :: es =>
    match toHIR e, toHIRList es with
    | some e', some es' => some (e' :: es')
    | _, _ => none

/-- `toHIR` over match arms; one bad arm fails the match. -/
def toHIRArms : List (Syntax.Pattern × Syntax.Expr) → Option (List (HIR.Pattern × HIR.Expr))
  | [] => some []
  | (pat, body) :: rest =>
    match toHIRPat pat, toHIR body, toHIRArms rest with
    | some pat', some body', some rest' => some ((pat', body') :: rest')
    | _, _, _ => none

end

/-! ## The contract, pinned -/

/-- Literals lower to themselves. -/
theorem toHIR_lit (v : Morph.Core.Value) : toHIR (.lit v) = some (.lit v) := rfl

/-- Bound slots map by index. -/
theorem toHIR_bvar (n : Nat) : toHIR (.bvar n) = some (.var ⟨n, "bv"⟩) := rfl

/-- Free names are carried, collision-free against slot 0. -/
theorem toHIR_fvar (x : String) :
    toHIR (.fvar x) = some (.var ⟨0, "free:" ++ x⟩) := rfl

/-- Tuples have no HIR counterpart. -/
theorem toHIR_tuple_none (es : List Syntax.Expr) : toHIR (.tuple_ es) = none := rfl

/-- Field projection has no HIR counterpart. -/
theorem toHIR_field_none (e : Syntax.Expr) (name : String) :
    toHIR (.field_ e name) = none := rfl

/-- Pipelines have no HIR counterpart. -/
theorem toHIR_pipe_none (e f : Syntax.Expr) : toHIR (.pipe e f) = none := rfl

/-- Ascriptions have no HIR counterpart. -/
theorem toHIR_typeAsc_none (e : Syntax.Expr) (τ : Morph.Core.Typ) :
    toHIR (.typeAsc e τ) = none := rfl

/-- Option constructors have no HIR counterpart. -/
theorem toHIR_some_none (e : Syntax.Expr) : toHIR (.some_ e) = none := rfl

/-- `none` has no HIR counterpart. -/
theorem toHIR_noneLit_none : toHIR .none_ = none := rfl

/-- `??` has no HIR counterpart. -/
theorem toHIR_nullCoalesce_none (a b : Syntax.Expr) :
    toHIR (.nullCoalesce a b) = none := rfl

/-- Array indexing has no HIR counterpart. -/
theorem toHIR_arrayIndex_none (a i : Syntax.Expr) :
    toHIR (.arrayIndex a i) = none := rfl

/-- References have no HIR counterpart. -/
theorem toHIR_refCreate_none (e : Syntax.Expr) (c : Morph.Core.Capability) (τ : Morph.Core.Typ) :
    toHIR (.refCreate e c τ) = none := rfl

/-- `for` loops have no HIR counterpart (anonymous, unreachable iterator). -/
theorem toHIR_forLoop_none (s e : Syntax.Expr) (body : List Syntax.Expr) :
    toHIR (.forLoop s e body) = none := rfl

/-- Applying a non-variable function has no HIR counterpart (call-by-`Id`). -/
theorem toHIR_app_lam_none (n : Nat) (body : Syntax.Expr) (args : List Syntax.Expr) :
    toHIR (.app (.lam n body) args) = none := by
  simp [toHIR, toHIRVar]

/-- `some`-patterns have no HIR counterpart. -/
theorem toHIRPat_some_none (p : Syntax.Pattern) : toHIRPat (.some_ p) = none := rfl

/-! ## Statement and program lowering (loop 83)

Surface statements are name-based (`Syntax.Id` is just a name; they never
entered the de Bruijn system), so lowering is scope-free: embedded
expressions go through `toHIR`, identifiers map to `Id ⟨0, name⟩`.
`whileLoop` is the only control statement HIR shares; `doWhile` (executes
at least once — no HIR counterpart, and desugaring would change
semantics), `ifStmt`, and `matchStmt` (HIR statements have no
conditional or match) are rejected. The scope-extending `matchStmt` arms
need no scope threading precisely because the whole statement is `none`.
-/

mutual

/-- Lower a surface statement; `none` where HIR statements stop. -/
def toHIRStmt : Syntax.Stmt → Option HIR.Stmt
  | .exprStmt e => toHIR e |>.map .exprStmt
  | .varDecl id ty init => toHIR init |>.map (.varDecl ⟨0, id.name⟩ ty ·)
  | .assign id e => toHIR e |>.map (.assign ⟨0, id.name⟩ ·)
  | .returnStmt e => toHIR e |>.map .returnStmt
  | .break => some .break
  | .continue => some .continue
  | .whileLoop cond body =>
    match toHIR cond, toHIRStmtList body with
    | some c, some b => some (.whileLoop c b)
    | _, _ => none
  | .doWhile _ _ => none
  | .ifStmt _ _ _ => none
  | .matchStmt _ _ => none
  | .nop => some .nop

/-- `toHIRStmt` over a statement list; one rejection fails the list. -/
def toHIRStmtList : List Syntax.Stmt → Option (List HIR.Stmt)
  | [] => some []
  | s :: ss =>
    match toHIRStmt s, toHIRStmtList ss with
    | some s', some ss' => some (s' :: ss')
    | _, _ => none

end

/-- Lower a surface program; `none` if any statement leaves the fragment. -/
def toHIRProgram : Syntax.Program → Option HIR.Program
  | ⟨stmts⟩ => toHIRStmtList stmts |>.map HIR.Program.mk

/-! ## The statement contract, pinned -/

/-- `break` lowers to itself. -/
theorem toHIRStmt_break : toHIRStmt .break = some .break := rfl

/-- `nop` lowers to itself. -/
theorem toHIRStmt_nop : toHIRStmt .nop = some .nop := rfl

/-- `doWhile` has no HIR counterpart (at-least-once vs HIR's `whileLoop`). -/
theorem toHIRStmt_doWhile_none (cond : Syntax.Expr) (body : List Syntax.Stmt) :
    toHIRStmt (.doWhile cond body) = none := rfl

/-- `ifStmt` has no HIR counterpart (HIR statements have no conditional). -/
theorem toHIRStmt_ifStmt_none (cond : Syntax.Expr) (th el : List Syntax.Stmt) :
    toHIRStmt (.ifStmt cond th el) = none := rfl

/-- `matchStmt` has no HIR counterpart (HIR statements have no match). -/
theorem toHIRStmt_matchStmt_none (scrut : Syntax.Expr)
    (arms : List (Syntax.Pattern × List Syntax.Stmt)) :
    toHIRStmt (.matchStmt scrut arms) = none := rfl

/-- Variable declarations keep their name at index 0. -/
theorem toHIRStmt_varDecl (init : Syntax.Expr) :
    toHIRStmt (.varDecl ⟨"y"⟩ .unitType init) =
      (toHIR init).map (fun e' => HIR.Stmt.varDecl ⟨0, "y"⟩ .unitType e') := rfl

/-- The empty program lowers to itself. -/
theorem toHIRProgram_empty : toHIRProgram ⟨[]⟩ = some ⟨[]⟩ := rfl

/-- Applying a variable function lowers structurally. -/
theorem toHIR_app_var (x : String) :
    toHIR (.app (.fvar x) []) = some (.app ⟨0, "free:" ++ x⟩ []) := rfl

end Morph.Frontend.HIRLower
