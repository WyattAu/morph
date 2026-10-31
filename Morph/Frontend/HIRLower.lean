/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Syntax
import Morph.HIR

namespace Morph.Frontend.HIRLower

open Morph.Syntax

/-!
# HIR lowering — `Syntax.Expr` to `HIR.Expr` (loops 82–84)

The roadmap (§6.1) names HIR lowering as the remaining frontend step
after parsing: `Morph.HIR` already defines the target language, but
nothing mapped the surface AST into it. This module is that map, in the
codebase's established partial-lowering discipline (`Lowering.lowerIn`
returns `Option`, rejecting what it cannot represent, rather than
miscompiling it).

**Variable scheme (loop 84).** Loop 82 mapped every de Bruijn slot to
`Id ⟨n, "bv"⟩`, which is correct only for closed, binder-free paths: a
body occurrence under a binder means something different from the same
index outside it, and nested same-named slots collide. The pass now
threads the binder depth `d` (the `liftUnder`/`resolveExpr` discipline —
binders extend, everything else passes through):

- a bound occurrence `bvar n` with `n < d` refers to the binder at level
  `d - 1 - n`, whose HIR name is `⟨d - 1 - n, "bv"⟩`;
- `bvar n` with `n ≥ d` is an outer reference to context slot `n - d`,
  named `⟨n - d, "ctx"⟩` — depth-relative, hence stable when a `let`
  pushes (the slot number does not move, only the surface index does);
- free variables map to `Id ⟨0, "free:" ++ x⟩` at any depth;
- `let_` at depth `d` binds `⟨d, "bv"⟩` and lowers its body at `d + 1`;
- `lam n` at depth `d` binds `⟨d + n - 1, "bv"⟩ … ⟨d, "bv"⟩`
  innermost-first (mirroring the parser's `params ++ scope`) and lowers
  its body at `d + n`;
- `match_` arms extend by exactly the binders their pattern introduces
  (`var_` binds one; `wild`/`lit_` bind none — extending by zero matters:
  the body's `bvar 0` still means the enclosing binder).

`forLoop`'s iterator is anonymous *and* unreachable by name (loop 78b),
so there is no HIR name to give it: `forLoop` is rejected.

**Supported fragment** (everything else is `none`): `bvar`/`fvar`/`lit`/
`unop`/`binop`/`lam`/`let_`/`ifThenElse`/`block`, `app` whose function
is a variable (HIR application is call-by-`Id`), `pipe` whose target is
a variable (lowered as that application), `field_`/`typeAsc` (both
runtime-erased, so lowered like their subject), and `match_` over
`wild`/`lit_`/`var_` patterns. Rejected: `some_`/`none_`/`ok_`/`err_`
(HIR has no option/result constructors), `tuple_`/`arrayLit`/
`arrayIndex` (HIR has no tuple/array), all `ref*` (HIR has no store),
`forLoop` (above), `app` of a non-variable function, and arms with
`some_`/`ok_`/`err_`/`none_` patterns (HIR patterns are
`lit`/`wildcard`/`var` only).

Preservation against HIR evaluation lives in `Morph.Frontend.HIREval`:
closed first-order-plus-`let` terms evaluate to the same literal on
both sides. `lam`/`app`/`match_`/`whileLoop` lower structurally but are
outside the proved fragment (application needs a substitution lemma;
`match_`/`whileLoop` need their HIR evaluators pinned first).
-/

/-- Lower one identifier occurrence at depth `d` to an HIR variable. -/
def toHIRVarAt (d : Nat) : Syntax.Expr → Option HIR.Id
  | .bvar n => some (if n < d then ⟨d - 1 - n, "bv"⟩ else ⟨n - d, "ctx"⟩)
  | .fvar x => some ⟨0, "free:" ++ x⟩
  | _ => none

/-- `toHIRVarAt` at the top level. -/
def toHIRVar : Syntax.Expr → Option HIR.Id := toHIRVarAt 0

/-- Lower a surface pattern at depth `d`; `none` where HIR patterns stop.
Only `var_` extends the depth (by exactly one). -/
def toHIRPatAt (d : Nat) : Syntax.Pattern → Option HIR.Pattern
  | .wild => some .wildcard
  | .var_ _ => some (.var ⟨d, "bv"⟩)
  | .lit_ v => some (.lit v)
  | .some_ _ => none
  | .none_ => none
  | .ok_ _ => none
  | .err_ _ => none

/-- `toHIRPatAt` at the top level. -/
def toHIRPat : Syntax.Pattern → Option HIR.Pattern := toHIRPatAt 0

mutual

/-- Lower a surface expression at binder depth `d` to HIR;
`none` outside the fragment above. -/
def toHIRAt (d : Nat) : Syntax.Expr → Option HIR.Expr
  | .bvar n => some (.var (if n < d then ⟨d - 1 - n, "bv"⟩ else ⟨n - d, "ctx"⟩))
  | .fvar x => some (.var ⟨0, "free:" ++ x⟩)
  | .lit v => some (.lit v)
  | .unop op e => toHIRAt d e |>.map (.unop op ·)
  | .binop op a b =>
    match toHIRAt d a, toHIRAt d b with
    | some a', some b' => some (.binop op a' b')
    | _, _ => none
  | .app f args =>
    match toHIRVarAt d f, toHIRListAt d args with
    | some id, some args' => some (.app id args')
    | _, _ => none
  | .lam n body =>
    toHIRAt (d + n) body |>.map
      (.lam ((List.range n).map fun j => ⟨d + n - 1 - j, "bv"⟩) ·)
  | .let_ init body =>
    match toHIRAt d init, toHIRAt (d + 1) body with
    | some init', some body' => some (.let ⟨d, "bv"⟩ init' body')
    | _, _ => none
  | .ifThenElse c t f =>
    match toHIRAt d c, toHIRAt d t, toHIRAt d f with
    | some c', some t', some f' => some (.ifThenElse c' t' f')
    | _, _, _ => none
  | .forLoop _ _ _ => none
  | .block es => toHIRListAt d es |>.map .block
  | .match_ scrut arms =>
    match toHIRAt d scrut, toHIRArmsAt d arms with
    | some scrut', some arms' => some (.match scrut' arms')
    | _, _ => none
  | .field_ e _ => toHIRAt d e
  | .pipe a f =>
    match toHIRVarAt d f, toHIRAt d a with
    | some id, some a' => some (.app id [a'])
    | _, _ => none
  | .typeAsc e _ => toHIRAt d e
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

/-- `toHIRAt` at the top level: what `morph` and the tests call. -/
def toHIR : Syntax.Expr → Option HIR.Expr := toHIRAt 0

/-- `toHIRAt` over an expression list; one rejection fails the list. -/
def toHIRListAt (d : Nat) : List Syntax.Expr → Option (List HIR.Expr)
  | [] => some []
  | e :: es =>
    match toHIRAt d e, toHIRListAt d es with
    | some e', some es' => some (e' :: es')
    | _, _ => none

/-- `toHIRListAt` at the top level. -/
def toHIRList : List Syntax.Expr → Option (List HIR.Expr) := toHIRListAt 0

/-- `toHIRAt` over match arms; `var_` bodies lower one level deeper. -/
def toHIRArmsAt (d : Nat) : List (Syntax.Pattern × Syntax.Expr) →
    Option (List (HIR.Pattern × HIR.Expr))
  | [] => some []
  | (pat, body) :: rest =>
    match toHIRPatAt d pat, toHIRAt (d + patBindCount pat) body,
        toHIRArmsAt d rest with
    | some pat', some body', some rest' => some ((pat', body') :: rest')
    | _, _, _ => none

/-- `toHIRArmsAt` at the top level. -/
def toHIRArms : List (Syntax.Pattern × Syntax.Expr) →
    Option (List (HIR.Pattern × HIR.Expr)) := toHIRArmsAt 0

end

/-! ## The fragment predicate (for the preservation theorem)

`FirstOrder e`: `e` stays inside the proved fragment — literals,
variables, unop/binop, `let_`, `ifThenElse`, `block`, plus the three
runtime-transparent forms (`field_`/`typeAsc` erase, `pipe` is application),
and `match_` over the HIR-representable patterns (`wild`/`lit_`/`var_`;
loop 86). `lam`/`app` need a substitution lemma; everything else never
lowers. -/
inductive FirstOrder : Syntax.Expr → Prop where
  | lit : ∀ v, FirstOrder (.lit v)
  | bvar : ∀ n, FirstOrder (.bvar n)
  | fvar : ∀ x, FirstOrder (.fvar x)
  | unop : ∀ op e, FirstOrder e → FirstOrder (.unop op e)
  | binop : ∀ op a b, FirstOrder a → FirstOrder b → FirstOrder (.binop op a b)
  | let_ : ∀ init body, FirstOrder init → FirstOrder body →
      FirstOrder (.let_ init body)
  | ifThenElse : ∀ c t f, FirstOrder c → FirstOrder t → FirstOrder f →
      FirstOrder (.ifThenElse c t f)
  | block : ∀ es, (∀ e ∈ es, FirstOrder e) → FirstOrder (.block es)
  | field_ : ∀ e name, FirstOrder e → FirstOrder (.field_ e name)
  | pipe : ∀ a f, FirstOrder a → FirstOrder f → FirstOrder (.pipe a f)
  | typeAsc : ∀ e τ, FirstOrder e → FirstOrder (.typeAsc e τ)
  | match_ : ∀ scrut arms, FirstOrder scrut →
      (∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ arms →
        p = .wild ∨ (∃ l, p = .lit_ l) ∨ (∃ x, p = .var_ x)) →
      (∀ (p : Syntax.Pattern) (b : Syntax.Expr), (p, b) ∈ arms →
        FirstOrder b) →
      FirstOrder (.match_ scrut arms)

/-! ## The contract, pinned -/

/-- Literals lower to themselves, at any depth. -/
theorem toHIRAt_lit (d : Nat) (v : Morph.Core.Value) :
    toHIRAt d (.lit v) = some (.lit v) := rfl

/-- A bound occurrence names its binder level. -/
theorem toHIRAt_bvar_bound (d n : Nat) (h : n < d) :
    toHIRAt d (.bvar n) = some (.var ⟨d - 1 - n, "bv"⟩) := by
  simp [toHIRAt, h]

/-- An outer occurrence names its context slot. -/
theorem toHIRAt_bvar_outer (d n : Nat) (h : ¬ n < d) :
    toHIRAt d (.bvar n) = some (.var ⟨n - d, "ctx"⟩) := by
  simp [toHIRAt, h]

/-- Top-level slots are context slots (loop 84 changed this from `"bv"`:
a bare `⟨n, "bv"⟩` would collide with the binder that a `let` at depth
`n` introduces). -/
theorem toHIR_bvar (n : Nat) : toHIR (.bvar n) = some (.var ⟨n, "ctx"⟩) := rfl

/-- Free names are carried, collision-free against both namespaces. -/
theorem toHIR_fvar (x : String) :
    toHIR (.fvar x) = some (.var ⟨0, "free:" ++ x⟩) := rfl

/-- A `let` body sees its binder at level 0, outer slots untouched:
`let_ 5 (bvar 1)` with context `[10]` still finds `10`. -/
theorem toHIR_let_outer : toHIR (.let_ (.lit (.int 5)) (.bvar 1)) =
    some (.let ⟨0, "bv"⟩ (.lit (.int 5)) (.var ⟨0, "ctx"⟩)) := rfl

/-- Nested binders stack: the inner body sees both levels distinctly. -/
theorem toHIR_let_nested :
    toHIR (.let_ (.lit (.int 5))
      (.let_ (.lit (.int 6))
        (.binop .add (.bvar 0) (.bvar 1)))) =
    some (.let ⟨0, "bv"⟩ (.lit (.int 5))
      (.let ⟨1, "bv"⟩ (.lit (.int 6))
        (.binop .add (.var ⟨1, "bv"⟩) (.var ⟨0, "bv"⟩)))) := rfl

/-- Tuples have no HIR counterpart. -/
theorem toHIR_tuple_none (es : List Syntax.Expr) : toHIR (.tuple_ es) = none := rfl

/-- Field projection is runtime-erased, so it lowers like its receiver. -/
theorem toHIR_field (d : Nat) (e : Syntax.Expr) (name : String) :
    toHIRAt d (.field_ e name) = toHIRAt d e := rfl

/-- A pipeline lowers exactly like the application it runs as. -/
theorem toHIR_pipe (d : Nat) (a f : Syntax.Expr) :
    toHIRAt d (.pipe a f) =
      match toHIRVarAt d f, toHIRAt d a with
      | some id, some a' => some (.app id [a'])
      | _, _ => none := rfl

/-- Ascriptions are runtime-erased, so they lower like their subject. -/
theorem toHIR_typeAsc (d : Nat) (e : Syntax.Expr) (τ : Morph.Core.Typ) :
    toHIRAt d (.typeAsc e τ) = toHIRAt d e := rfl

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
  simp [toHIR, toHIRAt, toHIRVarAt]

/-- `some`-patterns have no HIR counterpart. -/
theorem toHIRPat_some_none (d : Nat) (p : Syntax.Pattern) :
    toHIRPatAt d (.some_ p) = none := rfl

/-- Applying a variable function lowers structurally. -/
theorem toHIR_app_var (x : String) :
    toHIR (.app (.fvar x) []) = some (.app ⟨0, "free:" ++ x⟩ []) := rfl

/-! ## Statement and program lowering (loop 83)

Surface statements are name-based (`Syntax.Id` is just a name; they never
entered the de Bruijn system), so lowering is scope-free: embedded
expressions go through `toHIR` (depth 0 — statement bodies never extend
the expression scope, the loop-84 regression pin in
`Morph/Tests/NameResolution`), and statement identifiers join the `free:`
namespace (`Id ⟨0, "free:" ++ name⟩` — loop 87: the loop-83 choice of
`⟨0, name⟩` disagreed with the expression pass, so no lowered program with
a variable could evaluate, and a statement variable named `"bv"` would
have captured binder slot 0. Surface identifiers never contain `':'`, so
the prefix is injective, and the `hirId_free_ne_bv/ctx` separation in
`Morph.Frontend.HIREval` keeps statement ids disjoint from binder and
slot ids).
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
  | .varDecl id ty init => toHIR init |>.map (.varDecl ⟨0, "free:" ++ id.name⟩ ty ·)
  | .assign id e => toHIR e |>.map (.assign ⟨0, "free:" ++ id.name⟩ ·)
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

/-- Variable declarations join the `free:` namespace (loop 87: this is what
the expression pass produces for the same name, so declaration and use
sites agree). -/
theorem toHIRStmt_varDecl (init : Syntax.Expr) :
    toHIRStmt (.varDecl ⟨"y"⟩ .unitType init) =
      (toHIR init).map (fun e' => HIR.Stmt.varDecl ⟨0, "free:y"⟩ .unitType e') := rfl

/-- The empty program lowers to itself. -/
theorem toHIRProgram_empty : toHIRProgram ⟨[]⟩ = some ⟨[]⟩ := rfl

/-! ## The statement fragment (loop 88)

A surface statement is in the proved fragment when every embedded
expression is `FirstOrder`. Lowering success alone does not imply this
(`toHIR` also maps `lam`/variable-applied `app`, whose preservation
needs the substitution lemma); the statement preservation theorem takes
both hypotheses. -/
def stmtFirstOrder : Syntax.Stmt → Prop
  | .exprStmt e => FirstOrder e
  | .varDecl _ _ init => FirstOrder init
  | .assign _ e => FirstOrder e
  | .returnStmt e => FirstOrder e
  | .whileLoop cond body =>
      FirstOrder cond ∧ ∀ s ∈ body, stmtFirstOrder s
  | .break => True
  | .continue => True
  | .nop => True
  | .doWhile _ _ => False
  | .ifStmt _ _ _ => False
  | .matchStmt _ _ => False

end Morph.Frontend.HIRLower
