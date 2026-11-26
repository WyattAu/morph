/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIR

/-!
# HIR functions and the call-fragment lowering (Stage C item C8, HIR side)

Loop 186. The MIR half of single-level calls already executes
(`Morph.MIR.execInstrsCall`/`execBlockCall`/`execFuncCall` over
`MIR.Program.findFunc`), but the HIR side has nowhere to look a function
up: `HIR.Program` is just `{ stmts : List Stmt }`, while `evalHIR`'s `.app`
resolves its `Id` through the *environment* to a `lam` value
(`Morph.Frontend.HIREval`). This module is the HIR-side slice that closes
that gap, in the order the C8 design proposal sequences it:

1. **Functions beside programs, not instead of them.** `Func` is a named
   `lam` (`name`, `params`, `body : HIR.Expr`); `CallProg` pairs a function
   table with a `main` statement list. `Program`, `lowerProgram`, and the
   whole Branch leaf stack are untouched, so everything already proved
   keeps building — the C1 hedge move, replayed for C8.
2. **Statement-level calls first.** `lowerCallStmts` admits `.app` only
   directly under `varDecl`/`assign`/`returnStmt` — never nested inside
   `binop`/`unop`/`let`, where `lowerExpr` (which has no table) already
   returns `none`. Bare `.exprStmt (.app ..)` is refused: the oracle keeps
   the call's return value as the statement value, but `MIR.call` with
   `dst = none` discards it, so lowering it would lie. Actuals pass
   **reversed**: HIR `lam` params list innermost-first (mirroring de Bruijn
   levels — `toHIR` maps binder `j` to index `d + n - 1 - j`), so
   `params[j]` takes `argv[n-1-j]`, while MIR `bindCallArgs` binds
   positionally. Callee bodies must
   be `NoApp` (see below): the callee runs through the call-free block
   executor, which stalls on a nested `.call`, so a nested HIR call would
   succeed in the oracle and fail in MIR.
3. **The single-level ceiling is structural.** `exprNoApp`/`stmtNoApp`
   are executable (`Bool`) predicates: no `.app` anywhere in the subtree
   — including under `lam`, since a `lam` value can flow into a parameter
   position and be applied there. `lowerFunc` and every call arm refuse a
   body that fails the predicate, so recursion and mutual recursion lower
   to `none`, exactly what the MIR executor returns for them.

`FuncOk`/`CallProgOk` are the hypotheses the future C8c generalization
will carry; the end-to-end pin lives in `Morph.Proofs.Call.Evidence`.
-/

namespace Morph.HIRFunc

open Morph.HIR Morph.MIR Morph.Core Morph.HIRToMIR

/-! ## Functions beside programs -/

/-- A HIR function: a named `lam`. The body is an *expression* (like the
`lam` it mirrors), so callees lower to single-block MIR functions through
`lowerExpr`; branchy callees are a later stage. `name` is a full `HIR.Id`
so `.app fid` matches it directly; the MIR side sees `name.name`. -/
structure Func where
  name : HIR.Id
  params : List HIR.Id
  body : HIR.Expr
  deriving Repr

/-- A program with a function table: `funcs` plus a `main` statement list.
`main` is where (statement-level) calls live; it lowers to the `"main"`
MIR function, so no `Func` may be named `"main"` (`lowerCallProg` refuses
one — both `findHIRFunc` here and `MIR.findFunc` are first-match, and the
guard keeps the two tables' resolutions aligned). -/
structure CallProg where
  funcs : List Func
  main : List HIR.Stmt
  deriving Repr

/-- First-match lookup, mirroring `lookupHEnv` and `MIR.findFunc`. -/
def findHIRFunc : List Func → HIR.Id → Option Func
  | [], _ => none
  | f :: rest, id => if f.name = id then some f else findHIRFunc rest id

theorem findHIRFunc_cons_head (f : Func) (fs : List Func) :
    findHIRFunc (f :: fs) f.name = some f := by
  simp [findHIRFunc]

theorem findHIRFunc_cons_ne {f : Func} {fs : List Func} {id : HIR.Id}
    (h : ¬ f.name = id) : findHIRFunc (f :: fs) id = findHIRFunc fs id := by
  simp [findHIRFunc, h]

/-! ## The call-free predicate -/

/- No `.app` anywhere in the subtree. `lam` bodies recurse: a `lam`
value can flow into a parameter and be applied at the call site, so
allowing `app` under `lam` would smuggle a nested call past the
single-level ceiling. Explicit matches (no `List.all`): the termination
checker sees constructor arguments directly. -/
mutual
def exprNoApp : HIR.Expr → Bool
  | .app _ _ => false
  | .lam _ body => exprNoApp body
  | .unop _ e => exprNoApp e
  | .binop _ a b => exprNoApp a && exprNoApp b
  | .«let» _ init body => exprNoApp init && exprNoApp body
  | .ifThenElse c t f => exprNoApp c && exprNoApp t && exprNoApp f
  | .whileLoop c body => exprNoApp c && exprsNoApp body
  | .match s arms => exprNoApp s && matchExprsNoApp arms
  | .block es => exprsNoApp es
  | _ => true
def exprsNoApp : List HIR.Expr → Bool
  | [] => true
  | e :: es => exprNoApp e && exprsNoApp es
def matchExprsNoApp : List (Pattern × HIR.Expr) → Bool
  | [] => true
  | (_, e) :: arms => exprNoApp e && matchExprsNoApp arms
def stmtNoApp : HIR.Stmt → Bool
  | .exprStmt e => exprNoApp e
  | .varDecl _ _ init => exprNoApp init
  | .assign _ e => exprNoApp e
  | .returnStmt e => exprNoApp e
  | .whileLoop c body => exprNoApp c && stmtsNoApp body
  | .ifStmt c th el => exprNoApp c && stmtsNoApp th && stmtsNoApp el
  | .matchStmt s arms => exprNoApp s && matchStmtsNoApp arms
  | _ => true
def stmtsNoApp : List HIR.Stmt → Bool
  | [] => true
  | s :: ss => stmtNoApp s && stmtsNoApp ss
def matchStmtsNoApp : List (Pattern × List HIR.Stmt) → Bool
  | [] => true
  | (_, ss) :: arms => stmtsNoApp ss && matchStmtsNoApp arms
end

/-- A function is fragment-ok when its body is call-free. -/
def FuncOk (f : Func) : Prop := exprNoApp f.body = true

/-- A call program is fragment-ok when every callee body is call-free.
`main` is *not* required call-free — it is where the calls live; its
shape is enforced by `lowerCallStmts` (statement-level `.app` only). -/
def CallProgOk (p : CallProg) : Prop :=
  ∀ f ∈ p.funcs, FuncOk f

/-! ## Lowering: functions and statement-level calls -/

/-! ## Extraction: a parsed program becomes a `CallProg` -/

/-- Extract the call fragment from a parsed program: top-level
`varDecl name _ (.lam params body)` statements become the function table
(in source order) and every other statement stays in `main`. Refuses: a
duplicate function name, an assignment to a function name, and a program
with no functions (that is the straight-line fragment's job). -/
def toCallProg (p : HIR.Program) : Option CallProg :=
  go [] [] p.stmts
where
  go : List Func → List HIR.Stmt → List HIR.Stmt → Option CallProg
    | funcs, main, [] =>
        if funcs.isEmpty then none
        else some ⟨funcs.reverse, main.reverse⟩
    | funcs, main, .varDecl name _ (.lam params body) :: rest =>
        if funcs.any (fun f => f.name.name == name.name) then none
        else go (⟨name, params, body⟩ :: funcs) main rest
    | funcs, main, .assign name e :: rest =>
        if funcs.any (fun f => f.name.name == name.name) then none
        else go funcs (.assign name e :: main) rest
    | funcs, main, s :: rest => go funcs (s :: main) rest

/-- Lower call arguments left to right through `lowerExpr`, collecting
the argument registers. `lowerExpr` returns `none` on `.app`, so nested
calls in argument position are refused here, not later. -/
def lowerArgs (ρ : List (HIR.Id × ValId)) :
    Nat → List HIR.Expr → Option (List ValId × List Instr × Nat)
  | supply, [] => some ([], [], supply)
  | supply, a :: as =>
      match lowerExpr ρ supply a with
      | none => none
      | some (va, ia, s1) =>
          match lowerArgs ρ s1 as with
          | none => none
          | some (vs, ias, s2) => some (va :: vs, ia ++ ias, s2)

/-- Lower one function to a single-block MIR function. Parameters bind to
registers `1..n` (`0` stays the unit prologue, mirroring `lowerProgram`);
parameter types are unchecked metadata on both sides (`MIR.bindCallArgs`
ignores them), so they are `.unitType`. The body must be call-free: it
runs through the call-free block executor. -/
def lowerFunc (f : Func) : Option MIR.Func :=
  if exprNoApp f.body then
    let ρ := List.zip f.params (List.range' 1 f.params.length)
    match lowerExpr ρ (f.params.length + 1) f.body with
    | none => none
    | some (v, is, _) =>
        -- TODO (build-first item 1, next loop): the declared return type must
        -- be inferred from the body (MIR-side type inference over `is`/`v` --
        -- `Morph.Clif.bodyResultTyp` computes over CLIF instructions, which
        -- the lowering does not produce). Until then every callee is declared
        -- unit-typed, and the D-7 slot gate refuses call-bearing artifacts at
        -- emission (see docs/BUILD-FIRST-LEDGER.md).
        some ⟨f.name.name, (List.range' 1 f.params.length).map (·, .unitType),
          [⟨0, [.const 0 .unit] ++ is, .return_ v⟩], 0, .unitType⟩
  else none

/-- Lower straight-line statements with statement-level calls. Every
`lowerStmts` arm is mirrored (same register-file threading, same
`lastVal` accumulator discipline); control flow hits the same
`| _ :: _ => none`. Three arms are new:

- `varDecl`/`assign`/`returnStmt` directly over `.app fid args`: resolve
  `fid` in the table, check arity up front (the executor would fail it
  anyway via `bindCallArgs`), require a call-free callee body, lower the
  arguments, and emit one `.call` writing a fresh register — with the
  argument registers **reversed** (`vs.reverse`): HIR params are
  innermost-first (`params[j]` takes `argv[n-1-j]`), MIR formals bind
  positionally, so the call delivers actuals back-to-front. Forgetting
  the reversal is silent on commutative callees and wrong on the rest;
- bare `.exprStmt (.app ..)` is refused (the return value would be lost).
- `.app` anywhere else is already `none` via `lowerExpr`.

Takes the raw table (not an `Ok` proof) and re-checks each callee body,
so no caller can smuggle a nested call past the guard in `lowerFunc`. -/
def lowerCallStmts (tab : List Func) (ρ : List (HIR.Id × ValId))
    (supply : Nat) (lastVal : ValId) :
    List HIR.Stmt → Option (List (HIR.Id × ValId) × ValId × List Instr × Nat)
  | [] => some (ρ, lastVal, [], supply)
  | .exprStmt (.app _ _) :: _ => none
  | .exprStmt e :: rest =>
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerCallStmts tab ρ s1 v rest with
          | some (ρ', v', ie', s2) => some (ρ', v', ie ++ ie', s2)
          | none => none
      | none => none
  | .varDecl id _ (.app fid args) :: rest =>
      match findHIRFunc tab fid with
      | none => none
      | some f =>
          if f.params.length = args.length ∧ exprNoApp f.body then
            match lowerArgs ρ supply args with
            | none => none
            | some (vs, ias, s1) =>
                match lowerCallStmts tab ((id, s1) :: ρ) (s1 + 1) lastVal rest with
                | some (ρ', v', ia', s2) =>
                    some (ρ', v', ias ++ [.call (some s1) f.name.name vs.reverse] ++ ia', s2)
                | none => none
          else none
  | .varDecl id _ init :: rest =>
      match lowerExpr ρ supply init with
      | some (va, ia, s1) =>
          match lowerCallStmts tab ((id, va) :: ρ) s1 lastVal rest with
          | some (ρ', v', ia', s2) => some (ρ', v', ia ++ ia', s2)
          | none => none
      | none => none
  | .assign id (.app fid args) :: rest =>
      match findHIRFunc tab fid with
      | none => none
      | some f =>
          if f.params.length = args.length ∧ exprNoApp f.body then
            match lowerArgs ρ supply args with
            | none => none
            | some (vs, ias, s1) =>
                match lowerCallStmts tab (updAssoc ρ id s1) (s1 + 1) lastVal rest with
                | some (ρ', v', ia', s2) =>
                    some (ρ', v', ias ++ [.call (some s1) f.name.name vs.reverse] ++ ia', s2)
                | none => none
          else none
  | .assign id e :: rest =>
      match lowerExpr ρ supply e with
      | some (v, ie, s1) =>
          match lowerCallStmts tab (updAssoc ρ id v) s1 lastVal rest with
          | some (ρ', v', ie', s2) => some (ρ', v', ie ++ ie', s2)
          | none => none
      | none => none
  | .returnStmt (.app fid args) :: _ =>
      match findHIRFunc tab fid with
      | none => none
      | some f =>
          if f.params.length = args.length ∧ exprNoApp f.body then
            match lowerArgs ρ supply args with
            | none => none
            | some (vs, ias, s1) =>
                some (ρ, s1, ias ++ [.call (some s1) f.name.name vs.reverse], s1 + 1)
          else none
  | .returnStmt e :: _ =>
      (lowerExpr ρ supply e).map fun (v, ie, s1) => (ρ, v, ie, s1)
  | .nop :: rest => lowerCallStmts tab ρ supply lastVal rest
  | _ :: _ => none

/-- Lower a whole call program: every function through `lowerFunc`, then
`main` through `lowerCallStmts` wrapped as the `"main"` MIR function
(mirroring `lowerProgram`'s unit prologue). Refuses a `Func` named
`"main"`: it would shadow the entry under first-match resolution. -/
def lowerCallProg (p : CallProg) : Option MIR.Program :=
  if p.funcs.any (fun f => f.name.name == "main") then none
  else
    match p.funcs.mapM lowerFunc with
    | none => none
    | some funcsMIR =>
        match lowerCallStmts p.funcs [] 1 0 p.main with
        | none => none
        | some (_, v, is, _) =>
        -- TODO (build-first item 1): computed main return type, as above.
        some ⟨⟨"main", [], [⟨0, [.const 0 .unit] ++ is, .return_ v⟩],
          0, .unitType⟩ :: funcsMIR⟩

end Morph.HIRFunc
