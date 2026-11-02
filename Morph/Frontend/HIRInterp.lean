/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.HIREval
import Morph.Interp

/-!
# The HIR statement interpreter

Loop 87. Expression evaluation over HIR (`Morph.Frontend.HIREval.evalHIR`)
covers one expression; a lowered *program* is a statement sequence. This
module runs `HIR.Program`/`HIR.Stmt` over the same evaluator, mirroring
`Morph.Interp` stage by stage:

- the runtime environment is `HEnv` (identifier → value, first match wins);
  a declaration pushes a binding, an assignment updates the innermost one,
  and a loop body's environment is the next iteration's starting
  environment;
- expression positions evaluate with `evalHIR` seeded with 256 units of
  fuel, the same seed as surface `Executable.eval`, so exhaustion behavior
  agrees by construction;
- statement-level recursion (including `while` iterations) is bounded by an
  explicit fuel; exhaustion is `HFlow.stuck`, not divergence.

Only the statements HIR shares with the surface exist here — `whileLoop`
is the only control statement. `doWhile`/`ifStmt`/`matchStmt` never lower
(`Morph.Frontend.HIRLower`), so there is nothing to mirror for them.
-/

namespace Morph.Frontend.HIRInterp

open Morph.HIR
open Morph.Core
open Morph.Frontend.HIREval

/-- The HIR statement machine's outcome (mirrors `Interp.Flow`). -/
inductive HFlow where
  | value : HIR.Expr → HFlow
  | returned : HIR.Expr → HFlow
  | broke : HFlow
  | continued : HFlow
  | stuck : HFlow
  deriving Repr

/-- What one HIR statement sequence did, paired with the final environment. -/
abbrev HRan := HFlow × HEnv

/-- Replace the innermost binding of `id` (mirrors `Interp.updateBinding`).
Assignment never introduces a name: assigning to an undeclared identifier
leaves the environment unchanged. Propositional equality (via the
`DecidableEq HIR.Id` instance), matching `lookupHEnv`. -/
def updateHEnv : HEnv → HIR.Id → HIR.Expr → HEnv
  | [], _, _ => []
  | (j, w) :: rest, id, v =>
      if j = id then (j, v) :: rest else (j, w) :: updateHEnv rest id v

/-- A loop's own value is unit; remember the sequence's last expression
instead (an expression statement after the loop keeps its value). -/
def HFlow.replace : HFlow → HIR.Expr → HFlow
  | .value _, u => .value u
  | f, _ => f

mutual

/-- Run HIR statements to completion. `acc` carries the most recent
expression statement's value, so the sequence's value is its last
expression. Public (loop 88): the statement preservation theorem below
names this runner. -/
def runHIRStmts : Nat → HEnv → List HIR.Stmt → HFlow → HRan
  | 0, env, _, _ => (.stuck, env)
  | _ + 1, env, [], acc => (acc, env)
  | fuel + 1, env, .nop :: rest, acc => runHIRStmts fuel env rest acc
  | fuel + 1, env, .exprStmt e :: rest, _ =>
      match evalHIR 256 env e with
      | none => (.stuck, env)
      | some v => runHIRStmts fuel env rest (.value v)
  | fuel + 1, env, .varDecl id _ init :: rest, acc =>
      match evalHIR 256 env init with
      | none => (.stuck, env)
      | some v => runHIRStmts fuel ((id, v) :: env) rest acc
  | fuel + 1, env, .assign id e :: rest, acc =>
      match evalHIR 256 env e with
      | none => (.stuck, env)
      | some v => runHIRStmts fuel (updateHEnv env id v) rest acc
  | _fuel + 1, env, .returnStmt e :: _, _ =>
      match evalHIR 256 env e with
      | none => (.stuck, env)
      | some v => (.returned v, env)
  | _ + 1, env, .break :: _, _acc => (.broke, env)
  | _ + 1, env, .continue :: _, _acc => (.continued, env)
  | fuel + 1, env, .whileLoop cond body :: rest, acc =>
      match runHIRWhile fuel env cond body with
      | (.value u, env') => runHIRStmts fuel env' rest (acc.replace u)
      | (f, env') => (f, env')
  | fuel + 1, env, .ifStmt cond th el :: rest, acc =>
      match evalHIR 256 env cond with
      | some (.lit (.bool true)) =>
        match runHIRStmts fuel env th (.value (.lit .unit)) with
        | (.value u, env') => runHIRStmts fuel env' rest (acc.replace u)
        | (f, env') => (f, env')
      | some (.lit (.bool false)) =>
        match runHIRStmts fuel env el (.value (.lit .unit)) with
        | (.value u, env') => runHIRStmts fuel env' rest (acc.replace u)
        | (f, env') => (f, env')
      | _ => (.stuck, env)
  | fuel + 1, env, .matchStmt scrut arms :: rest, acc =>
      match evalHIR 256 env scrut with
      | none => (.stuck, env)
      | some v =>
        match runHIRMatchArms fuel env v arms with
        | (.value u, env') => runHIRStmts fuel env' rest (acc.replace u)
        | (f, env') => (f, env')

/-- `while (cond) body`: one fuel unit per iteration; the body's final
environment is the next iteration's starting environment. `break` exits
the loop as completed; `continue` starts the next iteration; `return`
propagates. The loop's own value is unit. Public (loop 88): named by
the statement preservation theorem. -/
def runHIRWhile (fuel : Nat) (env : HEnv) (cond : HIR.Expr)
    (body : List HIR.Stmt) : HRan :=
  match fuel with
  | 0 => (.stuck, env)
  | fuel + 1 =>
    match evalHIR 256 env cond with
    | some (.lit (.bool true)) =>
      match runHIRStmts fuel env body (.value (.lit .unit)) with
      | (.broke, env') => (.value (.lit .unit), env')
      | (.continued, env') => runHIRWhile fuel env' cond body
      | (.value _, env') => runHIRWhile fuel env' cond body
      | (f, env') => (f, env')
    | some (.lit (.bool false)) => (.value (.lit .unit), env)
    | _ => (.stuck, env)

/-- Bound ids of an HIR statement pattern (`var` binds one, else none). -/
def hirPatVars : HIR.Pattern → List HIR.Id
  | .var id => [id]
  | _ => []

/-- First-match-wins over HIR statement-match arms, mirroring
`Interp.runMatchArms`: a hit runs the arm body with the pattern's bindings
pushed; no hit is unit. -/
def runHIRMatchArms (fuel : Nat) (env : HEnv) (v : HIR.Expr)
    (arms : List (HIR.Pattern × List HIR.Stmt)) : HRan :=
  match fuel with
  | 0 => (.stuck, env)
  | fuel + 1 =>
    match arms with
    | [] => (.value (.lit .unit), env)
    | (pat, body) :: rest =>
      match matchHIRPat pat v with
      | some vs =>
        runHIRStmts fuel ((hirPatVars pat).zip vs ++ env) body
          (.value (.lit .unit))
      | none => runHIRMatchArms fuel env v rest

end

/-- Run a whole HIR program: 1024 statement-level fuel units (one per
statement, per `while` iteration), empty starting environment — the same
seed as `Interp.runProgram`. -/
def runHIRProgram (prog : HIR.Program) : HFlow :=
  (runHIRStmts 1024 [] prog.stmts (.value (.lit .unit))).1

/-! ## Statement-level preservation (loop 88)

`evalHIR_preservation` agrees on one expression. This section lifts it
to statements: when `toHIRStmtList ss = some ss'` and every embedded
expression is `FirstOrder`, related environments stay related and
surface success is HIR success — for statements and `while` loops,
mutually, by induction on fuel.

The relation is lookup-based (`relStmtEnv`): every surface
free-variable lookup succeeds with a literal the HIR side sees under
the `free:` id. Shadowed bindings are invisible on both sides
(`getFv?`/`lookupHEnv` are first-match-wins), so nothing is demanded
of them — and the all-literal invariant the expression bridge needs
comes along for free.

The statement is one-directional (surface success implies HIR
agreement), like `evalHIR_preservation`: a stuck surface run imposes
nothing, so failure coincidence never has to be proved.
-/

open Morph.Executable
open Morph.Frontend.HIRLower
open Morph.Interp
open Morph.Syntax

/-- Statement environments agree: every surface free-variable lookup
succeeds with a literal the HIR side sees under the `free:` id. -/
def relStmtEnv (env : List (String × Syntax.Expr)) (henv : HEnv) : Prop :=
  ∀ x v, (ctxOf env).getFv? x = some v →
    ∃ w, v = .lit w ∧ lookupHEnv henv ⟨0, "free:" ++ x⟩ = some (.lit w)

/-- Related values are equal literals, existentially packaged so both
construction and inversion are one step. The fragment never produces
anything else (`fo_eval_is_lit`), so preservation only ever agrees on
literals. -/
def relVal (v : Syntax.Expr) (v' : HIR.Expr) : Prop :=
  ∃ w, v = .lit w ∧ v' = .lit w

/-- Related outcomes: same shape, related values — except a stuck
surface run, which imposes nothing (one-directional preservation). -/
def relFlowFwd : Flow → HFlow → Prop
  | .value v, .value v' => relVal v v'
  | .returned v, .returned v' => relVal v v'
  | .broke, .broke => True
  | .continued, .continued => True
  | .stuck, _ => True
  | _, _ => False

/-- Forward agreement of full runner results: either the surface run is
stuck (no claim), or flows agree and environments stay related. -/
def agreeFwd (r : Ran) (hr : HRan) : Prop :=
  (r.1 = .stuck) ∨ (relFlowFwd r.1 hr.1 ∧ relStmtEnv r.2 hr.2)

/-- Statement environments have an empty de Bruijn stack. -/
theorem ctxOf_getBv?_none (env : List (String × Syntax.Expr)) (n : Nat) :
    (ctxOf env).getBv? n = none := by
  rfl

/-- `free:` ids are injective in the name. -/
theorem hirId_free_eq {x y : String} :
    (⟨0, "free:" ++ x⟩ : HIR.Id) = ⟨0, "free:" ++ y⟩ ↔ x = y := by
  constructor
  · intro h
    have hn := congrArg HIR.Id.name h
    simp only at hn
    have htl := congrArg String.toList hn
    rw [String.toList_append, String.toList_append] at htl
    obtain ⟨_, htail⟩ :=
      List.append_inj htl (rfl : ("free:".toList).length = ("free:".toList).length)
    have hof := congrArg String.ofList htail
    simpa using hof
  · intro h
    rw [h]

/-- Lookup over an extended surface environment. -/
theorem getFv?_cons (x : String) (v : Syntax.Expr)
    (env : List (String × Syntax.Expr)) (y : String) :
    (ctxOf ((x, v) :: env)).getFv? y =
      if x = y then some v else (ctxOf env).getFv? y := by
  simp only [ctxOf, Context.getFv?, List.findSome?]
  by_cases h : x = y
  · subst h
    simp
  · simp [beq_iff_eq, h]

/-- Propositional form of `updateBinding` over a cons: the Bool test
becomes a Prop test, so `if_pos`/`if_neg` apply directly. -/
theorem updateBinding_cons (n : String) (u : Syntax.Expr)
    (rest : List (String × Syntax.Expr)) (x : String) (w : Syntax.Expr) :
    updateBinding ((n, u) :: rest) x w =
      if n = x then (n, w) :: rest
      else (n, u) :: updateBinding rest x w := by
  simp only [updateBinding]
  by_cases h : n = x
  · subst n
    simp
  · simp only [beq_iff_eq, h, if_false]

/-- The surface statement context is all-literal whenever environments
are related. -/
theorem envAllLit_ctxOf {env : List (String × Syntax.Expr)} {henv : HEnv}
    (hrel : relStmtEnv env henv) : envAllLit (ctxOf env) := by
  refine ⟨?_, ?_⟩
  · intro n v hget
    rw [ctxOf_getBv?_none] at hget
    cases hget
  · intro x v hget
    obtain ⟨w, rfl, _⟩ := hrel x v hget
    exact ⟨_, rfl⟩

/-- Related statement environments induce the depth-0 expression
relation. -/
theorem relEnvAt_zero {env : List (String × Syntax.Expr)} {henv : HEnv}
    (hrel : relStmtEnv env henv) : relEnvAt 0 (ctxOf env) henv := by
  refine ⟨?_, ?_, ?_⟩
  · intro n w _ hget
    rw [ctxOf_getBv?_none] at hget
    cases hget
  · intro k w hlt _
    omega
  · intro x w hget
    obtain ⟨w', heq, hlook⟩ := hrel x (.lit w) hget
    have hw : w = w' := by simpa using heq
    subst hw
    exact hlook

/-- Expression preservation at statement level: surface `eval`
(= `evalWithFuel 256`) agrees with `evalHIR 256` on the fragment. -/
theorem evalHIR_of_eval {env : List (String × Syntax.Expr)} {henv : HEnv}
    {e : Syntax.Expr} {e' : HIR.Expr} {w : Value}
    (hfo : FirstOrder e) (hlower : toHIR e = some e')
    (hrel : relStmtEnv env henv)
    (heval : evalWithFuel 256 (ctxOf env) e = some (.lit w)) :
    evalHIR 256 henv e' = some (.lit w) := by
  have hlower0 : toHIRAt 0 e = some e' := hlower
  exact evalHIR_preservation 256 0 (ctxOf env) henv e e' w hfo hlower0
    (relEnvAt_zero hrel) (envAllLit_ctxOf hrel) heval

/-- `updateHEnv` lookup at the updated id. -/
theorem lookupHEnv_updateHEnv_head (henv : HEnv) (id : HIR.Id)
    (w : HIR.Expr) :
    lookupHEnv (updateHEnv henv id w) id =
      (lookupHEnv henv id).map fun _ => w := by
  induction henv with
  | nil => simp [updateHEnv, lookupHEnv]
  | cons hd tl ih =>
    obtain ⟨k, u⟩ := hd
    by_cases h : k = id
    · subst h
      simp [updateHEnv, lookupHEnv]
    · simp [updateHEnv, lookupHEnv, h, ih]

/-- `updateHEnv` lookup away from the updated id. -/
theorem lookupHEnv_updateHEnv_ne (henv : HEnv) (id : HIR.Id)
    (w : HIR.Expr) : ∀ (j : HIR.Id), j ≠ id →
    lookupHEnv (updateHEnv henv id w) j = lookupHEnv henv j := by
  induction henv with
  | nil =>
    intro j _
    simp [updateHEnv, lookupHEnv]
  | cons hd tl ih =>
    obtain ⟨k, u⟩ := hd
    intro j hj
    by_cases h : k = id
    · subst h
      by_cases h2 : j = k
      · subst h2
        exact (hj rfl).elim
      · simp [updateHEnv, lookupHEnv, Ne.symm h2]
    · by_cases h2 : j = k
      · subst h2
        simp [updateHEnv, lookupHEnv, h]
      · simp [updateHEnv, lookupHEnv, h, ih j hj]

/-- Surface update lookup characterization. -/
theorem getFv?_updateBinding (env : List (String × Syntax.Expr))
    (x : String) (w : Syntax.Expr) (y : String) :
    (ctxOf (updateBinding env x w)).getFv? y =
      if y = x then ((ctxOf env).getFv? y).map (fun _ => w)
      else (ctxOf env).getFv? y := by
  induction env with
  | nil =>
    by_cases hy : y = x <;>
      simp [updateBinding, hy, ctxOf, Context.getFv?]
  | cons hd tl ih =>
    obtain ⟨n, u⟩ := hd
    rw [updateBinding_cons]
    by_cases hn : n = x
    · subst n
      by_cases hy : y = x
      · subst y
        simp [getFv?_cons]
      · simp [getFv?_cons, hy, Ne.symm hy]
    · by_cases hy : y = x
      · have hny : n ≠ y := fun hcon => hn (hcon.trans hy)
        simp only [if_neg hn, getFv?_cons, if_neg hny, ih, if_pos hy]
      · by_cases hny : n = y
        · subst n
          simp [getFv?_cons, hy]
        · simp [getFv?_cons, hny, hy, hn, ih]

/-- Declaration preserves the environment relation. -/
theorem relStmtEnv_push {env : List (String × Syntax.Expr)} {henv : HEnv}
    {x : String} {w : Value} (hrel : relStmtEnv env henv) :
    relStmtEnv ((x, .lit w) :: env)
      ((⟨0, "free:" ++ x⟩, .lit w) :: henv) := by
  intro y v hget
  rw [getFv?_cons] at hget
  by_cases hy : x = y
  · rw [if_pos hy] at hget
    have hv : .lit w = v := Option.some.inj hget
    subst hv
    subst y
    exact ⟨w, rfl, lookupHEnv_cons_head _ _ _⟩
  · rw [if_neg hy] at hget
    obtain ⟨w', heq, hlook⟩ := hrel y v hget
    refine ⟨w', heq, ?_⟩
    have hne : (⟨0, "free:" ++ x⟩ : HIR.Id) ≠ ⟨0, "free:" ++ y⟩ := by
      intro hcon
      exact hy (hirId_free_eq.mp hcon)
    rw [lookupHEnv_cons_ne hne]
    exact hlook

/-- Assignment preserves the environment relation. -/
theorem relStmtEnv_update {env : List (String × Syntax.Expr)}
    {henv : HEnv} {x : String} {w : Value}
    (hrel : relStmtEnv env henv) :
    relStmtEnv (updateBinding env x (.lit w))
      (updateHEnv henv ⟨0, "free:" ++ x⟩ (.lit w)) := by
  intro y v hget
  rw [getFv?_updateBinding] at hget
  by_cases hy : y = x
  · rw [if_pos hy] at hget
    cases hm : (ctxOf env).getFv? y with
    | none => simp [hm] at hget
    | some u =>
      simp only [hm, Option.map_some, Option.some.injEq] at hget
      subst hget
      obtain ⟨w', _, hlook⟩ := hrel y u hm
      subst hy
      refine ⟨w, rfl, ?_⟩
      simp only [lookupHEnv_updateHEnv_head, hlook, Option.map_some]
  · rw [if_neg hy] at hget
    obtain ⟨w', heq, hlook⟩ := hrel y v hget
    refine ⟨w', heq, ?_⟩
    have hne : (⟨0, "free:" ++ y⟩ : HIR.Id) ≠ ⟨0, "free:" ++ x⟩ := by
      intro hcon
      exact hy (hirId_free_eq.mp hcon)
    rw [lookupHEnv_updateHEnv_ne _ _ _ _ hne]
    exact hlook

/-- The empty environments are related. -/
theorem relStmtEnv_nil : relStmtEnv [] [] := by
  intro x v hget
  simp [ctxOf, Context.getFv?] at hget

/-- A statement pattern that lowers is wild/lit/var, with the expected HIR image. -/
theorem toHIRStmtPat_shape {pat : Syntax.Pattern} {pat' : HIR.Pattern}
    (h : toHIRStmtPat pat = some pat') :
    (pat = .wild ∧ pat' = .wildcard) ∨
      (∃ v, pat = .lit_ v ∧ pat' = .lit v) ∨
      (∃ x, pat = .var_ x ∧ pat' = .var ⟨0, "free:" ++ x⟩) := by
  cases pat with
  | wild => simp [toHIRStmtPat] at h; subst h; exact Or.inl ⟨rfl, rfl⟩
  | var_ x => simp [toHIRStmtPat] at h; subst h; exact Or.inr (Or.inr ⟨x, rfl, rfl⟩)
  | lit_ v => simp [toHIRStmtPat] at h; subst h; exact Or.inr (Or.inl ⟨v, rfl, rfl⟩)
  | some_ p => simp [toHIRStmtPat] at h
  | none_ => simp [toHIRStmtPat] at h
  | ok_ p => simp [toHIRStmtPat] at h
  | err_ p => simp [toHIRStmtPat] at h

/-- Fragment arms give fragment bodies. -/
theorem stmtArmsFirstOrder_mem {arms : List (Syntax.Pattern × List Syntax.Stmt)} :
    ∀ {pat : Syntax.Pattern} {body : List Syntax.Stmt} {s : Syntax.Stmt},
    (pat, body) ∈ arms → stmtArmsFirstOrder arms → s ∈ body →
      stmtFirstOrder s := by
  induction arms with
  | nil => intro pat body s hmem _ _; simp at hmem
  | cons hd tl ih =>
    intro pat body s hmem hfo hs
    obtain ⟨p0, b0⟩ := hd
    simp only [stmtArmsFirstOrder] at hfo
    obtain ⟨hhead, htail⟩ := hfo
    simp at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact hhead s hs
    · exact ih hmem htail hs

/-- Lowered arms contain exactly the lowered images (membership lift). -/
theorem toHIRStmtArms_mem {arms : List (Syntax.Pattern × List Syntax.Stmt)}
    {arms' : List (HIR.Pattern × List HIR.Stmt)}
    (h : toHIRStmtArms arms = some arms')
    {pat : Syntax.Pattern} {body : List Syntax.Stmt}
    (hmem : (pat, body) ∈ arms) :
    ∃ pat' body', toHIRStmtPat pat = some pat' ∧
      toHIRStmtList body = some body' ∧ (pat', body') ∈ arms' := by
  induction arms generalizing arms' with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨p0, b0⟩ := hd
    obtain ⟨pat0', body0', rest', hp0, hb0, hr, rfl⟩ := toHIRStmtArms_cons h
    simp at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact ⟨pat0', body0', hp0, hb0, List.mem_cons_self⟩
    · obtain ⟨pat', body', hp, hb, hmem'⟩ := ih hr hmem
      exact ⟨pat', body', hp, hb, List.mem_cons_of_mem _ hmem'⟩

/-- Wild and lit patterns bind nothing on both sides. -/
theorem matchStmtPat_nobind {pat : Syntax.Pattern} {pat' : HIR.Pattern} {w : Value}
    (hlower : toHIRStmtPat pat = some pat')
    (hnobind : pat = .wild ∨ ∃ v, pat = .lit_ v)
    {vs : List Syntax.Expr} (h : matchPat pat (.lit w) = some vs) :
    vs = [] ∧ matchHIRPat pat' (.lit w) = some [] := by
  rcases hnobind with rfl | ⟨v, rfl⟩
  · simp [toHIRStmtPat] at hlower; subst hlower
    simp only [matchPat] at h
    cases h
    exact ⟨rfl, rfl⟩
  · simp [toHIRStmtPat] at hlower; subst hlower
    cases heq : (v == w)
    · have hnone : matchPat (Syntax.Pattern.lit_ v) (.lit w) = none := by
        simp [matchPat, heq]
      rw [hnone] at h
      cases h
    · simp only [matchPat, heq] at h
      cases h
      exact ⟨rfl, by simp [matchHIRPat, heq]⟩

/-- A `var` match binds the scrutinee value on both sides, preserving relation. -/
theorem relStmtEnv_match_var {env : List (String × Syntax.Expr)} {henv : HEnv}
    (hrel : relStmtEnv env henv) {x : String} {w : Value} :
    relStmtEnv ((x, Syntax.Expr.lit w) :: env)
      ((⟨0, "free:" ++ x⟩, HIR.Expr.lit w) :: henv) := by
  intro y v' hget
  rw [getFv?_cons] at hget
  by_cases hy : x = y
  · rw [if_pos hy] at hget
    have hv' : Syntax.Expr.lit w = v' := Option.some.inj hget
    subst hv'
    subst hy
    exact ⟨w, rfl, lookupHEnv_cons_head _ _ _⟩
  · rw [if_neg hy] at hget
    obtain ⟨w', heq, hlook⟩ := hrel y v' hget
    refine ⟨w', heq, ?_⟩
    have hne : (⟨0, "free:" ++ x⟩ : HIR.Id) ≠ ⟨0, "free:" ++ y⟩ := by
      intro hcon
      exact hy (hirId_free_eq.mp hcon)
    rw [lookupHEnv_cons_ne hne]
    exact hlook

/-- Inversion for the map-shaped lowering arms (`exprStmt`, `varDecl`,
`assign`, `returnStmt`). -/
theorem toHIRStmt_map_arm {e : Syntax.Expr} {s' : HIR.Stmt}
    {f : HIR.Expr → HIR.Stmt} (h : (toHIR e).map f = some s') :
    ∃ e', toHIR e = some e' ∧ s' = f e' := by
  cases he : toHIR e with
  | none => simp [he] at h
  | some e' =>
    simp [he] at h
    exact ⟨e', rfl, h.symm⟩

/-- Inversion for `toHIRStmtList` over a cons. -/
theorem toHIRStmtList_cons {s : Syntax.Stmt} {ss : List Syntax.Stmt}
    {ss' : List HIR.Stmt} (h : toHIRStmtList (s :: ss) = some ss') :
    ∃ s' rest', toHIRStmt s = some s' ∧ toHIRStmtList ss = some rest' ∧
      ss' = s' :: rest' := by
  cases hs : toHIRStmt s with
  | none => simp only [toHIRStmtList, hs, reduceCtorEq] at h
  | some s' =>
    cases hss : toHIRStmtList ss with
    | none => simp only [toHIRStmtList, hs, hss, reduceCtorEq] at h
    | some rest' =>
      simp only [toHIRStmtList, hs, hss] at h
      exact ⟨s', rest', rfl, rfl, (Option.some.inj h).symm⟩

/-- Inversion for a lowered `whileLoop`. -/
theorem toHIRStmt_while {cond : Syntax.Expr} {body : List Syntax.Stmt}
    {ss' : HIR.Stmt} (h : toHIRStmt (.whileLoop cond body) = some ss') :
    ∃ cond' body', toHIR cond = some cond' ∧
      toHIRStmtList body = some body' ∧
      ss' = .whileLoop cond' body' := by
  cases hc : toHIR cond with
  | none => simp only [toHIRStmt, hc, reduceCtorEq] at h
  | some cond' =>
    cases hb : toHIRStmtList body with
    | none => simp only [toHIRStmt, hc, hb, reduceCtorEq] at h
    | some body' =>
      simp only [toHIRStmt, hc, hb] at h
      exact ⟨cond', body', rfl, rfl, (Option.some.inj h).symm⟩

/-- A related value outcome is a literal on both sides. -/
theorem relFlowFwd_value {v : Syntax.Expr} {H : HFlow}
    (h : relFlowFwd (.value v) H) :
    ∃ hv, H = .value hv ∧ relVal v hv := by
  cases H with
  | value hv => exact ⟨hv, rfl, h⟩
  | returned _ => exact False.elim h
  | broke => exact False.elim h
  | continued => exact False.elim h
  | stuck => exact False.elim h

/-- A related returned outcome is a literal on both sides. -/
theorem relFlowFwd_returned {v : Syntax.Expr} {H : HFlow}
    (h : relFlowFwd (.returned v) H) :
    ∃ hv, H = .returned hv ∧ relVal v hv := by
  cases H with
  | returned hv => exact ⟨hv, rfl, h⟩
  | value _ => exact False.elim h
  | broke => exact False.elim h
  | continued => exact False.elim h
  | stuck => exact False.elim h

/-- A related `break` is a `break`. -/
theorem relFlowFwd_broke {H : HFlow} (h : relFlowFwd (.broke) H) :
    H = .broke := by
  cases H with
  | broke => rfl
  | value _ => exact False.elim h
  | returned _ => exact False.elim h
  | continued => exact False.elim h
  | stuck => exact False.elim h

/-- A related `continue` is a `continue`. -/
theorem relFlowFwd_continued {H : HFlow} (h : relFlowFwd (.continued) H) :
    H = .continued := by
  cases H with
  | continued => rfl
  | value _ => exact False.elim h
  | returned _ => exact False.elim h
  | broke => exact False.elim h
  | stuck => exact False.elim h

/-- Replacing the accumulator value preserves outcome agreement. -/
theorem relFlow_replace {f : Flow} {h : HFlow} {u : Syntax.Expr}
    {hu : HIR.Expr} (hrel : relFlowFwd f h) (huv : relVal u hu) :
    relFlowFwd (Flow.replace f u) (HFlow.replace h hu) := by
  cases f <;> cases h <;> simp_all [Flow.replace, HFlow.replace, relFlowFwd]

/-- Identical related outcomes agree (nil arms). -/
theorem agreeFwd_refl (acc : Flow) (hacc : HFlow)
    {env : List (String × Syntax.Expr)} {henv : HEnv}
    (hrel : relStmtEnv env henv) (h : relFlowFwd acc hacc) :
    agreeFwd (acc, env) (hacc, henv) := by
  cases acc with
  | stuck => exact Or.inl rfl
  | value v =>
    cases hacc with
    | value _ => exact Or.inr ⟨h, hrel⟩
    | returned _ => exact False.elim h
    | broke => exact False.elim h
    | continued => exact False.elim h
    | stuck => exact False.elim h
  | returned v =>
    cases hacc with
    | returned _ => exact Or.inr ⟨h, hrel⟩
    | value _ => exact False.elim h
    | broke => exact False.elim h
    | continued => exact False.elim h
    | stuck => exact False.elim h
  | broke =>
    cases hacc with
    | broke => exact Or.inr ⟨trivial, hrel⟩
    | value _ => exact False.elim h
    | returned _ => exact False.elim h
    | continued => exact False.elim h
    | stuck => exact False.elim h
  | continued =>
    cases hacc with
    | continued => exact Or.inr ⟨trivial, hrel⟩
    | value _ => exact False.elim h
    | returned _ => exact False.elim h
    | broke => exact False.elim h
    | stuck => exact False.elim h

/-- Statement agreement at fuel `fuel`: all lowered statement runs
agree and all lowered `while` runs agree. The `while` case of
statements needs agreement at the same fuel, and loop bodies recurse
at the predecessor fuel — hence the conjunction, proved by induction
on fuel. -/
theorem agreeBoth : ∀ (fuel : Nat),
    (∀ (env : List (String × Syntax.Expr)) (henv : HEnv)
      (ss : List Syntax.Stmt) (ss' : List HIR.Stmt)
      (acc : Flow) (hacc : HFlow),
      toHIRStmtList ss = some ss' →
      (∀ s ∈ ss, stmtFirstOrder s) →
      relStmtEnv env henv → relFlowFwd acc hacc →
      agreeFwd (runStmts fuel env ss acc)
        (runHIRStmts fuel henv ss' hacc))
    ∧ (∀ (env : List (String × Syntax.Expr)) (henv : HEnv)
      (cond : Syntax.Expr) (cond' : HIR.Expr)
      (body : List Syntax.Stmt) (body' : List HIR.Stmt),
      toHIR cond = some cond' → toHIRStmtList body = some body' →
      FirstOrder cond → (∀ s ∈ body, stmtFirstOrder s) →
      relStmtEnv env henv →
      agreeFwd (runWhile fuel env cond body)
        (runHIRWhile fuel henv cond' body'))
    ∧ (∀ (env : List (String × Syntax.Expr)) (henv : HEnv)
      (v : Value) (arms : List (Syntax.Pattern × List Syntax.Stmt))
      (arms' : List (HIR.Pattern × List HIR.Stmt)),
      toHIRStmtArms arms = some arms' →
      (∀ (p : Syntax.Pattern) (b : List Syntax.Stmt), (p, b) ∈ arms →
        p = .wild ∨ (∃ l, p = .lit_ l) ∨ (∃ x, p = .var_ x)) →
      stmtArmsFirstOrder arms →
      relStmtEnv env henv →
      agreeFwd (runMatchArms fuel env (.lit v) arms)
        (runHIRMatchArms fuel henv (.lit v) arms')) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro env henv ss ss' acc hacc hlower hfo hrel hflow
      simp only [runStmts, runHIRStmts]
      exact Or.inl rfl
    · intro env henv cond cond' body body' hcond hbody hfo_c hfo_b hrel
      simp only [runWhile, runHIRWhile]
      exact Or.inl rfl
    · intro env henv v arms arms' hlower hpat hfo hrel
      simp only [runMatchArms, runHIRMatchArms]
      exact Or.inl rfl
  | succ f ih =>
    obtain ⟨ihS, ihW, ihM⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro env henv ss ss' acc hacc hlower hfo hrel hflow
      cases ss with
      | nil =>
        cases ss' with
        | nil =>
          simp only [toHIRStmtList] at hlower
          cases hlower
          simp only [runStmts, runHIRStmts]
          exact agreeFwd_refl _ _ hrel hflow
        | cons =>
          simp only [toHIRStmtList] at hlower
          cases hlower
      | cons s rest =>
        obtain ⟨s', rest', hs, hss, rfl⟩ := toHIRStmtList_cons hlower
        have hfo_s := hfo s (List.mem_cons.mpr (Or.inl rfl))
        have hfo_rest : ∀ t ∈ rest, stmtFirstOrder t :=
          fun t ht => hfo t (List.mem_cons_of_mem s ht)
        match s with
        | .nop =>
          rw [toHIRStmt_nop] at hs
          cases hs
          simp only [runStmts, runHIRStmts]
          exact ihS env henv rest rest' acc hacc hss hfo_rest hrel hflow
        | .exprStmt e =>
          have hfo_e : FirstOrder e := by simpa [stmtFirstOrder] using hfo_s
          simp only [toHIRStmt] at hs
          obtain ⟨e', he, rfl⟩ := toHIRStmt_map_arm hs
          simp only [runStmts, runHIRStmts]
          cases hev : eval (ctxOf env) e with
          | none => exact Or.inl rfl
          | some v =>
            have hev256 : evalWithFuel 256 (ctxOf env) e = some v := hev
            obtain ⟨w, rfl⟩ := fo_eval_is_lit 256 (ctxOf env) e v hfo_e
              (envAllLit_ctxOf hrel) hev256
            have hhe := evalHIR_of_eval hfo_e he hrel hev256
            simp only [hhe]
            exact ihS env henv rest rest' (.value (.lit w))
              (.value (.lit w)) hss hfo_rest hrel ⟨w, rfl, rfl⟩
        | .varDecl x ty init =>
          have hfo_i : FirstOrder init := by simpa [stmtFirstOrder] using hfo_s
          simp only [toHIRStmt] at hs
          obtain ⟨e', he, rfl⟩ := toHIRStmt_map_arm hs
          simp only [runStmts, runHIRStmts]
          cases hev : eval (ctxOf env) init with
          | none => exact Or.inl rfl
          | some v =>
            have hev256 : evalWithFuel 256 (ctxOf env) init = some v := hev
            obtain ⟨w, rfl⟩ := fo_eval_is_lit 256 (ctxOf env) init v hfo_i
              (envAllLit_ctxOf hrel) hev256
            have hhe := evalHIR_of_eval hfo_i he hrel hev256
            simp only [hhe]
            exact ihS _ _ _ _ _ _ hss hfo_rest (relStmtEnv_push hrel) hflow
        | .assign x e =>
          have hfo_e : FirstOrder e := by simpa [stmtFirstOrder] using hfo_s
          simp only [toHIRStmt] at hs
          obtain ⟨e', he, rfl⟩ := toHIRStmt_map_arm hs
          simp only [runStmts, runHIRStmts]
          cases hev : eval (ctxOf env) e with
          | none => exact Or.inl rfl
          | some v =>
            have hev256 : evalWithFuel 256 (ctxOf env) e = some v := hev
            obtain ⟨w, rfl⟩ := fo_eval_is_lit 256 (ctxOf env) e v hfo_e
              (envAllLit_ctxOf hrel) hev256
            have hhe := evalHIR_of_eval hfo_e he hrel hev256
            simp only [hhe]
            exact ihS _ _ _ _ _ _ hss hfo_rest (relStmtEnv_update hrel) hflow
        | .returnStmt e =>
          have hfo_e : FirstOrder e := by simpa [stmtFirstOrder] using hfo_s
          simp only [toHIRStmt] at hs
          obtain ⟨e', he, rfl⟩ := toHIRStmt_map_arm hs
          simp only [runStmts, runHIRStmts]
          cases hev : eval (ctxOf env) e with
          | none => exact Or.inl rfl
          | some v =>
            have hev256 : evalWithFuel 256 (ctxOf env) e = some v := hev
            obtain ⟨w, rfl⟩ := fo_eval_is_lit 256 (ctxOf env) e v hfo_e
              (envAllLit_ctxOf hrel) hev256
            have hhe := evalHIR_of_eval hfo_e he hrel hev256
            simp only [hhe]
            exact Or.inr ⟨⟨w, rfl, rfl⟩, hrel⟩
        | .break =>
          rw [toHIRStmt_break] at hs
          cases hs
          simp only [runStmts, runHIRStmts]
          exact Or.inr ⟨trivial, hrel⟩
        | .continue =>
          simp only [toHIRStmt] at hs
          cases hs
          simp only [runStmts, runHIRStmts]
          exact Or.inr ⟨trivial, hrel⟩
        | .whileLoop cond body =>
          have hfo_w : FirstOrder cond ∧
            (∀ s ∈ body, stmtFirstOrder s) := by
            simpa [stmtFirstOrder] using hfo_s
          obtain ⟨hfo_c, hfo_b⟩ := hfo_w
          obtain ⟨cond', body', hcond, hbody, rfl⟩ := toHIRStmt_while hs
          simp only [runStmts, runHIRStmts]
          have hIW := ihW env henv cond cond' body body' hcond hbody
            hfo_c hfo_b hrel
          match hW : runWhile f env cond body with
          | (F, env2) =>
            match hH : runHIRWhile f henv cond' body' with
            | (H, henv2) =>
              rw [hW, hH] at hIW
              cases F with
              | value u =>
                rcases hIW with hstuck | ⟨hfl, henvrel⟩
                · simp at hstuck
                · obtain ⟨hu, rfl, huv⟩ := relFlowFwd_value hfl
                  obtain ⟨w, rfl, rfl⟩ := huv
                  exact ihS env2 henv2 rest rest'
                    (Flow.replace acc (.lit w))
                    (HFlow.replace hacc (.lit w)) hss hfo_rest henvrel
                    (relFlow_replace hflow ⟨w, rfl, rfl⟩)
              | returned v =>
                rcases hIW with hstuck | ⟨hfl, henvrel⟩
                · simp at hstuck
                · obtain ⟨hv, rfl, huv⟩ := relFlowFwd_returned hfl
                  exact Or.inr ⟨huv, henvrel⟩
              | broke =>
                rcases hIW with hstuck | ⟨hfl, henvrel⟩
                · simp at hstuck
                · have hH' : H = .broke := relFlowFwd_broke hfl
                  subst hH'
                  exact Or.inr ⟨trivial, henvrel⟩
              | continued =>
                rcases hIW with hstuck | ⟨hfl, henvrel⟩
                · simp at hstuck
                · have hH' : H = .continued := relFlowFwd_continued hfl
                  subst hH'
                  exact Or.inr ⟨trivial, henvrel⟩
              | stuck => exact Or.inl rfl
        | .doWhile cond body =>
          rw [toHIRStmt_doWhile_none] at hs
          cases hs
        | .ifStmt cond th el =>
          have hfo_if : FirstOrder cond ∧ (∀ s ∈ th, stmtFirstOrder s) ∧
              (∀ s ∈ el, stmtFirstOrder s) := by
            simpa [stmtFirstOrder] using hfo_s
          obtain ⟨hfo_c, hfo_th, hfo_el⟩ := hfo_if
          obtain ⟨cond', th', el', hcond, hth, hel, rfl⟩ := toHIRStmt_if hs
          simp only [runStmts, runHIRStmts]
          cases hev : eval (ctxOf env) cond with
          | none => exact Or.inl rfl
          | some v =>
            have hev256 : evalWithFuel 256 (ctxOf env) cond = some v := hev
            obtain ⟨w, rfl⟩ := fo_eval_is_lit 256 (ctxOf env) cond v hfo_c
              (envAllLit_ctxOf hrel) hev256
            have hhe := evalHIR_of_eval hfo_c hcond hrel hev256
            cases w with
            | bool b =>
              cases b with
              | true =>
                simp only [hhe]
                match hB : runStmts f env th (.value (.lit .unit)) with
                | (F, env2) =>
                  match hH : runHIRStmts f henv th' (.value (.lit .unit)) with
                  | (H, henv2) =>
                    have hIB := ihS env henv th th'
                      (.value (.lit .unit)) (.value (.lit .unit))
                      hth hfo_th hrel ⟨.unit, rfl, rfl⟩
                    rw [hB, hH] at hIB
                    cases F with
                    | value u =>
                      rcases hIB with hstuck | ⟨hfl, henvrel⟩
                      · simp at hstuck
                      · obtain ⟨hu, rfl, huv⟩ := relFlowFwd_value hfl
                        obtain ⟨w2, rfl, rfl⟩ := huv
                        exact ihS env2 henv2 rest rest'
                          (Flow.replace acc (.lit w2))
                          (HFlow.replace hacc (.lit w2)) hss hfo_rest
                          henvrel (relFlow_replace hflow ⟨w2, rfl, rfl⟩)
                    | returned v =>
                      rcases hIB with hstuck | ⟨hfl, henvrel⟩
                      · simp at hstuck
                      · obtain ⟨hv, rfl, huv⟩ := relFlowFwd_returned hfl
                        exact Or.inr ⟨huv, henvrel⟩
                    | broke =>
                      rcases hIB with hstuck | ⟨hfl, henvrel⟩
                      · simp at hstuck
                      · have hH' : H = .broke := relFlowFwd_broke hfl
                        subst hH'
                        exact Or.inr ⟨trivial, henvrel⟩
                    | continued =>
                      rcases hIB with hstuck | ⟨hfl, henvrel⟩
                      · simp at hstuck
                      · have hH' : H = .continued := relFlowFwd_continued hfl
                        subst hH'
                        exact Or.inr ⟨trivial, henvrel⟩
                    | stuck => exact Or.inl rfl
              | false =>
                simp only [hhe]
                match hB : runStmts f env el (.value (.lit .unit)) with
                | (F, env2) =>
                  match hH : runHIRStmts f henv el' (.value (.lit .unit)) with
                  | (H, henv2) =>
                    have hIB := ihS env henv el el'
                      (.value (.lit .unit)) (.value (.lit .unit))
                      hel hfo_el hrel ⟨.unit, rfl, rfl⟩
                    rw [hB, hH] at hIB
                    cases F with
                    | value u =>
                      rcases hIB with hstuck | ⟨hfl, henvrel⟩
                      · simp at hstuck
                      · obtain ⟨hu, rfl, huv⟩ := relFlowFwd_value hfl
                        obtain ⟨w2, rfl, rfl⟩ := huv
                        exact ihS env2 henv2 rest rest'
                          (Flow.replace acc (.lit w2))
                          (HFlow.replace hacc (.lit w2)) hss hfo_rest
                          henvrel (relFlow_replace hflow ⟨w2, rfl, rfl⟩)
                    | returned v =>
                      rcases hIB with hstuck | ⟨hfl, henvrel⟩
                      · simp at hstuck
                      · obtain ⟨hv, rfl, huv⟩ := relFlowFwd_returned hfl
                        exact Or.inr ⟨huv, henvrel⟩
                    | broke =>
                      rcases hIB with hstuck | ⟨hfl, henvrel⟩
                      · simp at hstuck
                      · have hH' : H = .broke := relFlowFwd_broke hfl
                        subst hH'
                        exact Or.inr ⟨trivial, henvrel⟩
                    | continued =>
                      rcases hIB with hstuck | ⟨hfl, henvrel⟩
                      · simp at hstuck
                      · have hH' : H = .continued := relFlowFwd_continued hfl
                        subst hH'
                        exact Or.inr ⟨trivial, henvrel⟩
                    | stuck => exact Or.inl rfl
            | int _ => simp only [hhe]; exact Or.inl rfl
            | string _ => simp only [hhe]; exact Or.inl rfl
            | float _ => simp only [hhe]; exact Or.inl rfl
            | unit => simp only [hhe]; exact Or.inl rfl
            | undef => simp only [hhe]; exact Or.inl rfl
            | none => simp only [hhe]; exact Or.inl rfl
            | some _ => simp only [hhe]; exact Or.inl rfl
            | ok _ => simp only [hhe]; exact Or.inl rfl
            | err _ => simp only [hhe]; exact Or.inl rfl
            | tuple_ _ => simp only [hhe]; exact Or.inl rfl
            | array_ _ => simp only [hhe]; exact Or.inl rfl
            | loc _ => simp only [hhe]; exact Or.inl rfl
            | pointer _ => simp only [hhe]; exact Or.inl rfl
            | closure _ _ => simp only [hhe]; exact Or.inl rfl
        | .matchStmt scrut arms =>
          have hfo_m : FirstOrder scrut ∧
              (∀ (p : Syntax.Pattern) (b : List Syntax.Stmt), (p, b) ∈ arms →
                p = .wild ∨ (∃ l, p = .lit_ l) ∨ (∃ x, p = .var_ x)) ∧
              stmtArmsFirstOrder arms := by
            simpa [stmtFirstOrder] using hfo_s
          obtain ⟨hfo_c, hpat_ok, hfo_arms⟩ := hfo_m
          obtain ⟨scrut', arms', hscrut, harms, rfl⟩ := toHIRStmt_match hs
          simp only [runStmts, runHIRStmts]
          cases hev : eval (ctxOf env) scrut with
          | none => exact Or.inl rfl
          | some v =>
            have hev256 : evalWithFuel 256 (ctxOf env) scrut = some v := hev
            obtain ⟨w, rfl⟩ := fo_eval_is_lit 256 (ctxOf env) scrut v hfo_c
              (envAllLit_ctxOf hrel) hev256
            have hhe := evalHIR_of_eval hfo_c hscrut hrel hev256
            simp only [hhe]
            have hAM := ihM env henv w arms arms' harms hpat_ok hfo_arms hrel
            match hA : runMatchArms f env (.lit w) arms with
            | (F, env2) =>
              match hH : runHIRMatchArms f henv (.lit w) arms' with
              | (H, henv2) =>
                rw [hA, hH] at hAM
                cases F with
                | value u =>
                  rcases hAM with hstuck | ⟨hfl, henvrel⟩
                  · simp at hstuck
                  · obtain ⟨hu, rfl, huv⟩ := relFlowFwd_value hfl
                    obtain ⟨w2, rfl, rfl⟩ := huv
                    exact ihS env2 henv2 rest rest'
                      (Flow.replace acc (.lit w2))
                      (HFlow.replace hacc (.lit w2)) hss hfo_rest
                      henvrel (relFlow_replace hflow ⟨w2, rfl, rfl⟩)
                | returned v =>
                  rcases hAM with hstuck | ⟨hfl, henvrel⟩
                  · simp at hstuck
                  · obtain ⟨hv, rfl, huv⟩ := relFlowFwd_returned hfl
                    exact Or.inr ⟨huv, henvrel⟩
                | broke =>
                  rcases hAM with hstuck | ⟨hfl, henvrel⟩
                  · simp at hstuck
                  · have hH' : H = .broke := relFlowFwd_broke hfl
                    subst hH'
                    exact Or.inr ⟨trivial, henvrel⟩
                | continued =>
                  rcases hAM with hstuck | ⟨hfl, henvrel⟩
                  · simp at hstuck
                  · have hH' : H = .continued := relFlowFwd_continued hfl
                    subst hH'
                    exact Or.inr ⟨trivial, henvrel⟩
                | stuck => exact Or.inl rfl
    · intro env henv cond cond' body body' hcond hbody hfo_c hfo_b hrel
      simp only [runWhile, runHIRWhile]
      cases hev : eval (ctxOf env) cond with
      | none => exact Or.inl rfl
      | some v =>
        have hev256 : evalWithFuel 256 (ctxOf env) cond = some v := hev
        obtain ⟨w, rfl⟩ := fo_eval_is_lit 256 (ctxOf env) cond v hfo_c
          (envAllLit_ctxOf hrel) hev256
        have hhe := evalHIR_of_eval hfo_c hcond hrel hev256
        cases w with
        | bool b =>
          cases b with
          | true =>
            simp only [hhe]
            match hB : runStmts f env body (.value (.lit .unit)) with
            | (F, env2) =>
              match hH : runHIRStmts f henv body' (.value (.lit .unit)) with
              | (H, henv2) =>
                have hIB := ihS env henv body body'
                  (.value (.lit .unit)) (.value (.lit .unit)) hbody hfo_b
                  hrel ⟨.unit, rfl, rfl⟩
                rw [hB, hH] at hIB
                cases F with
                | value u =>
                  rcases hIB with hstuck | ⟨hfl, henvrel⟩
                  · simp at hstuck
                  · obtain ⟨hu, rfl, huv⟩ := relFlowFwd_value hfl
                    obtain ⟨w, rfl, rfl⟩ := huv
                    exact ihW env2 henv2 cond cond' body body' hcond hbody
                      hfo_c hfo_b henvrel
                | broke =>
                  rcases hIB with hstuck | ⟨hfl, henvrel⟩
                  · simp at hstuck
                  · have hH' : H = .broke := relFlowFwd_broke hfl
                    subst hH'
                    exact Or.inr ⟨⟨.unit, rfl, rfl⟩, henvrel⟩
                | continued =>
                  rcases hIB with hstuck | ⟨hfl, henvrel⟩
                  · simp at hstuck
                  · have hH' : H = .continued := relFlowFwd_continued hfl
                    subst hH'
                    exact ihW env2 henv2 cond cond' body body' hcond hbody
                      hfo_c hfo_b henvrel
                | returned v =>
                  rcases hIB with hstuck | ⟨hfl, henvrel⟩
                  · simp at hstuck
                  · obtain ⟨hv, rfl, huv⟩ := relFlowFwd_returned hfl
                    exact Or.inr ⟨huv, henvrel⟩
                | stuck => exact Or.inl rfl
          | false =>
            simp only [hhe]
            exact Or.inr ⟨⟨.unit, rfl, rfl⟩, hrel⟩
        | int _ =>
          simp only [hhe]
          exact Or.inl rfl
        | string _ =>
          simp only [hhe]
          exact Or.inl rfl
        | float _ =>
          simp only [hhe]
          exact Or.inl rfl
        | unit =>
          simp only [hhe]
          exact Or.inl rfl
        | undef =>
          simp only [hhe]
          exact Or.inl rfl
        | none =>
          simp only [hhe]
          exact Or.inl rfl
        | some _ =>
          simp only [hhe]
          exact Or.inl rfl
        | ok _ =>
          simp only [hhe]
          exact Or.inl rfl
        | err _ =>
          simp only [hhe]
          exact Or.inl rfl
        | tuple_ _ =>
          simp only [hhe]
          exact Or.inl rfl
        | array_ _ =>
          simp only [hhe]
          exact Or.inl rfl
        | loc _ =>
          simp only [hhe]
          exact Or.inl rfl
        | pointer _ =>
          simp only [hhe]
          exact Or.inl rfl
        | closure _ _ =>
          simp only [hhe]
          exact Or.inl rfl
    · intro env henv v arms arms' hlower hpat hfoarms hrel
      cases arms with
      | nil =>
        simp only [toHIRStmtArms] at hlower
        cases hlower
        simp only [runMatchArms, runHIRMatchArms]
        exact Or.inr ⟨⟨.unit, rfl, rfl⟩, hrel⟩
      | cons hd tl =>
        obtain ⟨pat, body⟩ := hd
        obtain ⟨pat', body', rest', hppat, hpbody, hrest, rfl⟩ :=
          toHIRStmtArms_cons hlower
        have hpat_head : pat = .wild ∨ (∃ l, pat = .lit_ l) ∨
            (∃ x, pat = .var_ x) :=
          hpat pat body List.mem_cons_self
        have hpat_tail : ∀ (p : Syntax.Pattern) (b : List Syntax.Stmt),
            (p, b) ∈ tl →
              p = .wild ∨ (∃ l, p = .lit_ l) ∨ (∃ x, p = .var_ x) :=
          fun p b hmem => hpat p b (List.mem_cons_of_mem _ hmem)
        have hfo_head : ∀ s ∈ body, stmtFirstOrder s := by
          have h := hfoarms
          simp only [stmtArmsFirstOrder] at h
          obtain ⟨hh, _⟩ := h
          exact hh
        have hfo_tail : stmtArmsFirstOrder tl := by
          have h := hfoarms
          simp only [stmtArmsFirstOrder] at h
          exact h.2
        simp only [runMatchArms, runHIRMatchArms]
        rcases toHIRStmtPat_shape hppat with ⟨rfl, rfl⟩ | ⟨l, rfl, rfl⟩ | ⟨x, rfl, rfl⟩
        · have hB := ihS env henv body body'
            (.value (.lit .unit)) (.value (.lit .unit))
            hpbody hfo_head hrel ⟨.unit, rfl, rfl⟩
          simpa [matchPat, matchHIRPat, patVars, hirPatVars] using hB
        · cases heq : (l == v)
          · have hnone : matchPat (Syntax.Pattern.lit_ l) (.lit v) = none := by
              simp [matchPat, heq]
            have hnone' : matchHIRPat (.lit l) (.lit v) = none := by
              simp [matchHIRPat, heq]
            rw [hnone, hnone']
            exact ihM env henv v tl rest' hrest hpat_tail hfo_tail hrel
          · have hvs : matchPat (Syntax.Pattern.lit_ l) (.lit v) = some [] := by
              simp [matchPat, heq]
            have hvs' : matchHIRPat (.lit l) (.lit v) = some [] := by
              simp [matchHIRPat, heq]
            rw [hvs, hvs']
            have hB := ihS env henv body body'
              (.value (.lit .unit)) (.value (.lit .unit))
              hpbody hfo_head hrel ⟨.unit, rfl, rfl⟩
            simpa [patVars, hirPatVars] using hB
        · simp only [matchPat, matchHIRPat, patVars, hirPatVars]
          have hB := ihS ((x, Syntax.Expr.lit v) :: env)
            ((⟨0, "free:" ++ x⟩, HIR.Expr.lit v) :: henv) body body'
            (.value (.lit .unit)) (.value (.lit .unit))
            hpbody hfo_head (relStmtEnv_match_var hrel) ⟨.unit, rfl, rfl⟩
          simpa [patVars, hirPatVars] using hB

/-- Whole-program preservation: a surface program that lowers and runs
to a literal value runs to the same literal through HIR. -/
theorem runHIRProgram_preservation (prog : Syntax.Program)
    (hprog : HIR.Program)
    (hlower : toHIRProgram prog = some hprog)
    (hfo : ∀ s ∈ prog.stmts, stmtFirstOrder s) (u w : Value)
    (hrun : (runStmts 1024 [] prog.stmts (.value (.lit u))).1 =
      .value (.lit w)) :
    (runHIRStmts 1024 [] hprog.stmts (.value (.lit u))).1 =
      .value (.lit w) := by
  obtain ⟨stmts⟩ := prog
  obtain ⟨hstmts⟩ := hprog
  simp only [toHIRProgram] at hlower
  cases hs : toHIRStmtList stmts with
  | none => simp [hs] at hlower
  | some ss' =>
    simp [hs] at hlower
    cases hlower
    have hA := (agreeBoth 1024).1 [] [] stmts hstmts
      (.value (.lit u)) (.value (.lit u)) hs hfo
      relStmtEnv_nil ⟨u, rfl, rfl⟩
    rcases hA with hstuck | ⟨hfl, henv⟩
    · rw [hrun] at hstuck
      simp at hstuck
    · rw [hrun] at hfl
      obtain ⟨hu, hhu, huv⟩ := relFlowFwd_value hfl
      have hhu' : hu = .lit w := by
        obtain ⟨w2, h1, h2⟩ := huv
        cases h1
        assumption
      subst hhu'
      exact hhu

end Morph.Frontend.HIRInterp
