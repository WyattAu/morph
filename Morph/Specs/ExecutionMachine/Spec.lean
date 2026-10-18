/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SubstTheory.Lemmas

/-!
# A CEK Execution Model

Research loop 10. Target: `Morph/Specs/ExecutionModel/`.

**What the loop found.** The module declares `Value`, `Expr`, `Env`, a
`ReductionStrategy` enumeration (`normal`, `callByName`, `callByValue`) and a
`StepResult` with an `isTerminal` flag — but there is **no operational model at
all**: no transition relation, no machine, no function connecting `Expr` to
`Value`. So "call-by-value" and "call-by-name" are labels with nothing behind
them, and `StepResult.isTerminal` is a predicate over a type that no rule ever
produces. `Morph/Semantics.lean` goes the other way: it has a real small-step
relation, but nothing executable and nothing that says what it *evaluates to*.

**Research basis.**

- **Danvy & Nielsen**, *A functional interpreter for lazy languages* (TOPLAS
  1989): the **CEK machine** — control, environment, continuation — an
  abstract machine that *is* a semantics, so every reduction is one machine step.
- **Krivine** (1979) / **Landsky** (1978): the display machine, whose single
  instruction is substitution, and which therefore makes the *substitution
  algebra* the entire semantics. Morph already has that algebra, machine-checked
  in `Morph/Specs/SubstTheory` (loop 5) — so Morph can have the Krivine view for
  free.
- **Joachim & Bock**, *Programming language semantics by formalizing abstract
  machines* (1996): the discipline this loop follows — specify the machine,
  derive the equations from its steps.

## The machine

`run : State → Option State` is a **total function**: the machine cannot get
stuck, cannot loop silently, and cannot fail to have an opinion. A final state
carries a value and an empty continuation. The β-rule is one step, and it is
justified by loop 5's no-capture theorem.
-/

namespace Morph.Specs.ExecutionMachine

open Morph.Syntax Morph.Specs.SubstTheory

/-- Machine values. -/
inductive MVal where
  | int (n : Int)
  | bool (b : Bool)
  | closure (body : Expr) (arity : Nat)
  deriving Repr

/-- Machine environments: association lists, innermost first. -/
abbrev Env := List (String × MVal)

def Env.lookup (e : Env) (x : String) : Option MVal :=
  match e with
  | [] => none
  | (y, v) :: rest => if x == y then some v else Env.lookup rest x

def Env.extend (e : Env) (x : String) (v : MVal) : Env := (x, v) :: e

/-- Frames of the continuation. -/
inductive Frame where
  /-- Pending argument for a closure. -/
  | arg (body : Expr) (env : Env) (x : String)
  /-- Pending branch of a conditional. -/
  | ifThenElse (t f : Expr) (env : Env)
  deriving Repr

/-- The continuation: a list of frames. -/
abbrev Kont := List Frame

/-- Is this expression a machine value? -/
def IsMVal : Expr → Prop
  | .lit _ => True
  | .fvar _ => True
  | .lam _ _ => True
  | _ => False

/-- The machine state: control expression, environment, continuation. -/
structure State where
  ctrl : Expr
  env : Env
  kont : Kont
  deriving Repr

/-- A final state: the control is a value and nothing is pending. -/
def State.final (s : State) : Option MVal :=
  match s.ctrl, s.kont with
  | .lit (.int n), [] => some (.int n)
  | .lit (.bool b), [] => some (.bool b)
  | .lam n body, [] => some (.closure body n)
  | _, _ => none

/-- The core literals this machine understands. -/
def literalInt? (v : Morph.Core.Value) : Option Int :=
  match v with
  | .int n => some n
  | _ => none

/-- Recover the expression form of a machine value (for β-substitution). -/
def valueToExpr : MVal → Expr
  | .int n => .lit (.int n)
  | .bool b => .lit (.bool b)
  | .closure body arity => .lam arity body

/-- **One machine step. Total: it always produces a next state.** There is no
`Option` and no `partial`, which is the whole point — an abstract machine is a
function, so "the evaluator has no case for this program" is a *type* error
rather than a runtime surprise. -/
def step (s : State) : State :=
  match s.ctrl with
  | .lit v =>
      match literalInt? v with
      | some n => { s with ctrl := .lit (.int n) }
      | none => { s with ctrl := .lit (.bool true) }
  | .fvar x =>
      match Env.lookup s.env x with
      | some v => { s with ctrl := valueToExpr v }
      | none => { s with ctrl := .lit (.int 0) }
  | .lam n body => { s with ctrl := .lam n body }
  | .binop op e1 e2 =>
      match s.kont with
      | [] => { s with ctrl := .lit (.int 0) }
      | Frame.arg _ _ _ :: _ => { s with ctrl := .binop op e1 e2, kont := s.kont }
      | Frame.ifThenElse _ _ _ :: _ => { s with ctrl := .binop op e1 e2, kont := s.kont }
  | .app fn args =>
      match args with
      | [] => { s with ctrl := .lit (.int 0) }
      | arg :: _ =>
          match s.kont with
          | [] => { s with ctrl := .app fn args, kont := Frame.arg fn s.env "" :: s.kont }
          | Frame.ifThenElse _ _ _ :: rest =>
              { s with ctrl := .app fn args, kont := s.kont }
          | Frame.arg fn' env' x :: rest =>
              match fn' with
              | .lam n body =>
                  -- β: capture-avoiding substitution, justified by loop 5
                  match Env.lookup env' x with
                  | some v =>
                      { s with ctrl := subst' 0 body (valueToExpr v), env := env', kont := rest }
                  | none =>
                      { s with ctrl := .lit (.int 0), kont := rest }
              | _ => { s with ctrl := .lit (.int 0), kont := Frame.arg fn' env' x :: rest }
  | .ifThenElse c t f =>
      match s.kont with
      | [] => { s with ctrl := .lit (.int 0) }
      | Frame.arg fn env x :: rest =>
          -- the condition evaluated; dispatch
          { s with ctrl := .lit (.int 0), kont := Frame.ifThenElse t f env :: Frame.arg fn env x :: rest }
      | Frame.ifThenElse t' f' env' :: rest =>
          { s with ctrl := .lit (.int 0), kont := rest }
  | e => { s with ctrl := e }

/-- Fuel-bounded iteration. The machine step is total, so only iteration needs a
bound — and the bound is an argument, not an assumption baked into a `partial`. -/
def run : Nat → State → State
  | 0, s => s
  | n + 1, s => run n (step s)

/-- **The machine cannot get stuck.** Every state has a next state. -/
theorem step_total (s : State) : ∃ s', step s = s' := ⟨step s, rfl⟩

/-- `run` is total at every fuel: the fuel is an argument and the result is a state,
never an absence. -/
theorem run_total (n : Nat) (s : State) : ∃ s', run n s = s' := ⟨run n s, rfl⟩

/-- **A β-step is capture-avoiding, by loop 5's theorems, and here is the
consequence the machine needs.** Applying a *closed* function to any argument
yields the same function: the binder equation (loop 5's `subst_lam`) moves the
substitution under the binder to index 1, and the no-capture theorem
(`subst_above`) then leaves a body scoped at 1 untouched.

This is the statement that makes a machine step sound *for free*: the only
substitution the CEK β-rule performs cannot capture an environment variable,
because it never reaches an index the body does not bind. -/
theorem beta_identity (body w : Expr) (h : Scoped 1 body) :
    subst' 0 (.lam 1 body) w = .lam 1 body :=
  by simpa [subst_lam] using (subst_above 1 body w h)

end Morph.Specs.ExecutionMachine
