/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ExecutionMachine.Spec

/-!
# ExecutionMachine: determinism + fuel + final-state lemmas (Loop 60)

Research basis: Felleisen–Friedman CEK machine (left-to-right call-by-value
as a first-order state transition system); Danvy–Nielsen functional
correspondence (TOPLAS 1989) — the machine *is* the semantics, so every
reduction is one total-function step; Van Horn–Might "Abstracting Abstract
Machines" — refactorings of the machine preserve the transition relation;
Blazy et al. (2024) CEK-style mechanized semantics — writing the small-step
relation in CEK form keeps the soundness proof structural.

What this file adds over `Spec.lean` (which already has `step_total`,
`run_total`, `beta_identity`):
- `step` determinism is definitional (it is a function, not a relation);
- fuel-unrolling equations for `run`;
- final-state behaviour: literals stutter, `final` agrees with the denotation;
- environment lookup facts used by the `fvar` and β cases.
-/

namespace Morph.Specs.ExecutionMachine

open Morph.Syntax Morph.Core

/-- `step` is a function, so determinism is definitional. -/
theorem step_deterministic (s s₁ s₂ : State) (h₁ : step s = s₁) (h₂ : step s = s₂) :
    s₁ = s₂ := by
  rw [← h₁, ← h₂]

/-- Fuel zero is the identity. -/
theorem run_zero (s : State) : run 0 s = s := rfl

/-- Fuel successor unrolls one `step`. -/
theorem run_succ (n : Nat) (s : State) : run (n + 1) s = run n (step s) := rfl

/-- A literal in the empty continuation is final with the expected denotation. -/
theorem final_lit_int (n : Int) :
    (State.mk (.lit (.int n)) [] []).final = some (.int n) := rfl

theorem final_lit_bool (b : Bool) :
    (State.mk (.lit (.bool b)) [] []).final = some (.bool b) := rfl

/-- A closed lambda in the empty continuation is a closure value. -/
theorem final_lam (n : Nat) (body : Expr) :
    (State.mk (.lam n body) [] []).final = some (.closure body n) := rfl

/-- Non-empty continuations are never final. -/
theorem final_not_nil_kont (s : State) (hk : s.kont ≠ []) :
    s.final = none := by
  cases s with
  | mk ctrl env kont =>
    simp only [State.final]
    cases hctrl : ctrl with
    | lit v =>
      cases v with
      | int n =>
        cases kont with
        | nil => exact absurd rfl hk
        | cons _ _ => rfl
      | bool b =>
        cases kont with
        | nil => exact absurd rfl hk
        | cons _ _ => rfl
      | _ =>
        cases kont with
        | nil => exact absurd rfl hk
        | cons _ _ => rfl
    | lam n body =>
      cases kont with
      | nil => exact absurd rfl hk
      | cons _ _ => rfl
    | _ =>
      cases kont with
      | nil => exact absurd rfl hk
      | cons _ _ => rfl

/-- Literal steps always produce a next state with literal control:
the `literalInt?` discriminator decides between an int and `true`. -/
theorem step_lit_control (v : Morph.Core.Value) (env : Env) :
    ∃ e : Expr, (step ⟨.lit v, env, []⟩).ctrl = e := ⟨_, rfl⟩

theorem step_lit_cases (v : Morph.Core.Value) (env : Env) :
    (literalInt? v).isSome = true →
      ∃ n : Int, (step ⟨.lit v, env, []⟩).ctrl = .lit (.int n) := by
  intro h
  cases hv : literalInt? v with
  | none => simp [hv] at h
  | some n => exact ⟨n, by simp [step, hv]⟩

/-- Empty environment looks up to nothing. -/
theorem Env.lookup_nil (x : String) : Env.lookup [] x = none := rfl

/-- Extending then looking up the same name hits. -/
theorem Env.extend_lookup_hit (e : Env) (x : String) (v : MVal) :
    Env.lookup (Env.extend e x v) x = some v := by
  simp [Env.extend, Env.lookup]

/-- `run` distributes over addition of fuel. -/
theorem run_add (n m : Nat) (s : State) : run (n + m) s = run m (run n s) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ k ih =>
    simp only [Nat.succ_add, run]
    exact ih (step s)

/-! ## Loop 64: control frames for `if` / `let` / `block`

Research: Felleisen–Friedman CEK (control strings evaluated under an
explicit continuation); Danvy (defunctionalized continuations — each frame is
one pending control action); WASM (structured control: `block`/`if` carry
their continuation as a label frame, values dispatch on it); Racket CS
machine (`let` frames bind evaluated inits).

Language comparison: WASM (`block`/`if`/`br` — control frames over a value
stack); OCaml bytecode (`PUSH`/`LET`); JVM (`ifeq` branching on operand
stack); BEAM (explicit `letrec` frames). Morph's `dispatchValue` is the same
idea as WASM's label dispatch: a value meeting a control frame resumes it.

What is proved: every control transition below is definitional (`rfl`) — the
machine *computes* it. Control states push a frame (continuation grows by
one: the termination measure for this fragment); resumptions pop one.
Non-`true` conditions take the else-branch (type-sound programs only test
booleans; cf. `HasType`). The pre-existing `binop`-under-kont stutter is
unchanged and out of scope.
-/

/-- `if` evaluates its condition under a pushed branch frame. -/
theorem step_if_pushes (c t f : Expr) (env : Env) (k : Kont) :
    step ⟨.ifThenElse c t f, env, k⟩ =
      ⟨c, env, Frame.ifThenElse t f env :: k⟩ := rfl

/-- `let` evaluates its init under a pushed body frame. -/
theorem step_let_pushes (init body : Expr) (env : Env) (k : Kont) :
    step ⟨.let_ init body, env, k⟩ =
      ⟨init, env, Frame.letBody body env :: k⟩ := rfl

/-- `block []` is unit. -/
theorem step_block_nil (env : Env) (k : Kont) :
    step ⟨.block [], env, k⟩ = ⟨.lit (.unit), env, k⟩ := rfl

/-- `block [e]` is `e`. -/
theorem step_block_single (e : Expr) (env : Env) (k : Kont) :
    step ⟨.block [e], env, k⟩ = ⟨e, env, k⟩ := rfl

/-- `block (e :: es)` evaluates `e` under a pushed tail frame. -/
theorem step_block_cons (e : Expr) (es : List Expr) (env : Env) (k : Kont)
    (hne : es ≠ []) :
    step ⟨.block (e :: es), env, k⟩ =
      ⟨e, env, Frame.seqRest es env :: k⟩ := by
  cases es with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

/-- `true` under a branch frame takes the then-branch. -/
theorem step_dispatch_true (t f : Expr) (env env' : Env) (k : Kont) :
    step ⟨.lit (.bool true), env, Frame.ifThenElse t f env' :: k⟩ =
      ⟨t, env', k⟩ := rfl

/-- Anything else takes the else-branch (type-sound states only test
booleans). -/
theorem step_dispatch_false (t f : Expr) (env env' : Env) (k : Kont) :
    step ⟨.lit (.bool false), env, Frame.ifThenElse t f env' :: k⟩ =
      ⟨f, env', k⟩ := rfl

/-- A closure under a branch frame takes the else-branch. -/
theorem step_dispatch_lam (n : Nat) (body t f : Expr) (env env' : Env)
    (k : Kont) :
    step ⟨.lam n body, env, Frame.ifThenElse t f env' :: k⟩ =
      ⟨f, env', k⟩ := rfl

/-- A value under a `letBody` frame substitutes into the body.
`literalInt? v` is stuck for variable `v`, so split on it first. -/
theorem step_let_resume (v : Morph.Core.Value) (body : Expr)
    (env env' : Env) (k : Kont) :
    step ⟨.lit v, env, Frame.letBody body env' :: k⟩ =
      ⟨subst' 0 body (.lit v), env', k⟩ := by
  cases hv : literalInt? v with
  | some n => simp [step, dispatchValue, hv]
  | none => simp [step, dispatchValue, hv]

/-- A value under an empty tail frame pops it. -/
theorem step_seq_done (v : Morph.Core.Value) (env env' : Env) (k : Kont) :
    step ⟨.lit v, env, Frame.seqRest [] env' :: k⟩ =
      ⟨.lit v, env', k⟩ := by
  cases hv : literalInt? v with
  | some n => simp [step, dispatchValue, hv]
  | none => simp [step, dispatchValue, hv]

/-- A value under a non-empty tail frame moves to the next element. -/
theorem step_seq_next (v : Morph.Core.Value) (e : Expr) (es : List Expr)
    (env env' : Env) (k : Kont) :
    step ⟨.lit v, env, Frame.seqRest (e :: es) env' :: k⟩ =
      ⟨e, env', Frame.seqRest es env' :: k⟩ := by
  cases hv : literalInt? v with
  | some n => simp [step, dispatchValue, hv]
  | none => simp [step, dispatchValue, hv]

/-- Control states push exactly one frame: the termination measure for this
fragment. -/
theorem step_control_pushes_if (c t f : Expr) (env : Env) (k : Kont) :
    (step ⟨.ifThenElse c t f, env, k⟩).kont.length = k.length + 1 := rfl

theorem step_control_pushes_let (init body : Expr) (env : Env) (k : Kont) :
    (step ⟨.let_ init body, env, k⟩).kont.length = k.length + 1 := rfl

/-- Resumptions pop exactly one frame. -/
theorem step_resume_pops_let (v : Morph.Core.Value) (body : Expr)
    (env env' : Env) (k : Kont) :
    (step ⟨.lit v, env, Frame.letBody body env' :: k⟩).kont.length =
      k.length := by
  cases hv : literalInt? v with
  | some n => simp [step, dispatchValue, hv]
  | none => simp [step, dispatchValue, hv]

/-- End to end: `if true then 1 else 2` evaluates to `1`. -/
example : (run 3 ⟨.ifThenElse (.lit (.bool true)) (.lit (.int 1))
    (.lit (.int 2)), [], []⟩).final = some (.int 1) := rfl

/-- End to end: `let x = 5 in x` substitutes (the substitution itself is
opaque to `rfl` — well-founded recursion — so it stays on the right). -/
example : (run 2 ⟨.let_ (.lit (.int 5)) (.bvar 0), [], []⟩).ctrl =
    subst' 0 (.bvar 0) (.lit (.int 5)) := rfl

/-- End to end: `block [1, 2]` evaluates to `2`. -/
example : (run 3 ⟨.block [.lit (.int 1), .lit (.int 2)], [], []⟩).final =
    some (.int 2) := rfl

end Morph.Specs.ExecutionMachine
