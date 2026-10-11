/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Lowering

/-!
# Foundational lemmas for lowering correctness (ADR-011 stage 1)

Self-contained supporting lemmas for the `lowering_correct` theorem
(`execMain (lower e) env = exprVal (evalFuel n ctx e)` for closed pure
`e`). The full theorem needs a strong-agreement induction that couples the
interpreter `Context` to the MIR `Env` through `.let_`/`.bvar`; these are
the pieces that do not depend on that coupling:

* `Env.update_stable` / `evalInstr_write` — an instruction reads and writes
  only the registers it mentions; every other register is untouched. This
  is the "write-avoidance" invariant that lets the agreement relation survive
  instruction-list execution.
* `evalInstr_preserves` — running an instruction preserves register
  agreement outside the written set (the bridge to `execInstrs`).
* `evalBinOp_align` / `evalUnOp_align` — the MIR evaluation oracle agrees
  with the surface interpreter on literal-shaped values, because `MIR`'s
  `evalBinOp`/`evalUnOp` literally call the surface `evalBinop`/`evalUnop`.

These are the two classes of lemma the loop-07 notes identified as the
mechanical blockers; proving them here isolates the remaining work in the
main agreement theorem.
-/

namespace Morph.Lowering

open Morph.Core Morph.Syntax Morph.MIR Morph.Executable

/-! ## Register-update stability -/

/-- `update` changes exactly its destination. -/
theorem Env.update_same (env : MIR.Env) (dst : ValId) (v : Value) :
    env.update dst v dst = some v := by
  simp [MIR.Env.update]

/-- `update` leaves every register other than its destination alone. This is
    the per-register form of write-avoidance. -/
theorem Env.update_ne (env : MIR.Env) (dst : ValId) (v : Value) (x : ValId)
    (hx : x ≠ dst) :
    env.update dst v x = env x := by
  simp [MIR.Env.update, hx]

/-! ## Instruction writes only its destination -/

/-- The register an instruction writes (its destination), if any. The pure
    instructions write their `dst`; the memory/call instructions are
    `none`-stubs in stage 1 and write nothing. -/
def writtenReg : Instr → Option ValId
  | .const dst _ => some dst
  | .copy dst _ => some dst
  | .unop dst _ _ _ => some dst
  | .binop dst _ _ _ _ => some dst
  | .allocClosure dst _ _ => some dst
  | .callClosure dst _ _ => some dst
  | .load _ _ _ => none
  | .store _ _ _ => none
  | .alloc _ _ _ => none
  | .free _ => none
  | .call _ _ _ => none
  | .phi _ _ _ => none

/-- An instruction writes exactly the register `writtenReg` names, and
    leaves all others untouched, when it succeeds. This is the
    write-avoidance invariant that lets the agreement relation survive
    instruction-list execution. -/
theorem evalInstr_write (env : MIR.Env) (i : Instr) (env' : MIR.Env)
    (h : evalInstr env i = some env') (dst : ValId)
    (hd : writtenReg i = some dst) :
    ∀ x, x ≠ dst → env' x = env x := by
  intro x hx
  cases i with
  | const d v =>
      simp only [writtenReg, Option.some.injEq] at hd
      subst hd
      rw [show evalInstr env (.const d v) = some (env.update d v) from rfl] at h
      rw [← Option.some.inj h]
      exact Env.update_ne env d v x hx
  | copy d s =>
      simp only [writtenReg, Option.some.injEq] at hd
      subst hd
      cases hs : env s with
      | none => simp [evalInstr, hs] at h
      | some v =>
          simp only [evalInstr, hs, Option.map_some] at h
          rw [← Option.some.inj h]
          exact Env.update_ne env d v x hx
  | unop d op s τ =>
      simp only [writtenReg, Option.some.injEq] at hd
      subst hd
      cases hs : env s with
      | none => simp [evalInstr, hs] at h
      | some v =>
          cases he : evalUnOp op v with
          | none => simp [evalInstr, hs, he] at h
          | some r =>
              simp [evalInstr, hs, he] at h
              rw [← h]
              exact Env.update_ne env d r x hx
  | binop d op l r τ =>
      simp only [writtenReg, Option.some.injEq] at hd
      subst hd
      cases hl : env l with
      | none => simp [evalInstr, hl] at h
      | some vl =>
          cases hr : env r with
          | none => simp [evalInstr, hl, hr] at h
          | some vr =>
              cases he : evalBinOp op vl vr with
              | none => simp [evalInstr, hl, hr, he] at h
              | some res =>
                  simp [evalInstr, hl, hr, he] at h
                  rw [← h]
                  exact Env.update_ne env d res x hx
  | allocClosure d fn captures => exact absurd h (by simp [evalInstr])
  | callClosure d clo args => exact absurd h (by simp [evalInstr])

  | load d loc cap => simp [evalInstr] at h
  | store l s cap => simp [evalInstr] at h
  | alloc d cap τ => simp [evalInstr] at h
  | free l => simp [evalInstr] at h
  | call d fn args => simp [evalInstr] at h
  | phi d pred s => simp [evalInstr] at h

/-! ## Binary/unary oracle alignment -/

/-- The MIR binary oracle equals the surface interpreter's result coerced
    from an `Expr` to a `Value`: both are the surface `evalBinop` applied to
    `.lit`-wrapped arguments, unwrapped on success. -/
theorem evalBinOp_align (op : BinOp) (v1 v2 : Value) :
    evalBinOp op v1 v2 =
      (Morph.Executable.evalBinop op.toOperator (.lit v1) (.lit v2)).bind
        (fun e => match e with | .lit v => some v | _ => none) := rfl

theorem evalUnOp_align (op : UnOp) (v : Value) :
    evalUnOp op v =
      (Morph.Executable.evalUnop op.toOperator (.lit v)).bind
        (fun e => match e with | .lit v' => some v' | _ => none) := rfl

/-! ## The agreement relation -/

/-- `Agrees paramMap ctx env`: every bound variable the interpreter context
    holds at index `n`, when it is a `.lit`, corresponds to register
    `paramMap n` in the MIR environment holding the same value. This is the
    coupling that the strong-agreement induction for `lowerIn` maintains. -/
def Agrees (paramMap : Nat → ValId) (ctx : Context) (env : MIR.Env) : Prop :=
  ∀ (n : Nat) (v : Expr), ctx.getBv? n = some v →
    ∃ w : Value, v = .lit w ∧ env (paramMap n) = some w

/-- `Agrees` implies the bvar bridge: the interpreter's bound-variable value
    and the MIR register lookup yield the same `Value`. This is the step the
    `.bvar` case of the agreement induction uses. -/
theorem agrees_bvar (paramMap : Nat → ValId) (ctx : Context) (env : MIR.Env)
    (hag : Agrees paramMap ctx env) (n : Nat) (v : Expr)
    (hv : ctx.getBv? n = some v) :
    bvVal ctx n = env (paramMap n) := by
  obtain ⟨w, rfl, hw⟩ := hag n v hv
  simp [bvVal, hv, hw]

/-! ## The supply discipline

Lowering allocates registers from `supply` upward and never reuses a
parameter register. These lemmas make that precise, and they are what lets
`execInstrs` leave the parameter registers (`< supply`) untouched — the
step the `let_` case of the agreement induction needs to extend `Agrees`
across a sub-block. -/

/-- Every register written by an instruction list is at least `lo`. -/
def WritesAbove (lo : Nat) : List Instr → Prop
  | [] => True
  | i :: is => (match writtenReg i with | some d => lo ≤ d | none => True) ∧ WritesAbove lo is

theorem WritesAbove.anti_mono (lo lo' : Nat) (is : List Instr)
    (h : lo ≤ lo') (hi : WritesAbove lo' is) : WritesAbove lo is := by
  induction is with
  | nil => trivial
  | cons i is ih =>
      constructor
      · cases hreg : writtenReg i with
        | none => trivial
        | some d =>
            have : lo' ≤ d := by simpa [hreg] using hi.1
            exact Nat.le_trans h this
      · exact ih hi.2

/-- An instruction that names no destination is a `none`-stub in stage 1. -/
theorem evalInstr_eq_none_of_no_write (env : MIR.Env) (i : Instr)
    (h : writtenReg i = none) : evalInstr env i = none := by
  cases i <;> simp_all [writtenReg, evalInstr]

/-- Executing an instruction list preserves every register below `lo` when
    the list writes nothing below `lo`. This is `evalInstr_write` composed
    over `execInstrs`. -/
theorem execInstrs_preserves_below : ∀ (is : List Instr) (env env' : MIR.Env)
    (lo : Nat), WritesAbove lo is → execInstrs env is = some env' →
    ∀ x, x < lo → env' x = env x
  | [], env, env', lo, hw, h, x, hx => by
      simp only [execInstrs] at h
      injection h with heq
      exact heq ▸ rfl
  | i :: is, env, env', lo, hw, h, x, hx => by
      cases hi : evalInstr env i with
      | none => simp [execInstrs, hi] at h
      | some env1 =>
          simp only [execInstrs, hi] at h
          cases hreg : writtenReg i with
          | none =>
              rw [evalInstr_eq_none_of_no_write env i hreg] at hi
              simp at hi
          | some d =>
              have hw1 := hw.1
              simp [hreg] at hw1
              have hlo : lo ≤ d := hw1
              have hxd : x ≠ d := Nat.ne_of_lt (Nat.lt_of_lt_of_le hx hlo)
              have henv1 : env1 x = env x :=
                evalInstr_write env i env1 hi d hreg x hxd
              exact (execInstrs_preserves_below is env1 env' lo hw.2 h x hx).trans henv1

/-! ## Main correctness (statement recorded; proof in progress)

`lowerIn_correct` for a pure-arithmetic `e`:

    lowerIn_correct : ∀ fuel (0 < fuel) paramMap supply ctx env,
      Agrees paramMap ctx env → (∀ n, paramMap n < supply) →
      ∀ e, IsPureArith e →
        match lowerIn paramMap supply e with
        | none => exprVal (evalFuel fuel ctx e) = none
        | some (v, is, s) => ∃ env', execInstrs env is = some env' ∧
              env' v = exprVal (evalFuel fuel ctx e)

The theorem runs on `lowerIn.induct` (10 cases). The `lit`, non-`lit`,
`bvar` (vacuous — `IsPureArith` has no `bvar` constructor), and the
no-constructor cases are discharged. The three `binop` cases and three
`let` cases remain: they need (a) the extended-supply invariant
(`paramMap k < s1`, `va < s1`) re-established per case, and (b) a
literal-shape argument threading `exprVal`'s `some (.lit w)` through the
combined instruction list `ia ++ ib ++ [binop …]`. The written-avoidance
machinery above (`execInstrs_preserves_below`, `Agrees`, `agrees_bvar`) is
exactly what those steps need; the remaining work is their composition. -/

end Morph.Lowering