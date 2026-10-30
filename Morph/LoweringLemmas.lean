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

/-- Structural helpers for `WritesAbove`. `WritesAbove` is defined by
    pattern matching, so `constructor`/`⟨⟩` cannot split it; these lemmas
    give the combination rules directly. -/

theorem WritesAbove.snoc : ∀ (lo : Nat) (is : List Instr) (i : Instr),
    WritesAbove lo is →
    (match writtenReg i with | some d => lo ≤ d | none => True) →
    WritesAbove lo (is ++ [i]) := by
  intro lo is i hw hi
  induction is with
  | nil => exact ⟨hi, trivial⟩
  | cons j js ihj =>
      simp only [List.cons_append]
      exact ⟨hw.1, ihj hw.2⟩

theorem WritesAbove.append' : ∀ (lo : Nat) (is js : List Instr),
    WritesAbove lo is → WritesAbove lo js → WritesAbove lo (is ++ js) := by
  intro lo is js hw hj
  induction is with
  | nil => simpa using hj
  | cons i is ihi =>
      exact ⟨hw.1, ihi hw.2⟩

/-! ## The extended-supply invariant -/

/-- The extended-supply invariant, for pure-arithmetic expressions only:
    lowering `a` from `supply` never reuses a parameter register and never
    allocates below the new supply. Induction is on `IsPureArith` (a
    non-nested inductive), whose three constructors line up exactly with the
    three forms `lowerIn` lowers. -/
theorem advances_pure (a : Expr) (hpa : IsPureArith a)
    (paramMap : Nat → ValId) (supply : Nat) (hpm : ∀ n, paramMap n < supply) :
    match lowerIn paramMap supply a with
    | none => True
    | some (v, _is, s) => supply ≤ s ∧ v < s ∧ ∀ k, paramMap k < s :=
  IsPureArith.rec (motive := fun a _ =>
    (paramMap : Nat → ValId) → (supply : Nat) → (∀ n, paramMap n < supply) →
    match lowerIn paramMap supply a with
    | none => True
    | some (v, _is, s) => supply ≤ s ∧ v < s ∧ ∀ k, paramMap k < s)
    (fun n paramMap supply hpm => by
      simp only [lowerIn]
      refine ⟨?_, Nat.lt_succ_self _, fun k => Nat.lt_trans (hpm k) ?_⟩ <;> omega)
    (fun bop a b hop _ _ iha ihb paramMap supply hpm => by
      simp only [lowerIn, hop]
      cases hA : lowerIn paramMap supply a with
      | none => simp
      | some valA =>
        rcases valA with ⟨va, ia, s1⟩
        cases hB : lowerIn paramMap s1 b with
        | none => simp [hB]
        | some valB =>
          rcases valB with ⟨vb, ib, s2⟩
          have h1 := iha paramMap supply hpm
          rw [hA] at h1
          have h2 := ihb paramMap s1 h1.2.2
          rw [hB] at h2
          simp only [hB]
          refine ⟨?_, Nat.lt_succ_self _, fun k => Nat.lt_trans (h2.2.2 k) ?_⟩ <;> omega)
    (fun a b _ _ iha ihb paramMap supply hpm => by
      simp only [lowerIn]
      cases hA : lowerIn paramMap supply a with
      | none => simp
      | some valA =>
        rcases valA with ⟨va, ia, s1⟩
        have h1 := iha paramMap supply hpm
        rw [hA] at h1
        have hpm' : ∀ n, (fun n => if n = 0 then va else paramMap (n - 1)) n < s1 := by
          intro n
          cases n with
          | zero => exact h1.2.1
          | succ k => exact Nat.lt_of_lt_of_le (hpm k) h1.1
        cases hB : lowerIn (fun n => if n = 0 then va else paramMap (n - 1)) s1 b with
        | none => simp [hB]
        | some valB =>
          rcases valB with ⟨vb, ib, s2⟩
          have h2 := ihb (fun n => if n = 0 then va else paramMap (n - 1)) s1 hpm'
          rw [hB] at h2
          simp only [hB]
          refine ⟨Nat.le_trans h1.1 h2.1, h2.2.1, ?_⟩
          intro k
          cases k with
          | zero =>
              exact Nat.lt_of_lt_of_le (hpm 0) (Nat.le_trans h1.1 h2.1)
          | succ k' =>
              have hkk := h2.2.2 (k' + 2)
              show paramMap (k' + 1) < s2
              rw [show (fun n => if n = 0 then va else paramMap (n - 1)) (k' + 2) = paramMap (k' + 1) from rfl] at hkk
              exact hkk)
    hpa paramMap supply hpm

/-! ## Lowering writes only above the supply -/

theorem lowerIn_writes_above (a : Expr) (hpa : IsPureArith a)
    (paramMap : Nat → ValId) (supply : Nat) (hpm : ∀ n, paramMap n < supply) :
    match lowerIn paramMap supply a with
    | none => True
    | some (_v, is, _s) => WritesAbove supply is :=
    IsPureArith.rec (motive := fun a _ => (paramMap : Nat → ValId) → (supply : Nat) →
      (∀ n, paramMap n < supply) →
      match lowerIn paramMap supply a with
      | none => True
      | some (v, is, s) => WritesAbove supply is)
      (fun n paramMap supply _hpm => by
        simp only [lowerIn]
        exact ⟨Nat.le_refl _, trivial⟩)
      (fun bop a b hop _ _ iha ihb paramMap supply hpm => by
        simp only [lowerIn, hop]
        cases hA : lowerIn paramMap supply a with
        | none => simp
        | some valA =>
          rcases valA with ⟨va, rest⟩; rcases rest with ⟨ia, s1⟩
          have hia := iha paramMap supply hpm
          simp only [hA] at hia
          have h1 := advances_pure a ‹IsPureArith a› paramMap supply hpm
          simp only [hA] at h1
          cases hB : lowerIn paramMap s1 b with
          | none => simp [hB]
          | some valB =>
            rcases valB with ⟨vb, rest⟩; rcases rest with ⟨ib, s2⟩
            have hib := ihb paramMap s1 h1.2.2
            rw [hB] at hib
            -- the extended-supply invariant for `b`: s1 ≤ s2
            have h2 := advances_pure b ‹IsPureArith b› paramMap s1 h1.2.2
            rw [hB] at h2
            simp only [hB, List.append_assoc]
            -- `ia` above `supply`; `ib` above `s1 ≥ supply`; the trailing
            -- `binop` writes `s2`, and `supply ≤ s1 ≤ s2`
            have hia' : WritesAbove supply ia := hia
            have hib' := WritesAbove.anti_mono supply s1 ib h1.1 hib
            refine WritesAbove.append' supply ia (ib ++ [Instr.binop s2 bop va vb .intType]) hia' ?_
            exact WritesAbove.snoc supply ib (Instr.binop s2 bop va vb .intType) hib' (by
              simp only [writtenReg]
              exact Nat.le_trans h1.1 h2.1))
      (fun a b _ _ iha ihb paramMap supply hpm => by
        simp only [lowerIn]
        cases hA : lowerIn paramMap supply a with
        | none => simp
        | some valA =>
          rcases valA with ⟨va, rest⟩; rcases rest with ⟨ia, s1⟩
          have hia := iha paramMap supply hpm
          simp only [hA] at hia
          have h1 := advances_pure a ‹IsPureArith a› paramMap supply hpm
          simp only [hA] at h1
          have hpm' : ∀ n, (fun n => if n = 0 then va else paramMap (n - 1)) n < s1 := by
            intro n
            cases n with
            | zero => exact h1.2.1
            | succ k => exact Nat.lt_of_lt_of_le (hpm k) h1.1
          cases hB : lowerIn (fun n => if n = 0 then va else paramMap (n - 1)) s1 b with
          | none => simp [hB]
          | some valB =>
            rcases valB with ⟨vb, rest⟩; rcases rest with ⟨ib, s2⟩
            have hib := ihb _ _ hpm'
            rw [hB] at hib
            simp only [hB]
            exact WritesAbove.append' supply ia ib hia
              (WritesAbove.anti_mono supply s1 ib h1.1 hib))
      hpa paramMap supply hpm

/-! ## Lowering rejection mirrors interpreter stuckness -/

set_option linter.unusedVariables false in
/-- Lowering rejection mirrors interpreter stuckness, for **any** fuel:
    if `lowerIn` rejects a pure-arithmetic expression, `evalFuel` produces
    nothing at any fuel level. This is the `none` branch of `lowerIn_correct`
    — the interpreter is stuck exactly where lowering gave up. -/
theorem evalStuck : ∀ (a : Expr) (hpa : IsPureArith a) (paramMap : Nat → ValId)
    (supply fuel : Nat) (ctx : Context),
    lowerIn paramMap supply a = none → evalFuel fuel ctx a = none :=
  fun a hpa =>
    IsPureArith.rec (motive := fun a _ => (paramMap : Nat → ValId) → (supply : Nat) →
      (fuel : Nat) → (ctx : Context) → lowerIn paramMap supply a = none →
      evalFuel fuel ctx a = none)
      (fun n paramMap supply fuel ctx h => by simp [lowerIn] at h)
      (fun bop a b hop _ _ iha ihb paramMap supply fuel ctx h => by
        cases fuel with
        | zero => simp [evalFuel]
        | succ k =>
          simp only [lowerIn, hop] at h
          cases hA : lowerIn paramMap supply a with
          | none =>
            have hst := iha paramMap supply k ctx hA
            simp [evalFuel, hst]
          | some valA =>
            rcases valA with ⟨va, rest⟩; rcases rest with ⟨ia, s1⟩
            cases hB : lowerIn paramMap s1 b with
            | none =>
              have hst := ihb paramMap s1 k ctx hB
              simp [evalFuel, hst]
                        | some valB =>
              -- both sides lower, but `h` says lowering failed: contradiction
              simp only [hA, hB] at h
              exact absurd h (by simp))
      (fun a b _ _ iha ihb paramMap supply fuel ctx h => by
        cases fuel with
        | zero => simp [evalFuel]
        | succ k =>
          cases hA : lowerIn paramMap supply a with
          | none =>
            have hst := iha paramMap supply k ctx hA
            simp [evalFuel, hst]
          | some valA =>
            rcases valA with ⟨va, rest⟩; rcases rest with ⟨ia, s1⟩
            -- `a` lowers, so `h` forces `b` to be stuck; the interpreter
            -- evaluates `a` first and propagates the stuckness from `b`
            cases hB : lowerIn (fun n => if n = 0 then va else paramMap (n - 1)) s1 b with
            | none =>
              -- `b` is stuck for `lowerIn`; the interpreter reaches `b` in the
              -- pushed context only when `a` succeeded, which is the case here
              rw [evalFuel]
              simp only [bind]
              cases hv : evalFuel k ctx a with
              | none =>
                -- `a` is stuck for the interpreter too, so the whole `let`
                -- is stuck without ever reaching `b`
                simp
              | some v1 =>
                have hst := ihb _ _ k (ctx.pushBv v1) hB
                simp only [Option.bind_some]
                rw [hst]
            | some valB => simp [lowerIn, hA, hB] at h)
      hpa

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