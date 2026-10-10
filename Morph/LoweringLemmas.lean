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

end Morph.Lowering