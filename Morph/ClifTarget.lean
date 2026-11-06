/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.MIR

/-!
# Stage B target model: the CLIF subset the encoder emits

`docs/STAGEB-SCOPE.md` §4.1. This is the *target* semantics for Stage B, not a
model of CLIF in general: it contains exactly the instructions the stage-B
encoder can emit (`iconst`, `iadd`, `isub`, `imul`, `icmp`, `band`, `bor`,
`bnot`, `ishl`, `sshr`) plus a single-block function with one return register.
An instruction with no agreement lemma would be an unproved obligation, so the
model grows only when a corresponding lemma lands.

Two design points that exist to make the Stage B theorem statable:

- **Fixed width is explicit.** Lean's `Value.int` is an unbounded `Int` and
  `MIR.evalBinOp` does plain `Int` arithmetic, while CLIF integers wrap at 64
  bits. `wrap` models the machine's wrap, and `wrap_eq_self` is the lemma that
  converts the range hypothesis of `docs/STAGEB-SCOPE.md` §1.1 into an
  equality. Without that hypothesis MIR and CLIF genuinely disagree — `2^63 + 1`
  is a value in one and a wrapped value in the other — so Stage B claims
  preservation only for in-range programs.
- **Shift amounts are checked at runtime in the model.** `ishl`/`sshr` return
  `none` unless `0 ≤ n < 64`, which is CLIF's defined range. The B3 agreement
  lemma discharges the check from the fragment's amount hypothesis rather than
  leaving it implicit.

Nothing here lowers MIR yet (B2) and nothing here proves agreement with MIR
(B3/B4); this file is the target the lowering is proved against.
-/

open Morph.Core

namespace Morph.Clif

/-- CLIF value number. SSA, scoped to a function, like `MIR.ValId`. -/
abbrev Reg := Nat

/-- Two's-complement wrapping to the i64 range, written with `Int`'s Euclidean
modulo so it is total and always lands in `[-2^63, 2^63)`. -/
def wrap (x : Int) : Int :=
  (x + (2 : Int) ^ 63) % (2 : Int) ^ 64 - (2 : Int) ^ 63

/-- `wrap` is the identity on representable values. This is the only fact about
`wrap` the Stage B correctness theorem needs, and it is why that theorem carries
a range hypothesis: outside these bounds `wrap x ≠ x`, so no preservation claim
is available (and none is made). -/
theorem wrap_eq_self {x : Int} (hlo : -(2 : Int) ^ 63 ≤ x) (hhi : x < (2 : Int) ^ 63) :
    wrap x = x := by
  have h63 : ((2 : Int) ^ 63) = 9223372036854775808 := by decide
  have h64 : ((2 : Int) ^ 64) = 18446744073709551616 := by decide
  rw [h63] at hlo hhi
  unfold wrap
  rw [h63, h64]
  have h1 : 0 ≤ x + 9223372036854775808 := by omega
  have h2 : x + 9223372036854775808 < 18446744073709551616 := by omega
  rw [Int.emod_eq_of_lt h1 h2]
  omega

/-- `wrap` output is always in range, which lets a simulation keep its range
invariant across clauses that introduce new values. -/
theorem wrap_bounds (x : Int) :
    -(2 : Int) ^ 63 ≤ wrap x ∧ wrap x < (2 : Int) ^ 63 := by
  have h63 : ((2 : Int) ^ 63) = 9223372036854775808 := by decide
  have h64 : ((2 : Int) ^ 64) = 18446744073709551616 := by decide
  unfold wrap
  rw [h63, h64]
  have hpos : (0 : Int) < 18446744073709551616 := by decide
  have hnonneg : 0 ≤ (x + 9223372036854775808) % 18446744073709551616 :=
    Int.emod_nonneg _ (by omega)
  have hlt : (x + 9223372036854775808) % 18446744073709551616 < 18446744073709551616 :=
    Int.emod_lt_of_pos _ hpos
  constructor <;> omega

/-- `icmp` conditions, restricted to the ones the encoder emits. -/
inductive Cond where
  | eq | ne | slt | sle | sgt | sge
  deriving Repr, BEq, DecidableEq, DecidableEq

/-- The CLIF instruction subset of Stage B. Every constructor has (or will have)
a per-operator agreement lemma in `Morph/ClifLower.lean`; `iconst` takes an
`Int` because the encoder only emits integer and 0/1 constants (`bool` is an
`i8` 0/1 and is materialised as `.bool` in the model's `Env`). -/
inductive Instr where
  | iconst (dst : Reg) (v : Int)
  | iadd (dst : Reg) (l r : Reg)
  | isub (dst : Reg) (l r : Reg)
  | imul (dst : Reg) (l r : Reg)
  | icmp (dst : Reg) (c : Cond) (l r : Reg)
  | band (dst : Reg) (l r : Reg)
  | bor (dst : Reg) (l r : Reg)
  | bnot (dst : Reg) (src : Reg)
  | ishl (dst : Reg) (l r : Reg)
  | sshr (dst : Reg) (l r : Reg)
  deriving Repr, BEq

/-- A single-block CLIF function: straight-line instructions and the register
whose value is returned. Stage B's fragment is single-block by construction
(`StraightStmts 256`), so there is no terminator beyond the return. -/
structure Func where
  instrs : List Instr
  retSrc : Reg
  deriving Repr, BEq

/-- CLIF register file, partial like `MIR.Env`. -/
abbrev Env := Reg → Option Value

/-- Functional update on the register file. -/
def Env.set (env : Env) (r : Reg) (v : Value) : Env :=
  fun r' => if r' = r then some v else env r'

@[simp] theorem Env.set_same (env : Env) (r : Reg) (v : Value) : env.set r v r = some v := by
  simp [Env.set]

theorem Env.set_other (env : Env) {r r' : Reg} (v : Value) (h : r' ≠ r) :
    env.set r v r' = env r' := by
  simp [Env.set, h]

/-- Integer view of a value, `none` for non-integers (`iconst`/`iadd` on a
`bool` register is a mistyped program, exactly as in the MIR oracle). -/
def asInt : Value → Option Int
  | .int n => some n
  | _ => none

/-- Boolean view of a value. -/
def asBool : Value → Option Bool
  | .bool b => some b
  | _ => none

/-- `icmp` on the value domain. Integer comparisons cover all six conditions;
boolean registers support `eq`/`ne` (an `i8` compare), matching what the encoder
emits for MIR's boolean comparisons. -/
def evalCond (c : Cond) (v1 v2 : Value) : Option Value :=
  match v1, v2 with
  | .int a, .int b =>
    some (.bool (match c with
      | .eq => a == b | .ne => a != b
      | .slt => a < b | .sle => a ≤ b
      | .sgt => a > b | .sge => a ≥ b))
  | .bool a, .bool b =>
    match c with
      | .eq => some (.bool (a == b))
      | .ne => some (.bool (a != b))
      | _ => none
  | _, _ => none

/-- Shift amount for `ishl`/`sshr`: CLIF defines shifts for `0 ≤ n < 64` and
nothing outside it, so the model stalls there instead of inventing a convention. -/
def shiftAmount (v : Value) : Option Nat :=
  match v with
  | .int n => if 0 ≤ n ∧ n < 64 then some n.toNat else none
  | _ => none

/-- Execute one instruction. -/
def step (env : Env) : Instr → Option Env
  | .iconst dst v => some (env.set dst (.int (wrap v)))
  | .iadd dst l r => do
    let a ← asInt (← env l)
    let b ← asInt (← env r)
    some (env.set dst (.int (wrap (a + b))))
  | .isub dst l r => do
    let a ← asInt (← env l)
    let b ← asInt (← env r)
    some (env.set dst (.int (wrap (a - b))))
  | .imul dst l r => do
    let a ← asInt (← env l)
    let b ← asInt (← env r)
    some (env.set dst (.int (wrap (a * b))))
  | .icmp dst c l r => do
    let v ← evalCond c (← env l) (← env r)
    some (env.set dst v)
  | .band dst l r => do
    let a ← asBool (← env l)
    let b ← asBool (← env r)
    some (env.set dst (.bool (a && b)))
  | .bor dst l r => do
    let a ← asBool (← env l)
    let b ← asBool (← env r)
    some (env.set dst (.bool (a || b)))
  | .bnot dst src => do
    let a ← asBool (← env src)
    some (env.set dst (.bool (!a)))
  | .ishl dst l r => do
    let a ← asInt (← env l)
    let n ← shiftAmount (← env r)
    some (env.set dst (.int (wrap (a * (2 : Int) ^ n))))
  | .sshr dst l r => do
    let a ← asInt (← env l)
    let n ← shiftAmount (← env r)
    -- Arithmetic (floor) shift right: `Int`'s Euclidean division by a positive
    -- divisor is floor division, which is what `sshr` computes.
    some (env.set dst (.int (a / (2 : Int) ^ n)))

/-- Run a straight-line instruction list. -/
def runInstrs (env : Env) : List Instr → Option Env
  | [] => some env
  | i :: is => (step env i) >>= fun env' => runInstrs env' is

/-- Run a single-block function from an empty register file and read the return
register. This is the Stage B counterpart of `MIR.execFunc`. -/
def run (f : Func) : Option Value :=
  (runInstrs (fun _ => none) f.instrs) >>= fun env => env f.retSrc

end Morph.Clif
