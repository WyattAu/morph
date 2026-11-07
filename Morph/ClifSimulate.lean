/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifLower

/-!
# Stage B item B4: simulation of a typed MIR trace by the CLIF model

`docs/STAGEB-SCOPE.md` §3–4. `agree_*` in `Morph/ClifLower.lean` proves one
instruction at a time; this file lifts that to a whole straight-line body.

## Why a trace relation rather than a bare hypothesis on `evalInstrFull`

The natural statement — "if `evalInstrFull` succeeds then `Clif.step` matches
it" — cannot be proved, because succeeding does not *expose* the operand values:
`evalInstrFull` either returns `none` or an environment, and the range hypothesis
Stage B needs is about the operands' values. Recovering them means inverting the
`do`-chain (`Option.bind`) case by case, which is mechanical but only reproduces
information the caller already had.

`Step` instead records what the fragment's typing judgement knows: the operand
shapes and the range fact for the value the instruction writes. It is a
*certificate*, exactly as `StraightStmts` was for Stage A — the fragment owes it,
and this file proves the certificate is enough. Two lemmas connect it in both
directions:

- `step_simulate` : one `Step` is one CLIF instruction, producing the same environment.
- `step_evalInstr` : one `Step` is the MIR step it claims to be, against `evalInstr`.

`run_simulate` then folds the first over an instruction list, which is the
content of `clif_simulate`; `Trace` + `instrEncodes` is what a `clif_correct`
composes with once the `evalInstrFull` bridge lands.

## What is deliberately not claimed

The certificate is a *premise*, not a conclusion: this does not prove that any
particular source program is in range, and it makes no claim about programs
outside the fragment. In-range-ness of intermediates is the fragment's obligation
and is discharged outside this file (eventually by a range analysis over the HIR).
-/

open Morph.Core
open Morph.MIR (ValId)

namespace Morph.Clif

/-- The values a register may hold in the fragment: an i64-range integer, or a
boolean. Anything else means the program left the fragment. -/
def ValInRange : Value → Prop
  | .int n => -(2 : Int) ^ 63 ≤ n ∧ n < (2 : Int) ^ 63
  | .bool _ => True
  | _ => False

/-- Wrapping is the identity on a value the fragment admits. Marked `@[simp]`
so that `hval : ValInRange (.int v)` in context discharges `wrap v = v` on its
own; the side condition is proved by assumption. -/
@[simp] theorem wrap_of_valInRange {n : Int} (h : ValInRange (.int n)) : wrap n = n :=
  wrap_eq_self h.1 h.2

/-- One fragment step: the operand shapes, the range fact for the written value,
and the environment transition. Every constructor corresponds to one `agree_*`
lemma and one `instrEncode` case. -/
inductive Step : Morph.MIR.Env → Morph.MIR.Instr → Morph.MIR.Env → Prop where
  | const {m : Morph.MIR.Env} {dst : ValId} {n : Int} (hval : ValInRange (.int n)) :
      Step m (.const dst (.int n)) (m.update dst (.int n))
  | add {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b))
      (hval : ValInRange (.int (a + b))) :
      Step m (.binop dst .add l r τ) (m.update dst (.int (a + b)))
  | sub {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b))
      (hval : ValInRange (.int (a - b))) :
      Step m (.binop dst .sub l r τ) (m.update dst (.int (a - b)))
  | mul {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b))
      (hval : ValInRange (.int (a * b))) :
      Step m (.binop dst .mul l r τ) (m.update dst (.int (a * b)))
  | eq {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
      Step m (.binop dst .eq l r τ) (m.update dst (.bool (a == b)))
  | neq {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
      Step m (.binop dst .neq l r τ) (m.update dst (.bool !(a == b)))
  | lt {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
      Step m (.binop dst .lt l r τ) (m.update dst (.bool (a < b)))
  | leq {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
      Step m (.binop dst .leq l r τ) (m.update dst (.bool (a ≤ b)))
  | gt {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
      Step m (.binop dst .gt l r τ) (m.update dst (.bool (a > b)))
  | geq {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
      Step m (.binop dst .geq l r τ) (m.update dst (.bool (a ≥ b)))
  | band {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Bool}
      (hl : m l = some (.bool a)) (hr : m r = some (.bool b)) :
      Step m (.binop dst .and l r τ) (m.update dst (.bool (a && b)))
  | bor {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Bool}
      (hl : m l = some (.bool a)) (hr : m r = some (.bool b)) :
      Step m (.binop dst .or l r τ) (m.update dst (.bool (a || b)))
  | shl {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b))
      (hb : 0 ≤ b ∧ b < 64) (hval : ValInRange (.int (a * Int.pow 2 b.toNat))) :
      Step m (.binop dst .shl l r τ) (m.update dst (.int (a * Int.pow 2 b.toNat)))
  | shr {m : Morph.MIR.Env} {dst l r : ValId} {τ : Typ} {a b : Int}
      (hl : m l = some (.int a)) (hr : m r = some (.int b))
      (hb : 0 ≤ b ∧ b < 64) :
      Step m (.binop dst .shr l r τ) (m.update dst (.int (Int.shiftRight a b.toNat)))
  | notb {m : Morph.MIR.Env} {dst src : ValId} {τ : Typ} {a : Int}
      (hl : m src = some (.int a)) (hval : ValInRange (.int (-a - 1))) :
      Step m (.unop dst .notb src τ) (m.update dst (.int (-a - 1)))

/-- A run of fragment steps over a straight-line body. -/
inductive Trace : List Morph.MIR.Instr → Morph.MIR.Env → Morph.MIR.Env → Prop where
  | nil (m : Morph.MIR.Env) : Trace [] m m
  | cons {is : List Morph.MIR.Instr} {i : Morph.MIR.Instr} {m m₁ m₂ : Morph.MIR.Env} :
      Step m i m₁ → Trace is m₁ m₂ → Trace (i :: is) m m₂

/-! ## One step, both ways -/

/-- A `Step` is exactly the CLIF instruction the encoder emits for it. -/
theorem step_simulate {m m' : Morph.MIR.Env} {i : Morph.MIR.Instr} {c : Instr}
    (h : Step m i m') (henc : instrEncode i = some c) : step m c = some m' := by
  -- Reduce `instrEncode` on the constructor, then substitute `c` so that the
  -- `match c` inside `step` reduces; `simp_all` alone rewrites the wrong way.
  cases h <;>
    (simp only [instrEncode, binopInstr, unopInstr, Option.some.injEq] at henc ⊢
     subst henc
     simp_all [step, asInt, asBool, evalCond, shiftAmount, update_eq_set])

/-- A `Step` is the MIR transition it records, against the pure evaluator. -/
theorem step_evalInstr {m m' : Morph.MIR.Env} {i : Morph.MIR.Instr}
    (h : Step m i m') : Morph.MIR.evalInstr m i = some m' := by
  cases h <;>
    simp_all [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.MIR.evalUnOp,
      Morph.Executable.evalBinop, Morph.Executable.evalUnop, Morph.MIR.BinOp.toOperator,
      Morph.MIR.UnOp.toOperator]

/-! ## Folding a trace -/

/-- `clif_simulate`: a typed trace and its encoding produce the same
environment. This is the instruction-fold half of `clif_correct`. -/
theorem run_simulate {is : List Morph.MIR.Instr} {m m' : Morph.MIR.Env} {cs : List Instr}
    (htr : Trace is m m') (henc : instrEncodes is = some cs) :
    runInstrs m cs = some m' := by
  induction htr generalizing cs with
  | nil =>
    simp only [instrEncodes, Option.some.injEq] at henc
    subst henc
    rfl
  | cons hstep _htr ih =>
    rcases instrEncodes_cons.mp henc with ⟨c, cs', henc1, henc2, rfl⟩
    have hst := step_simulate hstep henc1
    simp_all [runInstrs, ih henc2]

end Morph.Clif
