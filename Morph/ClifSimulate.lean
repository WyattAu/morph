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
lemma and one `instrEncode` case — except `const_unit`, the entry prologue:
it reads nothing, so transport is unconditional, but it has no CLIF counterpart
(`instrEncode` rejects it) and the encoder drops it (`stripPrologue`). -/
inductive Step : Morph.MIR.Env → Morph.MIR.Instr → Morph.MIR.Env → Prop where
  | const {m : Morph.MIR.Env} {dst : ValId} {n : Int} (hval : ValInRange (.int n)) :
      Step m (.const dst (.int n)) (m.update dst (.int n))
  | const_unit {m : Morph.MIR.Env} {dst : ValId} :
      Step m (.const dst .unit) (m.update dst .unit)
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
    (simp only [instrEncode, binopInstr, unopInstr, Option.some.injEq, reduceCtorEq] at henc ⊢
     all_goals
       (subst henc
        simp_all [step, asInt, asBool, evalCond, shiftAmount, update_eq_set]))

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

/-! ## Store preservation, and the store-aware semantics

`evalInstr` is the pure evaluator; `execInstrsFull`/`execFunc` walk
`evalInstrFull`, which carries the heap. Every instruction in the fragment is
pure, so a `Trace` is also an execution of `execInstrsFull` with the store
untouched. That is the connection `compile_total` speaks in.
-/

/-- A `Step` is a `evalInstrFull` step with an unchanged store. -/
theorem step_execInstrFull {m m' : Morph.MIR.Env} {i : Morph.MIR.Instr}
    (h : Step m i m') (σ : Morph.Store) :
    Morph.MIR.evalInstrFull ⟨m, σ⟩ i = some ⟨m', σ⟩ := by
  cases h <;>
    simp_all [Morph.MIR.evalInstrFull, Morph.MIR.evalBinOp, Morph.MIR.evalUnOp,
      Morph.Executable.evalBinop, Morph.Executable.evalUnop, Morph.MIR.BinOp.toOperator,
      Morph.MIR.UnOp.toOperator]

/-- A whole `Trace` is an `execInstrsFull` run that leaves the store alone. -/
theorem trace_execInstrsFull {is : List Morph.MIR.Instr} {m m' : Morph.MIR.Env}
    (htr : Trace is m m') (σ : Morph.Store) :
    Morph.MIR.execInstrsFull ⟨m, σ⟩ is = some ⟨m', σ⟩ := by
  induction htr with
  | nil => rfl
  | cons hstep _ ih =>
    simp only [Morph.MIR.execInstrsFull, step_execInstrFull hstep]
    exact ih

/-! ## The unit register

`lowerProgram` prefixes the program body with `.const 0 .unit` (the accumulator
prologue), so a MIR execution of the lowered body starts from
`update (fun _ => none) 0 .unit`, while `Clif.run` starts from `fun _ => none`.
The two register files differ at register 0 only, which holds `.unit` — a value
no `Step` constructor can read, because every one of them demands `.int` or
`.bool`. `AgreesOnValues` names that difference, and the transport lemma below
shows it is invisible to a whole trace.

This is why Stage B's encoder can reject `.const dst .unit` (CLIF has no unit
value) and still cover the prologue: the prologue is dropped from the emitted
function, not mistranslated.
-/

@[simp] theorem int_ne_unit {n : Int} : (.int n : Value) ≠ .unit := by
  intro h
  cases h

@[simp] theorem bool_ne_unit {b : Bool} : (.bool b : Value) ≠ .unit := by
  intro h
  cases h

/-- `m₂` agrees with `m₁` on every value that is not `.unit`. The direction is
chosen so that a trace *over `m₁`* transports to `m₂`: the hypothesis is about
what `m₁` holds, and the conclusion is what `m₂` reads. -/
def AgreesOnValues (m₁ m₂ : Morph.MIR.Env) : Prop :=
  ∀ (x : ValId) (v : Value), m₁ x = some v → v ≠ .unit → m₂ x = some v

/-- Agreement survives a register write. The proof goes through `Env.set`
(`update_eq_set`): `MIR.Env.update` tests `x == d` with `BEq`, which `simp` will
not reduce definitionally, while `Clif.Env.set` tests `x = d` and already has
`set_same`/`set_other`. -/
theorem agrees_update {m₁ m₂ : Morph.MIR.Env} (hag : AgreesOnValues m₁ m₂)
    (d : ValId) (value : Value) :
    AgreesOnValues (m₁.update d value) (m₂.update d value) := by
  intro x v hx hne
  rw [update_eq_set] at hx ⊢
  unfold Env.set at hx ⊢
  by_cases hxd : x = d
  · subst hxd
    simp at hx
    simpa using hx
  · simp [hxd] at hx ⊢
    exact hag x v hx hne

/-- The prologue environment agrees with the empty one on every non-unit value. -/
theorem agrees_prologue (m : Morph.MIR.Env) :
    AgreesOnValues (m.update 0 .unit) m := by
  intro x v hx hne
  rw [update_eq_set] at hx
  unfold Env.set at hx
  by_cases hx0 : x = 0
  · subst hx0
    simp at hx
    subst hx
    exact absurd rfl hne
  · simp [hx0] at hx
    exact hx

/-- One step transports across an agreement: the same instruction, over `m₂`,
produces a value-agreeing environment. Writes are to the same register with the
same value, because every operand the step reads is an `.int`/`.bool`, which
agreement reproduces exactly. -/
theorem step_transport {m₁ m₂ m₁' : Morph.MIR.Env} {i : Morph.MIR.Instr}
    (h : Step m₁ i m₁') (hag : AgreesOnValues m₁ m₂) :
    ∃ m₂', Step m₂ i m₂' ∧ AgreesOnValues m₁' m₂' := by
  cases h with
  | const hval =>
    exact ⟨_, .const hval, agrees_update hag _ _⟩
  | const_unit =>
    exact ⟨_, .const_unit, agrees_update hag _ _⟩
  | add hl hr hval =>
    exact ⟨_, .add (hag _ _ hl (by simp)) (hag _ _ hr (by simp)) hval,
      agrees_update hag _ _⟩
  | sub hl hr hval =>
    exact ⟨_, .sub (hag _ _ hl (by simp)) (hag _ _ hr (by simp)) hval,
      agrees_update hag _ _⟩
  | mul hl hr hval =>
    exact ⟨_, .mul (hag _ _ hl (by simp)) (hag _ _ hr (by simp)) hval,
      agrees_update hag _ _⟩
  | eq hl hr =>
    exact ⟨_, .eq (hag _ _ hl (by simp)) (hag _ _ hr (by simp)), agrees_update hag _ _⟩
  | neq hl hr =>
    exact ⟨_, .neq (hag _ _ hl (by simp)) (hag _ _ hr (by simp)), agrees_update hag _ _⟩
  | lt hl hr =>
    exact ⟨_, .lt (hag _ _ hl (by simp)) (hag _ _ hr (by simp)), agrees_update hag _ _⟩
  | leq hl hr =>
    exact ⟨_, .leq (hag _ _ hl (by simp)) (hag _ _ hr (by simp)), agrees_update hag _ _⟩
  | gt hl hr =>
    exact ⟨_, .gt (hag _ _ hl (by simp)) (hag _ _ hr (by simp)), agrees_update hag _ _⟩
  | geq hl hr =>
    exact ⟨_, .geq (hag _ _ hl (by simp)) (hag _ _ hr (by simp)), agrees_update hag _ _⟩
  | band hl hr =>
    exact ⟨_, .band (hag _ _ hl (by simp)) (hag _ _ hr (by simp)), agrees_update hag _ _⟩
  | bor hl hr =>
    exact ⟨_, .bor (hag _ _ hl (by simp)) (hag _ _ hr (by simp)), agrees_update hag _ _⟩
  | shl hl hr hb hval =>
    exact ⟨_, .shl (hag _ _ hl (by simp)) (hag _ _ hr (by simp)) hb hval,
      agrees_update hag _ _⟩
  | shr hl hr hb =>
    exact ⟨_, .shr (hag _ _ hl (by simp)) (hag _ _ hr (by simp)) hb, agrees_update hag _ _⟩
  | notb hl hval =>
    exact ⟨_, .notb (hag _ _ hl (by simp)) hval, agrees_update hag _ _⟩

/-- A whole trace transports across an agreement. -/
theorem trace_transport {is : List Morph.MIR.Instr} {m₁ m₂ m₁' : Morph.MIR.Env}
    (htr : Trace is m₁ m₁') (hag : AgreesOnValues m₁ m₂) :
    ∃ m₂', Trace is m₂ m₂' ∧ AgreesOnValues m₁' m₂' := by
  induction htr generalizing m₂ with
  | nil => exact ⟨_, .nil _, hag⟩
  | cons hstep _ ih =>
    obtain ⟨m₂₁, hstep₂, hag₁⟩ := step_transport hstep hag
    obtain ⟨m₂₂, htr₂, hag₂⟩ := ih hag₁
    exact ⟨m₂₂, .cons hstep₂ htr₂, hag₂⟩

/-! ## The block-level theorem -/

/-- Invert `blockEncode`: the emitted function's body is the encoding of the
block's instruction list, and its return register is the block's. -/
theorem blockEncode_return {instrs : List Morph.MIR.Instr} {ret : ValId}
    {is' : List Instr} {rc : Reg}
    (h : blockEncode ⟨0, instrs, .return_ ret⟩ = some ⟨is', rc⟩) :
    instrEncodes instrs = some is' ∧ rc = ret := by
  simp only [blockEncode] at h
  cases hc : instrEncodes instrs with
  | none =>
    rw [hc] at h
    exact absurd h (by simp)
  | some cs =>
    rw [hc] at h
    -- `simp only` matches syntactically, so expose the `Option.map` redex first.
    have heq : Func.mk cs ret = Func.mk is' rc := Option.some.inj h
    obtain ⟨h1, h2⟩ : cs = is' ∧ ret = rc := Func.mk.inj heq
    -- `cases hc :` replaced `instrEncodes instrs` in the goal by `some cs`, so
    -- the branch closes reflexively; `hc` restores the general statement.
    rw [← h1, ← h2]
    exact ⟨rfl, rfl⟩

/-- `clif_correct` for a straight-line body: an encodable block whose MIR
execution is certified by a `Trace` runs in the CLIF model to the same value.

The trace starts at the prologue environment `update (fun _ => none) 0 .unit`,
which is what `lowerProgram` produces; `Clif.run` starts from the empty register
file, and the difference at register 0 is invisible (`trace_transport`). -/
theorem clif_correct {instrs : List Morph.MIR.Instr} {ret : ValId} {cf : Func}
    {m' : Morph.MIR.Env} {w : Int}
    (henc : blockEncode ⟨0, instrs, .return_ ret⟩ = some cf)
    (htr : Trace instrs (Morph.MIR.Env.update (fun _ => none) 0 .unit) m')
    (hret : m' ret = some (.int w)) :
    run cf = some (.int w) := by
  cases cf with
  | mk is' rc =>
    obtain ⟨hcs, hrc⟩ := blockEncode_return henc
    obtain ⟨m₂, htr₂, hag⟩ := trace_transport htr (agrees_prologue (fun _ => none))
    have hrun := run_simulate htr₂ hcs
    have hval : m₂ rc = some (.int w) := by
      rw [hrc]
      exact hag ret (.int w) hret (by simp)
    simp only [run, hrun]
    exact hval

/-! ## Call simulation (Stage C, item C8 remainder)

B4's `run_simulate` starts its trace at the prologue environment; a callee
starts its trace at the bound-argument environment instead. The two binders
supply the two sides (`MIR.bindCallArgs` for the trace, `bindCArgs` for the
CLIF run), and the value-passing bridge rewrites one to the other, so the
trace does the rest. `callee_correct` is the `runCallee`-level statement: a
call-free, encodable callee body run from the same argument values returns
the trace's return register on both sides. The certificate discipline is
B4's — the fragment (a range analysis) owes the `Trace`, this file says the
certificate is enough. -/

/-- A typed trace run from a bound-argument environment reaches the same
environment on the CLIF side, when the binders agree. -/
theorem call_simulate {is : List Morph.MIR.Instr} {cs : List Instr}
    {ps : List (Morph.MIR.ValId × Typ)} {rs : List Reg} {ws : List Value}
    {menv m' : Morph.MIR.Env} {cenv : Env}
    (hregs : ps.map Prod.fst = rs)
    (hm : Morph.MIR.bindCallArgs ps ws = some menv)
    (hc : bindCArgs rs ws = some cenv)
    (htr : Trace is menv m') (henc : instrEncodes is = some cs) :
    runInstrs cenv cs = some m' := by
  have heq : menv = cenv := bindCallArgs_bindCArgs_agree hregs hm hc
  subst heq
  exact run_simulate htr henc

/-- A resolved callee runs to the same value on both sides. -/
theorem callee_correct {is : List Morph.MIR.Instr} {cs : List Instr}
    {ps : List (Morph.MIR.ValId × Typ)} {rs : List Reg} {ws : List Value}
    {menv : Morph.MIR.Env} {cenv : Env} {m' : Morph.MIR.Env}
    {cf : CFunc} {ret : Reg} {w : Value}
    (hregs : ps.map Prod.fst = rs)
    (hm : Morph.MIR.bindCallArgs ps ws = some menv)
    (hc : bindCArgs rs ws = some cenv)
    (hbody : cf.body = ⟨cs, ret⟩)
    (hsig : cf.sig = rs)
    (htr : Trace is menv m') (henc : instrEncodes is = some cs)
    (hret : m' ret = some w) :
    runCallee cf ws = some w := by
  have hrun : runInstrs cenv cs = some m' :=
    call_simulate hregs hm hc htr henc
  have hbind : bindCArgs cf.sig ws = some cenv := by rw [hsig]; exact hc
  have hins : cf.body.instrs = cs := by simp [hbody]
  have hretSrc : cf.body.retSrc = ret := by simp [hbody]
  simp only [runCallee, hbind, hins, hrun, hretSrc]
  exact hret

/-! ## Typed call simulation (D-7 option B, slice B2)

The same two statements over the typed binder: a successful typed bind
has already checked every actual, so `bindCallArgs_bindTArgs_agree`
rewrites the trace environment to the typed one and the trace does
the rest. The encoder hypothesis keeps the default (empty) program,
so an encodable callee body is call-free by construction — the typed
layer certifies the leaf calls slice B1 admits. -/

/-- A typed trace run from a bound-argument environment reaches the same
environment on the CLIF side, when the binders agree. -/
theorem call_simulate_typed {is : List Morph.MIR.Instr} {cs : List Instr}
    {ps : List (Morph.MIR.ValId × Typ)} {ts : TSig} {ws : List Value}
    {menv : Morph.MIR.Env} {tenv : Env} {m' : Morph.MIR.Env}
    (h : ps = ts)
    (hm : Morph.MIR.bindCallArgs ps ws = some menv)
    (ht : bindTArgs ts ws = some tenv)
    (htr : Trace is menv m') (henc : instrEncodes is = some cs) :
    runInstrs tenv cs = some m' := by
  have heq : menv = tenv := bindCallArgs_bindTArgs_agree h hm ht
  subst heq
  exact run_simulate htr henc

/-- A resolved typed callee runs to the same value on both sides. -/
theorem tcallee_correct {is : List Morph.MIR.Instr} {cs : List Instr}
    {ps : List (Morph.MIR.ValId × Typ)} {ts : TSig} {ws : List Value}
    {menv : Morph.MIR.Env} {tenv : Env} {m' : Morph.MIR.Env}
    {cf : TCFunc} {ret : Reg} {w : Value}
    (h : ps = ts)
    (hm : Morph.MIR.bindCallArgs ps ws = some menv)
    (ht : bindTArgs ts ws = some tenv)
    (hbody : cf.body = ⟨cs, ret⟩)
    (hsig : cf.tsig = ts)
    (htr : Trace is menv m') (henc : instrEncodes is = some cs)
    (hret : m' ret = some w) :
    runTCallee cf ws = some w := by
  have hrun : runInstrs tenv cs = some m' :=
    call_simulate_typed h hm ht htr henc
  have hbind : bindTArgs cf.tsig ws = some tenv := by rw [hsig]; exact ht
  have hins : cf.body.instrs = cs := by simp [hbody]
  have hretSrc : cf.body.retSrc = ret := by simp [hbody]
  simp only [runTCallee, hbind, hins, hrun, hretSrc]
  exact hret

end Morph.Clif
