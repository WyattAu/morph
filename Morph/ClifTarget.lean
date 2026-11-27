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

`sshr` computes `Int.shiftRight`, the same primitive the MIR oracle uses for
`.shr`, so the arithmetic-shift agreement is definitional rather than a proof
about division. `bnot` is the i64 bitwise complement (hence `-a - 1` under two's
complement), which pairs with MIR's `.notb`; MIR's `.not` is *boolean* negation
and needs a different CLIF idiom, so the encoder rejects it.

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

/-- The CLIF instruction subset of Stage B, plus a named `call` (D-7
option B slice A). Every constructor has (or will have)
a per-operator agreement lemma in `Morph/ClifLower.lean`; `iconst` takes an
`Int` because `Value` payloads other than integers have no encoding in this
subset, so the encoder rejects `.const` with a non-integer payload rather than
inventing one. `call` names the callee, the actual registers, and the
declared return type; bare `step` cannot resolve the callee, so calls stall
there and run additively (`runCallee`/`runCall`) instead. -/
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
  | call (dst : Reg) (fn : String) (args : List Reg) (ret : Typ)
  deriving Repr, BEq

/-- A single-block CLIF function: straight-line instructions and the register
whose value is returned. Stage B's fragment is single-block by construction
(`StraightStmts 256`), so there is no terminator beyond the return. -/
structure Func where
  params : List (Reg × Typ)
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
      | .eq => a == b | .ne => !(a == b)
      | .slt => a < b | .sle => a ≤ b
      | .sgt => a > b | .sge => a ≥ b))
  | .bool a, .bool b =>
    match c with
      | .eq => some (.bool (a == b))
      | .ne => some (.bool !(a == b))
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
    let a ← asInt (← env src)
    some (env.set dst (.int (wrap (-a - 1))))
  | .ishl dst l r => do
    let a ← asInt (← env l)
    let n ← shiftAmount (← env r)
    -- `Int.pow 2 n` is `2 ^ n`; it is spelled the oracle's way so the agreement
    -- lemma needs no power-conversion bridge.
    some (env.set dst (.int (wrap (a * Int.pow 2 n))))
  | .sshr dst l r => do
    let a ← asInt (← env l)
    let n ← shiftAmount (← env r)
    -- `Int.shiftRight` is floor division by `2^n` (`Int.shiftRight_eq_div_pow`),
    -- which is what an arithmetic shift right computes; it cannot overflow, so
    -- unlike `ishl` there is no `wrap` here.
    some (env.set dst (.int (Int.shiftRight a n)))
  -- A call names a callee `step` cannot resolve (no program in scope), so
  -- the program-blind step stalls; resolved callees run additively through
  -- `runCallee`/`runCall`. The encoder's refusal pins stay green through
  -- this arm: nothing that encoded before changes shape.
  | .call .. => none

/-- Run a straight-line instruction list. -/
def runInstrs (env : Env) : List Instr → Option Env
  | [] => some env
  | i :: is => (step env i) >>= fun env' => runInstrs env' is

/-- Run a single-block function from an empty register file and read the return
register. This is the Stage B counterpart of `MIR.execFunc`. -/
def run (f : Func) : Option Value :=
  (runInstrs (fun _ => none) f.instrs) >>= fun env => env f.retSrc

/-! ## Single-level calls (Stage C, item C8 remainder)

The target now names calls (`Instr.call` carries the callee, the actuals,
and the declared return type — D-7 option B slice A), but executes them
additively, beside the existing runners (the C1/C8a hedge move): bare
`step` is program-blind — it cannot resolve a callee — so a call stalls
there exactly as an unmodelled instruction would, while resolved callees
run through `runCallee`/`runCall`. A callable still pairs a `Func` body A callable pairs a `Func` body with
its signature, and the program is a name-indexed list, mirroring
`MIR.Program`/`findFunc`. The call discipline mirrors `MIR.execFuncCall`:
single-level only. The callee body runs through the call-free `runInstrs`, so
a callee that itself needs a call stalls to `none`; recursion and mutual
recursion return `none`, exactly the fragment §3 admits.

A Cranelift signature declares parameter and return types; this model is
untyped (values carry their own tags), so `Sig` is the parameter register
list and its length is the arity check. Binding is the same shape as
`MIR.bindCallArgs` — recurse to the end, then set on the way out — so the
value-passing correspondence (`bindCallArgs_bindCArgs_agree` in
`Morph.ClifLower`) is a clean induction rather than a reordering argument.
-/

/-- A CLIF signature: the parameter registers, in order. Its length is the
arity the caller must pass. -/
abbrev Sig := List Reg

/-- A callable: a name, its signature, and a single-block body. -/
structure CFunc where
  name : String
  sig : Sig
  body : Func
  deriving Repr, BEq

/-- A CLIF call program: name-indexed callables. -/
abbrev CProgram := List CFunc

/-- Find a callable by name. -/
def findCFunc (prog : CProgram) (fn : String) : Option CFunc :=
  prog.find? (fun f => f.name == fn)

/-- Bind argument values to the signature's registers over an empty file
(`none` on arity mismatch). Parameter types are unchecked, as on the MIR
side; the callee's own execution checks what it uses. -/
def bindCArgs : Sig → List Value → Option Env
  | [], [] => some (fun _ => none)
  | r :: rs, v :: vs =>
      match bindCArgs rs vs with
      | none => none
      | some env => some (env.set r v)
  | _, _ => none

/-- Binding succeeds only on matching arity. -/
theorem bindCArgs_some_length {rs : Sig} {ws : List Value}
    {env : Env} (h : bindCArgs rs ws = some env) :
    rs.length = ws.length := by
  induction rs generalizing ws env with
  | nil =>
      cases ws with
      | nil => rfl
      | cons w ws => simp [bindCArgs] at h
  | cons r rs ih =>
      cases ws with
      | nil => simp [bindCArgs] at h
      | cons v vs =>
          simp only [bindCArgs] at h
          cases hbind : bindCArgs rs vs with
          | none => rw [hbind] at h; exact absurd h (by simp)
          | some env' =>
              have := ih (ws := vs) (env := env') hbind
              simp only [List.length_cons] at this ⊢
              omega

/-- Arity mismatch fails to bind. -/
theorem bindCArgs_length_mismatch {rs : Sig} {ws : List Value}
    (h : rs.length ≠ ws.length) : bindCArgs rs ws = none := by
  cases hbind : bindCArgs rs ws with
  | none => rfl
  | some env =>
      exact absurd (bindCArgs_some_length hbind) h

/-- Run a resolved callee: bind the arguments, run the call-free body, read
the return register. -/
def runCallee (cf : CFunc) (ws : List Value) : Option Value :=
  match bindCArgs cf.sig ws with
  | none => none
  | some env =>
      match runInstrs env cf.body.instrs with
      | none => none
      | some env' => env' cf.body.retSrc

/-- Run by name: look the callee up, then run it. Unknown names stall, as on
the MIR side (`execInstrsCall` returns `none` when `findFunc` fails). -/
def runCall (prog : CProgram) (fn : String) (ws : List Value) : Option Value :=
  match findCFunc prog fn with
  | none => none
  | some cf => runCallee cf ws

/-- Unknown callees stall. -/
theorem runCall_none_unknown (prog : CProgram) (fn : String) (ws : List Value)
    (h : findCFunc prog fn = none) : runCall prog fn ws = none := by
  simp [runCall, h]

/-- Arity mismatches stall. -/
theorem runCall_none_arity (prog : CProgram) (cf : CFunc) (ws : List Value)
    (hfind : findCFunc prog cf.name = some cf)
    (hlen : cf.sig.length ≠ ws.length) :
    runCall prog cf.name ws = none := by
  have hbind : bindCArgs cf.sig ws = none := bindCArgs_length_mismatch hlen
  simp [runCall, hfind, runCallee, hbind]

/-! ## Typed signatures (D-7 decision, option B)

D-7 DECIDED 2026-11-25 (maintainer direction, ahead of the S3 deadline):
option B+C — typed signatures per the `Morph.Runtime.marshal` table,
declared Morph-side with locations assigned Cranelift-side.

The untyped `Sig`/`bindCArgs` layer above stays untouched (the C1/C8
hedge: nothing proved moves); this section adds the typed layer beside
it. `TSig` pairs each parameter register with its declared `Typ`, and
`bindTArgs` binds only when every actual's value type is the declared
one. Values with no ABI representation (`undef`, option/result
wrappers, tuples, floats — the CLIF subset has no float instructions)
are unrepresentable and refuse. Which declared types occupy call slots
in emitted text (unit→void, string/pointer→address) is the emission
step, not this one. -/

/-- The ABI value type of a runtime value, `none` when the value has no
call representation. This is the model side of the
`Morph.Runtime.marshal` table: int/bool/string/pointer/unit cross calls;
everything else refuses here rather than at emission. -/
def valueTyp : Value → Option Typ
  | .int _ => some .intType
  | .bool _ => some .boolType
  | .string _ => some .stringType
  | .pointer _ => some .pointerType
  | .unit => some .unitType
  | _ => none

/-- A typed CLIF signature: parameter registers with declared types. -/
abbrev TSig := List (Reg × Typ)

/-- Whether an actual may cross under a declared formal type. -/
def typMatches (v : Value) (τ : Typ) : Bool :=
  match valueTyp v with
  | some τ' => τ' == τ
  | none => false

@[simp] theorem typMatches_some {v : Value} {τ τ' : Typ}
    (h : valueTyp v = some τ') : typMatches v τ = (τ' == τ) := by
  simp [typMatches, h]

@[simp] theorem typMatches_none {v : Value} {τ : Typ}
    (h : valueTyp v = none) : typMatches v τ = false := by
  simp [typMatches, h]

/-- Bind arguments under a typed signature. Succeeds only on matching
arity with every actual's value type equal to the declared formal type. -/
def bindTArgs : TSig → List Value → Option Env
  | [], [] => some (fun _ => none)
  | (r, τ) :: ts, v :: vs =>
      match typMatches v τ with
      | true => (bindTArgs ts vs).map (fun env => env.set r v)
      | false => none
  | _, _ => none

/-- Binding succeeds only on matching arity. -/
theorem bindTArgs_some_length {ts : TSig} {ws : List Value}
    {env : Env} (h : bindTArgs ts ws = some env) :
    ts.length = ws.length := by
  induction ts generalizing ws env with
  | nil =>
      cases ws with
      | nil => rfl
      | cons w ws => simp [bindTArgs] at h
  | cons p ts ih =>
      obtain ⟨r, τ⟩ := p
      cases ws with
      | nil => simp [bindTArgs] at h
      | cons v vs =>
          cases he : typMatches v τ with
          | false => simp [bindTArgs, he] at h
          | true =>
              simp only [bindTArgs, he] at h
              cases hbind : bindTArgs ts vs with
              | none => simp [hbind] at h
              | some env' =>
                  have hlen := ih hbind
                  simp only [List.length_cons] at hlen ⊢
                  omega

/-- A length mismatch refuses the whole bind. -/
theorem bindTArgs_length_mismatch {ts : TSig} {ws : List Value}
    (h : ts.length ≠ ws.length) : bindTArgs ts ws = none := by
  cases hb : bindTArgs ts ws with
  | some env => exact absurd (bindTArgs_some_length hb) h
  | none => rfl

/-- A head type mismatch refuses: the equation on `==` is the premise
because `Typ`'s derived `BEq` is not proved lawful, so propositional
inequality cannot supply it. -/
theorem bindTArgs_head_mismatch {r : Reg} {τ τ' : Typ} {ts : TSig}
    {v : Value} {vs : List Value}
    (hv : valueTyp v = some τ') (he : (τ' == τ) = false) :
    bindTArgs ((r, τ) :: ts) (v :: vs) = none := by
  simp [bindTArgs, hv, he]

/-- An unrepresentable head actual refuses. -/
theorem bindTArgs_head_unrepresentable {r : Reg} {τ : Typ} {ts : TSig}
    {v : Value} {vs : List Value} (hv : valueTyp v = none) :
    bindTArgs ((r, τ) :: ts) (v :: vs) = none := by
  simp [bindTArgs, hv]

/-- A refusal in the tail refuses the whole bind, whatever the head
checks to. -/
theorem bindTArgs_cons_none {r : Reg} {τ : Typ} {ts : TSig}
    {v : Value} {vs : List Value} (h : bindTArgs ts vs = none) :
    bindTArgs ((r, τ) :: ts) (v :: vs) = none := by
  cases he : typMatches v τ with
  | false => simp [bindTArgs, he]
  | true => simp [bindTArgs, he, h]

/-! ## Declared CLIF types (D-7 option B, step 2)

`clifTyOfTyp` is the model side of the `Runtime.marshal` table: the
first-order types cross calls, everything else occupies no call slot.
`addr` covers strings and pointers; it renders as `i64` (address-sized
on the x86-64 SystemV target — the assumption the `CallingConvention`
revisit records). -/

/-- The CLIF value types a declared signature can name. -/
inductive ClifTy where
  | i64
  | i8
  | addr
  deriving Repr, BEq, DecidableEq

/-- The option-B type mapping. Unit and non-first-order types map to
`none`: they occupy no slot in a declared signature. -/
def clifTyOfTyp : Typ → Option ClifTy
  | .intType => some .i64
  | .boolType => some .i8
  | .stringType => some .addr
  | .pointerType => some .addr
  | _ => none

/-! ## Per-instruction result types (D-7 option B, step 2)

The type pass's instruction half: every constructor writes exactly one
register, and the result type is read off the constructor — arithmetic,
constants and shifts produce ints; comparisons and boolean ops produce
bools. This is the same split the `step` views (`asInt`/`asBool`)
enforce, so `step_resultTyp` below holds without extra hypotheses: a
successful step has already checked its inputs. -//-- The register an instruction writes. Every constructor writes exactly
one destination, `call` its declared return register. -/
def Instr.dst : Instr → Reg
  | .iconst d _ => d
  | .iadd d _ _ => d
  | .isub d _ _ => d
  | .imul d _ _ => d
  | .icmp d _ _ _ => d
  | .band d _ _ => d
  | .bor d _ _ => d
  | .bnot d _ => d
  | .ishl d _ _ => d
  | .sshr d _ _ => d
  | .call d _ _ _ => d

/-- The result type of one instruction. -/
def Instr.resultTyp : Instr → Typ
  | .iconst _ _ => .intType
  | .iadd _ _ _ => .intType
  | .isub _ _ _ => .intType
  | .imul _ _ _ => .intType
  | .icmp _ _ _ _ => .boolType
  | .band _ _ _ => .boolType
  | .bor _ _ _ => .boolType
  | .bnot _ _ => .intType
  | .ishl _ _ _ => .intType
  | .sshr _ _ _ => .intType
  | .call _ _ _ τ => τ

/-- `evalCond` only ever produces booleans. -/
theorem evalCond_bool {c : Cond} {v1 v2 w : Value}
    (h : evalCond c v1 v2 = some w) : valueTyp w = some .boolType := by
  cases v1 with
  | int a => cases v2 with
    | int b =>
        simp only [evalCond] at h
        obtain rfl := Option.some.inj h
        rfl
    | bool b => simp [evalCond] at h
    | string s => simp [evalCond] at h
    | pointer p => simp [evalCond] at h
    | float f => simp [evalCond] at h
    | unit => simp [evalCond] at h
    | undef => simp [evalCond] at h
    | some v => simp [evalCond] at h
    | none => simp [evalCond] at h
    | ok v => simp [evalCond] at h
    | err v => simp [evalCond] at h
    | tuple_ l => simp [evalCond] at h
    | array_ l => simp [evalCond] at h
    | loc n => simp [evalCond] at h
    | closure f e => simp [evalCond] at h
  | bool a => cases v2 with
    | bool b =>
        cases c with
        | eq =>
            simp only [evalCond] at h
            obtain rfl := Option.some.inj h
            rfl
        | ne =>
            simp only [evalCond] at h
            obtain rfl := Option.some.inj h
            rfl
        | slt => simp [evalCond] at h
        | sle => simp [evalCond] at h
        | sgt => simp [evalCond] at h
        | sge => simp [evalCond] at h
    | int n => simp [evalCond] at h
    | string s => simp [evalCond] at h
    | pointer p => simp [evalCond] at h
    | float f => simp [evalCond] at h
    | unit => simp [evalCond] at h
    | undef => simp [evalCond] at h
    | some v => simp [evalCond] at h
    | none => simp [evalCond] at h
    | ok v => simp [evalCond] at h
    | err v => simp [evalCond] at h
    | tuple_ l => simp [evalCond] at h
    | array_ l => simp [evalCond] at h
    | loc n => simp [evalCond] at h
    | closure f e => simp [evalCond] at h
  | string s => simp [evalCond] at h
  | pointer p => simp [evalCond] at h
  | float f => simp [evalCond] at h
  | unit => simp [evalCond] at h
  | undef => simp [evalCond] at h
  | some v => simp [evalCond] at h
  | none => simp [evalCond] at h
  | ok v => simp [evalCond] at h
  | err v => simp [evalCond] at h
  | tuple_ l => simp [evalCond] at h
  | array_ l => simp [evalCond] at h
  | loc n => simp [evalCond] at h
  | closure f e => simp [evalCond] at h

/-- A successful step writes a value of the instruction's result type.
This is the per-instruction half of the type pass; the body half
(`bodyResultTyp`) comes with the `allI64` succession. -/
theorem step_resultTyp {env : Env} {i : Instr} {env' : Env}
    (h : step env i = some env') :
    ∃ v, env' i.dst = some v ∧ valueTyp v = some i.resultTyp := by
  cases i with
  | iconst d n =>
      simp only [step] at h
      obtain rfl := Option.some.inj h
      exact ⟨_, Env.set_same _ _ _, rfl⟩
  | iadd d l r =>
      cases hl : env l with
      | none => simp [step, hl] at h
      | some vl =>
          cases ha : asInt vl with
          | none => simp [step, hl, ha] at h
          | some a =>
              cases hr : env r with
              | none => simp [step, hl, hr] at h
              | some vr =>
                  cases hb : asInt vr with
                  | none => simp [step, hl, hr, hb] at h
                  | some b =>
                      simp [step, hl, ha, hr, hb] at h
                      rw [← h]
                      exact ⟨_, Env.set_same _ _ _, rfl⟩
  | isub d l r =>
      cases hl : env l with
      | none => simp [step, hl] at h
      | some vl =>
          cases ha : asInt vl with
          | none => simp [step, hl, ha] at h
          | some a =>
              cases hr : env r with
              | none => simp [step, hl, hr] at h
              | some vr =>
                  cases hb : asInt vr with
                  | none => simp [step, hl, hr, hb] at h
                  | some b =>
                      simp [step, hl, ha, hr, hb] at h
                      rw [← h]
                      exact ⟨_, Env.set_same _ _ _, rfl⟩
  | imul d l r =>
      cases hl : env l with
      | none => simp [step, hl] at h
      | some vl =>
          cases ha : asInt vl with
          | none => simp [step, hl, ha] at h
          | some a =>
              cases hr : env r with
              | none => simp [step, hl, hr] at h
              | some vr =>
                  cases hb : asInt vr with
                  | none => simp [step, hl, hr, hb] at h
                  | some b =>
                      simp [step, hl, ha, hr, hb] at h
                      rw [← h]
                      exact ⟨_, Env.set_same _ _ _, rfl⟩
  | icmp d c l r =>
      cases hl : env l with
      | none => simp [step, hl] at h
      | some vl =>
          cases hr : env r with
          | none => simp [step, hl, hr] at h
          | some vr =>
              cases he : evalCond c vl vr with
              | none => simp [step, hl, hr, he] at h
              | some w =>
                  simp [step, hl, hr, he] at h
                  rw [← h]
                  exact ⟨w, Env.set_same _ _ _, evalCond_bool he⟩
  | band d l r =>
      cases hl : env l with
      | none => simp [step, hl] at h
      | some vl =>
          cases ha : asBool vl with
          | none => simp [step, hl, ha] at h
          | some a =>
              cases hr : env r with
              | none => simp [step, hl, hr] at h
              | some vr =>
                  cases hb : asBool vr with
                  | none => simp [step, hl, hr, hb] at h
                  | some b =>
                      simp [step, hl, ha, hr, hb] at h
                      rw [← h]
                      exact ⟨_, Env.set_same _ _ _, rfl⟩
  | bor d l r =>
      cases hl : env l with
      | none => simp [step, hl] at h
      | some vl =>
          cases ha : asBool vl with
          | none => simp [step, hl, ha] at h
          | some a =>
              cases hr : env r with
              | none => simp [step, hl, hr] at h
              | some vr =>
                  cases hb : asBool vr with
                  | none => simp [step, hl, hr, hb] at h
                  | some b =>
                      simp [step, hl, ha, hr, hb] at h
                      rw [← h]
                      exact ⟨_, Env.set_same _ _ _, rfl⟩
  | bnot d s =>
      cases hs : env s with
      | none => simp [step, hs] at h
      | some vs =>
          cases ha : asInt vs with
          | none => simp [step, hs, ha] at h
          | some a =>
              simp [step, hs, ha] at h
              rw [← h]
              exact ⟨_, Env.set_same _ _ _, rfl⟩
  | ishl d l r =>
      cases hl : env l with
      | none => simp [step, hl] at h
      | some vl =>
          cases ha : asInt vl with
          | none => simp [step, hl, ha] at h
          | some a =>
              cases hr : env r with
              | none => simp [step, hl, hr] at h
              | some vr =>
                  cases hn : shiftAmount vr with
                  | none => simp [step, hl, hr, hn] at h
                  | some n =>
                      simp [step, hl, ha, hr, hn] at h
                      rw [← h]
                      exact ⟨_, Env.set_same _ _ _, rfl⟩
  | sshr d l r =>
      cases hl : env l with
      | none => simp [step, hl] at h
      | some vl =>
          cases ha : asInt vl with
          | none => simp [step, hl, ha] at h
          | some a =>
              cases hr : env r with
              | none => simp [step, hl, hr] at h
              | some vr =>
                  cases hn : shiftAmount vr with
                  | none => simp [step, hl, hr, hn] at h
                  | some n =>
                      simp [step, hl, ha, hr, hn] at h
                      rw [← h]
                      exact ⟨_, Env.set_same _ _ _, rfl⟩
  | call d fn args τ =>
      simp [step] at h

/-! ## Body result types (D-7 option B, step 2)

The type pass's body half: `lastDef` finds the last instruction defining
a register (later definitions shadow earlier ones; single-assignment is
not assumed), and `bodyResultTyp` reads its `resultTyp`. `lastDef_mem`
lets step 3's gate switch move from a computed body type to a member of
the encoded body. -/

/-- The last instruction defining a register, if any. -/
def lastDef : List Instr → Reg → Option Instr
  | [], _ => none
  | i :: is, r =>
      match lastDef is r with
      | some j => some j
      | none =>
          match (i.dst == r) with
          | true => some i
          | false => none

/-- The result type of the value a body returns in a register. -/
def bodyResultTyp (is : List Instr) (ret : Reg) : Option Typ :=
  (lastDef is ret).map Instr.resultTyp

/-- `lastDef` returns a member of the body. -/
theorem lastDef_mem {is : List Instr} {r : Reg} {i : Instr}
    (h : lastDef is r = some i) : i ∈ is := by
  induction is with
  | nil => simp [lastDef] at h
  | cons j js ih =>
      simp only [lastDef] at h
      cases htail : lastDef js r with
      | some k =>
          simp only [htail] at h
          obtain rfl := Option.some.inj h
          exact List.mem_cons_of_mem _ (ih htail)
      | none =>
          simp only [htail] at h
          cases he : (j.dst == r) with
          | false => simp [he] at h
          | true =>
              simp only [he] at h
              obtain rfl := Option.some.inj h
              exact List.mem_cons.mpr (Or.inl rfl)

/-! ## Typed call programs and program-aware stepping (D-7 option B, slice B1)

`CFunc`/`runCall` bind by arity only. The typed twins below check the
declared types as well (`TSig` from step 1): a typed callee stalls on
arity *or* type mismatch. `stepIn` runs one instruction against a typed
target program — pure instructions delegate to `step`, calls resolve
through `runTCall` — so the model executes what the explicit-program
encoder accepts. The dynamic check runs at bind time; the static half
(checking caller actuals against callee formals) arrives with the type
environment in slice B2. The untyped layer stays for the C8 evidence
that predates typed signatures; it converges onto this one in B2. -/

/-- A typed callable: a name, its typed signature, and a single-block body. -/
structure TCFunc where
  name : String
  tsig : TSig
  body : Func
  deriving Repr, BEq

/-- A typed CLIF call program: name-indexed typed callables. -/
abbrev TCProgram := List TCFunc

/-- Find a typed callable by name. -/
def findTCFunc (prog : TCProgram) (fn : String) : Option TCFunc :=
  prog.find? (fun f => f.name == fn)

/-- Run a resolved typed callee: bind the arguments (arity *and*
types), run the call-free body, read the return register. -/
def runTCallee (cf : TCFunc) (ws : List Value) : Option Value :=
  match bindTArgs cf.tsig ws with
  | none => none
  | some env =>
      match runInstrs env cf.body.instrs with
      | none => none
      | some env' => env' cf.body.retSrc

/-- Run by name: look the callee up, then run it. -/
def runTCall (prog : TCProgram) (fn : String) (ws : List Value) : Option Value :=
  match findTCFunc prog fn with
  | none => none
  | some cf => runTCallee cf ws

/-- Unknown callees stall. -/
theorem runTCall_none_unknown (prog : TCProgram) (fn : String) (ws : List Value)
    (h : findTCFunc prog fn = none) : runTCall prog fn ws = none := by
  simp [runTCall, h]

/-- Arity or type mismatches stall. -/
theorem runTCall_none_bind (prog : TCProgram) (cf : TCFunc) (ws : List Value)
    (hfind : findTCFunc prog cf.name = some cf)
    (hbind : bindTArgs cf.tsig ws = none) :
    runTCall prog cf.name ws = none := by
  simp [runTCall, hfind, runTCallee, hbind]

/-- Program-aware single step. Pure instructions delegate to `step`;
calls look their actuals up in the environment and resolve through
`runTCall`, writing the return value to the declared destination. Any
failure along the way — unbound register, unknown name, arity or type
mismatch, stalled body — stalls the step. -/
def stepIn (tprog : TCProgram) (env : Env) : Instr → Option Env
  | .call d fn args _ =>
      match args.mapM env with
      | none => none
      | some vs =>
          match runTCall tprog fn vs with
          | none => none
          | some w => some (env.set d w)
  | i => step env i

end Morph.Clif
