/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifRender
import Morph.ClifLower
import Morph.HIRToMIR

/-!
# Emitting the CLIF artifact (stage B item B6)

`lowerProgram` produces a function with **one** block whose body begins with
`.const 0 .unit`, the prologue that binds register 0 to unit so that the
simulation's starting environment is a real prefix of the execution. CLIF has no
unit value, so that instruction cannot be encoded; it is *dropped*, and the
emitted function is the body after it. Dropping it is sound precisely because
register 0 is the prologue's own destination: nothing in the block can read 0 for
a value, and B4's `trace_transport` starts its agreement at an environment where
0 already holds unit (`AgreesOnValues`).

So the gate here is the shape `lowerProgram` promises: exactly one block, that
block is the entry block, its terminator is `return`, and its body starts with
the prologue. Every other shape is `none` — a silent `none` on a *malformed*
function rather than a source-level rejection, because a well-formed `Func` from
`lowerProgram` can never take those branches (see `emitFunc_lowerProgram`).

The rejection that source programs actually reach is inside `blockEncode`: an
instruction the CLIF subset cannot encode (division, parity-defined bitwise ops,
bool constants, `copy`, memory, calls) makes `instrEncodes` fail, and that
failure is what the CLI reports with the D-4 message.
-/

namespace Morph.Codegen

open Morph.MIR

/-- Whether every instruction in a body produces an i64. `icmp` and the boolean
`band`/`bor` produce i8 truth values, and CLIF has no implicit widening, so a
body containing one is not printable under the `-> i64` signature `renderFunc`
declares.

This is a *conservative* test: a program that computes a comparison and then
returns an integer is refused too, because the printer carries no per-register
type. Exact would mean a type pass over the body (`lastDef` + a type per
instruction); conservative-but-sound is the right trade until the corpus shows a
case that needs the difference. -/
def allI64 : List Instr → Bool
  | [] => true
  | i :: rest =>
      (match i with
        | .binop _ op _ _ _ =>
            (match op with
              | .eq => false | .neq => false | .lt => false
              | .leq => false | .gt => false | .geq => false
              | .and => false | .or => false
              | _ => true)
        | .unop _ op _ _ => (match op with | .not => false | .notb => true)
        | _ => true) && allI64 rest

/-- The corollaries that make the gate non-vacuous: any comparison, boolean
`and`/`or`, or boolean `.not` makes the body unprintable. -/
theorem allI64_no_lt (is : List Instr) (d l r : ValId) (τ : Morph.Core.Typ) :
    allI64 (.binop d .lt l r τ :: is) = false := rfl

theorem allI64_no_and (is : List Instr) (d l r : ValId) (τ : Morph.Core.Typ) :
    allI64 (.binop d .and l r τ :: is) = false := rfl

theorem allI64_no_not (is : List Instr) (d s : ValId) (τ : Morph.Core.Typ) :
    allI64 (.unop d .not s τ :: is) = false := rfl

/-! ## The type pass succeeds the `allI64` gate (D-7 option B, step 2)

`allI64` is conservative by design (see its docstring): a body that
computes a comparison and returns an integer is refused alongside one
that returns a boolean. The exact pass is `lastDef` (the last
instruction defining the return register) read through `resultTyp`.
`encodes_allI64_int` says an `allI64` body that encodes successfully
encodes to all-`intType` instructions — each case is one row of the
encoder's rejection table (`instrEncode`, `binopInstr`, `unopInstr`):
refused constructs contradict a successful encode, bool-producing ones
contradict `allI64`. `encodes_bodyResultTyp_int` is the form step 3's
gate switch rests on: the computed body type of such a body is
`intType`, so the `-> i64` signature `renderFunc` declares stays
sound. -/

/-- An `allI64` tail stays `allI64`. -/
theorem allI64_cons_tail {i : Instr} {is : List Instr}
    (h : allI64 (i :: is) = true) : allI64 is = true := by
  cases htail : allI64 is with
  | true => rfl
  | false => simp [allI64, htail] at h

/-- An `allI64` body that encodes successfully encodes to
all-`intType` instructions. -/
theorem encodes_allI64_int {is : List Instr} {cs : List Morph.Clif.Instr}
    (hall : allI64 is = true) (henc : Morph.Clif.instrEncodes is = some cs) :
    ∀ c ∈ cs, Morph.Clif.Instr.resultTyp c = .intType := by
  induction is generalizing cs with
  | nil =>
      simp only [Morph.Clif.instrEncodes] at henc
      obtain rfl := Option.some.inj henc
      intro c hmem
      simp at hmem
  | cons i is ih =>
      rw [Morph.Clif.instrEncodes_cons] at henc
      obtain ⟨c', cs', hci, hrest, rfl⟩ := henc
      have htail := allI64_cons_tail hall
      intro c hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · cases i with
        | const dst v =>
            cases v with
            | int n =>
                simp only [Morph.Clif.instrEncode] at hci
                obtain rfl := Option.some.inj hci
                rfl
            | bool b => simp [Morph.Clif.instrEncode] at hci
            | string s => simp [Morph.Clif.instrEncode] at hci
            | pointer p => simp [Morph.Clif.instrEncode] at hci
            | float f => simp [Morph.Clif.instrEncode] at hci
            | unit => simp [Morph.Clif.instrEncode] at hci
            | undef => simp [Morph.Clif.instrEncode] at hci
            | some w => simp [Morph.Clif.instrEncode] at hci
            | none => simp [Morph.Clif.instrEncode] at hci
            | ok w => simp [Morph.Clif.instrEncode] at hci
            | err w => simp [Morph.Clif.instrEncode] at hci
            | tuple_ l => simp [Morph.Clif.instrEncode] at hci
            | array_ l => simp [Morph.Clif.instrEncode] at hci
            | loc n => simp [Morph.Clif.instrEncode] at hci
            | closure f e => simp [Morph.Clif.instrEncode] at hci
        | copy dst src => simp [Morph.Clif.instrEncode] at hci
        | unop dst op src τ =>
            cases op with
            | not => simp [allI64] at hall
            | notb =>
                simp only [Morph.Clif.instrEncode, Morph.Clif.unopInstr] at hci
                obtain rfl := Option.some.inj hci
                rfl
        | binop dst op l r τ =>
            cases op with
            | add =>
                simp only [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
                obtain rfl := Option.some.inj hci
                rfl
            | sub =>
                simp only [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
                obtain rfl := Option.some.inj hci
                rfl
            | mul =>
                simp only [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
                obtain rfl := Option.some.inj hci
                rfl
            | shl =>
                simp only [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
                obtain rfl := Option.some.inj hci
                rfl
            | shr =>
                simp only [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
                obtain rfl := Option.some.inj hci
                rfl
            | eq => simp [allI64] at hall
            | neq => simp [allI64] at hall
            | lt => simp [allI64] at hall
            | leq => simp [allI64] at hall
            | gt => simp [allI64] at hall
            | geq => simp [allI64] at hall
            | and => simp [allI64] at hall
            | or => simp [allI64] at hall
            | not => simp [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
            | div => simp [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
            | mod => simp [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
            | andb => simp [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
            | orb => simp [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
            | xorb => simp [Morph.Clif.instrEncode, Morph.Clif.binopInstr] at hci
        | load dst loc cap => simp [Morph.Clif.instrEncode] at hci
        | store loc src cap => simp [Morph.Clif.instrEncode] at hci
        | alloc dst cap τ => simp [Morph.Clif.instrEncode] at hci
        | free loc => simp [Morph.Clif.instrEncode] at hci
        | call dst fn args => simp at hci
        | phi dst pred src => simp [Morph.Clif.instrEncode] at hci
        | allocClosure dst fn captures => simp [Morph.Clif.instrEncode] at hci
        | callClosure dst clo args => simp [Morph.Clif.instrEncode] at hci
      · exact ih htail hrest c hmem

/-- The computed body type of an `allI64` encoded body is `intType`.
`lastDef` returns a member of the body (`lastDef_mem`), and every
member is `intType` by `encodes_allI64_int`. -/
theorem encodes_bodyResultTyp_int {is : List Instr} {cs : List Morph.Clif.Instr}
    {ret : Nat} {τ : Morph.Core.Typ}
    (hall : allI64 is = true) (henc : Morph.Clif.instrEncodes is = some cs)
    (hbody : Morph.Clif.bodyResultTyp cs ret = some τ) :
    τ = .intType := by
  unfold Morph.Clif.bodyResultTyp at hbody
  cases hlast : Morph.Clif.lastDef cs ret with
  | none => simp [hlast] at hbody
  | some i =>
      simp only [hlast] at hbody
      obtain rfl := Option.some.inj hbody
      exact encodes_allI64_int hall henc i (Morph.Clif.lastDef_mem hlast)

/-! ## Signature-declaration preamble (D-7 option B, slice B2)

A call-bearing artifact names its callees (`Instr.text`'s `call` arm),
so the text must declare them: one `function %name(params) -> ret` line
per MIR function in the program, typed through `clifTyOfTyp` (the
`Runtime.marshal` table). Parameters without a call slot (unit and
non-first-order types) refuse the whole declaration (`none`); a `unit`
return is void and takes no suffix (via `retSuffix`). The preamble of
the empty program is empty, so every existing statement about the
one-argument form holds unchanged. -/

/-- One signature declaration for the emission preamble. -/
def sigDecl (f : Func) : Option String :=
  match f.params.mapM (fun p => Morph.Clif.clifTyOfTyp p.2) with
  | none => none
  | some ts =>
      some ("function %" ++ f.name ++ "(" ++
        String.intercalate ", " (ts.map Morph.Clif.ClifTy.text) ++ ")" ++
        Morph.Clif.retSuffix f.retType ++ "\n")

/-- The emission preamble: the declarations of every function in the
program that has one, concatenated. -/
def preamble (prog : Program) : String :=
  (prog.funcs.filterMap sigDecl).foldl (· ++ ·) ""

/-- The empty program declares nothing, so the default-program emitter
is byte-for-byte the historic one. -/
theorem preamble_empty : preamble { funcs := [] } = "" := rfl

-- Slice B2: the single-function emitter threads a program (default
-- empty, so call-bearing bodies still fail at `instrEncodes` exactly as
-- before) and prepends its preamble; an explicit int-world program
-- admits calls per `callResolved`. The default-program refusal pins
-- stay green. -/
/-- Encode a lowered block, dropping `lowerProgram`'s unit prologue.

The prologue is required, not merely tolerated: a block that does not start with
`.const 0 .unit` did not come from `lowerProgram`, and encoding it would emit a
function whose register 0 is read but never bound.

Returning register 0 is refused for the same reason seen from the other side: a
program whose value is unit returns the prologue's own register, and since CLIF
has no unit value that register is never defined in the text. B4's *model* can
represent this — the trace starts at an environment where 0 already holds unit —
but a function `-> i64` that reads an undefined `v0` is not CLIF, so the printer
refuses it rather than write an artifact no reader can accept. This is the same
shape as the encoder's other narrowing decisions: the model admits more than the
text does, deliberately and visibly. -/
def emitBlock (b : Block) (prog : Program := { funcs := [] }) : Option Morph.Clif.Func :=
  match b.terminator with
  | .return_ src =>
      match b.instrs with
      | .const 0 .unit :: body =>
          if src = 0 then none
          else if allI64 body then Morph.Clif.blockEncode ⟨b.id, body, .return_ src⟩ prog
          else none
      | _ => none
  | _ => none

/-- The CLIF function for a lowered MIR function: its single entry block, minus
the unit prologue. -/
def emitFunc (f : Func) (prog : Program := { funcs := [] }) : Option Morph.Clif.Func :=
  match f.blocks with
  | [b] => if b.id = f.entry then emitBlock b prog else none
  | _ => none

/-- The artifact text for a lowered MIR function: the program's signature
preamble followed by the encoded function. -/
def emitClif (f : Func) (prog : Program := { funcs := [] }) : Option String :=
  (emitFunc f prog).map (fun cf => preamble prog ++ Morph.Clif.renderFunc cf)

/-! ## Characterizations

The CLI writes artifact text; these lemmas say what the text is, so the artifact
is not a black box: it is `renderFunc` applied to `blockEncode` of the block with
the prologue dropped. -/

/-- On the shape `lowerProgram` produces, the emitter *is* the encoder of the
prologue-free body. This is the lemma the gate above rests on: the prologue
disappears from the artifact and nothing else about the body changes. The
`src ≠ 0` premise is the unit case, which `emitBlock` refuses. -/
theorem emitBlock_prologue (id : Nat) (body : List Instr) (src : Nat) (hsrc : src ≠ 0)
    (hall : allI64 body = true) (prog : Program := { funcs := [] }) :
    emitBlock ⟨id, .const 0 .unit :: body, .return_ src⟩ prog
      = Morph.Clif.blockEncode ⟨id, body, .return_ src⟩ prog := by
  simp only [emitBlock]
  rw [if_neg hsrc, if_pos hall]

/-- Composing the shape with the emitter: on a lowered function the artifact is
the preamble plus `blockEncode`'s rendering, with no prologue instruction in
it. -/
theorem emitClif_lowered (body : List Instr) (v : Nat) (hv : v ≠ 0)
    (hall : allI64 body = true) (prog : Program := { funcs := [] }) :
    emitClif ⟨"main", [], [⟨0, .const 0 .unit :: body, .return_ v⟩], 0, .unitType⟩ prog
      = (Morph.Clif.blockEncode ⟨0, body, .return_ v⟩ prog).map
        (fun cf => preamble prog ++ Morph.Clif.renderFunc cf) := by
  simp [emitClif, emitFunc, emitBlock_prologue 0 body v hv hall prog]

/-- A unit-valued program is refused: its value is the prologue's register. -/
theorem emitBlock_unit (id : Nat) (body : List Instr)
    (prog : Program := { funcs := [] }) :
    emitBlock ⟨id, .const 0 .unit :: body, .return_ 0⟩ prog = none := by
  simp [emitBlock]

/-- A boolean-valued program is refused: the text's signature is `-> i64`. -/
theorem emitBlock_bool {id : Nat} {body : List Instr} {src : Nat}
    (hall : allI64 body = false) (prog : Program := { funcs := [] }) :
    emitBlock ⟨id, .const 0 .unit :: body, .return_ src⟩ prog = none := by
  by_cases hsrc : src = 0
  · simp [emitBlock, hsrc]
  · simp [emitBlock, hsrc, hall]

/-- A successful emission is a single block, the entry block, carrying the
prologue. -/
theorem emitFunc_sound {f : Func} {prog : Program} {cf : Morph.Clif.Func}
    (h : emitFunc f prog = some cf) :
    ∃ b : Block, f.blocks = [b] ∧ b.id = f.entry ∧ emitBlock b prog = some cf := by
  unfold emitFunc at h
  split at h
  · rename_i b hblocks
    split at h
    · rename_i hid
      exact ⟨b, hblocks, hid, h⟩
    · simp at h
  · simp at h

/-- The artifact text is the preamble plus the rendering of the encoded
function. -/
theorem emitClif_sound {f : Func} {prog : Program} {s : String}
    (h : emitClif f prog = some s) :
    ∃ cf : Morph.Clif.Func, emitFunc f prog = some cf ∧
      s = preamble prog ++ Morph.Clif.renderFunc cf := by
  unfold emitClif at h
  cases hf : emitFunc f prog with
  | none => rw [hf] at h; simp at h
  | some cf => rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h
               exact ⟨cf, rfl, h.symm⟩

/-- `lowerProgram`'s shape, stated so the emitter's gate is visibly vacuous on
lowered functions: the body starts with the unit prologue and the block is the
entry block. -/
theorem emitFunc_lowerProgram {hprog : Morph.HIR.Program} {f : Func}
    (h : Morph.HIRToMIR.lowerProgram hprog = some f) :
    ∃ (v : Nat) (is : List Instr),
      f.blocks = [⟨0, .const 0 .unit :: is, .return_ v⟩] ∧ f.entry = 0 := by
  unfold Morph.HIRToMIR.lowerProgram at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, _, rfl, rfl⟩
  · simp at h

end Morph.Codegen
