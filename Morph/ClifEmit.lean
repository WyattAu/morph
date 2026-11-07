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

/-- Encode a lowered block, dropping `lowerProgram`'s unit prologue.

The prologue is required, not merely tolerated: a block that does not start with
`.const 0 .unit` did not come from `lowerProgram`, and encoding it would emit a
function whose register 0 is read but never bound. -/
def emitBlock (b : Block) : Option Morph.Clif.Func :=
  match b.terminator with
  | .return_ src =>
      match b.instrs with
      | .const 0 .unit :: body => Morph.Clif.blockEncode ⟨b.id, body, .return_ src⟩
      | _ => none
  | _ => none

/-- The CLIF function for a lowered MIR function: its single entry block, minus
the unit prologue. -/
def emitFunc (f : Func) : Option Morph.Clif.Func :=
  match f.blocks with
  | [b] => if b.id = f.entry then emitBlock b else none
  | _ => none

/-- The artifact text for a lowered MIR function. -/
def emitClif (f : Func) : Option String :=
  (emitFunc f).map Morph.Clif.renderFunc

/-! ## Characterizations

The CLI writes artifact text; these lemmas say what the text is, so the artifact
is not a black box: it is `renderFunc` applied to `blockEncode` of the block with
the prologue dropped. -/

/-- On the shape `lowerProgram` produces, the emitter *is* the encoder of the
prologue-free body. This is the lemma the gate above rests on: the prologue
disappears from the artifact and nothing else about the body changes. -/
theorem emitBlock_prologue (id : Nat) (body : List Instr) (src : Nat) :
    emitBlock ⟨id, .const 0 .unit :: body, .return_ src⟩
      = Morph.Clif.blockEncode ⟨id, body, .return_ src⟩ := rfl

/-- Composing the shape with the emitter: on a lowered function the artifact is
`blockEncode`'s rendering, with no prologue instruction in it. -/
theorem emitClif_lowered (body : List Instr) (v : Nat) :
    emitClif ⟨"main", [], [⟨0, .const 0 .unit :: body, .return_ v⟩], 0, .unitType⟩
      = (Morph.Clif.blockEncode ⟨0, body, .return_ v⟩).map Morph.Clif.renderFunc :=
  rfl

/-- A successful emission is a single block, the entry block, carrying the
prologue. -/
theorem emitFunc_sound {f : Func} {cf : Morph.Clif.Func}
    (h : emitFunc f = some cf) :
    ∃ b : Block, f.blocks = [b] ∧ b.id = f.entry ∧ emitBlock b = some cf := by
  unfold emitFunc at h
  split at h
  · rename_i b hblocks
    split at h
    · rename_i hid
      exact ⟨b, hblocks, hid, h⟩
    · simp at h
  · simp at h

/-- The artifact text is the rendering of the encoded function. -/
theorem emitClif_sound {f : Func} {s : String} (h : emitClif f = some s) :
    ∃ cf : Morph.Clif.Func, emitFunc f = some cf ∧ s = Morph.Clif.renderFunc cf := by
  unfold emitClif at h
  cases hf : emitFunc f with
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
