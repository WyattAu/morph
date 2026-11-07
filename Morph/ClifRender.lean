/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifTarget

/-!
# Stage B item B5: the printed form and its inverse

`docs/STAGEB-SCOPE.md` §5, item B5. Two layers, deliberately separated.

**The token stream.** `toksFunc` prints a `Func` as a `List Tok` of
self-delimiting lexical units and `parseFunc` reads it back. The round trip
(`parseFunc_toksFunc`) is *proved*, and it is the part that can be: at token
level every unit is unambiguous, so the parser is total, structurally recursive
and invertible.

**The text.** `renderFunc` lays a `Func` out as the CLIF that `cranelift-reader`
consumes. This file does **not** prove `parse (render f) = f`, and the reason is
a scoping decision rather than an omission: no verified CLIF reader exists in
this pipeline. The reader is `cranelift-reader` on the Rust side, which ADR-032
§3 already lists as trusted; re-implementing the CLIF lexer in Lean would add
code to the TCB, not remove it. What B5 owes is that the units we emit are the
units we mean — that is `parseFunc_toksFunc` — plus the grammar below, so the
artifact can be read against something stated rather than assumed.

## Grammar

```
function %main() -> i64 {        -- one single-block function, one i64 result
block0:                          -- the fragment has a single block, numbered 0
  %v0 = iconst.i64 42            -- iconst, immediate in i64 range
  %v1 = iadd %v0, %v0            -- iadd isub imul band bor ishl sshr
  %v2 = icmp slt %v1, %v0        -- icmp with eq ne slt sle sgt sge
  %v3 = bnot %v2                 -- bnot, one operand
  return %v3                     -- returns one register
}
```

An instruction is `%dst = <op> <operands>`, registers are `%v<n>` with `<n>`
decimal, and an immediate is an optional `-` followed by decimals. `icmp` carries
its condition as an infix keyword. Nothing else is emitted, so anything else must
be rejected by the reader; the token-level analogue of that rejection is the
`none` case of `parseInstr`.

The layout here matches the fragment, not CLIF at large: one block, straight-line
instructions, one `return`. A `Func` with more blocks cannot be expressed, which
is the same restriction `StraightStmts 256` puts on the source.
-/

open Morph.Core

namespace Morph.Clif

/-- Instruction names, plus the two framing keywords of a token stream. Keeping
the name out of `Instr` is what lets the printer stay total: nothing needs to
format an `Instr` value to print an instruction's name. -/
inductive Name where
  | iconst | iadd | isub | imul | icmp
  | band | bor | bnot | ishl | sshr
  | fn | ret
  deriving Repr, BEq, DecidableEq

/-- One lexical unit of the token stream. Units carry their payload, so no unit
can be confused with another and no separators are needed to parse. -/
inductive Tok where
  | kw (n : Name)
  | reg (r : Reg)
  | imm (i : Int)
  | cond (c : Cond)
  | arity (n : Nat)
  deriving Repr, BEq, DecidableEq

/-- The condition keywords, in the order the grammar above lists them. -/
def Cond.text : Cond → String
  | .eq => "eq"
  | .ne => "ne"
  | .slt => "slt"
  | .sle => "sle"
  | .sgt => "sgt"
  | .sge => "sge"

/-- The tokens of one instruction, name first. Each unit fixes the arity, which
is why `parseInstr` needs no backtracking. -/
def toksInstr : Instr → List Tok
  | .iconst d v => [.kw .iconst, .reg d, .imm v]
  | .iadd d l r => [.kw .iadd, .reg d, .reg l, .reg r]
  | .isub d l r => [.kw .isub, .reg d, .reg l, .reg r]
  | .imul d l r => [.kw .imul, .reg d, .reg l, .reg r]
  | .icmp d c l r => [.kw .icmp, .reg d, .cond c, .reg l, .reg r]
  | .band d l r => [.kw .band, .reg d, .reg l, .reg r]
  | .bor d l r => [.kw .bor, .reg d, .reg l, .reg r]
  | .bnot d s => [.kw .bnot, .reg d, .reg s]
  | .ishl d l r => [.kw .ishl, .reg d, .reg l, .reg r]
  | .sshr d l r => [.kw .sshr, .reg d, .reg l, .reg r]

/-- Read one instruction, returning it with the tokens it did not consume. -/
def parseInstr : List Tok → Option (Instr × List Tok)
  | .kw .iconst :: .reg d :: .imm v :: rest => some (.iconst d v, rest)
  | .kw .iadd :: .reg d :: .reg l :: .reg r :: rest => some (.iadd d l r, rest)
  | .kw .isub :: .reg d :: .reg l :: .reg r :: rest => some (.isub d l r, rest)
  | .kw .imul :: .reg d :: .reg l :: .reg r :: rest => some (.imul d l r, rest)
  | .kw .icmp :: .reg d :: .cond c :: .reg l :: .reg r :: rest => some (.icmp d c l r, rest)
  | .kw .band :: .reg d :: .reg l :: .reg r :: rest => some (.band d l r, rest)
  | .kw .bor :: .reg d :: .reg l :: .reg r :: rest => some (.bor d l r, rest)
  | .kw .bnot :: .reg d :: .reg s :: rest => some (.bnot d s, rest)
  | .kw .ishl :: .reg d :: .reg l :: .reg r :: rest => some (.ishl d l r, rest)
  | .kw .sshr :: .reg d :: .reg l :: .reg r :: rest => some (.sshr d l r, rest)
  | _ => none

/-- `parseInstr` is a left inverse of `toksInstr`, with the rest of the stream
carried through untouched. This is the interesting half of the round trip: every
case is decided by the name token alone. -/
theorem parseInstr_toksInstr (i : Instr) (rest : List Tok) :
    parseInstr (toksInstr i ++ rest) = some (i, rest) := by
  cases i <;> rfl

/-- Read `n` instructions. Bounded by `n` rather than by a terminator so the
recursion is structural in the fuel; the arity header supplies the bound, and
`parseInstrs_toksInstrs` shows `n := is.length` is exactly right. -/
def parseInstrs : Nat → List Tok → Option (List Instr × List Tok)
  | 0, toks => some ([], toks)
  | n + 1, toks =>
    match parseInstr toks with
    | some (i, rest) =>
      match parseInstrs n rest with
      | some (is, rest') => some (i :: is, rest')
      | none => none
    | none => none

/-- One unfolding step of `parseInstrs` at a successor fuel, stated separately so
the round-trip proof never has to convince the elaborator that `n + 1` is a
successor. -/
theorem parseInstrs_succ (n : Nat) (toks : List Tok) :
    parseInstrs (n + 1) toks =
      (match parseInstr toks with
       | some (i, rest) =>
         match parseInstrs n rest with
         | some (is, rest') => some (i :: is, rest')
         | none => none
       | none => none) := rfl

/-- The token stream of a whole function: a `function` marker, the instruction
count, the instructions, then the returned register. -/
def toksFunc (f : Func) : List Tok :=
  .kw .fn :: .arity f.instrs.length ::
    (f.instrs.flatMap toksInstr ++ [.kw .ret, .reg f.retSrc])

/-- Read a whole function. The arity header bounds the body, and the return
marker closes it; anything left over is rejected, so a stream that encodes a
prefix of a function is not a function. -/
def parseFunc : List Tok → Option Func
  | .kw .fn :: .arity n :: rest =>
    match parseInstrs n rest with
    | some (is, .kw .ret :: .reg r :: []) => some ⟨is, r⟩
    | _ => none
  | _ => none

/-- Reading back `n` encoded instructions returns them and leaves the tail alone.
Fuel `is.length` is the exact bound `toksFunc` writes in the header. -/
theorem parseInstrs_toksInstrs (is : List Instr) (rest : List Tok) :
    parseInstrs is.length (is.flatMap toksInstr ++ rest) = some (is, rest) := by
  induction is generalizing rest with
  | nil => rfl
  | cons i is ih =>
    rw [show (i :: is).flatMap toksInstr ++ rest
          = toksInstr i ++ (is.flatMap toksInstr ++ rest) from by simp]
    show parseInstrs (is.length + 1) (toksInstr i ++ (is.flatMap toksInstr ++ rest))
      = some (i :: is, rest)
    rw [parseInstrs_succ]
    simp only [parseInstr_toksInstr, ih]

/-- **B5's round trip.** Every `Func` survives print-then-parse unchanged. -/
theorem parseFunc_toksFunc (f : Func) : parseFunc (toksFunc f) = some f := by
  cases f with
  | mk instrs retSrc =>
    show parseFunc (.kw .fn :: .arity instrs.length ::
      (instrs.flatMap toksInstr ++ [.kw .ret, .reg retSrc]))
      = some ⟨instrs, retSrc⟩
    simp only [parseFunc, parseInstrs_toksInstrs]

/-- Nothing may follow the return: a printed stream is not merely *accepted*, it
is accepted at exactly its own length. Together with `parseFunc_toksFunc` this
says the printer's image is the parser's domain, not a subset of it. -/
theorem parseFunc_toksFunc_append (f : Func) (t : Tok) :
    parseFunc (toksFunc f ++ [t]) = none := by
  cases f with
  | mk instrs retSrc =>
    show parseFunc (.kw .fn :: .arity instrs.length ::
      ((instrs.flatMap toksInstr ++ [.kw .ret, .reg retSrc]) ++ [t])) = none
    rw [show (instrs.flatMap toksInstr ++ [.kw .ret, .reg retSrc]) ++ [t]
          = instrs.flatMap toksInstr ++ ([.kw .ret, .reg retSrc] ++ [t]) from by simp]
    have hlist : ([.kw .ret, .reg retSrc] ++ [t]) = [.kw .ret, .reg retSrc, t] := rfl
    rw [hlist]
    simp only [parseFunc, parseInstrs_toksInstrs]

/-- Text of one instruction, in the grammar at the top of the file. -/
def Instr.text : Instr → String
  | .iconst d v => s!"  %v{d} = iconst.i64 {v}"
  | .iadd d l r => s!"  %v{d} = iadd %v{l}, %v{r}"
  | .isub d l r => s!"  %v{d} = isub %v{l}, %v{r}"
  | .imul d l r => s!"  %v{d} = imul %v{l}, %v{r}"
  | .icmp d c l r => s!"  %v{d} = icmp {c.text} %v{l}, %v{r}"
  | .band d l r => s!"  %v{d} = band %v{l}, %v{r}"
  | .bor d l r => s!"  %v{d} = bor %v{l}, %v{r}"
  | .bnot d s => s!"  %v{d} = bnot %v{s}"
  | .ishl d l r => s!"  %v{d} = ishl %v{l}, %v{r}"
  | .sshr d l r => s!"  %v{d} = sshr %v{l}, %v{r}"

/-- The CLIF text for a function. Not proved to be its own inverse here: the
reader of this text is `cranelift-reader`, a trusted component per ADR-032 §3. -/
def renderFunc (f : Func) : String :=
  "function %main() -> i64 {\nblock0:\n" ++
    String.intercalate "\n" (f.instrs.map Instr.text) ++
    "\n  return %v" ++ toString f.retSrc ++ "\n}\n"

end Morph.Clif
