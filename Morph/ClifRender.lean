/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifBlocks

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
function %main() -> i64 {        -- one function, one i64 result
block0:                          -- Stage B: a single block, numbered 0
  v0 = iconst.i64 42             -- iconst, immediate in i64 range
  v1 = iadd v0, v0               -- iadd isub imul band bor ishl sshr
  v2 = icmp slt v1, v0           -- icmp with eq ne slt sle sgt sge
  v3 = bnot v2                   -- bnot, one operand
  return v3                      -- returns one register
}
```

An instruction is `v<dst> = <op> <operands>`, registers are bare `v<n>` with `<n>`
decimal, and an immediate is an optional `-` followed by decimals. `icmp` carries
its condition as an infix keyword. Nothing else is emitted, so anything else must
be rejected by the reader; the token-level analogue of that rejection is the
`none` case of `parseInstr`.

The `%` is on the *function* name only: CLIF spells SSA values `v0`, and spells a
function `%name` in a `function` header. Printing `%v0` (the wasm-text habit)
makes the artifact unreadable by `cranelift-reader`, which reports it as a
malformed block — found in loop 153 by pointing the reader at the output.

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
  | call
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
  | str (s : String)
  | typ (τ : Typ)
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
  | .call d fn args ret =>
      [.kw .call, .reg d, .str fn, .arity args.length] ++
        args.map .reg ++ [.typ ret]

/-- Read `n` register tokens. Bounded by `n` so the recursion is
structural in the fuel; the call arity header supplies the bound, and
`parseRegs_toksRegs` shows `n := args.length` is exactly right. -/
def parseRegs : Nat → List Tok → Option (List Reg × List Tok)
  | 0, toks => some ([], toks)
  | n + 1, .reg r :: rest =>
      match parseRegs n rest with
      | some (rs, rest') => some (r :: rs, rest')
      | none => none
  | _, _ => none

/-- Reading back the registers a call tokenises returns them and leaves
the tail alone. -/
theorem parseRegs_toksRegs (rs : List Reg) (rest : List Tok) :
    parseRegs rs.length (rs.map .reg ++ rest) = some (rs, rest) := by
  induction rs generalizing rest with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons]
      show parseRegs (Nat.succ rs.length) (.reg r :: (rs.map .reg ++ rest)) = _
      simp only [parseRegs, ih]

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
  | .kw .call :: .reg d :: .str fn :: .arity n :: rest =>
      match parseRegs n rest with
      | some (args, .typ ret :: rest') => some (.call d fn args ret, rest')
      | _ => none
  | _ => none

/-- `parseInstr` is a left inverse of `toksInstr`, with the rest of the stream
carried through untouched. This is the interesting half of the round trip: every
case is decided by the name token alone. -/
theorem parseInstr_toksInstr (i : Instr) (rest : List Tok) :
    parseInstr (toksInstr i ++ rest) = some (i, rest) := by
  cases i with
  | iconst d v => rfl
  | iadd d l r => rfl
  | isub d l r => rfl
  | imul d l r => rfl
  | icmp d c l r => rfl
  | band d l r => rfl
  | bor d l r => rfl
  | bnot d s => rfl
  | ishl d l r => rfl
  | sshr d l r => rfl
  | call d fn args ret =>
      rw [show toksInstr (.call d fn args ret) ++ rest
            = .kw .call :: .reg d :: .str fn :: .arity args.length ::
              (args.map .reg ++ ([.typ ret] ++ rest)) from by simp [toksInstr]]
      simp only [parseInstr, parseRegs_toksRegs, List.singleton_append]

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

/-- Render a declared CLIF type. `addr` is address-sized on the x86-64
SystemV target, hence `i64` — the assumption the `CallingConvention`
revisit records. Placed before the printers: the declared type
vocabulary belongs to the whole `Clif` model, not to the multi-block
layer. -/
def ClifTy.text : ClifTy → String
  | .i64 => "i64"
  | .i8 => "i8"
  | .addr => "i64"

/-- The declared return signature of a call being printed. Types with no
call slot (unit and non-first-order) take no result suffix. -/
def retSuffix : Typ → String
  | τ =>
      match clifTyOfTyp τ with
      | some t => " -> " ++ t.text
      | none => ""

/-- Text of one instruction, in the grammar at the top of the file. -/
def Instr.text : Instr → String
  | .iconst d v => s!"  v{d} = iconst.i64 {v}"
  | .iadd d l r => s!"  v{d} = iadd v{l}, v{r}"
  | .isub d l r => s!"  v{d} = isub v{l}, v{r}"
  | .imul d l r => s!"  v{d} = imul v{l}, v{r}"
  | .icmp d c l r => s!"  v{d} = icmp {c.text} v{l}, v{r}"
  | .band d l r => s!"  v{d} = band v{l}, v{r}"
  | .bor d l r => s!"  v{d} = bor v{l}, v{r}"
  | .bnot d s => s!"  v{d} = bnot v{s}"
  | .ishl d l r => s!"  v{d} = ishl v{l}, v{r}"
  | .sshr d l r => s!"  v{d} = sshr v{l}, v{r}"
  | .call d fn args ret =>
      -- The preamble (`fn0` reference) and signature declarations arrive
      -- with emission (slice B); this arm names the callee, the actuals,
      -- and the declared return type in the shape the preamble will anchor.
      "  v" ++ toString d ++ " = call %" ++ fn ++ "(" ++
        String.intercalate ", " (args.map (fun a => "v" ++ toString a)) ++
        ")" ++ retSuffix ret

/-- The CLIF text for a function. Not proved to be its own inverse here: the
reader of this text is `cranelift-reader`, a trusted component per ADR-032 §3. -/
def renderFunc (f : Func) : String :=
  "function %main() -> i64 {\nblock0:\n" ++
    String.intercalate "\n" (f.instrs.map Instr.text) ++
    "\n  return v" ++ toString f.retSrc ++ "\n}\n"

end Morph.Clif

/-! ## Stage C: the multi-block form

`docs/STAGEC-SCOPE.md` §4.3. The grammar above is Stage B's: one block, no
parameters, no terminator but `return`. A branching function adds exactly three
things, and the token layer above is *not* extended to cover them — that layer
exists to prove the Stage B round trip, and widening it would mean re-proving
B5 for a fragment the reader (`cranelift-reader`) already owns. What is printed
here is checked by C6's native rows instead.

```
block1(v4: i64):                 -- parameters, with types
  v5 = iconst.i64 10
  jump block3(v5)                -- an edge carries arguments, untyped
block3(v6: i64):
  brif v3, block1(v7), block2(v8)  -- one argument list per target
  return v6
```

Two details that are easy to get wrong and are not stylistic: a parameter list
carries `: i64` (the header declares types) while edge arguments do not; and
`brif` takes an argument list *per target*, which is how the two arms of an `if`
pass different values to the same join parameter.
-/

namespace Morph.Clif
namespace Cfg

/-- A parameter list, with the type every value in this subset has. -/
def paramSuffix (params : List Reg) : String :=
  match params with
  | [] => ""
  | _ => "(" ++ String.intercalate ", " (params.map (fun p => "v" ++ toString p ++ ": i64")) ++ ")"

/-- An edge's argument list, without types. -/
def argSuffix (args : List Reg) : String :=
  match args with
  | [] => ""
  | _ => "(" ++ String.intercalate ", " (args.map (fun a => "v" ++ toString a)) ++ ")"

/-- Text of one terminator. -/
def termText : Term → String
  | .ret src => "  return v" ++ toString src
  | .jump t args => "  jump block" ++ toString t ++ argSuffix args
  | .brif c tt ta ff fa =>
    "  brif v" ++ toString c ++ ", block" ++ toString tt ++ argSuffix ta ++
      ", block" ++ toString ff ++ argSuffix fa

/-- Text of one block: header with parameters, instructions, terminator. -/
def blockText (b : Block) : String :=
  "block" ++ toString b.id ++ paramSuffix b.params ++ ":\n" ++
    (if b.instrs.isEmpty then ""
     else String.intercalate "\n" (b.instrs.map Morph.Clif.Instr.text) ++ "\n") ++
    termText b.term

/-- The CLIF text for a multi-block function. -/
def funcText (f : Func) : String :=
  "function %main() -> i64 {\n" ++
    String.intercalate "\n" (f.blocks.map blockText) ++ "\n}\n"

end Cfg

end Morph.Clif
