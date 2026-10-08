/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Executable

/-!
# Mid-Level Intermediate Representation (MIR)

Target-independent MIR per ADR-011 §1: a control-flow graph of basic blocks
over an SSA value graph. MIR is *not* machine code — no registers, no
instruction encoding, no calling convention. Values are indexed by integer
IDs (`ValId`) scoped to a function; blocks by `BlockId`; functions by name
(`FnId`).

This module provides:

* the data types (`Instr`, `Terminator`, `Block`, `Func`, `Program`);
* small, computable well-formedness checks (`wfBlockUse`, `WFCFG`,
  `WFParams`, `WF`) that a stage-1 lowering can be held to, plus a soundness
  lemma for the single-block use check;
* a partial evaluation oracle (`evalInstr`) for the pure instructions, to be
  extended with store- and call-aware evaluation when stage-1 lowering lands.

The single-block assumption: `wfBlockUse` checks each block's uses against the
function parameters plus the values defined *in that block*. Cross-block use
rules (phi/dominance) come with the SSA work of ADR-011 stage 3.

**Related Files:**
- `Morph/Core.lean` - `Value`, `Typ`, `Capability`
- `Morph/Executable.lean` - surface interpreter reused as the eval oracle
- `.specs/02_adrs/ADR-011-mir-lowering-and-borrow-check.md` - design of record
-/

namespace Morph.MIR

open Morph.Core

/-! ## Identifiers -/

/-- SSA value identifier, scoped to a function. -/
abbrev ValId := Nat

/-- Basic-block identifier, scoped to a function. -/
abbrev BlockId := Nat

/-- Function identifier, scoped to a program. -/
abbrev FnId := String

/-! ## Operators

Binary and unary operators at the MIR level. These map onto the surface
`Operator` during stage-1 lowering (see `BinOp.toOperator`); the set is
self-contained so the IR can be reasoned about without the surface syntax.
`BinOp.not` exists for surface parity but is a *unary* operation — lowering
must emit `Instr.unop` with `UnOp.not` instead.
-/

/-- Binary operators at the MIR level. -/
inductive BinOp where
  | add | sub | mul | div | mod
  | eq | neq | lt | leq | gt | geq
  | and | or | not
  | andb | orb | xorb | shl | shr
  deriving Repr, BEq, DecidableEq

/-- Unary operators at the MIR level. -/
inductive UnOp where
  | not | notb
  deriving Repr, BEq, DecidableEq

/-- Map a MIR binary operator to the surface `Operator` understood by the
`Morph.Executable` oracle. -/
def BinOp.toOperator : BinOp → Operator
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod
  | .eq => .eq
  | .neq => .neq
  | .lt => .lt
  | .leq => .leq
  | .gt => .gt
  | .geq => .geq
  | .and => .and
  | .or => .or
  | .not => .not
  | .andb => .andb
  | .orb => .orb
  | .xorb => .xorb
  | .shl => .shl
  | .shr => .shr

/-- Map a MIR unary operator to the surface `Operator` understood by the
`Morph.Executable` oracle. -/
def UnOp.toOperator : UnOp → Operator
  | .not => .not
  | .notb => .notb

/-! ## Instructions, blocks, functions, programs -/

/-- A MIR instruction. Every instruction except `store` and `free` defines its
destination `dst`; `phi` is a use of `src` registered for a predecessor block
(resolved during verification, per ADR-011). -/
inductive Instr where
  | const  (dst : ValId) (v : Value)
  | copy   (dst : ValId) (src : ValId)
  | unop   (dst : ValId) (op : UnOp) (src : ValId) (τ : Typ)
  | binop  (dst : ValId) (op : BinOp) (l r : ValId) (τ : Typ)
  | load   (dst : ValId) (loc : ValId) (cap : Capability)
  | store  (loc : ValId) (src : ValId) (cap : Capability)
  | alloc  (dst : ValId) (cap : Capability) (τ : Typ)
  | free   (loc : ValId)
  | call   (dst : Option ValId) (fn : FnId) (args : List ValId)
  | phi    (dst : ValId) (pred : BlockId) (src : ValId)
  deriving Repr, BEq

/-- Default instruction: `const 0 (.int 0)` (needed for `.head!`-style list
access in tests; the payload constructors of `Value`/`Capability` carry no
`Inhabited` instance, so this is declared manually). -/
instance : Inhabited Instr := ⟨.const 0 (.int 0)⟩

/-- How control flow exits a basic block. -/
inductive Terminator where
  | goto    (target : BlockId)
  | branch  (cond : ValId) (tt ff : BlockId)
  | return_ (src : ValId)
  | switch  (scrut : ValId) (targets : List (Nat × BlockId)) (default : BlockId)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A basic block: a straight-line sequence of instructions ending in a
terminator. -/
structure Block where
  id         : BlockId
  instrs     : List Instr
  terminator : Terminator
  deriving Repr, BEq, Inhabited

/-- A function: a CFG of blocks over SSA values, with an entry block. -/
structure Func where
  name    : String
  params  : List (ValId × Typ)
  blocks  : List Block
  entry   : BlockId
  retType : Typ
  deriving Repr, BEq

/-- A whole program: a list of functions. -/
structure Program where
  funcs : List Func
  deriving Repr, BEq

/-! ## Defs and uses

Conservative dataflow facts used by the well-formedness checks. `defOf` /
`usesOf` are per-instruction; `defsOf` collects a block's definitions.
-/

/-- Values an instruction defines (its destination, when it has one; `call`
defines `dst` only when it is `some`). -/
def defOf : Instr → List ValId
  | .const dst _ => [dst]
  | .copy dst _ => [dst]
  | .unop dst _ _ _ => [dst]
  | .binop dst _ _ _ _ => [dst]
  | .load dst _ _ => [dst]
  | .store _ _ _ => []
  | .alloc dst _ _ => [dst]
  | .free _ => []
  | .call dst _ _ => dst.toList
  | .phi dst _ _ => [dst]

/-- Values an instruction uses. -/
def usesOf : Instr → List ValId
  | .const _ _ => []
  | .copy _ src => [src]
  | .unop _ _ src _ => [src]
  | .binop _ _ l r _ => [l, r]
  | .load _ loc _ => [loc]
  | .store loc src _ => [loc, src]
  | .alloc _ _ _ => []
  | .free loc => [loc]
  | .call _ _ args => args
  | .phi _ _ src => [src]

/-- All values a block defines, in instruction order. -/
def defsOf (b : Block) : List ValId :=
  b.instrs.flatMap defOf

/-! ## Well-formedness

These are deliberately small, computable checks — enough for a stage-1
lowering to be held to, not a full SSA verifier. Dominance and cross-block
use rules arrive with ADR-011 stage 3 (SSA + layout); the borrow checking of
stage 2 is a separate analysis over `WFCFG`.
-/

/-- Worklist for `wfBlockUse`: walk the instruction list with an accumulator of
available ids (params ∪ defs so far); every use must be in the accumulator. -/
private def blockUseGo : List ValId → List Instr → Bool
  | _, [] => true
  | avail, i :: rest =>
    (usesOf i).all (avail.contains ·) && blockUseGo (defOf i ++ avail) rest

/-- Single-block use check: every value an instruction of `b` uses is available
at that point — covered by the function parameters `fparams` or by a
definition earlier in the block. COMPUTABLE so tests and lowering can `#eval`
it. Note the single-block assumption: uses defined in *other* blocks (and not
via a phi) fail this check; cross-block rules come with the dominance work. -/
def wfBlockUse (fparams : List ValId) (b : Block) : Bool :=
  blockUseGo fparams b.instrs

/-- Soundness of the computable use check: if `wfBlockUse` passes, every value
used anywhere in the block belongs to the parameters or to the block's own
definitions. -/
theorem wfBlockUse_sound (fparams : List ValId) (b : Block)
    (h : wfBlockUse fparams b = true) :
    ∀ i ∈ b.instrs, ∀ v ∈ usesOf i, v ∈ fparams ++ defsOf b := by
  unfold wfBlockUse at h
  have go_sound : ∀ (instrs : List Instr) (avail : List ValId),
      (∀ i ∈ instrs, i ∈ b.instrs) →
      (∀ v ∈ avail, v ∈ fparams ++ defsOf b) →
      blockUseGo avail instrs = true →
      ∀ i ∈ instrs, ∀ v ∈ usesOf i, v ∈ fparams ++ defsOf b := by
    intro instrs
    induction instrs with
    | nil => intro avail _ _ _ i hi; cases hi
    | cons i rest ih =>
      intro avail hin havail hg
      simp only [blockUseGo, Bool.and_eq_true] at hg
      have huses : ∀ v ∈ usesOf i, v ∈ fparams ++ defsOf b := by
        intro v hv
        have := List.all_eq_true.mp hg.1 v hv
        exact havail v (List.contains_iff_mem.mp this)
      refine fun i' hi' v hv => ?_
      rcases List.mem_cons.mp hi' with rfl | hi'rest
      · exact huses v hv
      · exact ih (defOf i ++ avail)
          (fun j hj => hin j (List.mem_cons.mpr (Or.inr hj)))
          (fun w hw => by
            rcases List.mem_append.mp hw with h1 | h2
            · exact List.mem_append_right _
                (List.mem_flatMap.mpr ⟨i, hin i (List.mem_cons.mpr (Or.inl rfl)), h1⟩)
            · exact havail w h2)
          hg.2 i' hi'rest v hv
  exact go_sound b.instrs fparams (fun _ hi => hi)
    (fun v hv => List.mem_append_left _ hv) h

/-- Terminator targets: `goto`/`branch`/`switch` outgoing edges (branch
targets only; the scrutinee/condition are values, not blocks). -/
def blockTargets : Terminator → List BlockId
  | .goto t => [t]
  | .branch _ tt ff => [tt, ff]
  | .return_ _ => []
  | .switch _ targets default => targets.map Prod.snd ++ [default]

/-- A list has no duplicate elements (kernel-reduction-friendly duplicate
check for the `decide`-able WF predicates). -/
def noDups : List ValId → Bool
  | [] => true
  | a :: rest => !rest.contains a && noDups rest

/-- CFG well-formedness: all terminator targets exist as blocks, the entry
block exists, and block ids are unique. -/
def WFCFG (f : Func) : Bool :=
  let ids := f.blocks.map Block.id
  ids.contains f.entry
    && noDups ids
    && f.blocks.all (fun b => (blockTargets b.terminator).all ids.contains)

/-- No duplicate `ValId` among the function's parameters. -/
def WFParams (f : Func) : Bool :=
  noDups (f.params.map Prod.fst)

/-- Whole-function well-formedness: CFG integrity, unique params, and the
single-block use check on every block. -/
def WF (f : Func) : Bool :=
  WFCFG f && WFParams f && f.blocks.all (wfBlockUse (f.params.map Prod.fst))

/-! ## Evaluation oracle

Value environment for one function invocation, and evaluation of the PURE
instructions (`const`/`copy`/`unop`/`binop`). `load`/`store`/`alloc`/`free`/
`call` need the store and the program; they are `none`-stubs for now —
store- and call-aware evaluation arrives with stage 1 lowering.

Binops delegate to `Morph.Executable.evalBinop` so the MIR oracle and the
surface interpreter cannot drift apart.
-/

/-- Value environment: `ValId ↦ Value` for one function invocation. -/
abbrev Env := ValId → Option Value

namespace Env

/-- Register `dst ↦ v`, shadowing any previous binding of `dst`. -/
def update (env : Env) (dst : ValId) (v : Value) : Env :=
  fun x => if x == dst then some v else env x

end Env

/-- Evaluate a MIR binop on `Value`s via the surface oracle
`Morph.Executable.evalBinop`. Both operands must be literal-shaped values of
a kind the operator accepts; otherwise `none`. -/
def evalBinOp (op : BinOp) (v1 v2 : Value) : Option Value := do
  let e ← Morph.Executable.evalBinop op.toOperator (.lit v1) (.lit v2)
  match e with
  | .lit v => some v
  | _ => none

/-- Evaluate a MIR unop on a `Value` via the surface oracle
`Morph.Executable.evalUnop`. -/
def evalUnOp (op : UnOp) (v : Value) : Option Value := do
  let e ← Morph.Executable.evalUnop op.toOperator (.lit v)
  match e with
  | .lit v => some v
  | _ => none

/-- Evaluate one instruction in an environment, returning the updated
environment. Only the pure instructions evaluate; memory and call
instructions are `none`-stubs until stage-1 lowering provides the store and
the program. -/
def evalInstr (env : Env) : Instr → Option Env
  | .const dst v => some (env.update dst v)
  | .copy dst src => env src |>.map (env.update dst)
  | .unop dst op src _τ => do
    let v ← env src
    let r ← evalUnOp op v
    some (env.update dst r)
  | .binop dst op l r _τ => do
    let vl ← env l
    let vr ← env r
    let v ← evalBinOp op vl vr
    some (env.update dst v)
  | .load _ _ _ => none
  | .store _ _ _ => none
  | .alloc _ _ _ => none
  | .free _ => none
  | .call _ _ _ => none
  | .phi _ _ _ => none


/-! ## Store-aware execution (Loop 8) -/

/-- Full execution environment: value registers + the store. -/
structure FullEnv where
  env   : Env
  store : Store

/-- Extract a location value from the environment. -/
def FullEnv.locOf (fenv : FullEnv) (vid : ValId) : Option Loc :=
  match fenv.env vid with
  | some (Value.loc l) => some l
  | _ => none

/-- Extract an integer value from the environment. -/
def FullEnv.intOf (fenv : FullEnv) (vid : ValId) : Option Int :=
  match fenv.env vid with
  | some (Value.int n) => some n
  | _ => none

/-- Extract a boolean value from the environment. -/
def FullEnv.boolOf (fenv : FullEnv) (vid : ValId) : Option Bool :=
  match fenv.env vid with
  | some (Value.bool b) => some b
  | _ => none

/-- Store-aware execution: handles pure instructions plus load/store/alloc/free. -/
def evalInstrFull (fenv : FullEnv) : Instr → Option FullEnv
  | .const dst v => some ⟨(fenv.env).update dst v, fenv.store⟩
  | .copy dst src => do
      let v ← fenv.env src
      some ⟨(fenv.env).update dst v, fenv.store⟩
  | .unop dst op src _τ => do
      let v ← fenv.env src
      let r ← evalUnOp op v
      some ⟨(fenv.env).update dst r, fenv.store⟩
  | .binop dst op x y _τ => do
      let vl ← fenv.env x
      let vr ← fenv.env y
      let v ← evalBinOp op vl vr
      some ⟨(fenv.env).update dst v, fenv.store⟩
  | .load dst loc _cap => do
      let l := fenv.locOf loc
      let l' ← l
      let result ← Store.load fenv.store l'
      some ⟨(fenv.env).update dst result.2, fenv.store⟩
  | .store loc src _cap => do
      let l := fenv.locOf loc
      let l' ← l
      let v ← fenv.env src
      let σ' ← Store.store fenv.store l' v Typ.intType
      some ⟨fenv.env, σ'⟩
  | .alloc dst _cap τ => do
      let (σ', loc) := Store.alloc fenv.store τ Value.unit
      some ⟨(fenv.env).update dst (Value.loc loc), σ'⟩
  | .free loc => do
      let l := fenv.locOf loc
      let l' ← l
      let σ' ← Store.free fenv.store l'
      some ⟨fenv.env, σ'⟩
  | _ => none

/-- Find a block by its id. -/
def findBlock (f : Func) (bid : BlockId) : Option Block :=
  f.blocks.find? (fun b => b.id == bid)

/-- Execute a single block: walk instructions, then handle the terminator. -/
def execInstrsFull (fenv : FullEnv) : List Instr → Option FullEnv
  | [] => some fenv
  | i :: is =>
      match evalInstrFull fenv i with
      | none => none
      | some fenv' => execInstrsFull fenv' is

/-- Execute a single block: walk instructions, then handle the terminator. -/
def execBlockFuel (fuel : Nat) (f : Func) (b : Block) (fenv : FullEnv) : Option Value :=
  match fuel with
  | 0 => none
  | fuel+1 =>
      match execInstrsFull fenv b.instrs with
      | none => none
      | some fenv' =>
          match b.terminator with
          | .return_ v => fenv'.env v
          | .goto t =>
              match findBlock f t with
              | some b' => execBlockFuel fuel f b' fenv'
              | none => none
          | .branch cond tt ff =>
              match fenv'.boolOf cond with
              | some true =>
                  match findBlock f tt with
                  | some b' => execBlockFuel fuel f b' fenv'
                  | none => none
              | some false =>
                  match findBlock f ff with
                  | some b' => execBlockFuel fuel f b' fenv'
                  | none => none
              | none => none
          | .switch _ _ _ => none

/-- Execute a block by its id. -/
def execBlockById (fuel : Nat) (f : Func) (bid : BlockId) (fenv : FullEnv) : Option Value :=
  match findBlock f bid with
  | some b => execBlockFuel fuel f b fenv
  | none => none

/-- Execute a function from its entry block with a full environment. -/
def execFunc (fuel : Nat) (f : Func) (fenv : FullEnv) : Option Value :=
  execBlockFuel fuel f
    { id := f.entry, instrs := [], terminator := .goto f.entry }
    fenv

end Morph.MIR

