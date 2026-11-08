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
  /-- ADR-012: allocate a closure cell holding the captured registers, then
      bind `dst` to `Value.closure fn envLoc`. `allocClosure` is the only
      instruction that *creates* loans (one per captured place). -/
  | allocClosure (dst : ValId) (fn : FnId) (captures : List ValId)
  /-- ADR-012: dynamic dispatch through a closure value: read the closure
      cell to recover `(fn, envLoc)` and invoke `fn`. -/
  | callClosure  (dst : ValId) (clo : ValId) (args : List ValId)
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
  | .allocClosure dst _ _ => [dst]
  | .callClosure dst _ _ => [dst]
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
  | .allocClosure _ _ captures => captures
  | .callClosure _ clo args => clo :: args
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
def blockUseGo : List ValId → List Instr → Bool
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

/-- Completeness of the computable use check (loop 95): if every use of
every instruction is covered by the parameters or by earlier definitions,
the check passes. Pairs with `wfBlockUse_sound`; together they say the
check decides coverage. Lowering correctness (`Morph.HIRToMIR`) proves
the premise for generated code. -/
theorem wfBlockUse_complete (fparams : List ValId) (b : Block)
    (h : ∀ pre i suf, b.instrs = pre ++ i :: suf →
      ∀ v ∈ usesOf i, v ∈ fparams ++ pre.flatMap defOf) :
    wfBlockUse fparams b = true := by
  unfold wfBlockUse
  have go : ∀ (is : List Instr) (avail : List ValId) (pre : List Instr),
      (∀ w ∈ fparams ++ pre.flatMap defOf, w ∈ avail) →
      (∀ p i s, is = p ++ i :: s →
        ∀ v ∈ usesOf i, v ∈ fparams ++ (pre ++ p).flatMap defOf) →
      blockUseGo avail is = true := by
    intro is
    induction is with
    | nil => intro avail pre _ _; rfl
    | cons i rest ih =>
        intro avail pre hav hcov
        have hi : (usesOf i).all (avail.contains ·) = true := by
          rw [List.all_eq_true]
          intro v hv
          rw [List.contains_iff_mem]
          apply hav
          have hmem := hcov [] i rest rfl v hv
          simpa using hmem
        have ht : blockUseGo (defOf i ++ avail) rest = true := by
          refine ih (defOf i ++ avail) (pre ++ [i]) ?_ ?_
          · intro w hw
            have hw' : w ∈ fparams ++ pre.flatMap defOf ++ defOf i := by
              simpa [List.flatMap_append, List.append_assoc] using hw
            rcases List.mem_append.mp hw' with h1 | h1
            · exact List.mem_append_right _ (hav w h1)
            · exact List.mem_append_left _ h1
          · intro p i' s heq v hv
            have hmem := hcov (i :: p) i' s (by simpa using heq) v hv
            simpa [List.flatMap_append, List.append_assoc] using hmem
        simp only [blockUseGo, Bool.and_eq_true]
        exact ⟨hi, ht⟩
  exact go b.instrs fparams [] (by simp)
    (fun p i s heq v hv => h p i s heq v hv)

/-- Monotonicity of the use-check accumulator: enlarging the available set
(membership-wise) preserves success. Lowering correctness grows the
accumulator with each generated prefix, so every composition step goes
through here. -/
theorem blockUseGo_mono (avail avail' : List ValId) (is : List Instr)
    (hsub : ∀ v ∈ avail, v ∈ avail') (h : blockUseGo avail is = true) :
    blockUseGo avail' is = true := by
  induction is generalizing avail avail' with
  | nil => rfl
  | cons i rest ih =>
      simp only [blockUseGo, Bool.and_eq_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ih (defOf i ++ avail) (defOf i ++ avail') ?_ h2⟩
      · rw [List.all_eq_true] at h1 ⊢
        intro v hv
        have hmem : v ∈ avail := List.contains_iff_mem.mp (h1 v hv)
        exact List.contains_iff_mem.mpr (hsub v hmem)
      · intro v hv
        rcases List.mem_append.mp hv with h3 | h3
        · exact List.mem_append_left _ h3
        · exact List.mem_append_right _ (hsub v h3)

/-- Composition: checking `l₁ ++ l₂` splits into checking `l₁`, then `l₂`
with the definitions of `l₁` added to the accumulator. The workhorse for
lowering correctness (`Morph.HIRToMIR`), where each construct appends its
own instructions after its children's. -/
theorem blockUseGo_append (avail : List ValId) (l₁ l₂ : List Instr)
    (h1 : blockUseGo avail l₁ = true)
    (h2 : blockUseGo (l₁.flatMap defOf ++ avail) l₂ = true) :
    blockUseGo avail (l₁ ++ l₂) = true := by
  induction l₁ generalizing avail with
  | nil => simpa using h2
  | cons a l₁ ih =>
      rw [List.cons_append]
      simp only [blockUseGo, Bool.and_eq_true] at h1 ⊢
      obtain ⟨ha, h1t⟩ := h1
      refine ⟨ha, ih (defOf a ++ avail) h1t ?_⟩
      have hmem : ∀ v ∈ (a :: l₁).flatMap defOf ++ avail,
          v ∈ l₁.flatMap defOf ++ (defOf a ++ avail) := by
        intro v hv
        have h1 : v ∈ defOf a ++ l₁.flatMap defOf ++ avail := by
          simpa [List.flatMap_cons] using hv
        rcases List.mem_append.mp h1 with h | h
        · rcases List.mem_append.mp h with h | h
          · exact List.mem_append_right _ (List.mem_append_left _ h)
          · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_append_right _ h)
      exact blockUseGo_mono _ _ _ hmem h2

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

/-- Whole-program well-formedness: every function is well-formed. -/
def WFProg (p : Program) : Bool :=
  p.funcs.all WF

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
  | .allocClosure _ _ _ => none
  | .callClosure _ _ _ => none
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
  | .allocClosure dst fn captures =>
      -- ADR-012: read every capture first, then allocate the env cell and
      -- bind `dst` to the closure value. Reading captures before allocating
      -- keeps the step deterministic even when `Store.alloc` reuses a
      -- freed location.
      match captures.mapM (fun c => fenv.env c) with
      | none => none
      | some _vals =>
          let (σ', loc) := Store.alloc fenv.store Typ.intType Value.unit
          some ⟨(fenv.env).update dst (Value.closure fn loc), σ'⟩
  | .callClosure dst clo _args =>
      -- ADR-012: read the closure cell to recover `(fn, envLoc)`.
      match fenv.env clo with
      | some (Value.closure _fn envLoc) =>
          some ⟨(fenv.env).update dst (Value.loc envLoc), fenv.store⟩
      | _ => none
  | .call _ _ _ => none
  | .phi _ _ _ => none

/-- Find a block by its id. -/
def findBlock (f : Func) (bid : BlockId) : Option Block :=
  f.blocks.find? (fun b => b.id == bid)

/-- Execute a block's straight-line instruction list. (The block's
terminator is `execBlockFuel`'s business, not this function's.) -/
def execInstrsFull (fenv : FullEnv) : List Instr → Option FullEnv
  | [] => some fenv
  | i :: is =>
      match evalInstrFull fenv i with
      | none => none
      | some fenv' => execInstrsFull fenv' is

/-! ## Edge-aware execution (Stage C item C1)

`execInstrsFull` runs a block without being told which edge was taken, so every
`phi` stalls there (`evalInstrFull` returns `none` for it). Branching programs
merge values with `phi`, and `Instr.phi` already records the predecessor in its
`pred` field, so the only missing datum is the block we arrived from.
`execInstrsFullFrom` adds exactly that parameter.

The Stage A/B executors are deliberately left untouched: every theorem that
names `execFunc`/`execBlockFuel` keeps applying to the fragment it was proved
for, and no agreement lemma is needed to say so — the old code does not change.
-/

/-- Edge-aware instruction execution. `phi dst pred src` reads `src` when the
block was entered from `pred`, and is skipped otherwise — including at the entry
block (`prev = none`), whose phis are dead. Every other instruction defers to
`evalInstrFull`. -/
def execInstrsFullFrom (prev : Option BlockId) (fenv : FullEnv) :
    List Instr → Option FullEnv
  | [] => some fenv
  | .phi dst pred src :: rest =>
      match prev with
      | none => execInstrsFullFrom prev fenv rest
      | some p =>
          if pred = p then
            match fenv.env src with
            | none => none
            | some v =>
                execInstrsFullFrom prev ⟨fenv.env.update dst v, fenv.store⟩ rest
          else execInstrsFullFrom prev fenv rest
  | i :: rest =>
      match evalInstrFull fenv i with
      | none => none
      | some fenv' => execInstrsFullFrom prev fenv' rest

@[simp] theorem execInstrsFullFrom_nil (prev : Option BlockId) (fenv : FullEnv) :
    execInstrsFullFrom prev fenv [] = some fenv := rfl

/-- A phi in the entry block never fires: there is no edge to match. -/
@[simp] theorem execInstrsFullFrom_phi_none (dst : ValId) (pred : BlockId)
    (src : ValId) (rest : List Instr) (fenv : FullEnv) :
    execInstrsFullFrom none fenv (.phi dst pred src :: rest) =
      execInstrsFullFrom none fenv rest := rfl

/-- Arriving from the phi's own predecessor binds it. -/
theorem execInstrsFullFrom_phi_hit (dst : ValId) (pred p : BlockId) (src : ValId)
    (rest : List Instr) (fenv : FullEnv) (h : pred = p) :
    execInstrsFullFrom (some p) fenv (.phi dst pred src :: rest) =
      (match fenv.env src with
       | none => none
       | some v => execInstrsFullFrom (some p)
           ⟨fenv.env.update dst v, fenv.store⟩ rest) := by
  subst h
  simp [execInstrsFullFrom]

/-- Arriving from any other block leaves the phi unexecuted, which is what makes
a merge block well-defined: only the incoming edge's phi runs. -/
theorem execInstrsFullFrom_phi_miss (dst : ValId) (pred p : BlockId) (src : ValId)
    (rest : List Instr) (fenv : FullEnv) (h : pred ≠ p) :
    execInstrsFullFrom (some p) fenv (.phi dst pred src :: rest) =
      execInstrsFullFrom (some p) fenv rest := by
  simp [execInstrsFullFrom, h]

/-- A non-phi instruction steps identically with or without an edge parameter. -/
theorem execInstrsFullFrom_nonphi (prev : Option BlockId) (fenv : FullEnv)
    {i : Instr} {rest : List Instr} (h : ∀ dst pred src, i ≠ .phi dst pred src) :
    execInstrsFullFrom prev fenv (i :: rest) =
      (match evalInstrFull fenv i with
       | none => none
       | some fenv' => execInstrsFullFrom prev fenv' rest) := by
  cases i with
  | phi dst pred src => exact absurd rfl (h dst pred src)
  | _ => rfl

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

/-- Edge-aware block execution: the same walk as `execBlockFuel`, with the
predecessor threaded into the instructions (`phi` fires on the matching edge)
and into the successor call (`prev := some b.id`). -/
def execBlockFrom (fuel : Nat) (f : Func) (prev : Option BlockId) (b : Block)
    (fenv : FullEnv) : Option Value :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match execInstrsFullFrom prev fenv b.instrs with
      | none => none
      | some fenv' =>
          match b.terminator with
          | .return_ v => fenv'.env v
          | .goto t =>
              match findBlock f t with
              | some b' => execBlockFrom fuel f (some b.id) b' fenv'
              | none => none
          | .branch cond tt ff =>
              match fenv'.boolOf cond with
              | some true =>
                  match findBlock f tt with
                  | some b' => execBlockFrom fuel f (some b.id) b' fenv'
                  | none => none
              | some false =>
                  match findBlock f ff with
                  | some b' => execBlockFrom fuel f (some b.id) b' fenv'
                  | none => none
              | none => none
          | .switch _ _ _ => none

/-- Execute a function from its entry block, edge-aware. Unlike `execFunc` the
entry block is dispatched directly rather than through a synthetic
`goto`-block, so one block of straight-line code costs one unit of fuel. -/
def execFuncFrom (fuel : Nat) (f : Func) (fenv : FullEnv) : Option Value :=
  match findBlock f f.entry with
  | some b => execBlockFrom fuel f none b fenv
  | none => none

/-- Entry dispatch is the only difference between `execFuncFrom` and a direct
`execBlockFrom` call: there is no synthetic block in between. -/
theorem execFuncFrom_eq (fuel : Nat) (f : Func) (b : Block) (fenv : FullEnv)
    (h : findBlock f f.entry = some b) :
    execFuncFrom fuel f fenv = execBlockFrom fuel f none b fenv := by
  simp [execFuncFrom, h]

/-- One straight-line block, entered with no predecessor: run its instructions
then read the return register. This is the shape every Stage A/B function has,
and the base case C4's block statement has to reproduce. -/
theorem execBlockFrom_return (f : Func) (prev : Option BlockId) (b : Block)
    (v : ValId) (fenv : FullEnv) :
    execBlockFrom 1 f prev ⟨b.id, b.instrs, .return_ v⟩ fenv =
      (match execInstrsFullFrom prev fenv b.instrs with
       | none => none
       | some fenv' => fenv'.env v) := rfl

end Morph.MIR

