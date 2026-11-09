/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifTarget

/-!
# Stage C item C4a: the CLIF block model

`docs/STAGEC-SCOPE.md` §4.3. `Morph/ClifTarget.lean` is Stage B's target: one
instruction list and one return register, no blocks. This file adds the shape
`if` needs — several blocks, a terminator that chooses the next block, and the
block arguments that carry a value across an edge.

It lives in `Morph.Clif.Cfg` rather than replacing `Morph.Clif.Func`/`run`, for
the reason C1 kept the old MIR executors: B4's theorem, `blockEncode`, and
`emitFunc` are stated against the single-block surface, and they stay true for
that surface. The single-block shape becomes the *base case* here
(`run_singleBlockFunc`), not a definition to be rewritten.

## Why terminators carry arguments

The first sketch of this model (loop 154) had `jump (target)` and
`brif cond tt ff` with no `Block` parameter list. That cannot express a merge:
the reason an `if` needs a join block is that the branch's value has to cross an
edge into it, and a terminator with no arguments has nowhere to put the value.
CLIF's mechanism is the block argument — `jump block3(v1)` entering
`block3(v1: i64):`, and `brif v0, block1(v1), block2(v2)` with one argument
list per edge — and Cranelift's verifier requires that SSA shape.

So `Term.brif` carries two argument lists, not one. That is what makes the
one-armed `if` (scope §3) expressible: the untaken side passes the pre-branch
value, the taken side passes the arm's result, and the join's single parameter
receives whichever edge was taken.

## What this model enforces, and what it does not

Enforced:

- A block's terminator must name an existing block; a missing target is `none`.
- An edge's argument count must match the target's parameter count
  (`bindParams` fails otherwise), and a `brif` condition must be a boolean —
  an integer register is `none`, exactly as `evalCond` refuses a mistyped
  comparison.
- A join parameter that no edge argument binds is unreadable, so a lowering that
  forgets to pass the merged value returns `none` rather than a stale register.
  This is the whole point of making the parameters load-bearing.

Not enforced: **dominance.** The register environment is threaded from one block
into the next (with the target's parameters shadowing it), because that is how
the machine behaves after the SSA form is read — a value defined in a block that
dominates another is readable there. The model does not check the dominance
relation itself. Two consequences, both stated here rather than discovered
later:

- A program that reads a non-dominating register may run here and be rejected by
  Cranelift's verifier. The lowering does not produce such programs by
  construction (the entry block dominates every block, and the only
  multi-predecessor block, the join, reads its value from a parameter), and C6's
  native rows are the evidence for the parse-and-verify step.
- Parameter binding is a *shadow*, not a fresh scope, so a register that is both
  a parameter and an earlier definition takes the edge's value. That is the
  behaviour the phi↔argument correspondence in C4b needs.

These are the same kind of documented gap as `Morph.Clif.Value` holding `.bool`
where CLIF has an `i8`: the model is the smallest surface on which the theorem
can be stated and composed, and every place it is more permissive than the
verifier is listed.
-/

open Morph.Core

namespace Morph.Clif
namespace Cfg

/-- CLIF block label, local to a function. -/
abbrev BlockId := Nat

/-- Block terminator. `.ret` leaves the function; `.jump`/`.brif` transfer to a
block and pass one argument per parameter of the target. -/
inductive Term where
  /-- Return the value of `src`. -/
  | ret (src : Reg)
  /-- Transfer to `target`, binding its parameters to `args` in order. -/
  | jump (target : BlockId) (args : List Reg)
  /-- Branch on the boolean in `cond`, passing `ttArgs` to `tt` or `ffArgs` to
  `ff`. Two argument lists, because the two edges carry different values. -/
  | brif (cond : Reg) (tt : BlockId) (ttArgs : List Reg)
      (ff : BlockId) (ffArgs : List Reg)
  deriving Repr, BEq

/-- A basic block: parameters bound on entry, straight-line instructions, and a
terminator. -/
structure Block where
  id : BlockId
  params : List Reg
  instrs : List Instr
  term : Term
  deriving Repr, BEq

/-- A multi-block CLIF function. `blocks` is ordered with the entry first, which
is the order the printer emits; `entry` is what a call transfers to. -/
structure Func where
  blocks : List Block
  entry : BlockId
  deriving Repr, BEq

/-- Look up a register's value for each argument register, in order. -/
def evalArgs (env : Env) : List Reg → Option (List Value)
  | [] => some []
  | r :: rs => do
    let v ← env r
    let vs ← evalArgs env rs
    some (v :: vs)

/-- Bind a block's parameters to an edge's argument values, in order. Lengths
must agree: an edge with the wrong arity is not a runnable transfer. Parameters
shadow the incoming environment (`Env.set`), which is what makes a join
parameter take the value of the edge that was actually taken. -/
def bindParams (env : Env) : List Reg → List Value → Option Env
  | [], [] => some env
  | r :: rs, v :: vs =>
    match bindParams env rs vs with
    | none => none
    | some env' => some (env'.set r v)
  | _, _ => none

/-- What a block does when it finishes: return a value, or transfer along an
edge. -/
inductive Outcome where
  | ret (v : Value)
  | next (target : BlockId) (args : List Value)

/-- Execute a terminator in the environment the block left behind. -/
def runTerm (env : Env) : Term → Option Outcome
  | .ret src => (env src).map Outcome.ret
  | .jump t args => (evalArgs env args).map fun vs => Outcome.next t vs
  | .brif c tt ta ff fa => do
    let v ← env c
    let b ← asBool v
    let args ← evalArgs env (if b then ta else fa)
    some (.next (if b then tt else ff) args)

/-- Execute a block: its instructions, then its terminator. Returns the
post-body environment alongside the outcome, because an edge transfer binds the
target's parameters onto it — the environment is threaded from one block into
the next, with the parameters shadowing it (a value defined in a block that
dominates another is readable there). -/
def runBlock (env : Env) (b : Block) : Option (Env × Outcome) :=
  (runInstrs env b.instrs) >>= fun env' => (runTerm env' b.term).map (env', ·)

/-- The block with the given label, if any. -/
def findBlock (f : Func) (id : BlockId) : Option Block :=
  f.blocks.find? (fun b => b.id == id)

/-- Run from `b` with `fuel` block traversals left. Each block costs one unit —
the model counts blocks, not instructions, so the bound a theorem needs is a
bound on the path length (scope §4.4). The successor starts from the
predecessor's *post-body* environment with its parameters bound over it, which
is what makes this the model MIR's edge-aware executor corresponds to: both
thread the block's writes into the next block, and both give the edge's values
priority through shadowing (`bindParams` here, the phi fold there). -/
def runFuel : Nat → Func → Block → Env → Option Value
  | 0, _, _, _ => none
  | fuel + 1, f, b, env => do
    let (envPost, o) ← runBlock env b
    match o with
    | .ret v => some v
    | .next t args => do
      let b' ← findBlock f t
      let env' ← bindParams envPost b'.params args
      runFuel fuel f b' env'

/-- Run a function from an empty register file. A declared entry parameter can
never be bound, so it is unreadable — a well-formedness obligation of the
emitter, like `phi`'s predecessor in MIR (scope §7 Q2). -/
def run (fuel : Nat) (f : Func) : Option Value :=
  match findBlock f f.entry with
  | none => none
  | some b => runFuel fuel f b (fun _ => none)

/-- One step of `runFuel`, in the form the proofs use. -/
theorem runFuel_succ (fuel : Nat) (f : Func) (b : Block) (env : Env) :
    runFuel (fuel + 1) f b env =
      ((runBlock env b).bind fun (envPost, o) =>
        match o with
        | .ret v => some v
        | .next t args =>
          (findBlock f t).bind fun b' =>
            (bindParams envPost b'.params args).bind fun env' => runFuel fuel f b' env') :=
  rfl

/-- The single-block function shape: no parameters, one block, `.ret`. -/
def singleBlockFunc (instrs : List Instr) (src : Reg) : Func :=
  ⟨[⟨0, [], instrs, .ret src⟩], 0⟩

/-- **The base case.** On a one-block function this model and Stage B's
`Morph.Clif.run` agree. Stated with `fuel + 1` because any non-zero fuel
suffices: a returning block is reached in one traversal. This is the lemma that
keeps B4 a theorem about the single-block surface instead of restating it. -/
theorem run_singleBlockFunc (fuel : Nat) (instrs : List Instr) (src : Reg) :
    run (fuel + 1) (singleBlockFunc instrs src) = Morph.Clif.run ⟨instrs, src⟩ := by
  simp only [run, singleBlockFunc, findBlock, List.find?_cons, beq_self_eq_true]
  rw [runFuel_succ]
  simp only [runBlock, runTerm, Morph.Clif.run]
  cases hinstrs : runInstrs (fun _ => none) instrs with
  | none => simp
  | some env =>
    cases hsrc : env src with
    | none => simp [hsrc]
    | some v => simp [hsrc]

/-! ## Examples

Two shapes, both checked by the compiler. The diamond is the C2b lowering's
shape: a condition in the entry block, one block per arm, and a join whose
parameter takes the edge's argument. The integer-condition case is the model
refusing a mistyped branch rather than choosing a truthiness convention. -/

/-- The C2b diamond at the CLIF layer: `cond ? 10 : 20` with the join's value
arriving as a block argument. `v0` is the condition (`v1 < v2`), `v3`/`v4` are
the arms, and `join(v5)` receives whichever arm ran. -/
def diamond (m : Int) (n : Int) : Func :=
  ⟨[ ⟨0, [], [.iconst 1 m, .iconst 2 n, .icmp 0 .slt 1 2],
      .brif 0 1 [] 2 []⟩,
    ⟨1, [], [.iconst 3 10, .iconst 4 10], .jump 3 [3]⟩,
    ⟨2, [], [.iconst 5 20, .iconst 6 20], .jump 3 [5]⟩,
    ⟨3, [7], [], .ret 7⟩ ],
   0⟩

/-- Self-comparison taken: the true arm's value reaches the join's parameter. -/
example : (run 4 (diamond 1 2) == some (.int 10)) = true := by native_decide

/-- Self-comparison not taken: the *other* arm's value, through the *other*
argument list. A model that ignored which edge ran, or that passed only one
argument list, cannot satisfy both this and the previous example. -/
example : (run 4 (diamond 2 1) == some (.int 20)) = true := by native_decide

/-- A branch on an integer register is refused: `brif` reads a boolean. -/
def intBranch : Func :=
  ⟨[⟨0, [], [.iconst 0 1, .iconst 1 2], .brif 0 1 [] 1 []⟩,
    ⟨1, [], [], .ret 1⟩],
   0⟩

example : (run 4 intBranch == none) = true := by native_decide

/-- An edge whose arity does not match the target's parameters is refused, so a
lowering cannot smuggle a value into a join it did not declare. -/
def arityMismatch : Func :=
  ⟨[⟨0, [], [.iconst 0 7], .jump 1 [0]⟩,
    ⟨1, [], [], .ret 0⟩],
   0⟩

example : (run 4 arityMismatch == none) = true := by native_decide

/-- The join parameter is the only way in: without the argument the block cannot
read the value it returns. -/
def missingArg : Func :=
  ⟨[⟨0, [], [.iconst 0 7], .jump 1 []⟩,
    ⟨1, [3], [], .ret 3⟩],
   0⟩

example : (run 4 missingArg == none) = true := by native_decide

end Cfg
end Morph.Clif
