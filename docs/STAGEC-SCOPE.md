# Stage C scope — control flow, calls, and `morph test`

Status: design record, loop 154 (2026-11-08); **revised loop 159** after C1–C2b
landed and the CLIF block model was re-read against Cranelift's actual surface.
C1–C2b are in the tree; C2c and C3–C9 are not. Follows `docs/STAGEB-SCOPE.md`
(closed, B1–B9) and the staging in `docs/ERA2-BACKEND-SCOPE.md`. Governed by
ADR-032 (Cranelift, verified lowering) and D-4 (`docs/STAGEA-PREP-125.md` §1,
confirmed as a decision in ADR-032 §Status). Moves no gates: G-1, G-3, G-7
stay open per `HARD_GATES.md`.

## 0. What Stage C inherits

Stage B closed at `clif_correct_program` (`Morph/ClifCorrect.lean:72`), whose
hypothesis is `StraightStmts 256 prog.stmts` and whose conclusion is a
conjunction over a **single-block** MIR function. So the proved chain today is

```
HIR run  →  MIR run (one block, straight-line)  →  CLIF run (one block)
proved:    compile_total                        proved:    clif_correct_program
CLIF text → machine code                        evidence:  tests/codegen/native.sh
```

Stage C's job is the same three arrows, for programs that **branch** and (later)
**call**. Two things Stage C must not do:

- **Not rewrite B4.** `ClifSimulate`'s trace theorem is stated over
  `List Instr` and stays true for its fragment. A multi-block statement is
  added *beside* it, and the single-block theorem is the base case Stage C's
  new statement must reproduce when the CFG has one block.
- **Not claim the reverse.** Every Stage C theorem is "MIR produced `w` ⇒ CLIF
  produced `w`". A CLIF trap or a stall says nothing about MIR
  (`docs/ERA2-UNFREEZE.md`, the `compile_total` discipline).

## 1. Measured state (all four facts were read out of this tree)

### 1.1 HIR already has control-flow semantics; only the lowering is missing

`Morph/Interp.lean` defines `ifStmt` (`:101`), `whileLoop` (`:93`),
`doWhile`, `matchStmt` (`:108`), and `break`/`continue` as `Flow.broke` /
`.continued`. So the *oracle* for branching programs exists today; Stage C does
not have to invent HIR semantics, which is what makes the HIR→MIR side of this
stage a preservation proof rather than a design.

### 1.2 The fragment predicate, not the lowering function, is the gate

`Morph/HIRToMIR.lean:334` rejects every control-flow statement
(`_ :: _ => none`), and `lowerProgram` (`:345`) emits exactly one block. But the
stronger fact is in `Morph/HIRToMIRCore.lean:1584`: `StraightStmts` has
constructors only for `exprStmt`, `varDecl`, `assign`, `returnStmt`, `nop`.
Since `compile_total` takes `StraightStmts` as its hypothesis, **adding `if` to
`lowerStmts` alone would change nothing**: the program would lower, and no
theorem would apply to it. Stage C therefore has to extend the *predicate
algebra* and its projections (`StraightStmts_exprStmt`, …) in lockstep with the
lowering — the two are the contract and the implementation of the same thing.

### 1.3 MIR can express branching but cannot execute a merge

`execBlockFuel` (`Morph/MIR.lean:541`) already follows `goto` and `branch`;
`switch` is `none` (`:569`). The blocker is the merge:

- `Instr.phi` is `none` in both `evalInstr` (`:451`) and `evalInstrFull`
  (`:530`), and `execInstrsFull` walks a block's instructions without knowing
  which edge was taken.
- `phi dst pred src` already *carries* the predecessor (`Morph/MIR.lean:116`),
  so no new data is needed — what is missing is that the executor has to be
  told the incoming block. That is one parameter, `prev : Option BlockId`, and
  `phi` executes only when `prev = some pred`.

Any `if` lowering needs a merge block (the branch's value flows out), so
**edge-aware (phi-aware) execution precedes all Stage C lowering**. This is the
single largest finding of this note: the first Stage C work item is semantics,
not codegen, and no `if` program is executable until it lands.

### 1.4 The CLIF model has no blocks at all

`Morph.Clif.Func` (`Morph/ClifTarget.lean:110`) is `instrs` + `retSrc`; `run`
(`:214`) is one pass; `emitFunc` (`Morph/ClifEmit.lean:98`) rejects any
`blocks` list that is not the single entry block.

CLIF's real surface for control flow is `block0(v0: i64):`,
`brif v0, block1, block2`, `jump block1`, and the printer already emits a block
header — so the text layer is closer to ready than the model. What is missing on
the target side is: a block list, a terminator inductive
(`return`/`jump`/`brif`), and a fuel-indexed interpreter over blocks.

**Correction (loop 159): blocks must carry parameters, and terminators must
carry arguments.** The first sketch of the model (loop 154) had
`jump (target : BlockId)` / `brif (cond) (tt ff : BlockId)` with no `Block`
parameter list. That cannot express a merge. The stage's whole reason for
needing a merge block is that the `if`'s value has to reach the join; a
terminator with no arguments has nowhere to put it. CLIF's actual mechanism is
the block argument — `jump block3(v1)` into `block3(v1: i64):`, and
`brif v0, block1(v1), block2(v2)` with per-edge argument lists — and
Cranelift's verifier requires that SSA shape. So a slot-reading model
(registers global across blocks) would be easier to prove and would no longer
describe the text we emit, which is the one thing a CLIF-side theorem is for.
Consequence for C4b: the central lemma is **phi ↔ block argument** — MIR's
`phi dst pred src` at a join is `jump join(src)` plus `join(dst: i64):` in the
target, and the phi is executed by the join's parameter binding, not by an
instruction. This is also what makes the one-armed `if` row in §3 expressible:
per-edge arguments on `brif` are how the untaken arm passes the pre-branch
value.

### 1.5 Fuel is not free

`compile_total` concludes `execFunc 2 func` — fuel 2 is exactly what a
single-block function with `goto`-chained entry needs. A branching program needs
fuel proportional to the number of blocks actually traversed, and a loop needs
proportional to iterations. Stage C's theorems therefore quantify over a fuel
that is *computed from the HIR run's own fuel* (the oracle is fuel-indexed
already, `runStmts`/`runWhile`), e.g. `execFunc (2 * fuelH + 3) func`. The
constant has to be derived once and then reused; guessing it per-theorem is how
these proofs rot.

### 1.6 The corpus has no branches

`tests/codegen/manifest.tsv` is 9 straight-line programs. Nothing in the native
differential would notice a branch lowering bug today, so C6 is not optional
polish — it is the only evidence the new path will have.

## 2. The three prerequisites, in dependency order

1. **Edge environments** (§1.3). — **landed, loop 156**: `execInstrsFullFrom`,
   `execBlockFrom`, `execFuncFrom` in `Morph/MIR.lean`. `phi` reads `src` when
   `prev = some pred` and is skipped otherwise; `switch` stays rejected until it
   has a spec. `execInstrsFull`/`execBlockFuel`/`execFunc` are byte-for-byte
   unchanged, so the compatibility lemma this item originally called for turned
   out to be unnecessary: nothing already proved was touched. `execFuncFrom`
   dispatches the entry block directly instead of through a synthetic
   `goto`-block, so a straight-line function costs one unit of fuel here rather
   than two.
2. **Fragment algebra** (§1.2). — **landed, loops 157/158**, with one
departure from the loop-154 plan: `StraightStmts` was *not* extended. It is
`compile_total`'s hypothesis, so adding `ifStmt` to it would leave
`compile_total` with an unproved constructor until C3 and a red tree in the
interim. Instead `Morph/HIRToMIRBranch.lean` adds `BranchStmts`/`BranchStep`
*beside* it, with `straightStmts_to_branch` embedding the proved fragment and
`ArmStmts` carving out the arms the lowering handles. The contract and its
implementation still move in lockstep; they just have two names instead of
one. `StraightStmts` and every projection over it are untouched.
3. **Fuel derivation** (§1.5, §4.4). A bound lemma over `BranchStmts` —
"a program with `k` statement-level steps executes within `blockBound k`
blocks" — proved once against the executor, so C3 and C7 cite it instead of
redoing arithmetic.

## 3. The Stage C subset (the D-4 contract for control flow)

| HIR statement / MIR construct | Stage C | Reason |
| --- | --- | --- |
| `ifStmt c th el` with straight-line arms | **IN (C2/C3)** | two arm blocks + join, value merged by `phi`; `ArmStmts` refuses binding arms (`varDecl`/`assign`) until C2c |
| `ifStmt` with `return` in an arm | **IN** if both arms either return or fall through to the merge | the oracle replaces the accumulator per branch (`Flow.replace`, `Morph/Interp.lean:60`) |
| `ifStmt` with only one arm taken into the merge | **IN** — untaken arm's phi operand is the pre-branch value | needs a *second* phi, on the condition's block edge |
| `whileLoop c body` | **IN (C7)** | needs back edges + a loop-carried register: phi on the header, and fuel in the theorem |
| `break`/`continue` | **IN (C7)** with `whileLoop` | `Flow.broke`/`.continued` map to `jump` to the loop's exit/header |
| `doWhile` | **IN (C7)** | same as `whileLoop`, one fewer edge |
| `matchStmt` with literal/constructor patterns | **reject** | needs the pattern compiler; the one place a jump table (`switch`) would be justified, and so the last thing to enter |
| `switch` (MIR terminator) | **reject** | no oracle at MIR level; `matchStmt` will lower to branches first |
| `Instr.call` | **IN (C8)**, after control flow | `evalInstrFull` has no program (§1.3); CLIF `call` needs ABI/layout lemmas |
| `allocClosure`/`callClosure` | **reject** | ADR-012 runtime, Stage D |
| `load`/`store`/`alloc`/`free` | **reject** | still the store (Stage D's memory model), unchanged from Stage B |
| recursion / mutual recursion | **reject** | a call graph cycle needs a termination argument the theorem cannot supply from fuel alone |

The `if` row above is why C2 is "if without loops": it is the smallest
construct that exercises every new piece (two blocks, an edge parameter, a phi,
a merge) without needing bound-dependent fuel.

## 4. Target theorem statements (design, not implemented)

### 4.1 Edge-aware MIR execution

Landed at C1, with the signature it was specified against:

```lean
def execInstrsFullFrom (prev : Option BlockId) (fenv : FullEnv) : List Instr → Option FullEnv
def execBlockFrom (fuel : Nat) (f : Func) (prev : Option BlockId) (b : Block) (fenv : FullEnv) : Option Value
def execFuncFrom (fuel : Nat) (f : Func) (fenv : FullEnv) : Option Value
```

with `execFuncFrom_eq` as the derivation from the block-level definition. (The
loop-154 plan expected a `execBlockFuel = execBlockFrom … none …` bridge; C1
landed a separate `execFuncFrom` instead, so `execFuncFuel`/`execFunc` stay
byte-for-byte unchanged and no compatibility lemma is needed.)

```lean
theorem execBlockFrom_phi (prev pred src dst fenv …) :
    prev = some pred → execBlockFrom … (block with phi dst pred src :: rest) …
      = execBlockFrom … (block with rest) (fenv with dst := fenv.env src)
```

### 4.2 MIR preservation for `if`

Stated against the C2b lowering (`lowerStmtsCFG`, whose continuation is the
remaining list) rather than against the straight-line `lowerStmts`:

```lean
theorem lowerStmtsCFG_if_correct
    (h : lowerStmtsCFG ρ supply cont arm (.ifStmt c th el :: rest) = some (blocks, next))
    (hbs : BranchStmts budget (.ifStmt c th el :: rest))
    (hrun : runStmts fuelH env (.ifStmt c th el :: rest) acc = (out, env'))
    (hval : runValue? out = some (.lit w)) :
    execFuncFrom (blockBound (.ifStmt c th el :: rest) + 1) func ⟨envOf ρ, store⟩ = some w
```

The exact argument list is C3's to fix; what is fixed here is the shape: fuel
comes from `blockBound` (§4.4), and the *program* is not mentioned — the
theorem is about the executor and the lowerer, and `compile_total` for the
branching fragment is the corollary that composes them. Keeping that split is
what let Stage A/B stay one-directional.

### 4.3 CLIF blocks

```lean
inductive Term : Type
  | ret (src : Reg)
  | jump (target : BlockId) (args : List Reg)
  | brif (cond : Reg) (tt : BlockId) (ttArgs : List Reg)
      (ff : BlockId) (ffArgs : List Reg)

structure Block where
  id     : BlockId
  params : List Reg            -- bound on entry, in order
  instrs : List Instr
  term   : Term

structure Func where
  blocks : List Block          -- ordered, entry first
  entry  : BlockId

theorem clif_block_correct (h : ClifStepRel …) : Clif.run fuel f = some w
```

The single-block `run` of Stage B becomes the one-block case (`blocks = [b]`,
`params = []`, `term = .ret`), and the trace theorem is restated as
`ClifStepRel` (a small-step relation, so a loop's unbounded iterations need no
fuel argument in the *statement*, only in the soundness lemma that any
`ClifStepRel` run is realized by `run fuel`). `retSrc` disappears from the
structure because `.ret` now carries its register: the single-block shape is a
special case, not a field kept for it.

**Why params, not a flat register file** (§1.4): the model must describe the
text that `emitFunc` renders and `cranelift-reader` accepts. A model whose
blocks share one mutable register environment would prove something true about
a machine we do not emit. The cost is C4b's phi↔argument lemma; the benefit is
that the CLIF-side theorem is a statement about the artifact.

### 4.4 Fuel, stated once

`2 * fuelH + 3` (§4.2) is right for `if` — entry, one arm, join, so three
blocks traversed per oracle step — and wrong for `while`, which traverses a
block per iteration. Rather than repair the constant at C7, C3 states the bound
through a computable function:

```lean
def blockBound : List Stmt → Nat   -- structural, ≤ 3 per step, recomputed per arm
theorem execFuncFrom_bounded : blocks traversed ≤ blockBound stmts
```

C3's main theorem then cites `blockBound` and instantiates it, and C7 adds one
constructor to `blockBound` instead of restating every fuel arithmetic in the
stage. This is the §2 prerequisite 3 work, done as part of C3 rather than
before it.

## 5. Work items

| # | Item | Kind | Depends on |
| --- | --- | --- | --- |
| C1 | Edge-aware executor: `execInstrsFullFrom`, `execBlockFrom`, `execFuncFrom`, phi hit/miss lemmas, diamond tests | pure Lean, no corpus change — **done, loop 156** | — |
| C2a | Fragment predicate: `BranchStmts`/`BranchStep` (`Morph/HIRToMIRBranch.lean`), superset embedding from `StraightStmts`, boundary examples | pure Lean — **done, loop 157** | C1 |
| C2b | `lowerStmtsCFG`/`lowerProgramCFG`: arm blocks + join, value phi per edge, `ArmStmts` refusal of binding arms | pure Lean — **done, loop 158** | C2a |
| C2c | Binding merges: `varDecl`/`assign` inside arms, one phi per merged binding at the join | pure Lean | C2b |
| C3 | `lowerStmts_if_correct` (§4.2), `blockBound` + its bound lemma (§4.4), and the `if` case of the preservation bridge | pure Lean | C1, C2 |
| C4a | CLIF block model: `Term` with arguments, `Block` with params, block list, `ClifStepRel`, `run` over blocks, single-block base case reproved through the new surface | pure Lean | — (parallel with C1–C3) |
| C4b | **Multi-block MIR→CLIF correctness** — the Stage C counterpart of B4: a block-level MIR trace plus the encoder yields a `Clif.run` that returns the same value; contains the phi↔block-argument lemma | pure Lean | C4a |
| C5 | Multi-block `emitFunc` + `lowerProgram` extended to CFGs; golden artifacts for one `if` function | Lean + goldens | C2, C4a |
| C6 | Corpus: branch programs in `tests/codegen` (`if` with a value, `if` with a `return`, nested `if`), `native.sh` rows; refusal rows in `rejects.tsv` for binding arms and `matchStmt` | harness | C5, C4b |
| C7 | `whileLoop`/`break`/`continue`/`doWhile`: loop-carried phi, bound-dependent fuel, preservation | pure Lean | C3, C4b |
| C8 | `Instr.call`: program-in-executor semantics, single-function calls, ABI/layout lemmas, CLIF `call`/`sig` | Lean + ADR | C4b |
| C9 | `morph test`: run an in-source suite through `runHIRStmts` and report pass/fail per case; no new semantics | Lean CLI | — (independent) |

C9 is deliberately independent: `morph test` is a driver command over the
existing oracle, so it can ship while C1–C3 are still in progress, and it is
the piece pilots ask for first. It touches `Main.lean` + `Driver.lean` only,
in the same style as `check`/`run`.

### 5.1 C4b exists because the table was missing it (loop 159)

The loop-154 table had C4 (model), C5 (emitter), C6 (evidence) and no item
proving that a multi-block MIR function and its CLIF encoding return the same
value. Run as written, the branching path would be *proved* only as far as MIR
and *evidenced* from there, while the straight-line path is proved all the way
— a narrower proof for a wider fragment, which is the one trade the plan
forbids (`docs/FIVE-YEAR-ROADMAP.md` principle 1). C4b is the missing arrow;
C6's corpus is evidence for parse-and-run, not a substitute for it.

**Ordering.** C4a → C4b is the critical path: nothing on the target side
(`C5`, `C6`, `C7`, `C8`) can be finished without it, and C6 without C4b would
advertise a bridge the tree does not have. C3 is the long pole (its Stage A
counterpart `Morph/HIRToMIRCore.lean` is 2,175 lines) and is independent of
C4a, so the two run in parallel. C9 is the cheap pilot-facing win and is the
right thing to take when C3 stalls. C2c is **not** on C3's critical path
(`ArmStmts` is the hypothesis), so it waits behind C6; binding arms stay a loud
refusal, and C6 pins that refusal as a test row.

**Two hedges worth paying before C3's main theorem is stated:**

1. **A function parameter in the executor.** C8 needs `Instr.call`, which needs
   the executor to know other functions. If C3 proves `lowerStmts_if_correct`
   against a single-function executor, C8 restates and re-proves it. An inert
   program parameter on `execFuncFrom` (empty program for now) costs tens of
   lines and is the same move C1 validated: new definition beside the old, so
   nothing already proved moves.
2. **Fuel through `blockBound`, not a literal (§4.4).** Otherwise C7 repairs
   every fuel constant in the stage.

## 6. What Stage C will not claim

- Not that a program with a `while` terminates. The theorems are conditional on
  the oracle's run, exactly as Stage A's are; fuel exhaustion is `none` on both
  sides and nothing is claimed about it.
- Not `switch`/`matchStmt`, memory, closures, or recursion (§3).
- Not that the CLIF text for branches parses and executes — that stays
  evidence (C6), like B7/B8, until an ABI/parse argument exists. C4b relates
  MIR to the block *model*; the model-to-text step for branches is C5's encoder
  lemma plus C6's native rows, not a parse proof.
- Not that B4's trace theorem covers blocks. B4 stays a single-block theorem;
  the block statement is new, and its base case must reproduce B4.
- Not that the model is a grammar-faithful reading of CLIF. It is the smallest
  surface that (a) is what `emitFunc` renders and (b) carries block arguments,
  which is what makes the join expressible (§1.4).

## 7. Open questions for the audit (not decided here)

1. **Is a fuel-indexed preservation statement acceptable as a compiler
   theorem?** It says "if the oracle runs in `fuelH`, the machine runs in
   `2*fuelH+3`", which is weaker than "the machine runs whenever the oracle
   does" only in the sense that no total-correctness claim exists on either
   side. Alternative: a co-inductive `ClifStepRel` with a separate simulation
   proof, which is stronger but does not compose with `compile_total`'s
   existing shape.
2. **Should `phi` be a MIR instruction at all, or an edge parameter?** The
   current design keeps the instruction and derives the edge from `pred`. That
   makes malformed phis (duplicate predecessor, missing pred) a *well-formedness*
   obligation rather than an unrepresentable state. If verification is meant to
   reject them at the boundary, `WF` must grow the corresponding check, and that
   is a visible change to the language's contract.
3. **Does `morph test` belong to Stage C at all?** It is listed there in the
   roadmap, but it shares no machinery with codegen. Shipping it early (C9)
   makes the roadmap's "H1" look partly done while the hard items are open;
   the note recommends shipping it early and labelling it as such.
4. **Is a block-argument CLIF model the right level?** C4a adopts it because
   Cranelift requires SSA and because a slot model would not describe the
   emitted text (§1.4). The audit question is the reverse direction: should
   `phi` be *lowered away* at emission (Cranelift block args) with the model
   proving that lowering, or should the model keep `phi` as an instruction and
   treat block args as its rendering? The note takes the second (C4b's
   phi↔argument lemma), which keeps one semantics for MIR, at the price of a
   correspondence lemma that is not itself executable.
5. **What is the normative D-4 listing for control flow?** ADR-032 confirmed
   D-4 as a decision (strict, explicitly-listed subset) but the listing for
   Stage C lives in `BranchStmts`/`ArmStmts` and §3 here. If the audit wants a
   single document-level fragment table, this section is it — the Lean
   predicates are the machine-checked form.
