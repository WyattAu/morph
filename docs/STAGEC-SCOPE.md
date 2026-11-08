# Stage C scope — control flow, calls, and `morph test`

Status: scoping note, loop 154 (2026-11-08). Design record only — no Stage C
code is in the tree. Follows `docs/STAGEB-SCOPE.md` (closed, B1–B9) and the
staging in `docs/ERA2-BACKEND-SCOPE.md`. Governed by ADR-032 (Cranelift,
verified lowering) and D-4 (`docs/STAGEA-PREP-125.md` §1). Moves no gates:
G-1, G-3, G-7 stay open per `HARD_GATES.md`.

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
`blocks` list that is not the single entry block. CLIF's real surface for
control flow is `block0(v0: i64):`, `brif v0, block1, block2`, `jump block1`,
and the printer already emits a block header — so the text layer is closer to
ready than the model. What is missing on the target side is: a block list, a
terminator inductive (`return`/`jump`/`brif`), and a fuel-indexed interpreter
over blocks.

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

1. **Edge environments** (§1.3). New `execBlockFuelFrom (prev)`; `phi` reads
   `src` when `prev = some pred` and is skipped otherwise; `switch` stays
   rejected until it has a spec. Affects: `Morph/MIR.lean`, `MIRExecLemmas`,
   and any theorem that unfolds `execFunc` (they keep working — entry `prev` is
   `none` and no straight-line function has phis).
2. **Fragment algebra** (§1.2). `StraightStmts` gains `ifStmt` (condition
   `IsStraight`, both arms recursive, budget threaded), and the projections and
   inversion lemmas that the preservation proof consumes.
3. **Fuel derivation** (§1.5). A lemma of the shape "a `StraightStmts`-shaped
   program with `k` statement-level steps executes within `2k + 2` blocks",
   proved once against the executor, so each later theorem cites it instead of
   redoing arithmetic.

## 3. The Stage C subset (the D-4 contract for control flow)

| HIR statement / MIR construct | Stage C | Reason |
| --- | --- | --- |
| `ifStmt c th el` with straight-line arms | **IN (C2/C3)** | two blocks + merge, value merged by `phi` |
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

```lean
def execBlockFrom (fuel : Nat) (f : Func) (prev : Option BlockId)
    (b : Block) (fenv : FullEnv) : Option Value
```

with `execBlockFuel fuel f b fenv = execBlockFrom fuel f none b fenv` as the
first lemma (so nothing already proved about `execBlockFuel` breaks), and

```lean
theorem execBlockFrom_phi (prev pred src dst fenv …) :
    prev = some pred → execBlockFrom … (block with phi dst pred src :: rest) …
      = execBlockFrom … (block with rest) (fenv with dst := fenv.env src)
```

### 4.2 MIR preservation for `if`

```lean
theorem lowerStmts_if_correct
    (h : lowerStmts ρ supply (.ifStmt c th el :: rest) = some (ρ', v, is, s))
    (hss : StraightStmts budget (.ifStmt c th el :: rest))
    (hrun : runStmts fuelH env (.ifStmt c th el :: rest) acc = (out, env'))
    (hval : runValue? out = some (.lit w)) :
    execFunc (2 * fuelH + 3) func ⟨envOf ρ, store⟩ = some w
```

Note the shape: same `2 * fuelH + c` form as §1.5, and the *program* is not
mentioned — the theorem is about the executor and the lowerer, and
`compile_total` for the extended fragment is the corollary that composes them.
Keeping that split is what let Stage A/B stay one-directional.

### 4.3 CLIF blocks

```lean
inductive Term : Type
  | ret (src : Reg) | jump (target : BlockId) | brif (cond : Reg) (tt ff : BlockId)

structure Func where
  blocks : List Block          -- ordered, entry first
  entry  : BlockId
  retSrc : Reg                 -- the register `ret` reads

theorem clif_branch_correct (h : ClifStepRel …) : Clif.run fuel f = some w
```

The single-block `run` of Stage B becomes the one-block case, and the trace
theorem is restated as `ClifStepRel` (a small-step relation, so a loop's
unbounded iterations need no fuel argument in the *statement*, only in the
soundness lemma that any `ClifStepRel` run is realized by `run fuel`).

## 5. Work items

| # | Item | Kind | Depends on |
| --- | --- | --- | --- |
| C1 | Edge-aware executor: `execBlockFrom`, `phi`, `execBlockFuel` compatibility lemma | pure Lean, no corpus change | — |
| C2 | `StraightStmts` + `lowerStmts` for `ifStmt`, incl. merge/phi construction and the two-arm projections | pure Lean | C1 |
| C3 | `lowerStmts_if_correct` (§4.2) and the `if` case of the preservation bridge | pure Lean | C1, C2 |
| C4 | CLIF block model: `Term`, block list, `ClifStepRel`, `run` over blocks, single-block base case reproved through the new surface | pure Lean | — (parallel with C1–C3) |
| C5 | Multi-block `emitFunc` + `lowerProgram` extended to CFGs; golden artifacts for one `if` function | Lean + goldens | C2, C4 |
| C6 | Corpus: branch programs in `tests/codegen` (`if` with a value, `if` with a `return`, nested `if`), `native.sh` rows | harness | C5 |
| C7 | `whileLoop`/`break`/`continue`/`doWhile`: loop-carried phi, bound-dependent fuel, preservation | pure Lean | C3, C4 |
| C8 | `Instr.call`: program-in-executor semantics, single-function calls, ABI/layout lemmas, CLIF `call`/`sig` | Lean + ADR | C4 |
| C9 | `morph test`: run an in-source suite through `runHIRStmts` and report pass/fail per case; no new semantics | Lean CLI | — (independent) |

C9 is deliberately independent: `morph test` is a driver command over the
existing oracle, so it can ship while C1–C3 are still in progress, and it is
the piece pilots ask for first. It touches `Main.lean` + `Driver.lean` only,
in the same style as `check`/`run`.

## 6. What Stage C will not claim

- Not that a program with a `while` terminates. The theorems are conditional on
  the oracle's run, exactly as Stage A's are; fuel exhaustion is `none` on both
  sides and nothing is claimed about it.
- Not `switch`/`matchStmt`, memory, closures, or recursion (§3).
- Not that the CLIF text for branches parses and executes — that stays
  evidence (C6), like B7/B8, until an ABI/parse argument exists.
- Not that B4's trace theorem covers blocks. B4 stays a single-block theorem;
  the block statement is new, and its base case must reproduce B4.

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
