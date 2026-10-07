# ADR-011: MIR Lowering, Ownership Checking, and Multi-Target Code Generation

## Status
**Proposed** (Loop 1 research annotation, 2026-09-19: stage 2's role is
**expressiveness**, not soundness. Oxide (PLDI 2019) shows borrow checking can
be a declarative relation, and RustBelt (POPL 2018) shows soundness rests on
*semantic typing* — which for Morph is `HasTypeS` + the store invariant, both
already formalized. A program the surface checker and stage 2 both reject is
rejected; a program stage 2 rejects was never guaranteed unsafe. This loop
alsoqueues ADR-014, which removes the surface-level consumption machinery that
stage 2 was assumed to complement.)

## Context

Morph's surface language has a fully verified type system (`HasType` over `LinCtx`), a store-carrying operational semantics (`Step : Store → Expr → Store → Expr → Prop`), and store-typed safety theorems (`HasTypeS`, `progressS`, `preservationS`, and the `safety_*` corollaries). All of this is formalized in Lean 4 at the **surface syntax** level with de Bruijn indices.

To produce an actual implementation we need a compilation pipeline. Three requirements constrain its shape:

1. **Verification must be compositional.** Every stage must have a *stated and proved* translation, so that `surface → executable` is a chain of theorems rather than a chain of bugs. This is the CompCert discipline, and it is the only approach consistent with our "maximum rigor before VM" principle.

2. **Ownership checking cannot be done on the surface language.** Phase 1c carried `Usage` through `HasType` but deliberately did *not* enforce it: consumption requires path-sensitive tracking (a variable consumed on one branch and not another is fine, but the surface syntax hides the control flow), and it requires the whole-program view that only a lowered CFG exposes. Doing this in `HasType` would force a context-threading judgment through every rule and every existing proof for no benefit — the check belongs where the CFG is explicit.

3. **The IR must be target-independent.** We target both LLVM (via `llvm-ir` or a direct C ABI shim) and Cranelift. A MIR that bakes in SSA registers, machine types, or instruction selection cannot be proved correct once and compiled twice.

## Decision

### 1. A target-independent MIR with an explicit CFG

MIR is a control-flow graph of basic blocks over an SSA value graph. It is *not* machine code: no registers, no instruction encoding, no calling convention. Values are indexed by integer IDs scoped to a function.

```lean
structure Func where
  name     : String
  params   : List (ValId × Typ)
  blocks   : List Block
  entry    : BlockId
  retType  : Typ

structure Block where
  id       : BlockId
  instrs   : List Instr
  terminator : Terminator
```

The instruction set is deliberately minimal and machine-independent:

```lean
inductive Instr where
  | const    (dst : ValId) (v : Value)
  | copy    (dst : ValId) (src : ValId)
  | binop   (dst : ValId) (op : BinOp) (l r : ValId) (τ : Typ)
  | load    (dst : ValId) (loc : ValId) (cap : Capability)
  | store   (loc : ValId) (src : ValId) (cap : Capability)
  | alloc   (dst : ValId) (cap : Capability) (τ : Typ)
  | free    (loc : ValId)
  | call    (dst : Option ValId) (fn : FnId) (args : List ValId)
  | phi     (dst : ValId) (pred : BlockId) (src : ValId)   -- resolved during verification
```

Terminators are `goto`, `branch`, `return`, and `switch`. Branches carry explicit *capability transitions* (`iso → val`, `iso → ref`, `ref → iso`) as the only way a capability is weakened — a type-level operation with a syntactic cost, so it cannot be applied silently.

### 2. Ownership checking lives in MIR, not in `HasType`

Because MIR is an explicit CFG, ownership becomes a dataflow problem with a standard solution: a lattice-typed analysis whose transfer functions are per-instruction and whose fixpoint is computed over the block graph.

```lean
inductive Place      -- a path of field/index projections from an SSA value
inductive Loan       -- an active borrow: place + capability + region
inductive Liveness   -- definitely-live, maybe-live, dead
```

The borrow checker is a *liquid* analysis over this lattice. Its soundness story is deliberately split in two:

- **The analysis itself is proven correct** with respect to an abstract semantics: `Soundness : ∀ f, Analysis f = Result f → …` — the fixpoint it computes agrees with the least solution.
- **The result is proven sufficient** to discharge double-free and use-after-free, by exhibiting a *serialization order* of the accesses (a topological order of the loan graph) — the standard confluence argument from borrow checking.

This gives us the property the roadmap calls for, with an explicit theorem:

```lean
theorem serialization_exists (f : Func) (a : Analysis f)
    (h : a.Sound → …) : ∃ order : List Loan, Perm order (Loans f) ∧ Order.agrees order a
```

### 3. A four-stage pipeline, each stage a theorem

| Stage | From → To | Theorem to prove | Status |
|---|---|---|---|
| 1. Lambda lifting | `Expr` (de Bruijn) → MIR with closures | `lowering_correct` | not started |
| 2. Ownership check | MIR → MIR, with a certification | `analysis_sound` | not started |
| 3. SSA + layout | MIR → SSA form, no virtual registers | `ssa_correct` | not started |
| 4. Backend | SSA → LLVM IR / Cranelift IR | `codegen_correct` | not started |

The end-to-end guarantee is a composition:

```lean
theorem end_to_end (e : Expr) (τ : Typ)
    (ht : HasType [] [] e τ) (hs : HasTypeS [] [] [] e τ) :
    ∃ bin : Binary, Binary.eval bin = Eval e
```

Note what this does **not** claim: it claims the *behaviour* is preserved. It does not claim the compiler is free of undefined behaviour unless the ownership certificate is produced — a program that fails stage 2 has no certificate and therefore no `end_to_end` witness. This is how Rust discharges its guarantees too, and it means the compiler is allowed to reject programs while remaining semantically faithful for the ones it accepts.

### 4. What "verified" means at the backend boundary

Stage 4 is where we stop proving and start trusting. The boundary is drawn at the **instruction-selection** step: we prove that stages 1–3 preserve behaviour, and we prove a *reconstruction* theorem showing that any target backend that implements the documented lowering rules for our instruction set is correct. Both LLVM and Cranelift backends are then thin encoders whose conformance to those rules is checkable by review and by differential testing against the interpreter in `Morph/Executable.lean`.

We do **not** attempt to verify LLVM's register allocator. This is the standard CompCert TLS/Clight boundary and we adopt it deliberately: verifying a register allocator is a research project, whereas verifying our own IR is a bounded, feasible formalization.

## Consequences

### Positive

- Path-sensitive ownership checking becomes tractable: the CFG makes control flow explicit, so `Usage.merge` in `LinCtx` becomes a genuine lattice meet rather than an approximation over syntax.
- The surface type system stays as it is. Phase 1c-β (context threading and consumption in `HasType`) is **deferred**, not abandoned: it becomes the justification for stage 2's transfer functions.
- One verified front end, two backends. The LLVM and Cranelift backends share stages 1–3.
- The interpreter remains the oracle, so differential testing has a formal anchor.

### Negative

- Closures require a heap representation of environments, which interacts with the store model. We will need a decision on whether closures are store-allocated (and therefore subject to the capability system) or stack-allocated. **This is the largest open question in this ADR.**
- `Usage.merge` in `LinCtx` was designed for syntax-level branching and its `zero + one = zero` rule is wrong for path-sensitive checking. We will need a *second* merge operator for the CFG analysis and should expect to revise or supersede `LinCtx.merge`.
- The liquid-analysis soundness proof is the single largest formalization effort in the plan. It is the critical path.

### Follow-up

- ADR-012: closure representation (store-allocated vs stack-allocated) — blocking for stage 1.
- ADR-013: the CFG merge operator and its relationship to `LinCtx.merge`.
- Re-examine whether `HasType` should keep carrying `Usage` at all, or whether it should be reverted to `List Typ` with all usage information introduced by stage 2.

## References

- CompCert: Leroy, "The CompCert C verified compiler: a retrospective" (POPL 2012) — the four-stage discipline and the trusted-backend boundary.
- Rust's borrow checker: Niko Matsakis et al., "Polonius" (blog posts, 2019) — the region/invalidated-loan formulation we adapt for MIR.
- WebAssembly: "Validation of WebAssembly" (HAKMEM) — a smaller, cleaner example of the same certification discipline.
- ADR-010 for the store model and capability semantics this pipeline must preserve.
