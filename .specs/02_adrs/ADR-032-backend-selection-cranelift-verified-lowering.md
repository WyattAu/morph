# ADR-032: Backend Selection — Cranelift First, Verified Lowering Confirmed

## Status

**Accepted** (loop 134, 2026-11-04). Decides the backend question parked in
`docs/ERA2-BACKEND-SCOPE.md` §3 (loop 97) and `docs/YEAR2-KICKOFF.md` §3
item 3, under the loop-133 unfreeze (`docs/ERA2-UNFREEZE.md`). Two effects:

1. **Defaults D-2 and D-4 are confirmed as decisions** (they were recorded in
   `docs/STAGEA-PREP-125.md` as defaults-on-silence pending audit feedback).
2. **The first backend encoder is Cranelift**, with LLVM retained as the
   second backend under ADR-011's two-backend plan, not abandoned.

This ADR clears no gates: G-1 (billing), G-3 (external audit), G-7 (0.1
release) remain open per `HARD-GATES.md`. The audit questions in
`ERA2-BACKEND-SCOPE.md` stay open for reviewer feedback; the decision below
is the one implementation proceeds under, is one-directional (like
`agreeBoth`), and is revisable on audit findings.

## Context

Grounded pipeline state (loop 134):

- Surface → HIR: `Morph/Frontend/HIRLower.lean`, agreement proved in
  `Morph/Frontend/HIRInterp.lean`.
- Surface arithmetic → MIR: `Morph/Lowering.lean` (ADR-011 stage 1),
  `execMain` runs the single-block result.
- MIR: `Morph/MIR.lean` (SSA/CFG types, pure-instruction eval oracle);
  Stage A1 — store- and call-aware MIR small-step semantics — is in flight
  (`Morph/MIRExecLemmas.lean`, first work under the loop-133 unfreeze).
- Rust side: `compiler/` / `runtime/` / `cli/` — 218 tests green, no
  codegen yet. The TCB addition for any backend is therefore entirely
  future work, which is why deciding the proof interface now is cheap and
  deciding it later is expensive.

Two constraints are inherited, not new:

- **ADR-011's boundary (already decided).** Stages 1–3 (surface→HIR→MIR→
  our instruction set) are proved; the backend is a *thin encoder* over a
  documented instruction set, with a **reconstruction theorem** (any encoder
  implementing the documented lowering rules is correct), conformance
  checked by review and differential testing against the MIR oracle.
  Register allocation and instruction selection are *not* verified — the
  ADR-011 note ("verifying a register allocator is a research project,
  whereas verifying our own IR is a bounded, feasible formalization")
  stands.
- **STAGEA-PREP §2 (D-2 rationale).** The pipeline's correctness story is
  compositional preservation; a per-program translation validator would be
  new trusted code with no proof story in the tree, breaking ADR-011
  requirement 1 (verification must be compositional).

## Decision

### 1. Verified lowering — D-2 confirmed

`compile_correct` connects stages by *proved* translations only:

```
AST → HIR → MIR → our instruction set     (proved: preservation chain)
our instruction set → CLIF                (proved: verified lowering, Stage B)
CLIF → machine code                       (trusted: Cranelift)
```

Per-program translation validation is **rejected for Stage B**: the
validator itself is trusted code whose correctness has no proof story in
this repo, so the TV route adds exactly the kind of unverified middle
component the compositional discipline exists to avoid. TV is recorded as
the **fallback mechanism, not a removed option**: if a Stage-B fragment
instruction's encoder conformance cannot be established by review plus
differential testing against the MIR oracle, that construct ships behind
the strict-subset gate with a per-program validator for exactly that
construct, entered in the kill-criterion log — never silently.

### 2. First backend encoder — Cranelift

Decided on proof-interface simplicity, per the scope document's own
criterion. The four deciding facts:

1. **No marshalling layer at the verified/trusted boundary.** The compiler
   crates are Rust; Cranelift is a Rust library. `MIR → our instruction
   set` is a Lean function; its Rust transcription emits CLIF by in-process
   function calls. The LLVM route (`llvm-ir` text emission or a C++ FFI
   shim) puts an unverified serialisation/FFI surface exactly at the
   proved/trusted boundary — the one place the pipeline can least afford
   one.
2. **Smaller, legible trusted base.** Both Cranelift and LLVM are trusted
   code under the ADR-011 boundary, and neither is verified by us. Cranelift
   is roughly an order of magnitude smaller than LLVM and exists for exactly
   this role; LLVM brings optimization maturity and platform reach that
   Stage B does not need.
3. **A semantics to point at for the trusted stage.** Cranelift's ISLE-based
   instruction selection and its verification tooling give the CLIF→machine
   step a documented, machine-checked-adjacent semantics — the weakest
   acceptable form of "the trusted stage has a spec" for an audit that will
   ask what stands between CLIF and bytes.
4. **Deterministic in-process codegen** fits the `morph build` contract:
   thin IO over a pure pipeline, rejection and success both golden-tested.

Cranelift's x86-64 and aarch64 backends cover the Stage-B/C platform set.
LLVM's broader platform and optimization reach is recorded as a **revisit
criterion**: a Stage-C/D platform requirement Cranelift cannot meet reopens
this ADR for the LLVM encoder (which shares ADR-011 stages 1–3 unchanged).

### 3. The exact verification boundary (what this ADR claims and refuses to claim)

- **Proved (in Lean):** AST→HIR, HIR→MIR (composed: `compile_correct` for
  the Stage-A fragment, one-directional — HIR-lowering success implies MIR
  agreement), MIR small-step semantics (Stage A), MIR→instruction-set
  lowering rules with preservation, MIR→CLIF verified lowering.
- **Trusted (documented + tested, not proved):** the Rust transcription of
  the MIR→CLIF function (conformance to the Lean function by differential
  testing against a CLIF oracle evaluated against the MIR oracle),
  Cranelift's CLIF→machine code, any assembler/linker in the path, the
  runtime.
- **Not claimed:** end-to-end machine-code verification (the CakeML
  standard ADR-011 records as a team-size trade), absence of Cranelift
  miscompilation, or that the encoder is correct beyond the differential
  corpus. A proof failure upstream never implies anything about emitted
  code, and encoder divergence never implies a lowering-proof bug — the
  one-directional discipline `agreeBoth` established.

### 4. Unchanged dependencies and gates

- `morph build` keeps the **strict, explicitly-listed subset** contract
  (D-4 confirmed) from STAGEA-PREP §1; codegen rejection is golden-tested
  like the `--hir` path.
- `SPEC_CONTRADICTIONS.md` #11 (the ABI `Props` overstate) must be resolved
  before `AbiAlignmentAlgebra`/`AbiDataRefinement` go load-bearing (scope
  item 4). This ADR does not depend on those lemmas for the Stage-B
  boundary.
- Stage A (MIR small-step semantics) must land before `compile_correct`
  composes through MIR; the ADR stages behind it, as in
  `ERA2-BACKEND-SCOPE.md`'s build order.

## Consequences

- The Rust workspace gains a `codegen` boundary: `compiler` emits CLIF from
  MIR; `codegen` lowers CLIF via Cranelift. The differential bridge
  (MIR-oracle vs CLIF-oracle) is the Rust pipeline growth item's first
  consumer.
- The audit packet's TCB section gains, at its next refresh: the Cranelift
  dependency, the encoder crate, and the linker/runtime in the path.
- Kill criteria for this decision: (a) audit feedback rejecting D-2 — TV is
  reinstated per §1's fallback paragraph; (b) a Stage-B target platform
  Cranelift cannot emit for — the LLVM encoder is built under ADR-011's
  shared stages; (c) Cranelift maintenance risk materialises (upstream
  abandonment or a fork split incompatible with the CLIF semantics we
  target) — the decision reopens, and the verified MIR→instruction-set core
  survives any such reopening untouched.
- What would have made this ADR go the other way, recorded for honesty: an
  in-tree Lean proof about LLVM IR (none exists, and the text/FFI boundary
  would sit inside the proved chain), or a Stage-B requirement for LLVM-only
  optimization passes (none — the strict-subset contract does not promise
  optimization).
