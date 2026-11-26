# Era 2 backend — scoping (loop 97)

Started at maintainer direction with the roadmap's Era-1 exit gate still
open (external audit unpublished). **Update loop 133:** the Year-1 freeze
is lifted per maintainer directive (`docs/ERA2-UNFREEZE.md`) — Era-1 gates
stay open but no longer block implementation. This document remains the
scope the audit reacts to, and is now also the Stage A–D build order.

## Where the pipeline stands (grounded)

- Surface → HIR: `Morph/Frontend/HIRLower.lean` (first-order fragment,
  agreement proved in `Morph/Frontend/HIRInterp.lean`).
- Surface arithmetic → MIR: `Morph/Lowering.lean` (ADR-011 stage 1:
  `+`/`-`/`*`, `let` into a single-block MIR function; `execMain` runs it).
- MIR itself: `Morph/MIR.lean` (SSA/CFG data types, computable
  well-formedness, pure-instruction eval oracle, single-block use check).
- Design of record: `.specs/02_adrs/ADR-011-mir-lowering-and-borrow-check.md`.

## The gap to a verified compiler

1. **Full-fragment lowering.** Stage 1 covers pure arithmetic only. Needed:
   comparisons, division, control flow (`whileLoop`, `match`), calls —
   first HIR→MIR (the agreement theorem composes), then cross-block SSA
   (phi/dominance, ADR-011 stage 3).
2. **`compile_correct`.** One composed preservation theorem
   AST→HIR→MIR, not three folklore claims. Depends on (1) plus an MIR
   operational semantics the current oracle does not yet give
   (store- and call-aware evaluation).
3. **Backend choice ADR.** LLVM vs Cranelift, decided on
   proof-interface simplicity, not hype. The ADR must state the trusted
   computing base each backend adds (assembler, linker, runtime) and how
   `compile_correct` connects to emitted code (validation by translation
   validation vs. verified lowering — pick one per backend).
4. **ABI/layout lemmas go load-bearing.** `AbiAlignmentAlgebra` and
   `AbiDataRefinement` become code-generation correctness lemmas. Note:
   `SPEC_CONTRADICTIONS.md` #11 is **resolved** (loop 111): the validated
   conditional forms (`spec_type_refinement_holds`,
   `spec_data_validation_holds`, `spec_layout_compatibility_holds`) are the
   lowering basis.
5. **Commands.** `morph build` (binaries for the first-order fragment),
   `morph test` (golden + property suites). Both are thin IO over Driver
   functions, golden-tested like the existing eight commands.
6. **Memory/concurrency/security against the executable evaluator.**
   Channel safety, deadlock-freedom, taint noninterference, OCap — proven
   against `Morph.Executable`/`execMain`, with executable counterexamples
   for rejected programs.

## Staging (build order since loop-133 unfreeze; also the scope the audit reacts to)

- Stage A: HIR→MIR for the loop-88 first-order fragment (no control flow
  beyond `whileLoop`), MIR small-step semantics, `compile_correct` for
  that fragment.
- Stage B: backend ADR + single-backend lowering for straight-line code,
  `morph build` behind a flag. — ADR **done** (ADR-032, loop 134: Cranelift,
  verified lowering, D-2/D-4 confirmed); scope **written** (loop 144,
  `docs/STAGEB-SCOPE.md`); implementation **done** (loops 146–153, items B1–B9):
  proved MIR→CLIF for straight-line code, `morph build --codegen=cranelift`,
  and a 9/9 native differential under the trusted half. The ADR's "Rust emits
  CLIF" consequence is amended there to "Lean renders CLIF, Cranelift parses it"
  because the Rust `MorphIR` is a stack machine, not a transcription of Lean's
  SSA MIR. Audit packet refreshed (loop 154).
- Stage C: calls/control flow, `morph test`, ABI lemmas load-bearing. — scope
  **written** (loop 155, revised loop 159, `docs/STAGEC-SCOPE.md`): control flow
  needed phi-aware execution and a new fragment predicate (`BranchStmts`, beside
  `StraightStmts` rather than inside it), CLIF needs a block model *with block
  arguments* — a terminator with no arguments cannot carry the join's value —
  and `morph test` is an independent CLI item (C9). Items C1 (edge-aware
  executor), C2a (fragment predicate) and C2b (`if` lowering) are **done**
  (loops 156–158); the revision splits the target side into C4a (model, base
  case reproduces B4) and **C4b (multi-block MIR→CLIF correctness)**, which the
  loop-154 table was missing and which is the critical path for C5–C8.
- Stage D: concurrency/memory/security proofs, 1.0 standard freeze.

## Open questions for the audit (not decisions)

- Is translation validation acceptable for the backend, or must lowering
  itself be verified? (Drives the LLVM-vs-Cranelift ADR.)
- Does the HIR agreement proof's fragment characterization suffice as the
  compiler's supported-fragment contract, or should `morph build` take a
  stricter, explicitly listed subset?
