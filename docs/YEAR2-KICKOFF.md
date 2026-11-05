# Year-2 kickoff — entry-gated, design-only (loop 132)

> This started as Year-2 **preparation** under the Year-1 freeze (no
> Era-2 implementation until the audit publishes). **Update loop 133:**
> per maintainer directive the freeze is lifted — Era-1 gates (0.1 tag,
> live CI, audit) remain open but no longer block Era-2 implementation.
> See `docs/ERA2-UNFREEZE.md` for the unfreeze record. The queue in §3
> below is now the build order, not a blocked list.

## 1. Entry-gate verdict: Year 2 is open for implementation (loop 133 unfreeze)

| Era-1 exit requirement | Status | Gate |
|---|---|---|
| External audit published, findings triaged | Not started; invites unsent | G-3 |
| Morph 0.1 tagged and announced | Prepared, not cut | G-7 |
| CI per push + Pages live | Configs correct; runners blocked | G-1/G-2 |

**Consequence (updated loop 134):** Era-1 gates above remain open and
still block the 0.1 release and audit, but per `docs/ERA2-UNFREEZE.md`
they no longer block Era-2 implementation. The queue in §3 is the
build order: HIR→MIR extension, MIR operational semantics, backend
lowering, `morph build`, Rust AST→MIR growth, and differential-testing
proceed in parallel with the maintainer-only gate track.

## 2. Allowed now

- Audit-facing design clarification building on `docs/STAGEA-PREP-125.md`.
- Backend ADR outline and TCB questions.
- Exact theorem-shape statements for `compile_correct`.
- Toolchain/maintenance duty: keep `lake build` green.
- Documentation that prevents future confusion.

## 3. Year-2 build order (unfrozen loop 133 — implement in order)

1. **Stage A1:** store- and call-aware MIR small-step semantics.
2. **Stage A2:** `compile_correct` for the first-order fragment.
3. **Backend ADR:** LLVM vs Cranelift on proof-interface simplicity, with
   explicit TCB and verified-lowering vs translation-validation decision.
4. **Stage B:** single-backend straight-line lowering and flagged
   `morph build`, golden-tested.
5. **Rust pipeline growth:** AST→MIR mapping replacing parse/typecheck-only
   behavior, with Lean-vs-Rust differential testing advisory at first.

## 4. Audit dependencies

Year-2 implementation needs the audit's response to:

- Strict-subset `morph build` contract vs agreement-proof characterization.
- Verified lowering vs translation validation.
- Whether the MIR small-step theorem shape in Stage A is reviewable as stated.

Defaults on silence remain D-2 and D-4 as recorded in
`docs/STAGEA-PREP-125.md`.
