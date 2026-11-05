# Year-1 Stage-A design prep (loop 125, design-only)

> Historical note (loop 134): this was written under the Year-1 rule
> (**no Era-2 implementation until the audit publishes**). Per
> `docs/ERA2-UNFREEZE.md` that freeze is lifted — this note is now the
> design record the auditors react to *and* the basis Stage A builds on.
> Positions below (D-2 verified lowering, D-4 strict subset) are unchanged.
>
> Original header: this note moved no gates, added no code, and proposed
> no timeline. It answers the two open audit questions in
> `ERA2-BACKEND-SCOPE.md` with a conservative default per decision
> D-2/D-4, plus the MIR semantics gap that Stage A must close.

## 1. Supported-fragment contract (audit question 2)

**Position:** `morph build` takes a **strict, explicitly-listed subset**
(D-4 default). The HIR agreement proof's fragment characterization is
necessary but not sufficient as the user-facing contract, because it
describes what lowering *accepts*, not what codegen *guarantees*.

**Candidate contract (measured, not proposed):**

- IN (lowered 1:1 today): `IsStraight` per `Morph/HIRToMIR.lean` header —
  literals, variables, `unop`/`binop` over MIR-representable operators
  (`toBinOp`: `+ - * / % == != < <= > >= && || ! &` + surface-parity
  `.not`), `let`/`block`; statements `varDecl`/`assign`/`exprStmt`/
  `returnStmt`/`nop`. Surface `ifStmt`/`matchStmt` lower to HIR since
  loop 112 but are **rejected** by HIR→MIR (single-block MIR has no
  control flow) — so they are in the HIR fragment, out of the Stage-A
  build fragment.
- OUT (pinned rejections): `whileLoop`/`match`/calls (need multi-block
  CFGs + phi/dominance, Sprint 14); `doWhile`/`forLoop` (no faithful
  1:1 map — G-6, `toHIRStmt_doWhile_none`/`toHIR_forLoop_none`); `lam`/
  `app`, `break`/`continue` outside their loop.
- REJECTION SHAPE: `lowerExpr`/`lowerStmts` return `Option`; every `none`
  case has a golden (`Morph/Tests/HIRLower.lean`, `--hir` CLI path exits
  1 with the exact leaves-fragment message — verified loop 124).

**What the audit is asked:** is the strict-subset contract (list above)
the right `morph build` gate, or should the gate be the agreement
proof's characterization directly? Default on silence: strict subset.

## 2. Translation validation vs verified lowering (audit question 1)

**Position:** default **verified lowering** (D-2 conservative). Rationale:
the pipeline's existing correctness story is compositional preservation
(`agreeBoth` triple + `runHIRProgram_preservation`; Sprint 14 direction:
one-directional HIR-success-implies-MIR-agreement for the straight-line
fragment). Translation validation would replace that composition with a
per-program check whose checker becomes new trusted code with no proof
story in the tree today.

**TCB sketch the backend ADR must state (either backend):** assembler +
linker + runtime (`compiler/`/`runtime/`/`cli/` — 218 Rust tests green
but no codegen today, so the TCB addition is entirely future work).
Verified lowering keeps the TCB at the backend's own assembler/linker/
runtime; translation validation adds the validator itself.

**What the audit is asked:** is per-program translation validation
acceptable as the `compile_correct`-to-emitted-code connection, or must
lowering itself be verified? Default on silence: verified lowering.

## 3. MIR semantics gap (not a question, a work item for Stage A)

The current MIR oracle (`Morph/MIR.lean`: pure-instruction eval +
single-block use check) does not give Store- or call-aware evaluation.
Stage A needs a small-step MIR semantics before `compile_correct`
AST→HIR→MIR can be stated for even the straight-line fragment. This is
post-audit implementation work, listed here so the audit can confirm
the theorem statement shape it will be asked to review.
