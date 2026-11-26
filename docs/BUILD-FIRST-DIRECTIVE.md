# Build-first directive (2026-11-26, maintainer)

> Maintainer directive at the S9/S10 boundary: **"let's not review it yet —
> let's build till we have a finished language, and I will get people to
> review it on first launch."** Recorded per the HARD-GATES discipline
> (recorded, never silently dropped). This supersedes the S10–S12 sequence
> in `docs/YEAR1-SPRINTS.md`.

## What this directive defers

- **G-3 (external audit):** invites are **not sent**. The send-ready draft
  (`docs/AUDIT-INVITE-SEND-READY.md`) stays in the tree and is re-pinned at
  first launch — against the launched language, not the f24ee31 snapshot.
  The audit packet stays frozen at the pin until then.
- **S10–S11 (review window):** dropped — there are no reviewers to react to.
  Findings-triage discipline returns at first launch.
- **S12 (0.1.0 tag):** re-gated. The tag now waits for the finished-language
  milestone below, not for the audit. G-3 stays open and rides to first
  launch as the "review at launch" plan.

## What this directive prioritizes: the finished language

Build order, each item end-to-end (proved side + driver side + runner side):

1. **Multi-function artifacts with calls.** `morph build` already emits
   call-bearing CLIF for the D-7 typed-slice fragment; `morph-clif` compiles
   only single-function `morph_main` modules today. Grow the driver to
   multi-function modules with cross-function calls, and grow the runner
   ABI past `i64`/`i8` (strings, pointers, units — the marshal table's
   remaining rows).
2. **Real I/O in the runner.** A language whose only observable is a
   returned integer is not finished: printing from Morph source (runtime
   `io.rs` on the Rust side, a `print` intrinsic + runner plumbing on the
   pipeline side).
3. **Standard library core** (G-5): collections, string operations, the
   minimal IO surface — the first thing a first-launch reviewer will use.
4. **Actors** (D3–D6, ADR-033 defaults): `stepActor` real evaluation, the
   `ActorStmts` fragment, mailbox/mailbox-boundedness per
   `docs/STAGE-D3-INVARIANT-MEMO.md` (default A on silence).
5. **1.0 freeze list** (D6): the scope freeze and conformance harness, from
   which the standard is written.

## What stays true

- Zero `sorry`, zero stubs; proof scope is never cut to meet a milestone
  (five-year roadmap principle 1).
- D-4: `morph build` stays a strict, explicitly-listed subset with golden
  rejections (`tests/codegen/check.sh` 22/22).
- One-directional claims only: `compile_correct`-family theorems prove
  success-implies-agreement; the CLIF→bytes boundary stays in Cranelift's
  TCB (ADR-032 §3).
- The differential corpus (`native.sh`) must stay at 14/14 — every new
  driver capability lands with a corpus case.
