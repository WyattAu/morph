# Loop 09 — 2026-09-19

Research loop. Primary deliverable: the stage-2 borrow-judgment design that
Loop 6 flagged as critical path, plus the Oxide fetch that had been owed.

## Sources consulted

### Oxide: The Essence of Rust — arXiv:1903.00982v4 (FETCHED, v4 dated 2021-10-19)

Full abstract confirmed at https://arxiv.org/abs/1903.00982v4.

Authors: Aaron Weiss, Olek Gierczak, Daniel Patterson, Amal Ahmed.
Categories: cs.PL. DOI: https://doi.org/10.48550/arXiv.1903.00982

Four claims extracted, all directly load-bearing for ADR-013:

1. **Lifetimes are an approximation of provenances.** Oxide takes "a new view
   of lifetimes as an approximation of the provenances of references." This is
   the key framing difference from ADR-010: our `Capability`/`StoreTyp`
   discipline is provenance-tracking, and lifetimes should be the *derived*
   approximation, not the ground truth. Loop 6 suspected this; v4 confirms it.
2. **Provenance is computed automatically by a substructural typing
   judgment.** "Our type system is able to automatically compute this
   information through a substructural typing judgment." This settles P3: the
   borrow checker belongs in the type system, not in an out-of-band dataflow
   pass. It also explains why the surface `HasType` need not carry loan
   information — the judgment is separate and consumes MIR.
3. **First syntactic progress/preservation proof for borrow checking.**
   "We provide the first syntactic proof of type safety for borrow checking
   using progress and preservation." This is exactly the architecture Morph
   already uses for `HasType`/`HasTypeS`, so the proof engineering transfers.
4. **Non-lexical lifetimes are included.** v4 folds NLL into the judgment
   rather than treating it as a refinement pass. Relevant because it means
   loan-kill (NLL liveness) is a *judgment rule*, not a fixpoint artifact —
   good news for our provability, since it removes the dataflow bottleneck.

### Pony paper — DEFERRED

Still owed (carried from Loop 2). Not on the critical path: the Pony-OS
memory model is only relevant when we reach region-polymorphic signatures
(`for<'a>`), which ADR-013 explicitly excludes from stage 2. Carried to
Loop 10; if it remains unfetched there it drops out of the program scope.

## Adjudications

### P3 (where borrow checking lives) — **RESOLVED**

Prior register entry asked: "Unexamined whether a declarative (non-CFG)
formulation exists that would let it live in the type system."

Answered by Oxide v4. The formulation exists, it is substructural, it
computes provenances automatically, and it has a syntactic progress/
preservation proof. **ADR-013 proposed**:
`.specs/02_adrs/ADR-013-oxide-shaped-borrow-judgment.md`

Shape: `Place` (base/deref paths), `Loan` (place + capability + de Bruijn
lifetime level), `Provenances` (set of live loans), and the `Borrows` judgment
with one rule per MIR instruction. `NoConflictingLoan` is the executable
predicate; proving it sound means the borrow checker is sound.

Target theorems:

- `borrow_progress` — every well-formed instruction can be checked
- `borrow_preservation` — checking preserves the borrow invariant

Critically, this keeps P3's original intent while respecting ADR-011: MIR is
still the implementation path, but the *correctness theorem* is a typing
judgment, not raw dataflow agreement.

### P4 (refinement typing base) — **PARTIALLY ANSWERED**

Loop 2 established: safety/well-formedness refinements (not safety refinements)
are semantically justified and technically feasible, with liquid types as the
prior art. Pony remains owed but is no longer blocking, because the
justification came from the semantic argument, not from the Pony implementation.

## Proof changes made this loop

None. Design-only loop. No Lean or Rust files touched.

## Carried to Loop 10

1. Owed fetch: Pony paper (region polymorphism — only needed post-stage-2).
2. `lowering_correct` proof — write-avoidance simp engineering (loop-07 notes).
3. Loop 10 is the **program retrospective**: closure review, register
   disposition, remaining-work handoff.
