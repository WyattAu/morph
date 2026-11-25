# Stage D scope — memory, concurrency, security, 1.0 freeze (SKETCH)

Status: **design sketch, 2026-11-25 — not decided, authorizes no proof work.**
Follows `docs/STAGEC-SCOPE.md` (closed: C1–C9 in tree except full CLIF `call`
codegen, which needs ABI/layout design) and the staging in
`docs/ERA2-BACKEND-SCOPE.md` (Stage D: "concurrency/memory/security proofs,
1.0 standard freeze"). Year-3 H2 target (`docs/FIVE-YEAR-ROADMAP.md`): channel
safety, deadlock-freedom, taint noninterference, OCap — proven against the
executable evaluator with executable counterexamples — plus package manager
v1 on the `ModuleSystem` hash-determinism proofs.

## 0. What Stage D inherits

Stage C closed the first-order pipeline: HIR run → MIR run → CLIF text, for
straight-line code, branches, and HIR→MIR calls, with `morph test` goldens.
None of that touches the heap, more than one actor, or any security property.
Stage D's job is the *rest* of the execution story: what the heap guarantees,
what concurrent actors guarantee each other, and what untrusted code cannot do.
Two things Stage D must not do:

- **Not rewrite A2/C.** The `compile_total` / `lowerCallProg_correct` /
  `lowerProgramCFG_correct` chain stays the fragment contract for single-actor,
  heap-free programs. Stage D adds properties *beside* it; a heap-free program
  must satisfy Stage D's invariants vacuously, not by re-proof.
- **Not claim the machine.** As in Stage C, every theorem is one-directional
  over the verified model. A Cranelift miscompile or runtime bug says nothing
  about the theorems (the `compile_total` discipline, `docs/ERA2-UNFREEZE.md`).

## 1. Measured state (read out of this tree, 2026-11-25)

### 1.1 The heap already has an executable model

`Morph/Memory.lean` defines blocks with `make`/`read`/`write`/`freeBlock`,
poison and `undef` bytes, and bounds checks (`inBounds`, `rangeInBounds`).
`Morph/Runtime.lean` adds `Heap` (`heapAlloc`/`heapFree`/`heapLookup`),
a `Stack`, and an `ActorSystem` with `spawn`/`send`/`recv`/`stepActor`.
These are definitions plus (at sketch time) un-inventoried lemmas — no
fragment predicate or preservation statement exists over them yet.

### 1.2 The borrow model already has shape lemmas

`Morph/Borrows.lean` defines loans, provenances, `NoConflictingLoan`,
`CaptureOK`, and `WFBorrow`/`WFBorrowApp`. This is the natural
no-aliasing core for a memory-safety statement, but nothing connects it to
`Memory.lean` blocks or to any evaluator yet.

### 1.3 The spec modules exist; the bridge does not

`Morph/Specs/` ships `MemoryModel`, `MemoryBounds`, `MemoryAffineLogic`,
`MemoryAcyclicity`, `ConcurrencyProcessAlgebra`, `LayeredConcurrency`,
`ActorDeadlock`, `SchedulerRandomizedStealing`, `SchedulingModes`,
`SecurityFlow`, `SecurityOCap` (among others). What is missing in every case
is the same thing Stage C had to build: the *bridge* from the spec statement
to the executable model (`Memory.lean`/`Runtime.lean`), i.e. agreed
`Rel`-style relations and fragment predicates. The specs are the requirements;
the relations are the work.

### 1.4 The 1.0 freeze list does not exist yet

D-5 (`docs/FIVE-YEAR-ROADMAP.md`) freezes scope for pilots. No freeze list,
no pilot criteria, and no conformance-suite harness exist in the tree.
`tests/codegen/corpus` (13 CLI goldens) is the closest ancestor.

## 2. Candidate items, in dependency order

- **D1 — Heap fragment + preservation.** A `HeapSafe` predicate over
  `Memory.lean` states (allocated ⇒ in-bounds, freed ⇒ unreadable, no
  use-after-free) preserved by `read`/`write`/`freeBlock`. Pure model work;
  no evaluator involved. Unblocks D2.
- **D2 — Borrow–heap agreement.** `WFBorrow` (from `Borrows.lean`) implies
  `HeapSafe` (or an explicit `RelBorrowHeap` relation). This is the
  Stage-C-style bridge: two independently sensible models, one agreement
  lemma. Unblocks D5.
- **D3 — Actor step safety.** `stepActor` preserves per-actor progress plus a
  global invariant (mailbox boundedness? crash containment? — open, see §7).
  Needs a fragment predicate (`ActorStmts`?) the way C2a needed
  `BranchStmts`. Independent of D1/D2; unblocks D4.
- **D4 — Deadlock-freedom / channel safety.** Over `ActorSystem`
  (`spawn`/`send`/`recv`): the `ActorDeadlock` + `ConcurrencyProcessAlgebra`
  specs bridged to `Runtime.lean`. Needs D3's step invariant. Executable
  counterexamples required by the roadmap (a stuck-system witness the
  evaluator can produce, mirroring the C8 refusal pins).
- **D5 — Taint noninterference + OCap.** `SecurityFlow`/`SecurityOCap`
  bridged to the evaluator with explicit attacker-observable equivalence.
  Needs D2 (no-aliasing is load-bearing for noninterference). Likely the
  hardest item; explicitly last.
- **D6 — 1.0 freeze.** D-5 list, pilot criteria, conformance harness grown
  out of `tests/codegen/corpus`. Process work, not proof work; needs
  maintainer sign-off, not lemmas.

## 3. The Stage D subset (D-4 contract sketch)

By analogy with Stage C §3: each item lands with (a) a fragment predicate
naming exactly what is covered, (b) the agreement/preservation statement over
it, and (c) a corpus or pin exhibiting the boundary (success case *and* a
refusal/divergence case, executable). No item may weaken an A2/C theorem or
widen a fragment predicate silently — predicates grow by new constructors
beside the old ones (`BranchStmts` precedent).

## 4. Target theorem shapes (design, not implemented)

```lean
-- D1 shape: heap operations preserve heap safety
theorem heapWrite_safe : HeapSafe h → writeBlock h id off v = some h' → HeapSafe h'

-- D2 shape: borrow well-formedness implies heap safety
theorem wfBorrow_heapSafe : WFBorrow π → heapOf π = some h → HeapSafe h

-- D4 shape (one direction only, Stage C discipline):
-- a well-formed actor system never gets stuck without a witness
theorem actors_progress :
  WFActors sys → stepActor sys turn heap stack = (.stuck, _) →
  ∃ witness, DeadlockWitness sys witness
```

Names and signatures are placeholders. The statements are recorded here so
reviewers can attack them before any proof begins.

## 5. Work items (scoping work — the proofs come later)

1. Inventory existing lemmas over `Memory.lean`/`Runtime.lean`/`Borrows.lean`
   (what is already proved vs assumed).
2. Draft the D1 fragment predicate and circulate for attack.
3. Decide the §7 questions (maintainer call — see below).
4. Only then: D1 proofs, following the Stage C pattern
   (relations → agreement → composition → pins).

## 6. What Stage D will not claim

- No garbage collector, no allocator performance, no scheduler fairness
  beyond what is stated (fairness is a separate `SchedulingModes` concern).
- No FFI safety: `FFIContext` in `Runtime.lean` is registration/lookup only;
  crossing the boundary voids the invariants (must be stated, not assumed).
- No 1.0 standard text: D6 produces the *freeze list and harness*, from which
  the standard is later written.

## 7. Open questions (not decided here — maintainer calls)

- Which model is authoritative for memory: `Memory.lean` blocks,
  `Runtime.lean` heap, or a merge? (Two models + one agreement lemma, or one
  model? Stage C's lesson: the fragment predicate, not the function, is the
  gate — but two models need a D2-style bridge regardless.)
- What is the actor progress statement: per-actor, global, or witness-style?
  (The roadmap demands executable counterexamples — that pushes toward
  witness-style, but it must be written down, not assumed.)
- Does noninterference (D5) quantify over the HIR evaluator, the MIR
  executor, or both? (C8's lesson: prove at one level, pin refusal at the
  others.)
- What is on the 1.0 freeze list, and who are the pilots? (D6 is a decision,
  not a derivation.)
