# Stage D item D1 — inventory of the memory/concurrency/security models

Status: **measurement, 2026-11-25.** Companion to `docs/STAGED-SCOPE.md`
(sketch, no proof work authorized). This file records what already exists in
the tree so D1 can be scoped from facts instead of assumptions. Every number
below was read out of the tree with `grep`/`wc`; nothing here is a plan.

## 1. Summary

- `Morph/Memory.lean` (374 lines): **35 definitions, 0 theorems.**
- `Morph/Runtime.lean` (211 lines): **25 definitions, 0 theorems.**
- `Morph/Borrows.lean` (425 lines): 16 definitions, **16 theorems** —
  including `borrow_preservation`, a real MIR-level invariant.
- `Morph/Specs/MemoryModel/`: a **second, independent** memory model with
  34 theorems (`Lemmas.lean`, 521 lines) and zero `Prop := True` stubs. It
  does not import `Morph.Memory`.
- 10 concurrency/memory/security spec modules carry 223 theorems between
  them, all about their own spec-local models.

So the asymmetry is not "proofs are missing". It is that **the executable
models are unproved and the proved models are not the executable ones.** That
is precisely the bridge problem Stage C solved with relations
(`RelEnv`, `LamEnv`, `RelBorrowHeap`-shaped lemmas), and it is why D1 is
scoped as a fragment predicate plus a relation rather than as fresh lemmas
about `Memory.lean`.

## 2. The two memory models

| | `Morph/Memory.lean` (executable) | `Morph/Specs/MemoryModel` (proved) |
|---|---|---|
| Blocks | `Block` with `make`/`isAllocated`/`isFreed`/`inBounds` | `Block` with `isWellFormedBlock` |
| Bytes | `MemByte` = `value`/`undef`/`poison`, `isDefined`, `isPoison` | `UInt8` data, `readByte : … → Option UInt8` |
| State | `Memory` as a block list with `findBlock?`/`updateBlock` | `Memory` with `blocks` + `nextId` |
| Safety | none stated | `isMemorySafe` (real definition) |
| Ops | `read`/`write`/`freeBlock` (total, bounds-checked by caller) | `allocate`/`deallocate`/`readByte`/`writeByte` |
| Theorems | **0** | **34**, incl. allocation/deallocation/read/write preservation |
| Stubs | 0 | 0 (the seven `Prop := True` stubs were removed in loop 14) |
| Importers | `Morph.lean`, 12 spec `Spec.lean` files, `Morph/Tests/Memory.lean` | itself |

Both are plausible; neither is a refinement of the other. `Morph/Memory.lean`
is the one the pipeline could execute (it models undef/poison, which the
`MemByte` tests pin); `Specs/MemoryModel` is the one with the invariants.

**D1 decision this forces:** either (a) prove `HeapSafe` directly over
`Morph/Memory.lean` and treat `Specs/MemoryModel` as requirements, or (b) add
`RelMem : Specs.MemoryModel.Memory → Morph.Memory.Memory → Prop` and lift the
34 theorems across it. (b) is cheap only if the two byte/block shapes can be
related without simulation lemmas for every operation; that is not yet
measured. Recommendation: measure (b) on `read`/`write` before committing,
because a relation over two independently-designed block lists tends to need
an invariant that both sides must be proved to maintain.

## 3. The actor model

`Morph/Runtime.lean` defines `Heap`/`HeapBlock` (`heapAlloc`, `heapFree`,
`heapLookup`), `StackFrame`/`Stack` (`stackPush`, `stackPop`, `stackLookup`),
`Actor`/`ActorSystem` (`spawn`, `send`, `recv`, `stepActor`), and FFI
registration (`CallingConvention`, `FFIBinding`, `ffiRegister`, `ffiLookup`).
It has **no theorems**, no fragment predicate, and no tests importing it.

`stepActor` takes `(_heap : Heap) (_stack : Stack)` — the runtime state is
not threaded through a step, so an actor step currently cannot corrupt the
heap by construction, and equally cannot be proved to preserve it. Any D3
statement has to first decide whether the heap becomes part of the step
signature; that is an interface change, not a lemma.

`Morph/Specs/ActorDeadlock` (622 lines, 30 theorems, 1 documented stub
history) and `ConcurrencyProcessAlgebra` (779 lines, 41 theorems) model
deadlock-freedom and process equivalences over their own process algebra.
Neither mentions `Runtime.ActorSystem`.

## 4. The borrow model

`Morph/Borrows.lean` is the one place where an executable-side invariant
already exists and is proved:

- `WFBorrow π` / `WFBorrowApp π extra` — duplicate-free provenance sets;
- `Borrows fenv π i π'` — the per-instruction transfer relation;
- `borrow_preservation : WFBorrow π → Borrows fenv π i π' → WFBorrow π'`;
- `borrow_preservation_allocClosure`, `closureLoans_fresh`, `killLoans_*`,
  and four `…Bool_spec` bridges proving the executable booleans agree with
  the `Prop` definitions (`overlapsBool_spec`, `conflictBool_spec`,
  `noConflictingLoanBool_sound`, `capabilityBEq_sound`).

`Morph/Tests/Borrows.lean` imports it, so it is exercised. What is missing is
the link from `WFBorrow` to *heap* safety: `NoConflictingLoan` constrains
places and capabilities, never `Morph.Memory` blocks. That link is D2, and it
is the cheapest real theorem in Stage D because one side is already proved.

## 5. Security modules

`SecurityFlow` (20 theorems, 18 examples) and `SecurityOCap` (21 theorems)
are proved over spec-local models with no connection to `Morph/Memory.lean`,
`Runtime.ActorSystem`, or the HIR/MIR evaluators. Noninterference (D5) needs
an attacker-observable equivalence on the *evaluator*, which does not exist
yet.

## 6. What this means for the item order

The sketch's order (D1 heap fragment → D2 borrow–heap → D3 actor step →
D4 deadlock/witness → D5 noninterference → D6 freeze) survives contact with
the tree, with two adjustments:

1. **D2 is cheaper than D1.** `WFBorrow` is proved; `Morph/Memory.lean` has
   nothing. Starting with the borrow–heap relation gives a first real theorem
   without first designing a heap invariant from scratch — but it needs at
   least the *statement* of heap safety to relate to, so in practice the order
   is: state `HeapSafe` (D1's first half, a definition, no proof), then D2.
2. **D3 has an interface prerequisite**, not a proof prerequisite:
   `stepActor` must thread heap/stack state before any preservation statement
   is meaningful. That decision belongs to §7 of the sketch, not to a loop.

## 7. Known limits of this inventory

- Counts are `grep '^\s*(theorem|lemma)'`; they include `example`s only where
  stated separately, and they say nothing about whether a theorem is deep.
- No attempt was made to check whether the 34 `MemoryModel` theorems would
  survive being restated over `Morph/Memory.lean`; that is the measurement
  §2 recommends.
- `Morph/Runtime.lean` is imported by nothing but its own module list, so its
  definitions are currently unexercised: treat them as a design sketch that
  compiles, not as a runtime.
