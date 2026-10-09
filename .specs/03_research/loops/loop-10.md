# Loop 10 — 2026-09-19

Final loop of the 10-loop program. Closes the last owed fetch, resolves the
capability-matrix comparison, then retrospective and handoff.

## Sources consulted

### Pony papers — FETCHED (https://www.ponylang.io/learn/papers)

Eight papers indexed. Three matter for Morph.

#### 1. *A Principled Design of Capabilities in Pony*
(https://www.ponylang.io/media/papers/a_prinicipled_design_of_capabilities_in_pony.pdf)

> "Extends the deny capabilities work with a more complete formalization.
> Covers **viewpoint adaptation**, **safe-to-write**, and how capabilities
> compose under aliasing and subtyping."

**This is a validation, not a correction.** Pony's *safe-to-write* is
precisely our `SafeCast` derivation: the relation saying "a reference with
capability `κ` to a cell of type `τ` may be used at capability `κ'` when
`ValueType.safeToWrite` permits it." Loop 2 designed `SafeCast` from first
principles and Loop 3 implemented it; Loop 10 finds the same relation named
and formalized in a peer-reviewed Pony paper. Two independent derivations
landing on the same object is the strongest available evidence that
`iso → val` and `iso → ref` are the right derivations and that `ref → val`
being forbidden is not an artifact of our encoding.

Also relevant: **viewpoint adaptation** is Pony's treatment of capability
change when you narrow your viewpoint on a structure — the generalization of
what `refCast` does at a cell. Our `Expr.refCast` is a deliberately
restricted viewpoint adaptation (single cell, explicit target type). Pony's
version is deeper (per-field, structural). **Recommendation for stage 2:**
when `refCast` is generalized, move toward Pony's structural viewpoint
adaptation rather than inventing a new scheme.

#### 2. *Deny Capabilities for Safe, Fast Actors* (Colyer)
(https://www.ponylang.io/media/papers/fast-cheap.pdf)

> "Introduces deny capabilities... Shows how denying certain operations on a
> reference (rather than granting them) lets the type system guarantee
> data-race freedom."

The **dual** of our design: we grant capabilities (`val`/`ref`/`iso` in
`Capability`), Pony denies them. The duals are equivalent for safety but
differ in which cast rules are derivable and in ergonomics.

#### 3. *ORCA: GC and Type System Co-Design for Actor Languages*
(https://www.ponylang.io/media/papers/orca_gc_and_type_system_co-design_for_actor_languages.pdf)

> "ORCA uses the type system's knowledge of reference capabilities to do
> per-actor garbage collection with no stop-the-world pauses and **no read or
> write barriers**."

**Strengthens P5.** Loop 4 concluded "Perceus-style RC primary, GC fallback"
from the Perceus paper alone. ORCA independently demonstrates the other half:
if the type system tracks capability/provenance precisely enough, the GC needs
no barriers at all. Together they justify the full ARC shape:

- precise ownership → reference counting works (Perceus: no delayed-free bug)
- precise capabilities → GC needs no write barriers (ORCA)

P5 now has a two-source justification instead of one.

## Adjudications

### P4 (capability model completeness) — **RESOLVED**

This was the register's standing open item: *"Compare against Pony's
6-capability matrix; no construction-time capability (`trn`); no
deny-capabilities matrix."*

Pony has six reference capabilities: `iso`, `trn`, `ref`, `val`, `box`, `tag`.
Morph has three: `iso`, `val`, `ref`. Disposition of each gap:

| Pony cap | Morph status | Rationale |
|---|---|---|
| `iso` | present | same semantics (exclusive, consumable) |
| `ref` | present | same semantics (local mutable, non-shareable) |
| `val` | present | same semantics (immutable, shareable) |
| `trn` | **not adopted** | transition cap exists only to type the temporary window during field initialization. Morph has no destructuring-initialization sugar, so the window does not exist in the surface language. Reconsider when structs/ADTs land. |
| `box` | **deferred to P8** | "read-only to *you* but possibly mutable by someone else." Only meaningful with actor/shared-memory concurrency, which is P8's problem. Adding it now would be speculative. |
| `tag` | **deferred to P8** | object identity, comparable and shareable. Also an actor/concurrency concern. |

Deny-capabilities matrix: **recorded as the dual framing, not adopted.** Our
grant-based `Capability` is implemented (`Morph/Core.lean`) and proven against
(ADR-010, `safety_frozen_not_writable`). Rewriting to a deny-matrix would
touch proven code for no proven gain. Revisit in P9 (generics), where
deny-style capability constraints are often cleaner to state.

**P4 closes**: the 3-capability set is deliberate, each omission is justified
against a named need, and `box`/`tag` are correctly parked in P8 rather than
being pre-added.

### P5 (ARC base) — **REINFORCED** (see ORCA above)

### P8 (actor/async verification) — **STILL OPEN, now better informed**

ORCA was previously cited in the register as evidence that "no verification
story" exists. That remains true, but the register note is now sharper:
ORCA proves the *runtime* side (capabilities → barrier-free GC) is
independently valuable even unverified. That is an argument that P8's payoff
exists, not that the problem is solved. **Remains open.**

### P9 (generics + parametricity) — **STILL OPEN**, with new prior art

RustBelt §parametricity remains the difficulty. The Pony fetch adds one
concrete pointer: *Formalizing Generics for Pony* covers "how generic types
interact with reference capabilities" and capability-constrained type
parameters under subtyping. That is the exact intersection P9 needs.
**Remains open**, now with a named starting paper.

### P10 (error handling) — **STILL OPEN**

Unaffected by this loop.

### P11 (conformance testing) — **STILL OPEN**

Unaffected by this loop. Note that Loop 8's `evalInstrFull`/`execFunc` oracle
is a *step toward* P11's differential-testing program, but is not one: P11
requires comparing the Rust implementation against the Lean interpreter, and
no such harness exists.

## Register disposition (final)

| ID | Question | Status | Loop |
|----|----------|--------|------|
| P1 | Expressing linearity | RESOLVED — plain contexts + multiplicity-on-arrows (ADR-014) | 1 |
| P2 | VM vs MIR boundary | RESOLVED — boundary to CakeML; MIR pipeline (ADR-011) | 2 |
| P3 | Borrow checking placement | RESOLVED — Oxide-shaped substructural judgment (ADR-013) | 6, 9 |
| P4 | Capability model completeness | RESOLVED — 3 caps justified; `box`/`tag` → P8; `trn` unnecessary | 10 |
| P5 | ARC base | RESOLVED — RC primary + GC fallback (Perceus + ORCA) | 4, 10 |
| P6 | Type-level effects | RESOLVED — deleted as unused; spec kept separate | 5 |
| P7 | Mirror/indirection | RESOLVED-by-deferral — post-stage-3 | 5 |
| P8 | Actor/async verification | **OPEN** — no verification story; ORCA informs payoff | — |
| P9 | Generics + parametricity | **OPEN** — RustBelt §parametricity; *Formalizing Generics for Pony* is a new pointer | — |
| P10 | Error handling | **OPEN** — unexamined | — |
| P11 | Conformance testing | **OPEN** — no differential harness | — |
| P12 | Binder syntax blocked on P1 | RESOLVED — unblocked by ADR-014 | 1 |
| P13 | Is inference sound | RESOLVED — **proven** (`InferenceSound.lean`) | 3 |

**9 of 13 resolved. 4 open: P8, P9, P10, P11.** The open four are all
genuinely deferred (they need concurrency, generics, or a second
implementation), not stalled.

## Program retrospective

### What the 10 loops produced

**Construction (Lean, all proven, 0 sorry, 0 axioms):**
- Store-threaded semantics with done-rules for load/store/free
- Store typing discipline (`StoreTyp`, `ValueType`, `StoreInv`) with progress,
  preservation, and five safety theorems
- `SafeCast` end-to-end incl. `safety_frozen_not_writable`
- Non-consuming typing contexts with `linearFunctionType` + `countUses`
- Proven-sound checker (`InferenceSound.lean`), which caught 11 real drifts
- Target-independent MIR with WF theorems and a store-aware execution oracle
- MIR lowering definitions for the pure-arithmetic subset

**Architecture (ADRs):** ADR-010 (store model), ADR-011 (MIR pipeline),
ADR-013 (borrow judgment), ADR-014 (multiplicity).

**Net deletions:** ADR-014 stage 2 removed 1,612 lines of `LinCtx`
consumption machinery that turned out to be the wrong shape.

### What the loops did *not* deliver

Honest accounting:

1. **The MIR lowering correctness theorem is unproven.** Delivered as
   definitions plus a worked-out proof design (loop-07.md). The remaining
   work is mechanical, not conceptual — but it is unproven, and nothing in
   the lowering pipeline should be called verified until it lands.
2. **No borrow checker in Lean.** ADR-013 specifies the judgment; it does not
   exist as code. Largest single gap.
3. **Closures unaddressed.** ADR-012 has no representation decision. MIR
   `call`/`phi`, lambdas, and borrows-of-closures all depend on it.
4. **No backend, no compiler.** Zero lines of codegen. The LLVM/Cranelift
   path is a plan.
5. **P8–P11 unresolved** (concurrency, generics, error handling, differential
   testing).
6. **Effect system, mirror structure, pattern matching, generics** — deferred
   with notes, none implemented.

### Honest assessment

The research program succeeded at its stated purpose: it converted open design
questions into ADRs backed by external literature, early enough that most
wasted work was avoided. The 1,612-line `LinCtx` deletion is the visible cost
of learning that shape was wrong — cheap, because it was early.

What it did *not* do is close the distance between "specified" and "verified."
The repo holds a well-typed, well-proven **front half** (typing, soundness,
store discipline, IR shape, execution oracle) beside an **unproven back half**
(lowering, borrow checking, codegen). A reader consulting only the theorem
statements would overestimate what is verified. The handoff exists to prevent
that.

## Handoff

### Critical path (in order)

1. **ADR-012 closure representation.** Blocks: lambdas in MIR, `call`
   execution, borrows-of-closures, all of step 2.
2. **`lowerIn_correct` / `lower_correct`.** Full proof design in
   `loop-07.md`; write-avoidance simp engineering is the only blocker.
3. **ADR-013 implementation.** `Place`/`Loan`/`Provenances`/`Borrows` as Lean
   definitions + `borrow_progress` + `borrow_preservation`.
4. **MIR stage 2 (SSA).** Depends on 1 and 3.
5. **MIR stage 3–4 (backends).** Depends on 2.

### Open research questions, ranked by what they block

- **P9 (generics/parametricity)** — blocks the ADT/generics work that stage 2
  needs. Start with *Formalizing Generics for Pony*
  (https://www.ponylang.io/media/papers/formalizing_generics_for_pony.pdf),
  then RustBelt §parametricity.
- **P11 (conformance testing)** — blocks every future claim that the Rust
  implementation agrees with the Lean spec. Cheapest of the four to start
  (the oracle now exists), highest leverage on trust.
- **P8 (actors)** — blocks `box`/`tag` capabilities and the runtime. Largest
  scope, furthest from the current pipeline.
- **P10 (error handling)** — blocks surface-language completeness. Independent
  of the rest; can be interleaved.

### Recommended next source reads

- *A Principled Design of Capabilities in Pony* — structural viewpoint
  adaptation, to generalize `refCast` at stage 2.
- *Formalizing Generics for Pony* — P9's missing piece.
- Perceus — re-read for the read-barrier reconciliation, since P5 now has two
  sources and the interaction between RC and barrier-free GC is unexamined.

### Standing constraints

- `lake build Morph Morph.Tests`: 0 errors, 0 warnings, 0 sorry, 0 axioms.
- `cargo test --workspace`: 218 tests, 0 failures.
- Spec → Lean → Rust. Rigor precedes VM and codegen.
