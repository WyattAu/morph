# ADR-012: Closure Representation — Store-Allocated, Uniform with the Capability System

## Status
**Proposed** (post-program loop 1, 2026-10-09). Resolves the "largest open
question" flagged in ADR-011's negative consequences. Blocking for MIR stage 2
(closures in the pipeline) and for any `call`-instruction execution beyond
the current `none`-stub.

## Context

ADR-011's stage 1 lowers `Expr.lam`/`Expr.app` to MIR with closures, which
requires deciding where a closure's captured environment lives:

- **store-allocated**: the env is a heap cell (`Store.alloc`), the closure
  value points at it, and the whole closure is an ordinary value subject to
  the capability system (`Capability`) and the borrow judgment
  (`Morph.Borrows`); or
- **stack-allocated**: the env lives in the activation frame, outside the
  store, with escapes promoted to the heap at some later point.

This decision interacts with three already-adjudicated artifacts:

1. **ADR-010 (store model)** — all mutable state lives in the typed store;
   `StoreInv`/`StoreTyped` are the safety invariants.
2. **ADR-013 stage 1 (borrow judgment)** — checks MIR accesses against
   outstanding loans over `Place`s rooted in registers and store cells.
   Loan creation/kill is stage-2 work.
3. **P5 (ARC base)** — Perceus-style RC primary, GC fallback. ORCA showed
   precise capability information enables barrier-free collection.

## Decision

### 1. Semantics: every closure is a store cell

At the *semantic* level (surface `Expr` semantics and the MIR execution
oracle), closure creation **allocates**:

```lean
-- Value extension
| closure : FnId → Loc → Value   -- code pointer + env cell

-- Step rule (surface): lam allocates an env cell binding the free vars
-- Step: lam σ τ ... — allocates, yields Value.closure fn loc
-- MIR: Instr.allocClosure (dst : ValId) (fn : FnId) (captures : List ValId)
```

The captured environment is a store cell (a record of captured values). The
closure value `(FnId, Loc)` is an ordinary value: it can be stored, loaded,
copied, and — critically — **borrowed like any other reference-typed value**.

**Why store-allocated wins:**

- **One checking regime.** With closures as store values, closure captures
  are checked by exactly the ADR-013 judgment: `allocClosure` creates a loan
  on each captured place for as long as the closure lives (stage-2 loan
  creation — the first real loan-creation rule). A stack-allocated env would
  need a *second* borrow-checking regime for frame slots, doubling the proof
  burden for `analysis_sound` (ADR-011 stage 2).
- **Capabilities compose.** An `iso` closure owns its env exclusively
  (single-use, linear — matching `linearFunctionType`/`countUses` from
  ADR-014); a `val` closure shares an immutable env (callable many times).
  This is Pony-style viewpoint adaptation (Loop 10's P4 finding) applied to
  function values, and it falls out of the existing `ValueType` machinery
  rather than requiring new rules.
- **RC fits.** Closure cells are RC'd store cells (Perceus): dropping the
  last closure reference decrements the env cell. No new runtime mechanism.
- **Oxide-idiomatic.** Everything is a place; closures are places.

**Cost, acknowledged:** every closure allocation costs a store cell and an
RC increment, even for non-escaping closures.

### 2. Optimization: escape promotion is a MIR-level rewrite, not semantics

Non-escaping closures are common; paying allocation for them is not
acceptable in the backend. But the *elimination* is an optimization with its
own correctness obligation, layered after stage 2:

```lean
/-- Allocation elision: if the closure cell is never observed (only used
via callClosure within its defining block scope), the alloc + load pair
can be replaced by direct parameter passing. -/
theorem alloc_elision_correct : ...
```

The surface semantics stays simple (always allocates); the optimizer proves
elision preserves `evalInstrFull` results. This keeps `lowering_correct`
simple and puts the optimization where it is checkable (on MIR, with the
WF machinery already in place).

### 3. MIR additions (stage 2)

```lean
| allocClosure (dst : ValId) (fn : FnId) (captures : List ValId)
| callClosure  (dst : ValId) (clo : ValId) (args : List ValId)
```

- `allocClosure`: reads each capture register, allocates one env cell
  holding them, binds `dst := Value.closure fn envLoc`.
- `callClosure`: loads the closure cell, loads the env cell, calls the
  lifted `Func` with env values prepended to `args`.
- Lambda lifting (stage 1 extension): each `Expr.lam` body becomes a
  top-level `Func` whose leading params are the captured free variables
  (de Bruijn → named params at lift time); call sites allocate + dispatch.

### 4. Borrow rules for the new instructions (stage-2 loan creation)

```lean
| allocClosure : ∀ fenv π dst fn captures,
    -- each capture must be loan-free or shared-readable per the env's
    -- capability; creation ADDS a loan on each captured place
    (∀ c ∈ captures, CaptureOK π c κ) →
    Borrows fenv π (.allocClosure dst fn captures)
             (π ++ closureLoans fn captures κ)
| callClosure : ∀ fenv π dst clo args,
    NoConflictingLoan π (.base clo) .val →      -- reading the closure cell
    (∀ a ∈ args, ArgOK π a) →
    Borrows fenv π (.callClosure dst clo args) π
```

`closureLoans` is the first loan-**creation** rule in the judgment — this is
the point where stage 1's identity-transfer restriction is lifted, and
`borrow_preservation` must be restrengthened (loan sets grow, so the stage-1
"no duplicates" invariant needs a multiset/level discipline — expected, and
the reason loan creation was deferred until this ADR existed).

## Consequences

### Positive
- Single borrow-checking regime; `analysis_sound` (ADR-011 stage 2) is one
  theorem over one judgment, not two.
- Linear closures fall out of existing `Capability` + `linearFunctionType`
  machinery — no new type-system surface.
- RC story is uniform with P5.
- Unblocks: MIR `call`/`callClosure` execution, lambda lifting in
  `Lowering.lean`, borrows-of-closures, and the stage-2 loan-creation design.

### Negative
- Allocation cost per closure in the unoptimized pipeline (mitigated by
  §2 with its own proof obligation).
- `borrow_preservation` must be restrengthened once loans are created
  (stage-2 work; the invariant moves from "no duplicates" to a lifetime-
  ordered discipline à la Oxide).
- `evalInstrFull` grows two cases; the store threading gets its first
  instruction that allocates *and* reads registers in one step (ordering
  of reads vs. allocation must be pinned: read all captures first, then
  allocate — to keep the step deterministic even if `Store.alloc` reuses
  freed locations).

## Non-goals
- Closure **upcasting/subtyping** (`fn(A) -> B` subtyping under variance) —
  that is P9 (generics + parametricity).
- **Drop elaboration** for nested closure envs — runtime work, post-stage-4.
- Zero-cost **non-capturing** closures as static function pointers — a
  special case of §2's elision, not a separate representation.

## References
- ADR-010 (store model), ADR-011 (MIR pipeline), ADR-013 (borrow judgment),
  ADR-014 (multiplicity on arrows).
- Loop 10 P4 finding: Pony viewpoint adaptation (*A Principled Design of
  Capabilities in Pony*).
- Perceus (P5): precise RC; reuse makes allocation elision principled.

## Date
2026-10-09
