# ADR-008: Walrus Operator (`x := e`) Deferred to Phase 2

## Status
**Accepted**

## Context

The Morph language spec includes a walrus operator `x := e` (reassignment) as part of its expression language. During Phase 1 core formalization, we attempted to add this to the Lean operational semantics as an `Expr` constructor.

**Problem:** The current Lean formalization uses a pure substitution-based lambda calculus (no store/heap). The walrus operator requires **mutation** — it changes the binding of an existing variable. In a pure substitution semantics:

1. Substitution replaces all occurrences of a variable with its value at substitution time
2. Mutation requires the ability to change a binding that has already been substituted into multiple expressions
3. This is fundamentally incompatible: substitution is referentially transparent, mutation is not

**Mathematical argument:** The walrus operator requires a state monad `S → S × A` where `S` is the store mapping variables to locations and locations to values. This cannot be expressed in the current `Step` relation which operates purely on `Expr → Expr → Prop`.

## Decision

**Defer the walrus operator to Phase 2** (Execution Engine). It will be formalized when the VM provides:

1. A store (heap) with locations
2. Variable-to-location bindings (environment with indirection)
3. State transitions on the store
4. Location-based mutation semantics

The walrus operator will NOT be added to `Expr` in Phase 1. It will be introduced as a `Stmt` (statement) in Phase 2 alongside the store model.

## Considered Options

### Option A: Add store to Phase 1
- Add `Store : Nat → Value` to the `Step` relation
- Mutation becomes `Step (s, x := v) (s'[x ↦ v], unit)`
- **Rejected:** Would require rewriting ALL existing proofs (lift, weakening, substitution, progress, preservation) to carry store state. Estimated 4-6 weeks of rework for a single feature.

### Option B: Model as rebinding (shadowing)
- Treat `x := e` as creating a new binding that shadows the old one
- **Rejected:** Semantically incorrect — other references to `x` in closures should see the mutation, not the old value.

### Option C: Defer to Phase 2 (ACCEPTED)
- No changes to Phase 1
- Walrus formalized when VM provides store
- Clean architectural boundary

## Positive Consequences

1. Phase 1 soundness proof remains pure and tractable
2. No contamination of the substitution lemmas with store reasoning
3. Clean separation: Phase 1 = pure calculus, Phase 2 = effectful VM

## Negative Consequences

1. Walrus operator unavailable in Phase 1 test programs
2. Rust compiler already supports `assign` statements — spec formalization lags behind implementation

## Risks

- **Low:** The store model is well-understood (standard operational semantics technique)
- The Rust compiler's `assign` statement can be validated against Phase 2 semantics

## Related Standards

- ISO/IEC 15288: System Life Cycle — phased development
- Memory model spec §3.2: Mutation semantics require store model

## Related ADRs

- **ADR-006: Complete proof requirement** (zero sorry policy)

## Date
2026-06-09

## Author
Nexus (Principal Architect)
