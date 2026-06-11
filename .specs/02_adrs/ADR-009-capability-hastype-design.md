# ADR-009: Capability HasType Design

## Status
**Proposed**

## Context

The Morph language specification defines a capability-based ownership system with three capabilities:
- **`iso`** (isolated): Full ownership, linear semantics (must be used exactly once)
- **`val`** (immutable value): Shared immutable reference, affine semantics (used at most once)
- **`ref`** (mutable reference): Exclusive mutable borrow

The `Typ` inductive has `refType cap τ` but no `HasType` constructor exists for it. The memory model spec requires:
1. No use-after-free (affine/linear semantics)
2. No double-free (ARC safety)
3. Capability transitions: `iso → val → ref` (widening is safe)
4. Strong reference graph is a DAG under affine types

## Decision

### Phase 1: Minimal Capability Typing (Current Phase)

Add a `HasType` constructor that tracks capabilities WITHOUT enforcing linearity/affinity:

```lean
| ref_type : ∀ bvs Γ e cap τ,
    HasType bvs Γ e τ →
    HasType bvs Γ (.typeAsc e (.refType cap τ)) (.refType cap τ)
```

This allows expressions to be annotated with capability types but doesn't enforce substructural constraints. This is sufficient for:
- Type checking capability annotations
- Type inference recognizing capability types
- Soundness proof (no capability violations possible)

### Phase 2: Substructural Enforcement (Future)

Add a `LinearContext` alongside `bvs` that tracks usage counts:

```lean
-- Track how many times each bound variable has been used
inductive Usage where
  | unused : Usage
  | used : Usage

-- Extended typing context with usage tracking
abbrev LinCtx := List (Typ × Usage)

-- Affine typing: variables used at most once
inductive LinHasType : LinCtx → TypEnv → Expr → Typ → Prop where
  | ...
```

This requires:
1. Splitting `bvs` into affine and unrestricted zones
2. Usage tracking in the typing judgment
3. Consumption rules: `iso` variables consumed on use, `val` variables consumed on first write
4. Weakening only for unrestricted variables

Estimated effort: 3-4 weeks.

## Alternatives Considered

### Option A: No Capability Typing (Rejected)
- Can't verify memory safety properties
- Spec requires capability tracking

### Option B: Full Linear Types Now (Rejected)
- 3-4 weeks of work
- Would delay Phase 2 (VM) significantly
- Soundness proof becomes much harder

### Option C: Minimal Now, Full Later (Accepted)
- Phase 1: simple annotation typing (1-2 days)
- Phase 2: substructural enforcement (3-4 weeks, after VM)
- Clean separation of concerns

## Consequences

**Positive:**
- Capability types are representable in the type system
- Clean upgrade path to full substructural typing
- No delay to Phase 2 (VM) work

**Negative:**
- Phase 1 doesn't actually enforce ownership rules
- Memory safety proofs depend on Phase 2

## Related Standards
- Memory model spec §2.4: Affine type semantics
- Arc-affine integration spec: ARC + capability interaction
- ISO 26262 §6.7: Memory safety requirements

## Related ADRs
- ADR-008: Walrus deferred (mutation requires store)
- ADR-006: Complete proof requirement

## Date
2026-06-10

## Author
Nexus (Principal Architect)
