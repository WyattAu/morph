# Specification Gaps and Basis

This document identifies gaps in the Morph specification suite and the foundational basis (axioms, assumptions, and dependencies) on which specifications rest.

---

## Unproven Assumptions

The following assumptions were identified as needing formal validation. See `spec/validation/unproven_assumptions_spec.md` for the complete formal validation of each item.

| ID | Assumption | Status | Validation |
|----|-----------|--------|------------|
| GA-001 | Affine types guarantee cycle-freedom in ARC | Validated | Formal proof in `spec/memory/arc_affine_integration_spec.md` |
| GA-002 | SSUS pattern preserves referential transparency | Validated | See `spec/language/strict_state_unidirectional_spec.md` |
| GA-003 | Projectional editing can express all syntactic forms | Under Review | See `spec/language/dialect_projection_spec.md` |
| GA-004 | Actor message ordering is deterministic | Validated | See `spec/architecture/layered_concurrency_spec.md` |
| GA-005 | Type system is decidable for all Morph programs | Assumed | Requires formal proof |

---

## Specification Gaps

### Gap Analysis (Section 5.5)

*Referenced by:* `spec/language/syntax_translation_spec.md`

| Gap ID | Area | Description | Priority |
|--------|------|-------------|----------|
| SG-001 | Syntax Translation | Formal semantics for cross-dialect translation | Medium |
| SG-002 | Memory Model | Formal bounds on heap allocation growth | High |
| SG-003 | Security Flow | Taint tracking across dialect boundaries | High |
| SG-004 | Concurrency | Deadlock-freedom proof for actor system | Medium |
| SG-005 | Type System | Decidability proof for subtyping | High |

---

## Foundational Basis

The Morph specification suite rests on the following foundational assumptions:

1. **Lean 4 as metalanguage**: All formal proofs are expressed in Lean 4, depending on its consistency
2. **Constructive logic**: Specifications use constructive (intuitionistic) logic via Lean 4's type theory
3. **No runtime GC**: Memory management relies on affine types + ARC, not tracing garbage collection
4. **Deterministic execution**: All pure expressions have deterministic evaluation order
