# Specification Fix Proposal

This document tracks proposed fixes for identified issues across the Morph specification suite, prioritized by severity and dependency.

---

## Critical Fixes

### Fix #4: Dialect Projection Source of Truth (Week 1-2)

*Referenced by:* `spec/language/dialect_projection_spec.md`

Establish that the canonical projectional form is the single source of truth. Syntax projections are generated on-demand and never persisted as authoritative artifacts.

---

## High Priority Fixes (Week 5-6)

### Fix: Resolve Agent-First vs Human Usability

*Referenced by:* `spec/language/dual_optimization_spec.md`

Formalize the priority hierarchy: agent-first projectional editing is primary; human-readable syntax projections are secondary convenience artifacts. Update all cross-references to reflect this ordering.

---

## Medium Priority Fixes (Week 9-10)

### Fix: Document ARC with Affine Types

*Referenced by:* `spec/memory/arc_affine_integration_spec.md`

Provide formal specification of how affine types guarantee cycle-freedom, making ARC safe without supplemental cycle collection. Include proof sketches for key theorems.

### Fix: Validate Unproven Assumptions

*Referenced by:* `spec/validation/unproven_assumptions_spec.md`

Formally validate all assumptions cataloged in `SPEC_GAPS_AND_BASIS.md`. Prove, revise, or disprove each with mathematical rigor.

---

## Layered Concurrency Requirements

*Referenced by:* `spec/architecture/layered_concurrency_spec.md`

Define clear boundaries between SSUS (state management) and actor model (inter-component communication) layers. Specify message passing protocols at the boundary.
