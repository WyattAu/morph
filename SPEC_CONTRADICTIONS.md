# Specification Contradictions

This document catalogs contradictions identified across the Morph specification suite and their resolutions.

---

## Contradiction #1: Agent-First vs Human Usability

*Source:* `spec/language/dual_optimization_spec.md`

The specification simultaneously mandates projectional-only editing (agent-first) while requiring human-readable syntax (human usability). The resolution prioritizes agent-first design with human-readable projections as secondary artifacts.

*Status:* Resolved in `spec/language/dual_optimization_spec.md`

---

## Contradiction #2: Projectional Editing vs Syntax Persistence

*Source:* `spec/language/dialect_projection_spec.md`

The dialect projection system requires both a canonical projectional representation and multiple syntax projections, creating tension about which representation is authoritative for persistence. Resolution: canonical projectional form is the source of truth; syntax projections are derived transient artifacts.

*Status:* Addressed in `spec/language/dialect_projection_spec.md`

---

## Contradiction #3: Layered Concurrency Paradigm Coexistence

*Source:* `spec/architecture/layered_concurrency_spec.md`

The architecture attempts to unify unidirectional data flow (SSUS pattern) with actor model concurrency, which have fundamentally different message passing semantics. Resolution: layered architecture where SSUS governs intra-component state and actors handle inter-component communication.

*Status:* Resolved in `spec/architecture/layered_concurrency_spec.md`

---

## Contradiction #4: ARC vs Tracing GC for Memory Management

*Source:* `spec/memory/arc_affine_integration_spec.md`

The memory model must support both automatic reference counting (ARC) for deterministic resource cleanup and affine type system constraints, which can conflict when cycles exist. Resolution: affine types provide compile-time cycle prevention, making ARC safe without cycle collection.

*Status:* Addressed in `spec/memory/arc_affine_integration_spec.md`
