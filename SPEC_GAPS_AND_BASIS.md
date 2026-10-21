# Specification Gaps and Basis

This document identifies gaps in the Morph specification suite and the foundational basis (axioms, assumptions, and dependencies) on which specifications rest.

**Last updated:** 2026-05-29  
**Phase 0 status:** Spec integrity audit complete; 9 contradictions investigated (3 real, 6 false positives); 29 aspirational specs frozen.

---

## Resolved Contradictions (Phase 0)

| ID | Contradiction | Resolution | Date |
|----|--------------|-----------|------|
| C-001 | Duplicate LANG-REQ-071 | FALSE POSITIVE — both refer to Input Normalization | 2026-05-29 |
| C-002 | `async fn` in code examples violates LANG-REQ-023 | Fixed — all examples updated to `fn ... performs IO` | 2026-05-29 |
| C-003 | Effect category mismatch (4 vs 5) | Fixed — canonicalized to 4 effects {IO, Net, Time, System}; Pure is capability | 2026-05-29 |
| C-004 | Affine vs Linear semantics | Fixed — 3 occurrences of "exactly once" corrected to "at most once" | 2026-05-29 |
| C-005 | Keyword count off-by-one | FALSE POSITIVE — 22 is correct including `async` as contextual | 2026-05-29 |
| C-006 | Version drift in examples | FALSE POSITIVE — versions already correct | 2026-05-29 |

See `SPEC_CONTRADICTIONS.md` for full details.

---

## Unproven Assumptions

The following assumptions were identified as needing formal validation. See `spec/validation/unproven_assumptions_spec.md` for the complete formal validation of each item.

| ID | Assumption | Status | Validation |
|----|-----------|--------|------------|
| GA-001 | Affine types guarantee cycle-freedom in ARC | Validated (for type-level cycles) | Formal proof in `spec/memory/arc_affine_integration_spec.md`; runtime-cycle caveat recorded in `memory_bounds_spec.md` §5.3 |
| GA-002 | SSUS pattern preserves referential transparency | Validated | See `spec/language/strict_state_unidirectional_spec.md` |
| GA-003 | Projectional editing can express all syntactic forms | Under Review | See `spec/language/dialect_projection_spec.md` |
| GA-004 | Actor message ordering is deterministic | Validated | See `spec/architecture/layered_concurrency_spec.md` |
| GA-005 | Subtyping over `Typ` is decidable | **Corrected** | The claimed `instDecidableSubtype`/`isSubtype` (ADR-015) did not exist in the repository. Loop 12 supplies both: `Morph/Specs/Subtyping/` — `isSubtype` with `isSubtype_sound`/`isSubtype_complete` and the `instDecidableSub` instance. The *old* `Subtype` relation is exactly equality (`subtype_iff_eq`). |

---

## Specification Gaps

### Gap Analysis (Section 5.5)

*Referenced by:* `spec/language/syntax_translation_spec.md`

| Gap ID | Area | Description | Priority | Roadmap Phase |
|--------|------|-------------|----------|--------------|
| SG-001 | Syntax Translation | Formal semantics for cross-dialect translation | **CLOSED** (loop 7: `Morph/Specs/DialectSemantics/`, `spec/language/dialect_semantics_spec.md`) | — | — |
| SG-002 | Memory Model | Formal bounds on heap allocation growth | **CLOSED** | Phase 1.5 — `spec/memory/memory_bounds_spec.md` (research loop 2) |
| SG-003 | Security Flow | Taint tracking across dialect boundaries | **CLOSED** | Phase 1.6 — `spec/security/taint_flow_spec.md` (research loop 4) |
| SG-004 | Concurrency | Deadlock-freedom proof for actor system | **CLOSED** | Phase 4.4 — `spec/concurrency/actor_deadlock_freedom_spec.md` (research loop 3) |
| SG-005 | Type System | Decidability proof for subtyping | **CLOSED** (loop 12: `Morph/Specs/Subtyping/`, `spec/language/subtyping_spec.md`) | — | — |

---

## Frozen Aspirational Specs

29 specs moved to `spec/tooling/_future_research/` on 2026-05-29. These are excluded from the critical path and will be revisited after v1.0.0.

---

## Foundational Basis

The Morph specification suite rests on the following foundational assumptions:

1. **Lean 4 as metalanguage**: All formal proofs are expressed in Lean 4, depending on its consistency
2. **Constructive logic**: Specifications use constructive (intuitionistic) logic via Lean 4's type theory
3. **No runtime GC**: Memory management relies on affine types + ARC, not tracing garbage collection
4. **Deterministic execution**: All pure expressions have deterministic evaluation order

## Resolution log

| Gap | Status | Resolution |
|---|---|---|
| SG-001 | **CLOSED** | Loop 7: `Morph/Specs/DialectSemantics/` — translation validation; every accepted translation preserves the denotation, and refusal is total. `spec/language/dialect_semantics_spec.md`. |
| SG-002 | **CLOSED** | Loop 2: `Morph/Specs/MemoryBounds/` — affine discipline as an invariant, `invariant_preserved`, `quiescent_no_leak`, `allocs_bound`. `spec/memory/memory_bounds_spec.md`. |
| SG-003 | **CLOSED** | Loop 4: `Morph/Specs/TaintFlow/` — taint preserved across dialect boundaries; `boundary_preserves_noninterference`. `spec/security/taint_flow_spec.md`. |
| SG-004 | **CLOSED** | Loop 3: `Morph/Specs/ActorDeadlock/` — deadlock freedom from a rank invariant; `progress_invariant`. `spec/concurrency/actor_deadlock_freedom_spec.md`. |

Four further modules had no stated theory at all and now do, each with its own
spec document: `SubstTheory` (loop 5, no-capture), `EffectAlgebra` (loop 6),
`StealingFairness` (loop 8, partial), `TotalLexer` (loop 9, partial),
`ExecutionMachine` (loop 10, partial). See `docs/RESEARCH-LOOPS.md`.
