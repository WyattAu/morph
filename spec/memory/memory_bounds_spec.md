# Memory Bounds and Garbage-Freedom Specification

**Spec ID:** MEM-BND-001
**Version:** 1.1.0
**Status:** Formalized (Lean 4)
**Date:** 2026-10-31
**Formal Module:** `Morph/Specs/MemoryBounds/Spec.lean`, `Morph/Specs/MemoryBounds/Lemmas.lean`
**Closes:** SG-002 (formal bounds on heap allocation growth)
**Related Specifications:** [`memory_model_spec.md`](./memory_model_spec.md),
[`memory_affine_logic_spec.md`](./memory_affine_logic_spec.md),
[`arc_affine_integration_spec.md`](./arc_affine_integration_spec.md)

---

## 1. Purpose

SG-002 asked for *formal bounds on heap allocation growth*. This specification
states the operational collector model used for the proof and records the
formal results, the research that produced them, and the deliberate scope
limits.

---

## 2. Research Basis (research loop 2)

| Source | Result used | Why it applies to Morph |
|--------|-------------|------------------------|
| Reinking, Xie, de Moura, Leijen. *Perceus: Garbage Free Reference Counting with Reuse.* PLDI 2021 (distinguished paper), MSR-TR-2020-42 | Thm 4: "Perceus is precise and garbage free" — every reference retained in an intermediate state is reachable from the current value | Garbage-freedom is *algorithmic* there: Perceus must emit precise `dup`/`drop`. Morph's affine discipline makes it *structural*, so the obligation moves from the algorithm to the type system |
| Same, Thm 2 | Soundness of the reference-counted heap: every heap resource is "reachable from the expression **or part of a cycle**" | The escape clause is the price of permitting cycles. Morph rules cycles out at the type level, so the clause is unnecessary |
| Clebsch, Drossopoulou, Blessing, McNeil. *ORCA: GC and Type System Co-Design for Actor Languages.* OOPSLA 2015 | Per-actor reference-capability GC; **heap bounding is listed as future work** | Closest peer design (RC + GC co-design). It bounds neither heap size nor reclamation formally |
| Clebsch. *Pony: Co-designing a Type System and a Runtime.* 2018 | "the implementation of the runtime itself [is] not formally verified ... a formally verified runtime ... must be left for future work" | No production RC/GC runtime has a verified memory-bound theorem |
| Baraniok, Kawałkiewicz, Kovács, *Memory Bounds for Rust* (AURA line); RustBelt (Jung, Kim, Walkinshaw, POPL 2021) | Rust: memory *safety* verified; growth bounds **out of scope** (no GC ⇒ "bound" is not a runtime question) | Confirms that verified *bounds* are a different (harder) problem than verified *safety* |

**Conclusion of the survey.** No language runtime ships a mechanically checked
statement of the form "the heap holds at most `|dom heap₀| + #allocs − #collects`
objects". Perceus proves garbage-freedom with a cycle escape clause; Pony and
Rust prove safety but not bounds. Morph can go further than Perceus because its
affine ("at most one incoming edge") discipline rules the escape case out at the
type level — this specification is the formalization of that claim.

**Language comparison (are we solving something they could not?).** Not
entirely: Perceus's authors did not attempt an escape-clause-free theorem
because their calculus *permits* aliasing. Morph is in the position to attempt
it because `Iso` ownership is linear-ish. The residual risk is that the affine
discipline is enforced by a *checker* (`Iso` consumption) rather than by the
memory model, so the collector rules below must carry `Released` as a premise;
see §5.

---

## 3. Definitions: operational model

- `Heap : Addr → Option (List Addr)` — the object graph; each address maps to its
  field addresses, `none` meaning unallocated.
- `Config` = `heap` + `roots` (owned addresses) + `pending` (released addresses
  awaiting collection) + `allocs` (allocation counter).
- `Reach h base a` — `a` is derivable from `base` along heap edges.
- `Precise c` — (P1) every live address is reachable from `roots ++ pending`;
  (P2) every root owns a live entry.
- `Affine c` — the ownership discipline:
  - **A1** the queue holds only *released* addresses (`pending ∩ roots = ∅`)
  - **A2** a field target is not also a root
  - **A3** a field target is live (no dangling edges)
  - **A4** a queued address has no incoming edge (its owner released it)
  - **A5** *at most one incoming edge per address* (unique ownership)
  - **A6** an object's fields are pairwise distinct
  - **A7** no self-loops
- `Invariant c` = `Precise c ∧ Affine c ∧ roots.Nodup`.
- `Released h a` = no live object refers to `a`; a premise of `collect`.

### 3.1 Step relation

| Step | Effect | Preconditions |
|------|--------|---------------|
| `alloc` | fresh address with empty fields becomes a root; `allocs + 1` | `heap a = none`, `a ∉ roots`, `a ∉ pending` |
| `store` | affine move: root `f` is attached to root `a`'s fields and leaves `roots` | `a, f ∈ roots`, `a ≠ f` |
| `dropRoot` | root `a` leaves `roots` and is appended to `pending`; heap unchanged | `a ∈ roots` |
| `collect` | entry `a` is freed and its fields are queued | `a ∈ pending`, `a ∉ roots`, `Released heap a`, `heap a = some fs` |

`Steps n c₀ cₙ` is `n`-step execution.

---

## 4. Requirements: formal results (proved theorems)

| Theorem | Statement |
|---------|-----------|
| `reach_store` | The affine `store` move preserves reachability: shrinking the base by `f` is safe because the new edge `a → f` re-anchors `f` at `a` (needs `a ≠ f`) |
| `precise`/`invariant_preserved` | Every step preserves the full `Invariant` — all 10 components, for all four steps |
| `quiescent_no_leak` | At quiescence (`pending = []`), every live address is reachable from the roots alone — **garbage-freedom with no cycle escape clause** |
| `allocs_step` | Only `alloc` advances the counter; every other step is neutral |
| `allocs_bound` | After `n` steps, `allocs ≤ allocs₀ + n` — growth is paid for by allocation and nothing else |
| `invariant_is_invariant` | `Invariant` holds at the end of every execution |

---

## 5. Scope Limits (explicit non-claims)

These are deliberate and recorded so the theorem set is not over-read:

1. **No cardinality statement.** `|dom heap| ≤ |dom heap₀| + #allocs − #collects`
   requires a finite address domain (a bump pointer `nextAddr`). The heap is a
   total function here, so only the counting form (`allocs_bound`) is stated.
2. **No reclamation-completeness claim.** That every unreachable object is
   *eventually* freed requires cycle detection and a fairness argument on the
   collector; `Released` is a premise, not a theorem. Weak-reference cycles
   (`memory_model_spec.md` §2.6) remain the documented escape — and loop 94
   adds `weak_cut_released`: weakening a target's *only* strong in-reference
   (fields `Nodup`) makes it `Released`, so the escape demonstrably unblocks
   the very premise `collect` needs.
3. **Acyclicity is not derived — for arbitrary executions.** A5 plus A7 gives
   unique ownership and no self-loops; a cycle `a → b → a` still satisfies A5,
   and the `store` step permits building one. It *is* derived for executions
   that respect the **young-into-old construction discipline** (loop 94): a
   fresh object captures only already-allocated objects, so every strong edge
   runs from a strictly younger address to an older one (`StrongPath`) and no
   strong path returns to its origin (`strong_acyclic`). This is the same
   hypothesis under which Perceus (PLDI 2021) claims garbage-freedom —
   "cycle-free programs" — made explicit here as a construction discipline on
   the affine `store` move. Genuinely cyclic structures must cut each cycle
   with `Weak<T>` (§2.6 of the memory-model spec), and `weak_cut_released`
   shows the cut restores collectability.
4. **`collect` assumes `Released`.** Statically, `Iso` consumption guarantees
   it; dynamically it is the trial-deletion test (Bacon–Rajan 2001, as in
   Python's cycle collector). Making it a checked premise keeps this
   specification about the memory model rather than about the borrow checker
   (see ADR-013).

---

## 6. Traceability

| Requirement | Formalized in |
|-------------|---------------|
| SG-002 growth bound | `allocs_bound` |
| SG-002 no-leak | `quiescent_no_leak`, `invariant_preserved` |
| MMS-INV-008 (affine usage) | `Affine` (A1–A7), `store` rule |
| MMS-INV-009 (zero-copy affine moves) | `store` rule, `hAdd_live` |
| MMS-INV-014 (no tracing GC) | Step relation: only `collect` frees |
| MMS-INV-034 (young-into-old acyclicity, loop 94) | `StrongPath_lt`, `strong_acyclic`, `weak_cut_released` |

---

## Change Log

| Version | Date | Changes | Author |
|---------|------|---------|--------|
| 1.1.0 | 2026-10-31 | **Young-into-old acyclicity and the weak escape (research loop 94):** §5.3.3 narrowed to arbitrary executions — under the construction discipline, strong-heap acyclicity *is* derived (`StrongPath_lt`, `strong_acyclic` in Spec.lean); §5.3.2 note: `weak_cut_released` proves weakening a sole strong in-reference restores `Released`, so the §2.6 weak escape unblocks `collect`; traceability row for MMS-INV-034 added | Morph research loop 94 |
| 1.0.0 | 2026-10-15 | Initial specification: collector model, `Precise`/`Affine` invariants, four formal theorems, survey of Perceus/ORCA/Rust and the escape-clause argument | Morph research loop 2 |
