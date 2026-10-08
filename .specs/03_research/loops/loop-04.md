# Loop 04 — 2026-09-19

Whole-repo sweep. Focus: the ADR-014 residual (residual consumption
strictness), the owed P5 source, and the loop-03 correction.

## Sources consulted

| Source | Problem | Access | Key finding used |
|--------|---------|--------|------------------|
| Reinking, Xie, de Moura, Leijen — *Perceus: Garbage Free Reference Counting with Reuse* (PLDI 2021; extended MSR-TR-2020-42), [MSR page](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/) | P5 | **fetched, abstract verified** | "We give a novel formalization of reference counting in a **linear resource calculus**, and prove that Perceus is **sound and garbage free**." Linearity is Perceus's formal substrate — the same precondition ADR-014 stage 1 now provides. |
| Oxide full text | P3 | **deferred to Loop 5** (context budget; P3's adjudication does not depend on it) | — |

## Adjudications

### Residual ADR-014 strictness: **FIXED (this loop's proof change)**

Loop 1's ADR-014 was implemented (stage 1, Loop 2) but one residual survived:
`lam_type` — the *unrestricted* arrow — pushed parameters with
`Usage.initialUsage`, giving ref-typed parameters `.zero` slots, on which the
consuming `bvar_type` could fire and break the binder's pinned output. An
unrestricted `lam 1 (refFree (bvar 0))` was still rejected.

Fix: **every push site in the judgment and the checker now pushes `.many`**
(`lam_type`, `let_type`, `for_type`, `ArmsTyped.cons`, and the checker's
mirrors). Contexts carry no obligations, per ADR-014. Acceptance test HT-36:
the unrestricted-arrow idiom now typechecks. HT-33–35 unchanged. The checker
and judgment now push *identically*, which tightens `InferenceSound`'s
correspondence to push-for-push exact.

`bvar_type` (the consuming rule) is retained: it remains provable from
hand-built `.zero` contexts, no test exercises it, and it documents the
alternative design. If a future loop confirms it is dead weight, it can be
removed then.

### P5 — Memory strategy: **ADJUDICATED — Perceus-style RC is the primary track**

The Perceus abstract settles the feasibility question: precise reference
counting is formalizable **in a linear resource calculus** and provably sound
and garbage-free. Morph now has the linearity substrate (linear arrows,
`iso` ownership, explicit `refFree`). Adjudication:

- **Primary track: Perceus-style RC.** `refFree` maps to the decrement/drop
  point; `iso` uniqueness maps to precise (non-overlapping) ownership; reuse
  analysis (FBIP) is a later optimization opportunity.
- **Constraint confirmed**: actors still need cross-actor reclamation policy
  (ORCA-style deferred drops) — orthogonal to the per-actor RC story.
- **CakeML's verified GC** remains the fallback formalization if RC proves
  wrong for the actor workload; the store's explicit `freed` list supports
  both.

This closes P5's decision *in principle* (RC primary, GC fallback); the
formalization of the RC discipline in the store semantics is future work
(register updated — it is beyond the 10-loop research scope and belongs to the
runtime milestone).

### Loop 3 correction (self-audit)

Loop 3's log wrongly stated `inferType` returns `none` for
`refLoad`/`refStore`/`refFree` — only `refCast` is store-typed-only; the other
ref forms infer soundly. Corrected here; P13's soundness theorem covers all
inferred forms.

## Spec changes made this loop

1. Register updated: P5 adjudicated (RC primary/GC fallback); loop-03
   correction recorded.

## Proof changes made this loop

1. **All judgment/checker push sites unified to `.many`** (Spec.lean:
   `lam_type`, `let_type`, `for_type`, `ArmsTyped.cons`, `inferTypeC`;
   TypeChecker.lean: `checkType`). Weakening/substitution infrastructure
   restated in `.many` form (`Lemmas.lean`, `Preservation.lean`);
   `InferenceSound.lean` cases updated — correspondence now push-for-push
   exact.
2. **HT-36** acceptance test added.

## Open questions carried to Loop 5

1. Owed full texts: Oxide, Pony paper (Perceus now verified).
2. **ADR-014 stage 2**: revert `HasType`'s signature threading — the
   plumbing is inert (every rule passes through, `bvar_type` is
   hand-context-only) but it is unused complexity; the revert also collapses
   `bvar_type`/`bvar_type_many`.
3. **P6 default-REJECT fires at this loop's end**: `EffectSet` is unused and
   no effect design has been adjudicated. Per the Loop 2 disposition, delete
   it unless a design proposal appears.
4. P13 completeness (checker finds the most general type) — stretch, unscheduled.
