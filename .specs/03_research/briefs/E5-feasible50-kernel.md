# E5 — Feasible-50 Kernel Brief (P1–P5, loop 110)

## 1. What was proved

50 rows from the 1,250-entry register (E4 triage), in five ten-row batches,
153 theorems total, `Std`-only, no `sorry`, no axioms, full `lake build`
green with 0 warnings.

| Batch | Rows | Theorems | Artifact |
|---|---|---|---|
| P1 verification + types | E-104, 113, 116, 120, 123, 124, 137, 141, 148, 149 | 38 | `BatchP1/` + `Tests/BatchP1.lean` |
| P2 concurrency | E-151, 156, 157, 159, 160, 161, 162, 163, 172, 174 | 26 | `BatchP2/` + `Tests/BatchP2.lean` |
| P3 models + storage | E-177, 178, 187, 199, 354, 355, 360, 362, 363, 366 | 26 | `BatchP3/` + `Tests/BatchP3.lean` |
| P4 wire/session | E-380, 381, 382, 383, 384, 385, 392, 393, 396, 398 | 29 | `BatchP4/` + `Tests/BatchP4.lean` |
| P5 everyday product | E-1455, 1460, 1463, 1468, 1469, 1470, 1484, 1487, 1489, 1490 | 34 | `BatchP5/` + `Tests/BatchP5.lean` |

## 2. Design decisions (recurring)

1. **Nat-first, Bool checks, List state.** Every core is `Nat`/`List`/`Bool`;
   `Int` appears nowhere; no real numbers, no physics.
2. **Checkers, not systems.** Each row is a certificate or accounting law:
   validator soundness (E-104), agreement = equality (E-113), transfer keeps
   uses (E-116), acceptance = no conflict (E-120), join bounds (E-123),
   hull validity (E-124), lifecycle exactness (E-137), brand equality
   (E-141), wildcard coverage (E-148), concatenation fields (E-149) — and
   likewise through P2–P5.
3. **Invariants made explicit after omega refused.** Three models were
   *false as first stated* and the prover caught it: credit windows need
   `used ≤ limit` (E-162), peephole framing needed no fix but the SPSC ring
   needs `head ≤ tail` for push and `head < tail` for pop (E-1469 — pop on
   an empty ring is underflow, not a no-op). These are the most valuable
   findings of the cycle: the kernel discipline doing its job.
4. **No `ring`, no `push_neg`, no Mathlib.** Nonlinear goals go through
   distribution lemmas + `omega`; negations are handled by `by_cases`/`cases`
   on the `Bool` test (the `Bool` reflection pattern), never `push_neg`.
5. **Three-file pattern throughout** (ADR-004); no core file touched.

## 3. Proof burden

153 theorems over ~600 definition lines (≈ 2.5 proof lines per definition
line). All manual induction/`simp`/`omega`/`decide`. Build record (this
machine): each `Spec` ~1 s, each `Lemmas` one `lake env lean` pass, each
`Examples`+`Tests` pair one 5-job build, all 0 warnings. Full `lake build`
green.

## 4. Validation log — what the cycle caught

1. **False statements, caught by omega (E-162, E-1469).** Admission-soundness
   without window validity, and pop-accounting on an empty ring, are false;
   both were fixed by stating the invariant (`windowOk`, `head < tail`)
   rather than weakening the theorem.
2. **`cases h : x` does not substitute.** The equation must be fed back with
   `subst`/`rw`, or avoided via `cases h : test` on `Bool` tests (P1 peephole,
   P4 token bucket). Recurring Lean datum, now recorded three times.
3. **`simp only` vs `if` conditions.** `Bool` tests in `if` conditions need
   full-`simp` reduction (`false = true` → `False` via simprocs); `simp only`
   with `if_true`/`if_false` alone gets stuck (P1 `popt`, P4 `takeB`).
4. **Anonymous-constructor inference (P1 `Instrument`/`Bundle`-class).**
   Explicit type ascriptions on list literals, same as the HIJ E-60 datum.
5. **`List.sum_append` unavailable.** Proved a local `sum_append'` by
   induction wherever batch-additivity is needed (P2, P5).
6. **Overlapping match patterns.** The P1 peephole rule was rewritten with
   an explicit `isZero` test plus `if`s; the equation lemmas are then
   unconditional and `simp` behaves.
7. **Reserved words.** `local`/`remote` as binders (P4 Lamport) — renamed.
8. **Wrong example numbers.** Two `allow_burst` witnesses cited hypotheses
   that `decide` refuted (arithmetic checked by hand wrong); fixed to
   boundary-exact values. Evidence the examples are really checked.

## 5. Row status

All 50 rows: model L3 / claim L1. Same standing as FGH/HIJ: no external
kill criterion is testable in-repo, so none fired and no row was cut. The
difference this cycle is direction: every batch was chosen for core
adjacency, and §6 names the wirings.

## 6. Core-continuation gate (agreed, from E4)

Frontier batch work stops here. Next is core progression. Prime integration
candidates from the 50, by shortest path to a real pass:

- E-104 → peephole-validator harness over MIR fragments.
- E-116 → certified liveness feeding DCE justification.
- E-123 → the shared monotone-framework engine for MIR analyses.
- E-137 → typestate checker on the matching-engine fragment.
- E-148 → GADT-refined exhaustiveness for the HIR match fragment.
- E-159 → record/replay scheduler for the matching fragment.
- E-162 → credit/flow-control bounds on the feed→engine path.
- E-178 → store-buffer model backing fence-sufficiency claims.
- E-383 → token-bucket limiter on the order path.
- E-1463 → static duality check for channelized concurrency.

Kill criteria for these ten become testable the moment each is wired to its
corpus + baseline; that wiring is the core-continuation work.
