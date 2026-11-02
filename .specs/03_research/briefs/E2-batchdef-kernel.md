# Experiment Brief — BatchDEF first cycle (loops 105–107)

**Status:** first cycle complete (loop 107, 2026-11-01).
**Register rows:** ADR-019 §7 Batch D remainder (E-38–E-40), §8 Batch E
(E-41–E-45), §9 Batch F start (E-46, E-47).
**Artifact:** `Morph/Specs/BatchDEF/{Spec,Lemmas,Examples}.lean`,
`Morph/Tests/BatchDEF.lean`.
**Grade now:** model L3 (no `sorry`, no axioms, warning-free build) for the
formal kernel; **claim L1** for every register row, because no baseline was
measured. The two grades are deliberately separate — see §6.

---

## 1. What was built, and what was not

The ten rows name heavyweight theories (derived algebraic geometry,
Connes–Kreimer renormalization, geometric quantization, arithmetic topology,
GMT, families index, thermofield dynamics, inverse scattering, deformation
quantization, causal fermion systems). Building those is out of scope for one
cycle and would be dishonest to claim. What was built is the *computable
core* each row needs to be falsifiable, in the register's own terms
(ADR-019 §1: a decidable checking algorithm or computable synthesis
procedure, plus a kill criterion):

| Row | Kernel built | Key result |
|---|---|---|
| E-38 | `loadsOK`, `firstBad`, `satCount`, `solve` | solver is feasible exactly on clean instances; a blocked certificate names a genuine violation plus the true satisfied/total fraction |
| E-39 | `eval`, `prune`, `cuts`, `neg` | slicing preserves the value; every cut splits the value; negation negates it |
| E-40 | `lowerReg`, `lowerStack`, `evalCells` | both polarizations agree observationally and hold exactly `2n` cells |
| E-41 | `reachE`, `hasTwoCycle`, `hasCycle`, `massey3` | a firing Massey kernel forces a global cycle and certifies no back-edges |
| E-42 | `packAux`, `extents`, `disjointCheck` | the checker is sound and complete for pairwise disjointness; greedy packing always certifies |
| E-43 | `isPath`, `checkPath`, `bfs`, `deform` | BFS finds admissible reroutes; deformation preserves both endpoints |
| E-44 | `Entry`, `upsert`, `reconcile`, `findK`, `best` | reconciliation invents nothing; lookup reads the max version; upsert is idempotent |
| E-45 | `isBound`, `scatter`, `reconstruct`, `sumsq` | masks and filters rebuild the signal; energy splits exactly; counts preserved |
| E-46 | `bracket`, `cross`, `corr`, `star` | the bracket is antisymmetric; reversal negates the correction; the product reflects around the classical sum; vanishing brackets give the classical limit |
| E-47 | `EvOp`, `disc`, `classify`, `needsFence` | every operator gets a verdict; spacelike and timelike never coincide; small non-negative discriminant is lightlike |

Not built: an SOR solver, an optimizer pass, a backend generator, a deadlock
oracle, a layout pass, an FPGA toolchain, a replication protocol, a signal
library, an STM, a coherence classifier. No benchmark, harness, or
measurement code was written. Every row remains an experiment whose
*external* claim is untested.

## 2. Research basis (per row)

- **E-38.** Lurie–Toën derived algebraic geometry (Tor-defect execution of
  the fiber product) as the metaphor; the falsifiable part is the graded
  outcome discipline — feasible route vs. obstruction certificate carrying
  the maximal feasible fraction — which is standard deferred-reconciliation
  practice in constraint solving.
- **E-39.** Connes–Kreimer `H_CK` (coproduct `Δ(T)`, antipode `S(T)`) and
  BPHZ renormalization. The kernel is the optimizer reading: `cuts` is the
  coproduct (every subtree paired with its countertermed remainder), `neg`
  is the antipode, `prune` is DCE, and the theorems are value preservation.
- **E-40.** Kostant–Souriau prequantization (polarizations, BKS pairing).
  The kernel is the falsifiable fragment the register asks for: one kernel
  spec, two polarizations, observable agreement plus phase-volume (`2n`
  cells) preservation.
- **E-41.** Mazur–Kapranov–Reznikov arithmetic topology; Massey products as
  the higher-order linking invariant, with the Borromean rings as the
  ternary case with vanishing pairwise links. The kernel is the `n = 3`
  decision procedure plus soundness (fires ⇒ a real cycle) and exclusion
  (fires ⇒ no back-edges, so pairwise checks genuinely miss it).
- **E-42.** Federer–Fleming GMT (rectifiable currents, mass, boundary).
  First-fit layout is the mass-minimizing polyhedral approximation at fixed
  ABI boundary; the certificate is pairwise disjointness, proved sound and
  complete for the checker.
- **E-43.** Atiyah–Singer families index; the anomaly locus as the
  obstruction, deformation as the repair. The kernel is admission checking
  plus fuel-bounded BFS rerouting with endpoint preservation — the artifact
  the register names (the path deformer).
- **E-44.** Umezawa thermofield doubling (`H ⊗ H̃`); reconciliation as
  tracing out the failed side. The kernel is the max-version merge with its
  three laws: nothing invented, newest wins, repetition stable.
- **E-45.** Gardner–Greene–Kruskal–Miura IST (direct scattering → discrete
  eigenvalues vs. continuous reflection → GLM inversion). The discrete
  analog: bound/radiation split by a magnitude threshold, exact
  reconstruction by position mask, Parseval-style energy identity.
- **E-46.** Kontsevich formality (`f ⋆ g`, first-order bracket correction).
  The kernel is order-explicitness: antisymmetry makes reversal negate the
  correction, and the `⋆`-product reflects around the classical sum.
- **E-47.** Finster causal fermion systems (causality read off the spectrum
  of the operator product). The 2×2 discriminant is the spectral readout:
  negative means spacelike, large positive means timelike, the degenerate
  remainder is lightlike; the verdicts are disjoint by construction.

## 3. Design decisions

1. **One module family, ten sections.** ADR-019 allows a brief per coherent
   row family; the three-file pattern (ADR-004) forbids extra files per
   domain. `BatchDEF` holds all ten cores, with a mapping table in the
   `Spec.lean` docstring. Rows separate into their own modules later without
   changing definitions.
2. **Integer fragment throughout.** Everything is `Nat`/`Int`; no reals, no
   Mathlib (the `Spec` files import only `Std`). This keeps every example
   `decide`-checkable and every theorem elementary; it excludes continuous
   magnitudes, real spectra, and actual layout geometry by construction,
   which is stated rather than hidden.
3. **Fuel only where the register already uses it.** `bfs` (E-43) and
   `reachE` (E-41) are fuel-bounded, following the E-31 precedent; every
   other recursion is structural, so no termination arguments were needed.
4. **Explicit `simp only` proof discipline.** Hypotheses are pre-derived
   into `= true` / `= false` equations (the BatchBCD pattern) and each
   `simp only` lists exactly the rules it fires; `omega` closes the linear
   arithmetic residues. Full `simp` with hypotheses in context proved
   unpredictable (implication residuals, orientation chaos) and is banned
   from this module. See §5.
5. **Threshold IST, not spectral IST.** Computing actual discrete eigenvalues
   would need a real eigensolver; the checkable fragment of "alpha vs.
   noise" is the magnitude threshold `κ`, and the theorems (roundtrip,
   Parseval, count preservation) are the ones a threshold implementation
   must satisfy.

## 4. Implementation map and proof burden

| File | Lines | Content |
|---|---|---|
| `Morph/Specs/BatchDEF/Spec.lean` | 460 | 10 cores, mapping table, scope statement |
| `Morph/Specs/BatchDEF/Lemmas.lean` | 1047 | 76 theorems, no `sorry`, no axioms |
| `Morph/Specs/BatchDEF/Examples.lean` | 192 | 45 concrete instances, incl. law witnesses |
| `Morph/Tests/BatchDEF.lean` | 171 | 29 independent checks, incl. negative cases |

Proof burden: 76 theorems over ~400 lines of definitions (ratio ≈ 1.6 proof
lines per definition line, excluding comments). All proofs are manual
`induction`/`simp only`/`omega`/`decide`; no SMT, no automation beyond core
tactics. No core file (`Morph.HIR`, `Morph.MIR`, `Morph.Semantics`) was
touched, per the register's trusted-core rule.

Build record (warm cache, this machine):

- `lake build Morph.Specs.BatchDEF.Lemmas` — ~6.5 s.
- `lake build Morph.Specs.BatchDEF.Examples Morph.Tests.BatchDEF` — ~8–17 s.
- `lake build` (full) — success, 0 warnings, 0 `sorry` in the new files.

## 5. Validation log — what the cycle caught

The cycle is only worth its cost if it found defects. It found eight:

1. **Sign error in the E-46 examples.** The first draft asserted
   `corr [1, 2, 3] = 4` and `star [1, 2, 3] = 10`; `decide` proved both
   *false*. The bracket reads `bracket a b = a − b` with the earlier
   element first, so ordered-pair corrections over an increasing window
   are negative: `corr = −4`, `star = 2`. The theorems were right; the
   examples were wrong — evidence the checks are independent of the
   statements.
2. **`cases h : p.head?` substitutes into the goal.** In `deform_ends` the
   branch goals became `q.head? = some s ∧ q.getLast? = some d`, so
   `rw [hb.1, hs]` rewrote a goal that no longer mentioned `p.head?`.
   Fixed by proving the substituted goals directly (`⟨hs, hd⟩`,
   `⟨hb.1, hb.2.2.2⟩`).
3. **`cases h : some r = some q` eliminates a variable.** In `bfs_sound`
   the successor variable `r` vanished from scope (`unknown identifier`).
   Fixed with an explicit equation plus `subst`, keeping `r` for the
   downstream membership and invariant applications.
4. **Full `simp` with hypotheses is unpredictable.** The E-44 hit/miss
   branches left implication residuals (`¬e.key = k → …`) and unused-arg
   warnings from hypothesis reorientation. Converted to explicit
   `simp only` with pre-derived equations; the discipline in §4.4 is the
   result.
5. **Negated `Bool` conditions need `reduceCtorEq`.** A negated hypothesis
   normalizes to an inner rewrite (`isBound t x → false`), leaving
   `if false = true`, which `if_false` cannot fire without `reduceCtorEq`.
   Systematic rule, applied across E-43/E-44/E-45.
6. **`List.reverse_cons` is an equation, not a function.** Applying it to
   arguments is an error; the E-46 reversal facts use `by simp` instead.
7. **Parenthesized dot-notation builds a redex.** `((xs ++ l₂).map)
   (bracket x)` elaborated to `(fun f => List.map f …) (bracket x)`, which
   `rw [List.map_append]` cannot match. The helper was dropped in favour
   of `map_append`/`lsumI_append` inside `simp only`.
8. **No Mathlib in the fragment.** `add_zero` is unknown with only `Std`
   imported, so ground arithmetic residues (`0 + 0 = 0`) are closed with
   `omega`, not lemma names; `lsumI_append` had to precede `corr_append`
   (no forward references).

## 6. Row status against the ADR-019 kill criteria

None of the external kill criteria can fire yet: they name baselines (SOR
path latency, MIR benchmark corpus, two-backend maintenance cost,
project stress-test deadlocks, L1-split measurements, DPR simulation,
crash traces, FIR/IIR feeds, CAS-lock baseline, coherence simulation)
that no harness in this repository exercises. Status per row:

| Row | Model grade | Claim grade | Kill criterion status |
|---|---|---|---|
| E-38 | L3 | L1 | untested — needs SOR-path latency comparison + reconciliation-log usage data |
| E-39 | L3 | L1 | untested — needs slice minimality / compile time on the benchmark corpus |
| E-40 | L3 | L1 | untested — needs cross-target divergence + maintenance-cost data |
| E-41 | L3 | L1 | untested — needs a stress-test ternary deadlock escaping pairwise detection |
| E-42 | L3 | L1 | untested — needs measured L1-split / false-sharing win on real structs |
| E-43 | L3 | L1 | untested — needs a sim-observed glitch corpus + known-good path suite |
| E-44 | L3 | L1 | untested — needs failover latency / loss on identical crash traces |
| E-45 | L3 | L1 | untested — needs alpha sharpness / latency vs linear filters on same feeds |
| E-46 | L3 | L1 | untested — needs oracle determinism + cost vs CAS-lock baseline |
| E-47 | L3 | L1 | untested — needs coherence-simulator interference + coordination-saving data |

No row is cut. No row is promoted to "supported" either: a proved kernel is
not a measured replacement.

## 7. Next iteration (repeat)

1. **Measurement harnesses first.** Every row in §6 is blocked on the same
   thing: a baseline and a corpus. The next cycle should build one
   data-only harness per row family (SOR traces, MIR corpus runs,
   struct-layout measurements, DPR sim traces, crash traces, filter feeds)
   before any further kernel work — that is the first point at which a kill
   criterion becomes testable.
2. **E-41:** mine the project's own stress tests for a ternary deadlock
   that escapes `hasTwoCycle`; that single datum decides the row.
3. **E-46:** add the second correction term the register asks for and check
   it against the serialized oracle on a contention corpus.
4. **E-43:** prove BFS completeness (an admissible path is always found),
   not just soundness — that is the other half of the deformer contract.
5. **E-38:** prove the fraction maximal (`satCount` is the true maximum),
   which needs the optimality argument the current fraction lemmas omit.
