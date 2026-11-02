# Experiment Brief — Batch E0, first cycle (E-03, E-06, E-10, E-21–E-27)

**Status:** first cycle complete (loop 105, 2026-11-01).
**Register rows:** ADR-019, §2 (Batch 0 carry-forwards E-03, E-06, E-10),
§4 (Batch A E-21–E-25), §5 (Batch B E-26, E-27).
**Artifact:** `Morph/Specs/Earliest/{Spec,Lemmas,Examples}.lean`,
`Morph/Tests/Earliest.lean`.
**Grade now:** model L3 (no `sorry`, no axiom, warning-free build) for the
formal kernel; **claim L1** for the register rows, because no baseline was
benchmarked. The two grades are deliberately separate — see §5.

---

## 1. What was built, and what was not

The ten rows are Batch 0/A/B carry-forwards whose register entries name
large programmes (Itô-graded types, tropical scheduling, symplectic
integrators, Langlands compilation, holographic layout, Lefschetz thimbles,
fluctuation-typed speculation, chaos bounds, motivic backends, GIT
stability). Building those programmes is out of scope for one cycle and
would be dishonest to claim. What was built is the *computable core* each
row needs to be falsifiable, in the register's own terms (ADR-019 §1: a
decidable checking algorithm or computable synthesis procedure, plus a kill
criterion):

| Row | Kernel built | Key result |
|---|---|---|
| E-03 | `strategyOk`, `StrategyValid`, `stratOfIto`/`itoOfStrat` | acausality check is sound and complete; Itô↔Stratonovich round-trips |
| E-06 | `tadd`, `tmul`, `blockWCET`, `branchWCET` | semiring laws for the tropical ops; block sums, branch max dominates |
| E-10 | `shearX`, `shearY`, `leapfrog` | shears and leapfrog preserve the discrete symplectic area; leapfrog reverses |
| E-21 | `outEdges`, `synth`, `checkSim` | skeleton edges come from real transitions; checker implies simulation; identity and composition simulations |
| E-22 | `cutWeight`, `moveOut`, `extW`/`intW` | Kernighan–Lin move-delta formula; the moved vertex is gone |
| E-23 | `evalPoly`, `derivPoly`, `isCritical` | power rule (`derivAux_eval`); an accepted critical point zeroes the derivative |
| E-24 | `expectedCost`, `best` | the compiler's pick is optimal (`best_optimal`); cost is monotone in rollback |
| E-25 | `step`, `spread` | exact one-step expansion law; cone monotonicity; bounded-growth admission |
| E-26 | `evalKer`, `compileAff` | the affine closed form agrees with direct interpretation on every input; corpus conformance |
| E-27 | `mu`, `checkStable`, `findWitness` | stability check means no destabilizer in the sample; the witness is genuine; sign symmetry |

Not built: a quant library, a timing pass, an integrator package, a protocol
compiler, a placer, a pricing kernel, a scheduler, a checker backend, or a
stability prover. Every row remains an experiment whose *external* claim is
untested.

## 2. Research basis (per row)

- **E-03.** Itô vs Stratonovich calculus (Øksendal; the Stratonovich drift
  correction ½·b·∂b): with the factor 2 cleared (`A = 2a`) the conversion is
  exact integer arithmetic, hence decidable. Lookahead bias is the trading
  analogue of an acausal read; the checker rejects it the way a
  well-formedness check rejects a forward reference.
- **E-06.** Tropical / max-plus semirings (Baccelli–Cohen–Olsder–Quadrat;
  Cuninghame-Green) applied to WCET (Wilhelm et al.): straight-line cost
  adds, branch cost takes the max. The register's kill question — whether
  the max bound is tight — is asked about `branchWCET_ge`.
- **E-10.** Symplectic integrators (Hairer–Lubich–Wanner): Verlet/leapfrog
  is a palindromic shear composition, and shears have Jacobian determinant
  1. The kernel proves the shear structure, which is exactly what makes
  Verlet symplectic; the energy-drift bound is the benchmark, not a theorem
  here. Step sizes are unit-scaled integers (the ½ of textbook Verlet is
  cleared).
- **E-21.** Hecke operators as correspondences become, on finite protocols,
  transition preservers: handlers checked by finite-state simulation
  (Milner/CCS tradition). `synth` builds the event-loop skeleton;
  `checkSim` decides simulation on finite state/label sets; completeness
  ties skeleton edges back to real transitions.
- **E-22.** Balanced graph partitioning for placement, with the
  Kernighan–Lin move-gain formula as the checkable kernel: moving `v` out
  changes the cut by exactly `ext − int`. Ryu–Takayanagi names the register
  row; the KL delta is the formal content.
- **E-23.** Picard–Lefschetz theory: the contour deformation starts from a
  real critical point of the phase. The kernel is the verification side —
  Horner evaluation, the formal power rule, and the checked predicate
  `isCritical`. Search (finding the point) is the next iteration.
- **E-24.** The Crooks fluctuation relation constrains rollback likelihood;
  the compiler sets pipeline depth to the argmin of rollback-weighted cost.
  The kernel proves the pick optimal on any candidate list and cost monotone
  in rollback probability.
- **E-25.** OTOC / butterfly-cone scrambling (Maldacena–Shenker–Stanford)
  restricted to finite dependency graphs: spread is iterated neighbourhood
  expansion, and the integrable class (λ_L = 0) is the templates whose cone
  growth the checker admits. The one-step law is exact.
- **E-26.** Motives / realization functors (Voevodsky–Morel A¹-homotopy as
  documentation): one kernel source, two realizations, functoriality as the
  agreement theorem. Compiling to the affine closed form `x ↦ a·x + b` is
  the checkable fragment.
- **E-27.** Geometric invariant theory (Mumford): the Hilbert–Mumford
  numerical criterion μ(x,λ). The checker decides stability against a
  sampled subgroup list and returns the destabilizing witness the register's
  kill criterion demands.

## 3. Design decisions

1. **One module family, ten sections.** ADR-019 allows a brief to cover a
   coherent row family; the three-file pattern (ADR-004) forbids extra files
   per domain. `Earliest` holds all ten cores, with a mapping table in the
   `Spec.lean` docstring. Rows are separable into their own modules later
   without changing definitions.
2. **Integer arithmetic throughout.** Drift corrections clear the ½,
   expected costs are kept in thousandths, tropical weights are `Nat`, shear
   coefficients are `Int`. This keeps every identity decidable and every
   theorem elementary; continuous or stochastic effects are excluded by
   construction, which is stated rather than hidden.
3. **Finite, executable checkers.** `strategyOk`, `checkSim`,
   `checkStable`, `conformant`, `lyapZero` are all `Bool`-valued over finite
   inputs, so the register's "decidable checking algorithm" requirement is
   met literally and every example is `decide`-checked.
4. **Self-loops excluded from internal weight.** `intW` guards `v ≠ v`
   so a self-edge is never counted as internal affinity; the move-delta
   proof depends on it.
5. **Explicit-index derivative.** `derivAux` carries its starting index so
   the power rule (`derivAux_eval`) is an induction with no index
   arithmetic smuggled into the statement.

## 4. Implementation map and proof burden

| File | Lines | Content |
|---|---|---|
| `Morph/Specs/Earliest/Spec.lean` | 366 | 10 cores, mapping table, scope statement |
| `Morph/Specs/Earliest/Lemmas.lean` | 604 | 49 theorems, no `sorry`, no axioms |
| `Morph/Specs/Earliest/Examples.lean` | 224 | concrete instances incl. law witnesses |
| `Morph/Tests/Earliest.lean` | 190 | independent checks incl. negative cases |

Proof burden: 49 theorems over ~366 lines of definitions (ratio ≈ 1.6 proof
lines per definition line, excluding comments). All proofs are manual
`induction`/`simp`/`omega`; no SMT, no automation beyond core tactics. No
core file (`Morph.HIR`, `Morph.MIR`, `Morph.Semantics`) was touched, per the
register's trusted-core rule.

Build record (warm cache, this machine):

- `lake build Morph.Specs.Earliest.Lemmas` — success, 0 warnings.
- `lake build Morph.Tests.Earliest` — success (601 ms incremental).
- `lake build Morph Morph.Tests` — 420 jobs, success, 0 warnings, 0 `sorry`
  in the new files.

## 5. Validation log — what the cycle caught

The cycle is only worth its cost if it found defects. It found two, both in
the test layer rather than the proved kernel — evidence the layers are
genuinely independent:

1. **Unparseable minus sign in tests.** The first `Tests/Earliest.lean`
   draft used the Unicode minus U+2212 (`−4`) in four `Int` literals, which
   Lean 4 does not parse as negation — four parse errors, all caught by the
   build. Fixed to ASCII `-`; the remaining U+2212 occurrences in the family
   are inside comments only (verified by search).
2. **Fresh-instance discipline held.** Every test replays its row's laws on
   *new* instances (a fork protocol, a square cut, a quadratic phase, a
   two-region list, a star cone, a multiply-then-add backend) instead of
   re-deciding the examples. The one expositional risk this surfaced — which
   box a translated row names — was resolved at authorship because the build
   rejects a false witness.

## 6. Row status against the ADR-019 kill criteria

None of the external kill criteria can fire yet: they name baselines (agent
strategy corpora, MIR timing models, RTL sims, FIX protocol suites, Monte
Carlo pricers, wait-free hammer tests, GPU targets, pipeline sims) that no
harness in this repository exercises. Status per row:

| Row | Model grade | Claim grade | Kill criterion status |
|---|---|---|---|
| E-03 | L3 | L1 | untested — needs an agent-trial annotation-burden measurement |
| E-06 | L3 | L1 | untested — needs dynamic-control-flow confinement data |
| E-10 | L3 | L1 | untested — needs an energy-drift benchmark over required step counts |
| E-21 | L3 | L1 | untested — needs a 2-venue protocol synthesis trial |
| E-22 | L3 | L1 | untested — needs a placement win measured on multicore benchmarks |
| E-23 | L3 | L1 | untested — needs variance/latency vs baseline Monte Carlo |
| E-24 | L3 | L1 | untested — needs profiler-guided depth comparison on tail latency |
| E-25 | L3 | L1 | untested — needs hammer-test false-negative data |
| E-26 | L3 | L1 | untested — needs cross-backend divergence data from two real lowerings |
| E-27 | L3 | L1 | untested — needs known-good/known-stall pipeline configs from RTL sims |

No row is cut. No row is promoted to "supported" either: a proved kernel is
not a measured win.

## 7. Next iteration (repeat)

1. **E-23:** add critical-point *search* (existence), not just
   verification — the register's kill criterion turns on search cost.
2. **E-22:** iterate the move gain to a local optimum (KL sweep) and prove
   the sweep terminates with no improving move.
3. **E-24:** drive the depth choice from measured counters instead of a
   static list, so the profiler comparison becomes testable.
4. **E-27:** bound the sampling gap — either prove a completeness class for
   the sampled subgroups or exhibit a missed destabilizer as the recorded
   counterexample.
5. **E-21:** lift simulation to liveness (every specified request is
   eventually matched), which is the property a missed deadlock violates.
