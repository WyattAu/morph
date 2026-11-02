# Experiment Brief — BatchFGH first cycle (loop 108)

**Status:** first cycle complete (loop 108, 2026-11-01).
**Register rows:** ADR-019 §9 Batch F remainder (E-48–E-50), §10 Batch G
(E-51–E-55), §11 Batch H start (E-56, E-57).
**Artifact:** `Morph/Specs/BatchFGH/{Spec,Lemmas,Examples}.lean`,
`Morph/Tests/BatchFGH.lean`.
**Grade now:** model L3 (no `sorry`, no axioms, warning-free build) for the
formal kernel; **claim L1** for every register row, because no baseline was
measured. The two grades are deliberately separate — see §6.

---

## 1. What was built, and what was not

The ten rows name heavyweight theories (cluster algebras, Lieb–Robinson
bounds, Atiyah–Sutcliffe determinants, noncommutative Hodge theory,
Khovanov homology, Selberg trace, SUSY localization, cobordism anomalies,
Tannakian duality, Cuntz–Krieger algebras). Building those is out of scope
for one cycle and would be dishonest to claim. What was built is the
*computable core* each row needs to be falsifiable, in the register's own
terms (ADR-019 §1: a decidable checking algorithm or computable synthesis
procedure, plus a kill criterion):

| Row | Kernel built | Key result |
|---|---|---|
| E-48 | `Seed`, `mut0`, `seedPos` | mutation is an involution and preserves Laurent positivity |
| E-49 | `safeR`, `placeAll` | safe placements keep every mutator outside the cone |
| E-50 | `Pair2`, `gap`, `repel`, `repelN` | each repulsion step grows the gap by exactly two; separation is certified |
| E-51 | `msize`, `stepM`, `isNormal`, `normM` | every step shrinks the measure; fuel covering the measure reaches a normal form |
| E-52 | `bdyC`, `bdyD`, `cmap` | the pushforward commutes with the boundary; cycles map to cycles |
| E-53 | `alive`, `mids`, `route2`, `hopsAlive` | re-derived routes keep their endpoints and every hop is live |
| E-54 | `isum`, `total`, `pairSum`, `countGt`, `markov` | symmetric weights localize to the fixed locus; exceedances fit the Markov bound |
| E-55 | `within`, `aligned`, `admit`, `rejectReason` | admission is exactly the three checks; every rejection names its offender |
| E-56 | `XOp`, `AOp`, `transp`, `xrun`, `arun` | evaluation commutes with translation, per opcode and per program |
| E-57 | `DFA`, `run`, `reachN`, `minimize` | minimization preserves acceptance on in-budget words and never adds states |

Not built: a quote engine, a scheduler, an allocator, a macro system, a
network stack, a mesh model, a queueing library, a driver verifier, a
transpiler backend, a parser synthesizer. No benchmark, harness, or
measurement code was written. Every row remains an experiment whose
*external* claim is untested.

## 2. Research basis (per row)

- **E-48.** Fomin–Zelevinsky cluster algebras (exchange relation
  `x_k x'_k = M⁺ + M⁻`, Laurent phenomenon). The kernel is the
  exact-division content: mutation fires only with an explicit quotient
  witness, making involution provable and positivity checkable.
- **E-49.** Lieb–Robinson velocity as a discrete cone predicate. The kernel
  is the placement validator plus the soundness theorem (safe ⇒ outside
  every cone), which is the checkable form of zero-invalidation reads.
- **E-50.** Atiyah–Sutcliffe repulsion (`ln|Dₙ|` over configuration space,
  assumed heuristic per the register). The kernel replaces the potential
  with certified separation growth: the gap law is what a repulsion router
  must satisfy, proved by linear arithmetic alone.
- **E-51.** Noncommutative Hodge theory (Connes `B`, Kaledin–Kontsevich
  degeneration) as the termination metaphor. The kernel is the classical
  part that must exist first: a measure that drops on every rewrite plus a
  fuel-bounded normalizer with a coverage guarantee.
- **E-52.** Khovanov functoriality (`H(S)` for a cobordism `S`). The kernel
  is the commuting square on a two-state complex: boundary pushed forward
  equals boundary of the image, so conserved classes survive the reroute.
- **E-53.** Selberg trace philosophy (geodesics from spectrum) reduced to
  its checkable fragment: a liveness mask with direct-or-one-hop
  re-derivation. The theorems certify endpoints and per-hop liveness
  without graph traversal.
- **E-54.** Pestun localization (collapse to the `QV = 0` locus) in finite
  form: symmetric pair weights sum to fixed-plus-twice-representatives.
  The Markov bound is the closed-form tail estimate the register asks for,
  checked against the count.
- **E-55.** Freed–Hopkins anomaly check as a descriptor predicate. The
  kernel is two-way soundness (admit ⇔ checks pass) plus named-offender
  rejection, which is exactly the artifact the register names.
- **E-56.** Tannakian duality (fiber functors, `Isom(ω_x86, ω_ARM)`) reduced
  to its checkable fragment: a table map between two toy languages with
  per-opcode and per-program simulation laws.
- **E-57.** Cuntz–Krieger `K₀`-preserving moves reduced to the move with a
  complete proof: restriction to reachable states. Acceptance preservation
  (on in-budget words) plus state-count decrease are the timing-closure
  proxy the register asks for.

## 3. Design decisions

1. **One module family, ten sections.** Same three-file pattern as
   BatchDEF (ADR-004): `BatchFGH` holds all ten cores with a mapping table
   in the `Spec.lean` docstring. Rows separate later without changing
   definitions.
2. **Integer fragment throughout.** Everything is `Nat`/`Int`; no reals, no
   Mathlib (the `Spec` files import only `Std`). This forced two design
   wins: E-50 uses the gap law instead of nonlinear repulsion energy
   (`omega` cannot do squares), and E-54 states localization as an exact
   sum identity rather than an integral.
3. **No overlapping match patterns in checked definitions.** The first
   `stepM` draft used overlapping rewrite patterns; their equational
   lemmas did not fire under `simp only`, stalling the measure proof. The
   redexes became `if` guards on decidable equalities, which rewrite
   cleanly. See §5.
4. **Explicit `simp only` discipline, continued.** Same rule as BatchDEF:
   hypotheses are pre-derived into `= true` / `= false` equations, each
   `simp only` lists exactly the rules it fires, `omega` closes linear
   residues. All BatchDEF hazard rules re-fired here (negated `Bool`
   needs `reduceCtorEq`; `cases` substitutes the discriminant).
5. **Reachability without dedup.** `reachN` keeps duplicates and
   `minimize` filters the explicit state list instead, so no
   `eraseDups`/`nodup` API is needed; monotonicity is proved by
   `exists_eq_add_of_le` rather than induction on the `≤` proof (which
   trips the unused-variable linter).

## 4. Implementation map and proof burden

| File | Lines | Content |
|---|---|---|
| `Morph/Specs/BatchFGH/Spec.lean` | 396 | 10 cores, mapping table, scope statement |
| `Morph/Specs/BatchFGH/Lemmas.lean` | 408 | 32 theorems, no `sorry`, no axioms |
| `Morph/Specs/BatchFGH/Examples.lean` | 155 | 36 concrete instances, incl. law witnesses |
| `Morph/Tests/BatchFGH.lean` | 133 | 21 independent checks, incl. negative cases |

Proof burden: 32 theorems over ~340 lines of definitions. All proofs are
manual `induction`/`cases`/`simp only`/`omega`/`decide`; no SMT, no
automation beyond core tactics. No core file (`Morph.HIR`, `Morph.MIR`,
`Morph.Semantics`) was touched, per the register's trusted-core rule.

Build record (warm cache, this machine):

- `lake build Morph.Specs.BatchFGH.Spec` — ~10 s.
- `lake build Morph.Specs.BatchFGH.Examples Morph.Tests.BatchFGH` — ~9–40 s.
- `lake build` (full) — success, 0 warnings, 0 `sorry` in the new files.

## 5. Validation log — what the cycle caught

1. **`mul_comm` is unavailable with only `Std` imported.** The E-48
   involution needs `s.x * q = q * s.x`; the general lemma lives in
   Mathlib. Core `Int.mul_comm` covers it — the fragment stays
   Mathlib-free, but every algebraic fact must be re-checked against core.
2. **Overlapping patterns defeat `simp only`.** The first `stepM` used
   overlapping redex patterns; `simp only [stepM]` made no progress on
   them. Restructured with `if` guards (§3.3); the measure proof then went
   through unchanged in shape.
3. **`cases` substitution strikes again.** `rcases … with rfl` in
   `placeAll_sound` eliminated the mutator variable (same failure mode as
   BatchDEF `bfs_sound`); fixed with an underscore instantiation.
4. **Induction on a `≤` proof trips the unused-variable linter.**
   `induction h` consumes `h`, which the linter then flags. Replaced with
   `obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h` plus data induction.
5. **`decide` cannot see through `Prop` definitions.** `seedPos` is a
   conjunction, so `by decide` fails to synthesize an instance; the call
   site unfolds first (`by simp only [seedPos]; decide`). Same root cause
   as the BatchDEF `disj`/`Pairwise` finding.
6. **Metavariable discipline for law applications.** Five Tests
   applications initially left hypothesis variables to unification
   (`mut0_invol`, `massey`-style); all were made explicit following the
   BatchDEF rule — a `by decide` hypothesis must be concrete when written.

## 6. Row status against the ADR-019 kill criteria

None of the external kill criteria can fire yet: they name baselines
(matching-engine budget, NUMA placement, mutex/CAS race rates, expansion
savings, resync oracles, Dijkstra baselines, billion-sample MC, DMA fault
injection, native-compile oracles, heuristic FSM baselines) that no
harness in this repository exercises. Status per row:

| Row | Model grade | Claim grade | Kill criterion status |
|---|---|---|---|
| E-48 | L3 | L1 | untested — needs historical-feed phantom-spread events + latency budget data |
| E-49 | L3 | L1 | untested — needs tail-jitter win over NUMA-aware placement at equal core cost |
| E-50 | L3 | L1 | untested — needs race/contention rate vs mutex/CAS baseline |
| E-51 | L3 | L1 | untested — needs a diverging macro the depth limit misses, or cost comparison |
| E-52 | L3 | L1 | untested — needs chain-map replay vs resync oracle on failure traces |
| E-53 | L3 | L1 | untested — needs route quality/convergence vs Dijkstra on the same failures |
| E-54 | L3 | L1 | untested — needs closed form vs billion-sample MC agreement data |
| E-55 | L3 | L1 | untested — needs DMA/PCIe fault-injection misses + known-good descriptor suite |
| E-56 | L3 | L1 | untested — needs translated-binary divergence vs oracle + Rosetta-style cost |
| E-57 | L3 | L1 | untested — needs protocol-transition misses + timing closure vs heuristic baseline |

No row is cut. No row is promoted to "supported" either: a proved kernel is
not a measured replacement.

## 7. Next iteration (repeat)

1. **Measurement harnesses first.** As with BatchDEF, every row in §6 is
   blocked on a baseline plus a corpus. The next cycle should build the
   harnesses (feed replays, hammer benchmarks, fault injection, MC
   sampling, oracle diffing) before further kernel work.
2. **E-51:** the Hodge half is still missing — bound `HHₙ` finiteness over
   the finite rewrite fragment, with the `HP` decomposition as the
   admission certificate the register asks for.
3. **E-57:** the `K₀`/Bowen–Franks content is still missing — a
   state-split/merge move with the invariant preserved, plus a spectral
   radius proxy that actually decreases.
4. **E-52:** lift the complex past two states (a three-state chain with a
   nontrivial kernel element) and prove the class genuinely survives.
5. **E-53:** extend re-derivation past one intermediate (fuel-bounded BFS
   with the dead-set threaded through, i.e. the E-43 machine with
   liveness); prove completeness, not just soundness.
