# ADR-019: Frontier Research Dispositions — Acceptance Rule and Concept Verdicts

## Status
**Accepted** (2026-10-31). Amended same-day per maintainer directive:
**breadth-first implementation — no creative/research direction is cut on
taste alone; cuts require proof results and execution results
post-implementation.** Prior `R-*` verdicts in this file are therefore
reclassified from "Rejected" to "Tracked-open": every concept stays in the
register until an implementation plus its proof-burden log and execution
record trigger its kill criterion. This ADR records the standing register so
that nothing is lost and every future cut is evidence-based.

## Context

External review surveys proposed 55+ frontier concepts. This register now
covers all of them — nothing dropped:

Batch 0 (~35, original register): data-oriented design, compile-time
execution, value semantics, effects, structured concurrency,
content-addressed code, tensor/tiling architectures, arena-first memory,
dependent types, choreographic programming, refinement/SMT types, ZK
arithmetization, differential dataflow, spatial IRs, e-graphs, QTT, cubical
type theory, linear capabilities, differentiable semantics, quantum types,
concurrent separation logic, polyhedral compilation, relational synthesis,
probabilistic programming, directed HoTT, indefinite causal orders, epistemic
types, synthetic topology, optimal reduction, ludics, relativistic semantics,
game semantics, coalgebra, polygraphs, ordered linear logic, sheaf consensus,
gauge semantics, non-standard analysis, reversible computing, tropical
scheduling, SDG, path integrals, p-adic memory, symplectic types, braided
concurrency, spectral triples, Itô-graded types, ZX-calculus, derived
categories, directed topology, contact geometry, SUSY types, Malliavin
calculus, OPE tick feeds, mirror-symmetry compilation, holonomy consensus,
RG-flow optimization, Wasserstein allocators, APS crash tolerance.

Batch A (5, geometric representation / holography / non-equilibrium /
Picard-Lefschetz / chaos): E-21 geometric Langlands S-duality compilation,
E-22 Ryu-Takayanagi holographic interconnect layout, E-23 Picard-Lefschetz
thimbles for pricing kernels, E-24 Jarzynski-Crooks fluctuation-typed
speculation, E-25 OTOC / Lyapunov chaos bound for wait-free memory.

Batch B (5, motivic / GIT / bootstrap / Chern-Simons / twisted K-theory):
E-26 motivic IR, E-27 GIT Hilbert-Mumford pipeline stability, E-28 conformal
bootstrap latency bounds, E-29 Chern-Simons anyonic matching, E-30 twisted
K-theory hot-reload anomaly check.

Batch C (5, BV / Atiyah-Bott / Osterwalder-Schrader / Frobenius / Ramanujan):
E-31 BV master-equation memory safety, E-32 Atiyah-Bott risk localization,
E-33 OS reflection positivity for event sourcing, E-34 Frobenius/WDVV optimal
execution, E-35 Ramanujan expander interconnects.

Batch D (5, Baker-Norine / PT-symmetric / derived AG / Connes-Kreimer /
geometric quantization): E-36 Baker-Norine chip-firing arbitration, E-37
PT-symmetric exceptional-point telemetry, E-38 derived-AG over-constrained
routing, E-39 Connes-Kreimer Hopf AST slicing, E-40 Kostant-Souriau
quantization backend generator.

Batch E (5, arithmetic topology / GMT / families index / TFD / IST): E-41
arithmetic-topology Massey deadlock check, E-42 GMT rectifiable-current cache
packing, E-43 families-index glitch-free FPGA reconfiguration, E-44
thermofield state failover, E-45 IST soliton signal processing.

Batch F (5, formality / CFS / cluster algebras / Lieb-Robinson /
Atiyah-Sutcliffe): E-46 Kontsevich formality transaction quantization, E-47
causal-fermion spectral causality, E-48 cluster-algebra totally-positive
books, E-49 Lieb-Robinson cache isolation, E-50 Atiyah-Sutcliffe
non-interference repulsion.

Batch G (5, NC Hodge / Khovanov / Selberg / SUSY localization /
Freed-Hopkins): E-51 NC Hodge macro termination, E-52 Khovanov cobordism
reconfiguration, E-53 Selberg hyperbolic routing, E-54 Pestun localization
tail latency, E-55 Freed-Hopkins kernel-bypass safety.

Batch H (5, Tannakian / Cuntz-Krieger / Sato / Conley / perfectoid): E-56
Tannakian cross-ISA transpilation, E-57 Cuntz-Krieger FPGA parsers, E-58 Sato
Grassmannian buffer dynamics, E-59 Conley-index AMM stability, E-60
Fargues-Fontaine multi-currency semistability.

Batch I (5, Hitchin / Kempf-Ness / ADHM / Berkovich / SLE): E-61 Hitchin
spectral liquidation, E-62 Kempf-Ness zero-thrash scheduling, E-63 ADHM
instanton arbitrage check, E-64 Berkovich Fatou speculation guard, E-65 SLE
liquidity percolation execution.

Batch J (5, microlocal / wall-crossing / surface codes / NC motives /
Borcherds): E-66 microlocal wave-front race freedom, E-67 Bridgeland-KS
flash-crash guard, E-68 homological surface-code SRAM, E-69 NC-motive
side-channel freedom, E-70 Borcherds automorphic compression.

Batch K (5, paradigm-killers I): E-71 constructive bi-abduction memory, E-72
hardware interaction combinators, E-73 zero-cost effect inlining, E-74
differential catamorphic memory, E-75 SMT-discharged sized refinements.

Batch L (5, paradigm-killers II): E-76 e-graph superoptimization, E-77 O(1)
invertible AD semantics, E-78 categorical hardware extraction, E-79
choreographic BFT projection, E-80 Kan-extension zero-copy interop.

Batch M (5, OS / typing / silicon / projectional / relativistic): E-81
proof-carrying SASOS capabilities, E-82 zero-cost gradual typing, E-83
spatial in-memory categorical silicon, E-84 projectional semantic graphs,
E-85 Lorentz-covariant spacetime semantics.

Batch N (5, arithmetic / persistence / totality / capabilities / filters):
E-86 Gosper–Vuillemin continued-fraction arithmetic, E-87 orthogonal
persistent toposes, E-88 total productive coinduction, E-89 cryptographic
capability tagging (CHERI-limit), E-90 decidable filter-model principal
typings.

Batch O (5, testing / consensus / indexes / branches / optics): E-91
coalgebraic bisimulation testing, E-92 lattice CALM/I-confluence
coordination-freedom, E-93 information-geometric learned surjections, E-94
wave-interference multi-path silicon, E-95 all-optical holographic routing.

Batch P (5, clocks / migration / univalence / memory / annealing): E-96 QDI
asynchronous micropipelines, E-97 Spivak functorial data migration, E-98
univalent semantic transport, E-99 volumetric uniform-latency memory, E-100
Ising spin-glass ground-state compute.

Unfiltered adoption without a register would destroy the project (metaphors
without decision procedures mixed with genuine breakthroughs). Unfiltered
rejection would forfeit breakthroughs. This ADR is the register: acceptance
rule + per-concept scope, grade target, implementation shape, and kill
criterion that can only fire on proof + execution evidence.

## Decision

### 1. The acceptance rule (applies to all future proposals)

> **A research idea enters Morph iff it comes with a decidable checking
> algorithm or a computable synthesis procedure operating on our IR, plus a
> stated kill criterion. Beautiful mathematics without a decision procedure
> is tracked, never built.**

Operating rules under the breadth-first directive:

- Every registered experiment ships with three artifacts from its first
  commit: implementation (flagged or side-module, never entangled with the
  stable core), proof-burden log (proof:code ratio, auto vs manual discharge,
  stuck points), execution record (latency distributions, size, compile time,
  one agent trial).
- The trusted core (`Morph.HIR` → `Morph.MIR` lowering plus the `WF` checker
  family) stays frozen during experiments. Experiments attach as dialects in
  and backends out. An experiment needing core changes logs that fact as a
  finding with its proof cost.
- Proof grades apply to experiments: L0 (typechecks/runs), L1
  (`decide`-able checks + examples), L2 (solver-discharged), L3 (fully
  proved). Promotion is the decision process; demotion is allowed without
  shame — but only on proof/execution evidence, never on taste.
- No concept leaves this register without (a) an implementation attempt,
  (b) a proof result, (c) an execution result. Prior `R-*` labels below are
  retained as history but reclassified as tracked-open.

### 2. Accepted for experiment, Batch 0 (5, carried forward)

| ID | Concept | Scope | Kill criterion (fires only post-implementation) |
|----|---------|-------|-----------------------------------------------|
| E-03 | Filtration-graded Itô/Stratonovich types | Quant dialect only, L2/L3. Tag-checking + acausality (lookahead-bias) rejection first; Itô-drift-correction synthesis second. | Annotation burden per strategy exceeds what the agent trial produces in ≤3 iterations → demote to lint. |
| E-06 | Tropical max-plus timing analysis | WCET/latency-bound pass over straight-line MIR (exact there), L1/L2. | Dynamic control flow forces over-approximation that makes bounds useless → confine to straight-line fragment permanently. |
| E-10 | Certified symplectic integrators (library, not type system) | Quant-simulation dialect imports (Verlet/leapfrog with proved preservation), L3. | Energy-drift bound unprovable over required step counts → drop. |
| ZX-q | ZX-calculus IR, quantum-dialect only | Admitted iff Morph grows a quantum dialect; completeness used is stabilizer/Clifford+T only. | No end-to-end classical win required — scope is quantum from the start. |
| DAT-s | Directed-topology deadlock analysis, fixed protocols only | L3 verification targets for finite fixed protocols (one consensus round, one driver handshake). Never a general compiler pass. | Directed-homology computation fails to beat explicit model checking on the target protocol → drop. |

### 3. Batch 0 tracked-open (15, reclassified per 2026-10-31 directive — was "Rejected", now open pending proof + execution)

| ID | Concept | Why it looked weak | Reopen / kill condition (evidence-gated) |
|----|---------|-------------------|------------------------------------------|
| T-01 | Knot invariants (Jones/HOMFLY-PT) for races | #P-hard; races are unordered accesses, already decided by happens-before tracking. | Implement invariant pass on MIR concurrency fragment; kill iff no precision/false-positive win over happens-before on real programs with proof + measurements. |
| T-02 | Connes spectral triples for cache layout | No computable pipeline from Dirac commutators to placement. | Implement placement heuristic derived from the formalism; kill iff no measured L3-miss win over polyhedral/profile-guided placement. |
| T-04 | ZX-calculus as universal classical IR | Extraction (diagram → control flow) fails for general programs. | Implement source→diagram→binary on classical benchmarks; kill iff no win. Quantum-scoped ZX-q unaffected. |
| T-05 | Derived categories / six operations for joins | Duality is not an algorithm; joins need statistics. | Implement join-order pass; kill iff no win over cost-based optimizer on TPC-scale joins. |
| T-07 | SDG / smooth topos as language foundation | No LEM, no decidable point equality. Kept kernel: dual numbers for forward AD. | Kill as core foundation unless `decide`-compatible fragment exhibited; AD kernel proceeds as library experiment. |
| T-08 | Path-integral / RG-flow concurrency semantics | Partition functions over interleavings uncomputable. | Implement bounded-interleaving instantiation; kill iff no scheduler win with proof. |
| T-09 | p-adic address typing | Hardware exposes linear addresses + NUMA APIs. Kept kernel: NUMA-aware arenas. | Implement p-adic-typed allocator; kill iff no fragmentation win over jemalloc/mimalloc. |
| T-11 | Directed homology as general deadlock pass | Session types + structured concurrency already decide the tractable cases. Carve-out DAT-s stands. | General pass lives or dies on beating explicit model checking on fixed protocols with proof + timings. |
| T-12 | Contact geometry / Reeb-flow execution typing | Optimal control, not typechecking. Kept kernel: dissipation as graded-effect quantities. | Implement cost-graded effect tracking; kill iff annotation/proof burden exceeds payoff. |
| T-13 | ℤ₂-graded / SUSY types | θ² = 0 restates linearity. | Lives iff elaborator implementation shows expression win over affine types. |
| T-14 | Malliavin calculus as general compiler pass | Holds per payoff form, not per program. Carve-out: certified weights for discontinuous payoffs (L3 library). | General pass killed iff no per-program decision procedure; library carve-out judged on its own proof. |
| T-15 | OPE / Virasoro typing for tick feeds | No central charge of an order feed. Kept kernel: shedding as explicit effects. | Implement shedding-effect typing; kill iff no backpressure win. |
| T-16 | Mirror symmetry as CPU/FPGA compiler | No computable mirror map. Kept kernel: single-source HDL with checked equivalence. | Implement single-source flow; kill iff equivalence-check burden exceeds HLS baseline. |
| T-17 | Berry-holonomy consensus | Consensus is information-theoretic. | Implement loop-traversal protocol model; kill iff no fault-tolerance/latency win with proof. |
| T-18 | Wilsonian RG-flow compiler | No beta functions for programs. Kept kernel: equality saturation. | Implement RG-flavoured rewrite scheduler; kill iff no win over egg-style saturation. |
| T-19 | Wasserstein / gradient-flow allocators | No placement algorithm follows. Kept kernel: region/arena allocation. | Implement arena-phase allocator; kill iff no pause/fragmentation win. |
| T-20 | APS index / anomaly cancellation for crashes | Eta invariants don't recover nodes. Kept kernel: verified WAL / crash-recovery invariants (L3). | Implement WAL invariant proofs; kill iff proof cost exceeds payoff. |

Count note: T-ids preserve the original R-numbers (T-01, T-02, T-04, T-05,
T-07–T-09, T-11–T-20); there were never T-03/T-06/T-10 because those numbers
belong to the E-series.

### 4. Batch A — geometric representation / holography / stochastic analysis / chaos (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-21 | Geometric Langlands S-duality compilation (Kapustin–Witten; Hecke eigensheaves on `Bun_G`) | Do NOT implement full Langlands functor (not computable). Implement the falsifiable kernel: protocol DSL (curve + connection spec) → synthesised event-loop skeleton where packet handlers are checked as Hecke-type transition preservers (state-machine conformance check over finite marketplace/venue protocol). | Dialect experiment, L1→L2. | Kill iff synthesis fails on a 2-venue FIX-like protocol or generated handler has deadlock/divergence the conformance check misses. |
| E-22 | Ryu-Takayanagi holographic interconnect layout | Implement the computable kernel: thread-communication affinity graph → hyperbolic-embedding / min-cut placement pass over the NUMA/NoC topology model (Plateau/min-surface approximated as balanced graph partition + measured bisection). | Backend layout pass, L1→L2. | Kill iff no measured crossbar/NUMA win over profile-guided placement on the project's own multicore benchmarks. |
| E-23 | Picard-Lefschetz thimbles for pricing kernels | Implement symbolic pass on a restricted payoff IR: find real critical points, deform contour along downward flow of `Re(iS)`, emit positive-decaying kernel + residual-phase certificate. Start with 1-D oscillatory integrals (Fourier-type payoffs). | Quant-kernel library/dialect, L2/L3. | Kill iff variance/latency shows no win over baseline Monte Carlo on the same payoffs, or critical-point search dominates runtime. |
| E-24 | Jarzynski-Crooks fluctuation-typed speculation | Implement graded speculation effect: each speculative region carries predicted rollback probability + measured work distribution; compiler pass sets pipeline/speculation depth from the Crooks-derived bound and checks it against counters. | Effect-system experiment, L1/L2. | Kill iff bound never beats empirical profiler-guided depth on tail latency, or annotation burden exceeds agent-trial budget. |
| E-25 | OTOC / Lyapunov chaos bound for wait-free memory | Implement static scrambling check on wait-free structures (ring buffers, MPSC queues): bound information-spread velocity (butterfly cone) over the coherence model; certify integrable class (λ_L = 0) for approved templates. | Concurrency checker, L2/L3. | Kill iff check admits false negatives on hammer tests or restricts templates below hand-written baseline throughput. |

### 5. Batch B — motives / GIT / bootstrap / Chern-Simons / twisted K-theory (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-26 | Motivic IR (Chow motives, **A**¹-homotopy; backends as realization functors) | Do NOT implement motives as IR (no decision procedure). Implement the falsifiable kernel: single-source kernel DSL with two realization backends (CPU scalar + one vector/GPU target) plus functoriality conformance tests (same motive ⇒ same observable result across backends). | Multi-target experiment, L1/L2. | Kill iff cross-backend divergence escapes the conformance suite or backend cost exceeds maintaining two direct lowerings. |
| E-27 | GIT Hilbert-Mumford pipeline stability | Implement stability checker over a finite pipeline-parameter model (stage latencies, FIFO depths, retiming group action discretised): compute μ(x,λ) over sampled 1-PS subgroups; reject unstable configs with witness λ. | FPGA/ASIC pipeline config checker, L1/L2. | Kill iff checker rejects known-good pipelines or misses known stall configs from the project's own RTL sims. |
| E-28 | Conformal bootstrap latency bounds (SDPB) | Implement crossing-associativity encoding of a fixed 4-stage event pipeline (parse→signal→risk→wire) as polynomial constraints + SDP solve at build time; emit certified nanosecond upper bound. | Real-time bound pass, L2/L3. | Kill iff bounds are vacuous on the real engine or SDP solve time breaks the build loop. |
| E-29 | Chern-Simons anyonic matching engine | Do NOT implement topological matching as production path. Implement simulator experiment: orders as anyon charges, matching as fusion-rule evaluation (Verlinde table), jitter-invariance test harness comparing against central-sequencer baseline on identical feeds. | Simulator/dialect experiment, L0/L1. | Kill iff fusion matching diverges from price-time priority semantics or adds latency vs sequencer baseline. |
| E-30 | Twisted K-theory hot-reload anomaly check (Dixmier-Douady / AHSS d₃) | Implement the computable kernel: ABI-layout diff checker (struct offsets, vtables, TLS, calling convention) surfaced as H³-torsion-style obstruction report; hot-swap admitted iff obstruction vanishes. Category language is documentation; the checker is the artifact. | Toolchain checker, L1/L2. | Kill iff checker misses a real ABI-break segfault from the project's own reload tests or false-positives block routine reloads. |

### 6. Batch C — BV / Atiyah-Bott / Osterwalder-Schrader / Frobenius / Ramanujan (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-31 | BV formalism + quantum master equation for aliasing | Implement aliasing-as-gauge checker on MIR fragment with cyclic graphs: pointer/anti-field capability pairs, antibracket-style rewrite rules as canonical transforms, QME check `(S,S)=0`, `ΔS=0` as leak/dangle decision procedure over finite loan graphs. | MIR analysis experiment, L2/L3. | Kill iff check cost blows up on cyclic benchmarks or it admits leaks the borrow checker (ADR-011 stage 2) catches. |
| E-32 | Atiyah-Bott localization for risk aggregation | Implement equivariant-typed risk kernels where symmetric payoff integrals (rotational/scale/cash-flow invariance) lower to fixed-point sums; fall back to Monte Carlo otherwise. Start with closed-form basket/VaR templates. | Quant library, L2/L3. | Kill iff template coverage is too narrow or fixed-point evaluation loses to baseline MC on latency/accuracy. |
| E-33 | Osterwalder-Schrader reflection positivity for event sourcing | Implement replay/compaction checker: verify reflection-positivity-style kernel condition (positive-definiteness of the event-correlation Gram matrix) over bounded windows before parallel replay or compaction is admitted. | Event-log dialect, L1/L2. | Kill iff checker cost exceeds replay savings or it admits a causality violation the sequential replayer catches. |
| E-34 | Frobenius manifolds / WDVV optimal execution | Implement execution-trajectory synthesis on Frobenius-structured value functions (flat Dubrovin connection + Lax integration) for Almgren-Chriss-type liquidation; compare against numerical HJB baseline. | Quant execution library, L2/L3. | Kill iff trajectory quality/latency loses to grid HJB on the same impact models. |
| E-35 | Ramanujan expanders (Alon-Boppana) for interconnects | Implement Ramanujan-graph (LPS/`PGL₂(F_q)`) topology generator for NoC/FPGA routing model + Cheeger/mixing-time bound check; benchmark against dimension-order routing under bursty load. | Topology experiment (sim + FPGA model), L1/L2. | Kill iff congestion/head-of-line behaviour shows no win over baseline routing at equal wiring cost. |

### 7. Batch D — Baker-Norine / PT-symmetry / derived AG / Connes-Kreimer / quantization (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-36 | Baker-Norine chip-firing credit arbitration | Implement divisor-rank checker over the crossbar multigraph: credit distribution `D`, genus `g=|E|-|V|+1`; admit config iff `rank(D)≥0` (with `deg(D)≥g` fast path for FIFO sizing). | Hardware-model checker, L1/L2. | Kill iff rank computation dominates synth time or admitted configs still starve under adversarial packet tests. |
| E-37 | PT-symmetric exceptional-point telemetry | Implement EP-tuned congestion sensor model (gain/loss ring-buffer matrix at EP₂/EP₃) in the telemetry simulator; measure detection lead time vs linear watermark polling on identical microburst traces. | Telemetry experiment, L0/L1. | Kill iff no sub-polling-interval lead time on real traces or false-positive rate exceeds watermark baseline. |
| E-38 | Derived-AG over-constrained routing (Tor-defect execution) | Implement routing-constraint solver that returns graded outcomes: degree-0 feasible route, degree-1 obstruction certificate (which constraint pair conflicts + maximal feasible fraction) for deferred reconciliation instead of abort. | SOR constraint solver, L1/L2. | Kill iff solver latency exceeds current SOR path or reconciliation log goes unread/unused in agent trials. |
| E-39 | Connes-Kreimer Hopf AST slicing | Implement BPHZ-style DCE/CSE over MIR trees via coproduct/admissible-cut decomposition + antipode counterterm evaluation; compare minimality against iterative peeling passes. | Optimizer pass experiment, L1/L2. | Kill iff slice minimality or compile time loses to existing passes on the project's benchmark corpus. |
| E-40 | Kostant-Souriau geometric quantization backend generator | Implement the falsifiable kernel: single phase-space kernel spec lowered through two polarizations (register/dataflow vs stack/memory-mapped) with BKS-style conformance proof (observable spectra + phase-volume preservation tests). | Multi-target experiment, L1/L2. | Kill iff lowering diverges across targets or maintenance cost exceeds two direct backends. |

### 8. Batch E — arithmetic topology / GMT / families index / TFD / IST (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-41 | Arithmetic topology + Massey products for higher-order deadlocks (Mazur–Kapranov–Reznikov; Borromean ternary case) | Implement DGA/homology checker over finite module-interaction complexes: pairwise cycle check (Tarjan/toposort) first; when `H¹` cup products vanish, compute triple Massey `⟨u,v,w⟩ = [x∪w + u∪y]` as the ternary-deadlock decision procedure. Start at n=3. | Concurrency checker, L2/L3. | Kill iff no ternary deadlock from the project's own stress tests escapes pairwise detection but is caught here, or Massey computation cost exceeds bounded model checking on the same modules. |
| E-42 | GMT rectifiable currents for cache packing (Federer–Fleming; mass `M(T)`, boundary `∂T = Γ`) | Implement Plateau-style struct/SIMD packer: fixed ABI boundary `Γ`, mass-minimizing layout search over the 64-byte cache-line lattice via deformation-theorem-bounded polyhedral approximation; emit layout + split/false-sharing certificate. | Layout pass, L1/L2. | Kill iff no measured L1-split/false-sharing win over the existing SoA/tiling layout claims on real structs. |
| E-43 | Families index + Quillen holonomy for glitch-free FPGA DPR (Atiyah–Singer families, Bismut–Freed) | Implement reconfiguration-path checker over finite bitstream-config graph: reject paths crossing the anomaly locus (nontrivial Quillen holonomy / nonzero curvature witness); auto-deform path around it. Category language is documentation; the path deformer is the artifact. | FPGA toolchain checker, L1/L2. | Kill iff checker misses a sim-observed glitch or blocks known-good DPR paths. |
| E-44 | Thermofield dynamics for active-active failover (Umezawa doubling `H⊗H̃`) | Implement as state-replication protocol experiment: primary/standby as doubled state with reduced-density-matrix reconciliation (tracing out the failed side); measure failover latency vs sequence-number replay baseline. No superluminal claims — the artifact is the reconciler. | Redundancy experiment (sim + harness), L0/L1. | Kill iff failover latency/packet-loss shows no win over replay baseline on identical crash traces. |
| E-45 | IST soliton signal processing (KdV, Lax `Lψ = λψ`, GLM inversion) | Implement streaming-kernel experiment: direct scattering transform → split discrete eigenvalues `κₙ` (alpha) from continuous reflection `R(k)` (noise) → GLM reconstruction; compare dispersion/phase-lag vs FIR/IIR baselines on identical feeds. | Signal library, L1/L2. | Kill iff alpha sharpness/latency loses to linear filters on the same data. |

### 9. Batch F — formality / CFS / cluster algebras / Lieb-Robinson / Atiyah-Sutcliffe (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-46 | Kontsevich formality transaction quantization (`f⋆g`, `L∞` morphism, graph weights `w_Γ`) | Implement non-blocking composition for a bounded contention window: evaluate truncated `⋆`-product corrections (first-order bracket + one higher correction) for colliding order-book ops instead of lock/abort; check determinism against serialized oracle. | STM/concurrency experiment, L1/L2. | Kill iff truncated series diverges from oracle or costs more than CAS-lock baseline. |
| E-47 | Causal fermion systems for lock-free execution (Finster; causality from spectrum of `xy`) | Implement spectral-causality classifier on bounded operator models of thread events: spacelike (equal-modulus, nonreal spectrum) ⇒ zero-coordination path; timelike (real gapped spectrum) ⇒ ordered path. Compare against MESI/fence baseline in the coherence simulator. | Simulator experiment, L0/L1. | Kill iff classifier admits an interference the fenced baseline prevents, or coordination savings vanish. |
| E-48 | Cluster algebras + total positivity for order-book depth (Fomin–Zelevinsky mutation, Laurent phenomenon) | Implement quote-update engine on `Aₙ/Dₙ` cluster seeds: updates as mutations `x_k x'_k = M⁺ + M⁻`; invariant checker asserts Laurent positivity (no negative liquidity / inverted spread / zero-division) at line rate. | Execution invariant checker, L1/L2. | Kill iff checker misses a phantom-spread event from historical feeds or its latency exceeds the matching-engine budget. |
| E-49 | Lieb-Robinson velocity for cache-coherency bounds (`‖[A(t),B(0)]‖ ≤ c‖A‖‖B‖exp(−(d−v_LR|t|)/ξ)`) | Implement LR-cone placer: compute `v_LR` for the socket mesh model; place pricing readers outside mutators' LR light cones (`|t| ≥ d/v_LR`); verify zero-invalidation reads on hammer benchmarks. | Scheduler/placer pass, L1/L2. | Kill iff tail-jitter shows no win over NUMA-aware placement at equal core cost. |
| E-50 | Atiyah–Sutcliffe determinants for multi-agent non-interference (`Dₙ ≠ 0`, `|Dₙ| ≥ 1` on `Cₙ(R³)`) | Implement allocator guidance as repulsion potential `ln|Dₙ|` over (core × NUMA × offset) configuration space; route thread pointers along its gradient; test race rate vs mutex/CAS baseline. Conjectural inequality is assumed as heuristic, not proved. | Allocator experiment, L0/L1. | Kill iff race/contention rate shows no win over baseline or routing cost dominates. |

### 10. Batch G — NC Hodge / Khovanov / Selberg / SUSY localization / Freed-Hopkins (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-51 | NC Hodge + periodic cyclic homology for macro termination (Connes `B`, Kaledin–Kontsevich `E₁` degeneration) | Implement termination checker for the macro/comptime rewrite algebra `A`: bound `dim HHₙ(A)` finiteness check over the finite rewrite fragment + `HP` decomposition witness as the admission certificate instead of a raw depth limit. | Metaprogramming checker, L2/L3. | Kill iff checker admits a diverging expansion the depth limit catches, or its cost exceeds expansion savings. |
| E-52 | Khovanov homology for dynamic network cobordisms (categorified Jones, functorial `H(S): H(K₁) → H(K₂)`) | Implement state-carrying homology classes over finite network topologies: link-fail/reroute as cobordism `S` with explicit pushforward chain map; test invariant preservation vs pause-and-resync baseline on identical failure traces. | Distributed-state experiment, L1/L2. | Kill iff chain-map replay diverges from resync oracle or costs more. |
| E-53 | Selberg trace formula for hyperbolic routing (`Σh(rₙ)` ↔ geodesic lengths `ℓ(γ)`) | Implement spectral router: embed mesh topology in `H²` (Fuchsian `Γ ⊂ PSL₂(R)` model), compute Laplacian spectrum once, extract round-trip geodesics algebraically; re-derive on link failure without graph traversal. | Routing experiment (sim + mesh model), L1/L2. | Kill iff route quality/convergence loses to Dijkstra/Bellman-Ford on the same failures. |
| E-54 | Pestun SUSY localization for tail-latency distributions (`Q²=0`, `Z(t)` independent of `t`, `t→∞` to `QV=0`) | Implement exact-distribution evaluator for a BRST-typed queueing model: collapse the stochastic queue integral to the finite `QV=0` locus (matrix integral) and emit closed-form `P(latency>τ)`; validate against billion-sample MC on identical models. | Performance-analysis library, L2/L3. | Kill iff closed form disagrees with MC beyond tolerance or derivation cost exceeds empirical testing. |
| E-55 | Freed–Hopkins cobordism anomaly check for kernel-bypass drivers (`[α]=0 ∈ Ω_spin^{d+1}(BG)`) | Implement capability-characteristic checker over the user-space/NIC descriptor interface: admit raw DMA path iff the obstruction class vanishes; every rejection names the offending descriptor/offset. Cobordism language is documentation; the descriptor checker is the artifact. | Driver verifier, L2/L3. | Kill iff checker misses a DMA/PCIe fault from the project's own fault-injection tests or blocks known-good descriptors. |

### 11. Batch H — Tannakian / Cuntz-Krieger / Sato / Conley / perfectoid (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-56 | Tannakian duality for cross-ISA transpilation (`C ≃ Rep_k(G)`, `Isom(ω_x86, ω_ARM)`) | Implement transpiler fragment via fiber-functor intertwiner: abstract kernel semantics `C` projected through `ω_x86`/`ω_ARM` register models; solve register/flag mapping as representation equivalence on a fixed opcode subset; test output against native-compile oracle. | Transpiler experiment, L1/L2. | Kill iff translated binaries diverge from oracle or cost exceeds Rosetta-style DBT baseline. |
| E-57 | Cuntz–Krieger algebras for line-rate FPGA parsers (`O_A`, `K₀ ≅ Zⁿ/(I−Aᵀ)Zⁿ`, Bowen–Franks) | Implement parser minimizer: `SL(n,Z)` moves on the transition matrix preserving `K₀`/Bowen–Franks while minimizing spectral radius `ρ(A)`; emit minimal FSM and verify timing closure at target clocks vs heuristic-minimized baseline. | FPGA synthesis pass, L1/L2. | Kill iff minimized parser misses a protocol transition or fails timing where the baseline passes. |
| E-58 | Sato Grassmannian / KP hierarchy for buffer dynamics (`Gr(H)`, `τ`-function, Hirota equations) | Implement FIFO-sizing controller via `τ`-zero evaluation (Krichever data) on multiscale burst moments; drive drain as integrable flow with conserved Lax charges; test drop rate vs M/M/1-sized baseline under identical bursts. | Queue-controller experiment, L1/L2. | Kill iff drop/backpressure behaviour loses to baseline sizing. |
| E-59 | Conley index + barcodes for AMM stability (isolating `N`, `h(S)=[N₁/N₀]`, continuation) | Implement stability gate: track `CH_*(S_λ)` barcode over volatility/toxicity parameters; block quoting-parameter updates that induce birth/death transitions; test against crash-shock replay vs Lyapunov-gated baseline. | Risk-gate experiment, L1/L2. | Kill iff gate blocks profitable stable regimes or admits a runaway the baseline catches. |
| E-60 | Perfectoid / Fargues–Fontaine multi-currency semistability (`X_FF`, HN slopes `λᵢ`, `μ(E)=0`) | Implement HN-polygon evaluator over the multi-hop settlement graph: flag `μ(F)>0` sub-bundles as arbitrage signals and synthesize the restoring execution sequence; test P&L vs CIP-baseline router net of settlement risk. | Settlement experiment, L1/L2. | Kill iff signal P&L net of fees/risk loses to baseline or polygon computation breaks the execution loop. |

### 12. Batch I — Hitchin / Kempf-Ness / ADHM / Berkovich / SLE (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-61 | Hitchin systems + Higgs bundles for multi-asset liquidation (`h(E,Φ)=(Tr Φ,…,Tr Φⁿ)`, spectral `S={det(λI−Φ)=0}`, flow linear on `Jac(S)`) | Implement spectral-decoupling liquidator on a bounded venue/covariance model: compile impact tensors to `(E,Φ)`, evaluate Hitchin fiber, emit independent 1-D linear flows; compare slippage vs multi-asset Almgren–Chriss baseline. Full integrable-system proof is not required; the trajectory quality is. | Execution library, L1/L2. | Kill iff slippage/latency loses to baseline or spectral computation breaks the loop. |
| E-62 | Kempf–Ness + symplectic reduction for cluster scheduling (`X//G ≅ μ⁻¹(0)/K`, flow `dx/dt=−∇‖μ‖²`) | Implement imbalance-potential scheduler: cluster state as point of finite resource manifold, moment map `μ=0` as equilibrium, gradient descent on `‖μ‖²` as the migration policy; test bandwidth spent migrating vs round-robin/work-stealing on identical load traces. | Scheduler experiment (sim), L1/L2. | Kill iff migration overhead or tail latency loses to baselines, or flow oscillates on real traces. |
| E-63 | ADHM instanton check for atomic cross-venue arbitrage (`[B₁,B₂]+IJ=0`, real ADHM equation) | Implement matrix-commutator certifier for 4-leg bundles `(B₁,B₂,I,J)` on FPGA-model/sim: admit atomic route iff ADHM equations hold within tolerance; measure certify latency (target ≤3 systolic cycles in model) vs software leg-checker. | Arb-checker experiment, L1/L2. | Kill iff false-positive atomicity (filled-then-failed legs) escapes or certifier misses profitable routes the baseline takes. |
| E-64 | Berkovich Fatou/Julia speculation guard (`P¹_Berk`, equicontinuous `F(f)` vs chaotic `J(f)`) | Implement p-adic-stability speculation monitor over bounded branch model: stay in Fatou-like contractive regime, prune on approach to Julia-like chaotic boundary (branch-expansion metric); test flush rate vs unbounded speculation on identical traces. | Speculation experiment (sim), L0/L1. | Kill iff no flush-rate win over depth-limit baseline or pruner kills profitable speculation. |
| E-65 | SLE liquidity-percolation execution (`dg_t/dt=2/(g_t−ξ_t)`, `ξ_t=√κB_t`, `κ=6` crossing via Cardy `₂F₁`) | Implement conformal execution shaper: track liquidity-boundary map `g_t`, size iceberg slices to fractal `d=7/4` boundary; compare market impact vs TWAP/VWAP on identical replay. | Execution experiment, L1/L2. | Kill iff impact/adverse-selection loses to baselines on replay. |

### 13. Batch J — microlocal / wall-crossing / surface codes / NC motives / Borcherds (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-66 | Microlocal wave-front race freedom (Hörmander `WF(u)`, `WF(u)∩−WF(v)=∅`) | Implement cotangent non-interference check on finite thread-trace models: compute discrete `WF` directions per access stream; elide `mfence` iff Hörmander disjointness holds; validate against happens-before oracle + hammer tests. | Concurrency checker, L2/L3. | Kill iff elided fence admits a race the oracle catches, or elision rate is negligible. |
| E-67 | Bridgeland stability + KS wall-crossing for flash-crash guard (`φ=arg Z/π`, `arg Z(γ₁)=arg Z(γ₂)`, DT jump `ΔΩ`) | Implement stability-chamber tracker over fragmented-book state: central charge `Z` from depth/inventory model, distance-to-wall monitor, preemptive liquidity anchor before crossing; test on historical flash-crash replay vs volatility-gated baseline. | Risk-gate experiment, L1/L2. | Kill iff guard misses a replayed evaporation the baseline catches, or anchors cost more than slippage saved. |
| E-68 | Homological surface-code SRAM (`A_v`, `B_p`, code space, `H₁(Σ,Z₂)`, local MWPM) | Implement fault-tolerant cache-array model: planar-code layout + cellular-automaton MWPM decoder in sim; measure correctable SEU rate and read-path latency vs SECDED Hamming on identical fault injection. | Hardware-model experiment, L0/L1. | Kill iff decode latency hits the read path or correction rate loses to SECDED at equal area. |
| E-69 | NC motives + derived Azumaya side-channel freedom (`Br(X)⊂H²_ét(X,G_m)`, Morita triviality `ch(M)=0`) | Implement speculative-leak checker: model cache-hierarchy effects as Brauer-class deformation; admit fence-free speculation iff motive is Morita-trivial on the checked fragment; test vs `lfence`/retpoline baseline on Spectre-model probes. | Security checker, L2/L3. | Kill iff checker admits a probe leak the fenced baseline blocks, or throughput gain is nil. |
| E-70 | Borcherds–Kac–Moody automorphic compression (`e^ρ∏(1−e^α)^{mult} = Σdet(w)w(…)`) | Implement Weyl-group matrix codec on FPGA-model/sim for tick streams: encode as automorphic projection, decode by Weyl action; measure ratio vs zstd/LZ4 and single-cycle throughput claim on identical feeds. | Codec experiment, L0/L1. | Kill iff ratio/latency loses to zstd/LZ4 on real feeds. |

### 14. Batch K — paradigm-killers I: memory / concurrency / effects / dataflow / refinements (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-71 | Constructive bi-abduction memory (Calcagno–O'Hearn–Yang; `Pre∗[?]⊢Post∗[?]`) | Implement region/footprint inference on a bounded MIR fragment with cyclic graphs: infer anti-frame/frame + synthesize arena `malloc`/`free` without lifetime annotations; test annotation-free acceptance rate vs borrow checker (ADR-011 stage 2) + Infer-style bug recall. Kills Rust-style annotation burden iff it works — by measurement, not Sparring. | Ownership experiment, L2/L3. | Kill iff inference diverges on cyclic benchmarks, or accepted-safe programs include a use-after-free/double-free the borrow checker catches. |
| E-72 | Hardware-native interaction combinators (Lamping–Lafont `γ/δ/ε`, local symmetric rewrites) | Implement combinator-reduction simulator + FPGA-model mapping: compile a small functional core to `γ/δ/ε` nets, reduce independent active pairs in parallel with zero locks; measure speedup vs goroutine/actor runtimes on identical workloads. Bracket/croissant bookkeeping cost is part of the measurement. | Execution-model experiment, L0/L1. | Kill iff bookkeeping dominates or no speedup over Tokio/BEAM baselines. |
| E-73 | Zero-cost algebraic effect inlining (Plotkin–Pretnar, Koka-style handlers, linear continuations) | Implement whole-program handler inliner on a bounded effect set (Error/State/IO): flatten handlers to jumps/register mutations with no heap frames; benchmark vs MTL-style transformers and C-speed baseline. | Effect-compiler experiment, L1/L2. | Kill iff multishot continuations force allocation on the benchmark set or inlined code loses to baseline. |
| E-74 | Differential catamorphic memory (McSherry `(d,t,r)` derivatives over program graph) | Implement incrementally-maintained collections on a bounded query fragment: mutations propagate exact derivatives, joins auto-update; measure sub-ns update claim vs Postgres/Redis/ORM baseline on identical workloads including durability. | Memory/query experiment, L1/L2. | Kill iff durability/indexing cost erases the update win or fragment coverage is trivial. |
| E-75 | SMT-discharged sized refinements (Liquid Types `{v:τ\|φ(v)}` + Presburger/SMT in typechecker) | Implement refinement front-end on a bounded finance-kernel fragment: infer `{v:Vector⟨Order⟩\|Σqty=Target∧sorted}`-style predicates, discharge via SMT, emit counterexample traces on failure; measure auto-discharge rate vs handwritten Lean proofs and Python-annotation cost. | Typechecker experiment, L2/L3. | Kill iff solver timeouts dominate or counterexamples are unactionable on real kernels. |

### 15. Batch L — paradigm-killers II: superopt / reversible AD / HW extraction / choreography / Kan interop (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-76 | E-graph superoptimization (Massalin; saturation + ILP/SMT-QBF extraction `min Latency(σ\|HW)`) | Implement superoptimizing backend on fixed opcode subsets (≤10-instruction windows first): saturate equivalence graph, extract cycle-accurate minimum; compare output vs LLVM `-O3` + hand intrinsics (`_mm512_fmadd_ps` class) on identical kernels. | Backend experiment, L1/L2. | Kill iff extraction time explodes outside micro-windows or output loses to LLVM/hand-tuned baseline. |
| E-77 | O(1)-memory invertible semantics / universal reverse AD (Bennett `f†∘f=id`, `Memory=O(1)`) | Implement reversible core with analytic backward reconstruction (run forward in reverse, no tape/checkpoint); add `grad f` operator over loops/recursion/heap subset; measure memory (`O(T)`→`O(1)`) and overhead vs PyTorch/JAX on identical models. | AD/semantics experiment, L1/L2. | Kill iff irreversibility (IO/alloc entropy) forces tape fallback on the benchmark set or overhead exceeds checkpointing. |
| E-78 | Categorical hardware extraction (`F:Spec→Circuit`, sheaf of timed events, Curry–Howard–Lambek) | Implement functorial extractor from a bounded functional spec to RTL: CDC/timing violations as type-level coherence failures; compare tape-out-ready output + bug rate vs SystemVerilog + UVM flow on identical blocks. | HW-synthesis experiment, L1/L2. | Kill iff extractor admits a CDC/timing bug UVM catches, or accepted-spec coverage is trivial. |
| E-79 | Continuous choreographic BFT projection (`global AST → endpoint binaries`, `H¹(G,Aut(State))` minimal protocol) | Implement global-to-endpoint projector on a bounded gateway/engine/ledger topology: synthesize consensus/networking loops from one global program; test split-brain/deadlock rate vs Kubernetes/etcd/Raft/gRPC baseline on identical partitions. | Distributed-compiler experiment, L1/L2. | Kill iff projector admits a partition anomaly the baseline survives, or generated protocol costs more. |
| E-80 | Kan-extension zero-copy interop (`Lan_K`/`Ran_K` coend `∫^A Lang_B(K(A),B)⊗F(A)`) | Implement cross-language bridge synthesizer on a bounded pair (e.g. Rust-shape lifetimes → Python-shape use): preserve generics/ownership/non-null/sum types across the call with zero copy; test invariant-preservation vs C-ABI/PyBind/JNI + serde baseline. | Interop experiment, L1/L2. | Kill iff bridge drops an invariant the baseline preserves (soundness bug) or copy/serde cost remains. |

### 16. Batch M — SASOS / gradual typing / spatial silicon / projectional / Lorentz (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-81 | Proof-carrying linear capabilities on SASOS (Necula–Lee PCC, Midori-style SIPs; flat 64/128-bit space, no MMU/TLB/syscall) | Implement SIP-compiler fragment: linear-capability isolation proof for a bounded driver/service set in one address space; direct-call driver invocation; fault-injection isolation test vs Linux-syscall/DPDK baseline. Removing MMUs from silicon is out of scope; the compiler proof + call-overhead measurement is the artifact. | OS-model experiment, L2/L3. | Kill iff proof admits an escape the MMU baseline contains, or call overhead shows no win over syscall/DPDK path. |
| E-82 | Sound zero-cost gradual typing (Siek–Wadler; beat Takikawa 100× blame penalty via abstract interpretation + polyvariance) | Implement blame-erasing gradual front-end on a bounded dynamic/static boundary: abstract-invariant boundary proofs, checks pushed to topological edges and collapsed; benchmark mixed typed/untyped vs V8/PyPy/HotSpot warmup + contract-wrapper baseline. | Typechecker experiment, L2/L3. | Kill iff mixed-region slowdown approaches blame-wrapper levels or boundary proofs time out on real modules. |
| E-83 | Spatial in-memory categorical silicon (Backus liberation; `δE=0` relaxation on memristor/photonic grid, no ISA) | Implement geometric-mapping compiler to a simulated functional-cell grid: denotational morphisms → grid topology, in-place relaxation; measure bus-transit elimination vs x86/ARM/RISC-V register/cache baseline on identical kernels. Physical tape-out is out of scope; the sim + mapping cost is the artifact. | HW-model experiment, L0/L1. | Kill iff mapping cost or sim latency erases the bus-win, or expressible-kernel coverage is trivial. |
| E-84 | Continuous projectional semantics (Unison-style `G=(V,E,τ)` hypergraph, ephemeral syntax, pushout merges) | Implement semantic-graph codebase store for a bounded module set: content-addressed typed nodes, Python/C/LaTeX projections, structural pushout merge; test concurrent-refactor merge success vs Git line-merge conflicts + parser/linter cost. | Toolchain experiment, L0/L1. | Kill iff pushout merge admits a semantic conflict Git would flag, or projection round-trip loses fidelity. |
| E-85 | Lorentz-covariant spacetime semantics (`ds²=c²dt²−dx²−dy²−dz²`, backward-cone dependence, spacelike decoupling) | Implement relativistic typechecker fragment: dependence allowed only inside backward light cone (`ds²≥0,dt>0`); spacelike pairs decoupled with no ordering obligation; test multi-node determinism vs PTP/TrueTime/RTOS sync baseline on identical partitions. | Distributed-semantics experiment, L1/L2. | Kill iff checker admits a causality violation the clocked baseline prevents, or coordination savings vanish. |

### 17. Batch N — exact arithmetic / persistence / totality / capabilities / principal types (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-86 | Gosper–Vuillemin continued-fraction arithmetic (`x=[a₀;a₁,…]`, bihomographic `z=(axy+bx+cy+d)/(exy+fx+gy+h)`) | Implement exact-real kernel on a bounded pricing/SDE fragment: lazy partial-quotient streams, matrix term engine; test associativity/distributivity restoration + precision vs IEEE754 `f32/f64` (NaN/−0/subnormal/microcode) on identical long-horizon runs. | Numerics library/HW-model, L1/L2. | Kill iff term-stream latency exceeds float pipeline at equal accuracy, or coverage stops at toy fractions. |
| E-87 | Orthogonal persistent toposes on byte-addressable NVM (Grothendieck topos `E`, Merkle-DAG lenses, CXL/SCM, CoW lines) | Implement persistent-object store on a bounded order-book/table fragment: globally addressable objects, atomic line-level CoW, power-loss resume; compare `fsync`/WAL/serde cost vs ext4/ZFS + Postgres baseline. | Storage-model experiment, L1/L2. | Kill iff resume correctness fails a pull-the-plug test the WAL baseline passes, or write amplification erases the win. |
| E-88 | Total productive coinduction (Turner–Abel TFP; `νX.Output×X^{Time≤τ}`, sized termination/productivity) | Implement total fragment: inductive paths via well-founded/sized recursion, server/matching loops as sized-productive coinduction with `τ` bound; prove no-hang/no-overflow on the fragment vs Turing-complete baseline + watchdog restarts. | Language-core experiment, L2/L3. | Kill iff productive fragment rejects the project's own engine loops or size inference needs manual ordinals everywhere. |
| E-89 | Cryptographic capability tagging at the CHERI limit (`(Addr,Base,Limit,Perms,Tag₁)`, hardware unforgeability, monadic revocation) | Implement tagged-pointer checker + sim fault model: out-of-`[Base,Limit]`/forged-integer deref faults in zero model cycles, sweep revocation; test ROP/overflow/use-after-free exploit corpus vs ASLR/canary/DEP/CFI/ASan baseline. | Security-model experiment, L2/L3. | Kill iff exploit corpus member escapes the tag model or overhead exceeds sanitizer baseline. |
| E-90 | Decidable filter-model principal typings (Coppo–Dezani–Venneri `A∩B`; `terminating ⇔ typed`, principal typing) | Implement bounded intersection/union inference on a bounded higher-rank fragment (Rank-N, no value-restriction hack): infer principal filter types, monomorphize to unboxed assembly; test annotation-free acceptance vs HM + manual-signature baseline. | Typechecker experiment, L2/L3. | Kill iff inference blows up past sub-second budget or principal types are unreadable/unauditable in practice. |

### 18. Batch O — bisimulation / CALM / learned indexes / superposition / photonics (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-91 | Coalgebraic bisimulation instead of tests (`(S,α:S→F(S))`, `R⊆Spec×Impl`, `!_Spec=!_Impl` on final `Ω`) | Implement bisimulation extractor on bounded spec/impl pairs: compute `R` as subcoalgebra of the product, emit minimal divergence kernel on mismatch; measure proof coverage vs JUnit/pytest/QuickCheck/AFL baselines on identical bugs. | Verification experiment, L2/L3. | Kill iff extractor misses a fuzzer-found bug or divergence kernels are unactionable. |
| E-92 | Lattice monotonicity + I-confluence instead of consensus (Hellerstein CALM, Bailis `I(S₁)∧I(S₂)⇒I(S₁⊔S₂)`, Galois insertions) | Implement monotonic-lifting compiler on a bounded cross-datacenter fragment: local execution + `⊔`-merge, invariant-closure proof; test zero-coordination convergence vs Raft/Paxos/2PC/Chubby quorum latency on identical partitions (FLP acknowledged: only I-confluent invariants qualify). | Distributed-compiler experiment, L1/L2. | Kill iff a claimed invariant breaks under reorder/partition the quorum baseline survives, or lifting covers only toy invariants. |
| E-93 | Information-geometric learned surjections (`g_ij` Fisher metric, `f:Key→Offset`, Chebyshev/spline branchless eval) | Implement continuous index on a bounded trillion-row-model fragment: `f` maps keys to offsets in fixed branchless cycles; measure lookup + RAM vs B-Tree/LSM/RocksDB/skip/hash baselines including retrain drift. | Index experiment, L1/L2. | Kill iff drift/retrain cost erases lookup/RAM win or worst-case lookup exceeds tree baseline. |
| E-94 | Wave-interference multi-path silicon (`|Ψ⟩=α|True⟩+β|False⟩`, destructive cancel at merge) | Implement dual-path execution model on a bounded branchy fragment: both paths execute, predicate phase-shift cancels the invalid amplitude; test pipeline-bubble/jitter vs TAGE/BTB + `cmov`/branchless baseline, plus Spectre-model probe resistance. | HW-model experiment, L0/L1. | Kill iff dual-path energy/area exceeds predictor cost at equal throughput, or invalid-path effects leak. |
| E-95 | All-optical holographic routing (photonic catnets, geodesic waveguides, `Latency=d/c_fiber`, zero buffers) | Implement network-compiler model: endpoints get a continuous-waveguide path (no packets/headers/windows); simulate London–NYC multi-terabit bus behavior vs TCP/IP+BBR/Cubic (drops/retransmits/bufferbloat) on identical demand. Physical plant build-out is out of scope. | Network-model experiment, L0/L1. | Kill iff demand-adaptive reconfiguration cost exceeds TCP-goodput win or model assumes unbuildable optics. |

### 19. Batch P — async logic / functorial migration / univalence / volumetric memory / Ising (5 new, all open)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-96 | QDI asynchronous micropipelines (Martin CHP, NCL dual-rail `0/1/Null`, delay-insensitive correctness) | Implement QDI synthesis flow on bounded blocks: self-timed firing + ack tokens, isochronic-fork audit; compare average-case throughput/power vs 5GHz sync + STA/CDC flow (30–40% clock-tree power claim measured, not assumed). | HW-synthesis experiment, L1/L2. | Kill iff area/ack overhead erases throughput/power win or flow covers only toy blocks. |
| E-97 | Spivak functorial data migration (`I:C→Set`, `Σ_F⊣Δ_F⊣Π_F` over ologs `C/D`) | Implement schema-category migrator on bounded Postgres/Mongo/Neo4j/ClickHouse shapes: tables=objects, FKs=morphisms, constraints=diagrams; migrate via adjoint triple with zero-orphan proof; test vs ETL/Snowflake/BigQuery baseline on identical evolutions. | Data-migration experiment, L1/L2. | Kill iff migrator drops a constraint ETL preserves or migration proof cost exceeds pipeline cost. |
| E-98 | Univalent semantic transport (`(A≃B)≃(A=B)`, `transport^P(p):P(A)→P(B)`, content-hash ASTs) | Implement content-addressed store + equivalence transport on a bounded library set: link 50-version-style diamonds by hash, synthesize `A→B` maps across API bumps; test breakage rate vs Cargo/npm/pip + SemVer + Bazel/CMake rebuild baseline. | Toolchain experiment, L1/L2. | Kill iff transport synthesizes a wrong-arity call the versioned baseline would reject, or hash-store rebuild costs more. |
| E-99 | Uniform-latency volumetric 3D memory (`Latency(x,y,z)=τ_uniform≈1–2 cycles`, optical/spintronic stack) | Implement uniform-latency memory model + DOD-ablation harness: single-byte granularity, no lines/coherence/false-sharing; rerun pointer-graph vs SoA workloads; measure DOD-necessity claim vs L1/L2/L3+MESI baseline. Hardware fab is out of scope. | Memory-model experiment, L0/L1. | Kill iff harness shows DOD still wins at equal cost, or model assumes unbuildable physics. |
| E-100 | Spin-glass / Ising ground-state compute (`H(σ)=−ΣJ_ijσ_iσ_j−Σh_iσ_i`, `δH=0` in ns, no ISA) | Implement constraint-to-coupling mapper on bounded SAT/routing/portfolio fragments: `J/h` synthesis + relaxation solver (sim/annealer); compare time-to-optimum vs Dijkstra/A*/sort/CFG imperative baselines. | Solver experiment, L0/L1. | Kill iff solution quality/time loses to imperative baseline or mapper covers only toy sizes. |

## Consequences

### Positive- The full 1550-entry register is now on the record: Batch 0 (E-03, E-06,
  E-10, ZX-q, DAT-s + T-01–T-20) plus Batches A–D (E-21–E-40) plus Batches
  E–H (E-41–E-60) plus Batches I–L (E-61–E-80) plus Batches M–P
  (E-81–E-100), continued in ADR-020 (E-101–E-250), ADR-021 (E-251–E-400),
  ADR-022 (E-401–E-550), ADR-023 (E-551–E-700), ADR-024 (E-701–E-850),
  ADR-025 (E-851–E-1000), ADR-026 (E-1001–E-1100, incoming paradigms
  1–100), ADR-027 (E-1101–E-1200, incoming paradigms 101–200), ADR-028
  (E-1201–E-1300, incoming paradigms 201–300), ADR-029 (E-1301–E-1350,
  incoming paradigms 301–350), ADR-030 (E-1351–E-1450, incoming paradigms
  351–450: everyday-software clusters XXX–XXXIX), ADR-031 (E-1451–E-1550,
  incoming paradigms 451–550: everyday-software clusters XL–XLIX). Future
  proposals append as new ADR files; nothing is silently dropped.
- Every future proposal — including ones not yet seen — is decided by the
  acceptance rule in §1 plus the breadth-first directive, not by debate. The
  checklist is mechanical, and cuts require proof + execution evidence.
- Reclassifying prior rejections as tracked-open honors the maintainer's
  directive while keeping the original objections as the kill hypotheses to
  be tested by implementation.

### Negative

- The register is large by design. Overhead is real: each experiment owes an
  implementation, a proof-burden log, and an execution record. That is the
  price of the "cut only on evidence" directive and is non-negotiable while
  it stands.
- Beautiful work without a decision procedure stays tracked-but-unbuilt
  until a computable core appears. That boundary is intentional.

### Follow-up

- File one experiment brief per E-entry family before implementation starts
  (briefs may cover coherent row families, e.g. one brief per 25-row batch),
  each stating scope, grade target, workload, and kill criterion. The table
  rows across ADR-019–031 are the seed. E-1000 gates the experimentation
  phase; E-999 audits register continuity. The 351–550 tranche is weighted
  toward shippable product surface (UI runtimes, identity, VCS, cloud, build,
  data, OS userland, observability, tooling, app security), so briefs there
  can pair each row with an existing subsystem rather than a green field.
- Revisit this ADR when any kill/reopen condition fires on measured proof +
  execution evidence, or when a new frontier proposal arrives; append, do not
  rewrite history.

## References

- Batch 0 survey: choreographic programming (Choral/HasChor), SMT refinements
  (LiquidHaskell/F\*/Flux), ZK arithmetization (Noir/Circe/R1CS),
  differential dataflow (McSherry/Materialize/Salsa), Calyx, egg/E-graphs,
  Idris 2 QTT, cubical type theory, Austral capabilities, Enzyme/Dex, Silq
  uncomputation, Iris/Steel, MLIR affine, miniKanren/Barliman, Gen/Pyro,
  directed HoTT, process matrices, epistemic modal types, synthetic topology,
  Lamping/Lafont optimal reduction, Girard ludics, relativistic semantics,
  Abramsky game semantics, coalgebra/bisimulation, Guiraud–Malbos polygraphs,
  ordered linear logic, cellular sheaves, gauge semantics, non-standard
  analysis, Landauer-bounded types, tropical semirings, Kock–Lawvere SDG,
  Feynman path integrals, p-adic analysis, symplectic/Noether types, Artin
  braids, Connes NCG, Itô/Stratonovich calculus, Coecke–Duncan ZX,
  Grothendieck six operations, directed topology
  (Goubault/Fajstrup/Haucourt), contact/Reeb dynamics, supersymmetry/Grassmann
  types, Malliavin/Skorokhod calculus, CFT/OPE, mirror symmetry
  (Kontsevich), Berry/Wilczek–Zee holonomy, Wilsonian RG, Benamou–Brenier
  optimal transport, Atiyah–Patodi–Singer index.
- Batch A sources: Kapustin–Witten (2006) S-duality / geometric Langlands;
  Ryu–Takayanagi `S_A = Area(γ_A)/4G_N`; Picard–Lefschetz thimbles
  (`Im(iS)` = const along `J_σ`); Jarzynski `⟨e^{-βW}⟩ = e^{-βΔF}` + Crooks
  `P_F(W)/P_R(-W) = exp(β(W-ΔF))`; Maldacena–Shenker–Stanford OTOC
  `C(t) = -⟨[W(t),V(0)]²⟩`, `λ_L ≤ 2πk_BT/ℏ`.
- Batch B sources: Grothendieck motives / Voevodsky–Morel **A**¹-homotopy,
  realization functors `ω`; Mumford GIT `X//G`, Hilbert–Mumford `μ(x,λ)`;
  Rattazzi–Rychkov–Tonni–Vichi bootstrap crossing `Σ λ²F = 0` + SDPB;
  Chern-Simons `S_CS = k/4π ∫ Tr(A∧dA + ⅔A³)`, Verlinde `a⊗b = ⊕ N^c_ab c`;
  twisted K-theory `K⁰(X,[H])`, Dixmier–Douady `[H] ∈ H³(X,ℤ)`, AHSS
  `d₃(x) = Sq³(x) + x∪[H]`.
- Batch C sources: Batalin–Vilkovisky antibracket + `Δ_BV`, QME
  `½(S,S) − iℏΔS = 0`; Atiyah–Bott `∫_M α = Σ_F ∫_F i*α/e_T(N_F)`;
  Osterwalder–Schrader reflection positivity; Dubrovin Frobenius manifolds +
  WDVV; Lubotzky–Phillips–Sarnak Ramanujan graphs, Alon–Boppana
  `λ₂ ≥ 2√(d−1)`, Cheeger `(d−λ₂)/2 ≤ h(G) ≤ √(2d(d−λ₂))`.
- Batch D sources: Baker–Norine graph Riemann–Roch
  `rank(D) − rank(K−D) = deg(D) − g + 1`; PT-symmetry `[PT,H] = 0`,
  EP_N `Δλ ∼ ε^{1/N}`; Lurie–Toën derived AG, `O_{X×_Z^R Y} =
  O_X ⊗^L_{O_Z} O_Y`, `π_i ≅ Tor_i`; Connes–Kreimer `H_CK`,
  `Δ(T) = T⊗1 + 1⊗T + Σ P_c⊗R_c`, antipode `S(T)`; Kostant–Souriau
  prequantization `curv(∇) = −iω/ℏ`, polarizations, BKS pairing.
- Batch E sources: Mazur–Kapranov–Reznikov arithmetic topology, Massey `⟨u,v,w⟩ = [x∪w + u∪y]`; Federer–Fleming GMT currents `T(ω) = ∫⟨ω,ξ⟩θdHᵐ`, `M(T)`, `∂T(α)=T(dα)`; Atiyah–Singer families `ch(ind D) = ∫ Â∧ch(E)`, Quillen `L_det`, Bismut–Freed; Umezawa TFD `|Ψ(β)⟩ = Z^{-1/2}Σe^{-βEₙ/2}|n⟩⊗|ñ⟩`; Gardner–Greene–Kruskal–Miura IST, KdV `u_t+6uu_x+u_xxx=0`, `Lψ=-ψ''−uψ=λψ`, GLM `K+F+∫KF=0`.
- Batch F sources: Kontsevich formality `f⋆g = fg + ΣℏⁿBₙ`, `f⋆g−g⋆f = iℏ{f,g}+O(ℏ²)`; Finster CFS (spacelike equal-modulus nonreal vs timelike real-gapped spectra of `xy`); Fomin–Zelevinsky clusters `x_kx'_k = ∏x_i^{b_ik}+∏x_i^{-b_ik}`, Laurent positivity; Lieb–Robinson `‖[A(t),B(0)]‖ ≤ c‖A‖‖B‖exp(−(d−v_LR|t|)/ξ)`; Atiyah–Sutcliffe `v_ij=(x_j−x_i)/‖·‖`, `p_i(z)=∏(z−z_ij)`, `D_n=det M ≠ 0`.
- Batch G sources: Connes–Tsygan–Kontsevich NC Hodge `(b,B)`, `E₁^{p,q}=HH_{q−p}⇒HP`, Kaledin–Kontsevich degeneration; Khovanov `C^{*,*}(K)`, `H^{i,j}(K)`, `V(K)=Σ(−1)^iq^jdimH^{i,j}`, cobordism maps `H(S)`; Selberg `Σh(r_n)=Vol-term+ΣΣℓ(γ₀)/2sinh(kℓ/2)·g(kℓ)` on `X=Γ\H²`; Pestun SUSY localization `Q²=0`, `dZ/dt=0`, `t→∞` to `QV=0`, Nekrasov `Z=∫da det|Z_inst|²e^{−4π²Tr(a²)/g²}`; Freed–Hopkins anomalies `↔` torsion in `Ω_spin^{d+1}(BG)`.
- Batch H sources: Grothendieck–Deligne Tannakian `C≃Rep_k(G)`, `G=Aut^⊗(ω)`, `Isom(ω_x86,ω_ARM)`; Cuntz–Krieger `O_A`, `S_i^*S_i=ΣA_ijS_jS_j^*`, `K₀≅Zⁿ/(I−Aᵀ)Zⁿ`, Bowen–Franks `det(I−Aᵀ)`; Sato `Gr(H)`, `τ(t)`, Hirota `∮e^{Σ(t−t')zⁿ}τ(t−[z⁻¹])τ(t'+[z⁻¹])dz=0`, Krichever; Conley `h(S)=[N₁/N₀]`, `CH_*=H_*(N₁,N₀)`, continuation; Scholze–Fargues `X_FF=Proj(⊕B^{φ=p^d})`, HN `E≅⊕O(λ_i)`, `μ(E)=deg/rank=0` semistability.
- Batch I sources: Hitchin (1987) Higgs `(E,Φ)`, `h(E,Φ)=(TrΦ,…,TrΦⁿ)`, `S={det(λI−Φ)=0}`, `Jac(S)` linearization; Kempf–Ness `X//G≅μ⁻¹(0)/K`, `d_x(g)=ln‖g·x‖`, `dx/dt=−∇‖μ‖²`; Atiyah–Drinfeld–Hitchin–Manin `[B₁,B₂]+IJ=0`, `[B₁,B₁†]+[B₂,B₂†]+II†−J†J=0`; Berkovich `P¹_Berk`, Fatou equicontinuity vs Julia chaos; Schramm `∂_tg_t=2/(g_t−ξ_t)`, `ξ_t=√κB_t`, Cardy `P=3Γ(2/3)/Γ(1/3)²·η^{1/3}·₂F₁(1/3,2/3,4/3;η)`.
- Batch J sources: Hörmander `WF(u)⊂T*X\\{0}`, `WF(u)∩−WF(v)=∅`; Bridgeland `Stab(D)`, `(Z,A)`, `φ=argZ/π`, Kontsevich–Soibelman `∏exp(ΣΩe/n²)=∏exp(ΣΩe/n²)`; Kitaev toric/surface codes `A_v=∏X_e`, `B_p=∏Z_e`, `H₁(Σ,Z₂)`, MWPM; Kontsevich–Tabuada `NCMot`, Azumaya, `Br(X)⊂H²_ét(X,G_m)`; Borcherds `e^ρ∏(1−e^α)^{mult}=Σdet(w)w(e^ρΣϵe^β)` (Moonshine).
- Batches K–L sources: Calcagno–O'Hearn–Yang bi-abduction `Pre∗[?]⊢Post∗[?]` (Infer); Lamping–Lafont `γ/δ/ε` optimal reduction; Plotkin–Pretnar effects, Koka handlers; McSherry differential `(d,t,r)`; Liquid Types `{v:τ|φ}` + SMT/Presburger; Massalin superoptimization, `min Latency(σ|HW)` via ILP/SMT-QBF; Bennett `f†∘f=id` reversible `O(1)` AD; Curry–Howard–Lambek `F:Spec→Circuit`; choreographic `H¹(G,Aut(State))` BFT projection; Mac Lane Kan `Lan_K(F)(B)=∫^ALang_B(K(A),B)⊗F(A)`.
- Batch M sources: Necula–Lee PCC, Midori SASOS/SIPs (flat space, no `CR3`/TLB/`syscall`); Siek–Wadler gradual typing, Takikawa 100× blame; Backus 1977 vs Von Neumann (`δE=0` memristor/photonic relaxation); Unison-style `G=(V,E,τ)` projectional graphs, pushout merges; Minkowski `ds²=c²dt²−dx²−dy²−dz²`, backward-cone `ds²≥0,dt>0` vs spacelike `ds²<0`.
- Batch N sources: Gosper–Vuillemin `x=[a₀;a₁,…]`, `(axy+bx+cy+d)/(exy+fx+gy+h)` vs IEEE754 `f32/f64`, `(a+b)+c≠a+(b+c)`; CXL/SCM byte-addressable NVM, `State≅E` Merkle-DAG topos vs ext4/ZFS/`open/read/write`; Turner–Abel TFP, `νX.Output×X^{Time≤τ}` sized productivity vs Halting/Rice; CHERI-limit `(Addr,Base,Limit,Perms,Tag₁)`, unforgeability, sweep revocation vs ASLR/CFI/ROP; Coppo–Dezani–Venneri `A∩B`, `terminating⇔typed`, principal typings vs HM Rank-1/value-restriction.
- Batch O sources: coalgebra `(S,α:S→F(S))`, bisimulation `R⊆Spec×Impl`, final `Ω`, `!_Spec=!_Impl` vs JUnit/QuickCheck/AFL; Hellerstein CALM + Bailis `I(S₁)∧I(S₂)⇒I(S₁⊔S₂)`/`⊔`-merge vs Paxos/Raft/2PC/FLP; Kraska `g_ij=E[∂lnp·∂lnp]`, `f:Key→Offset` Chebyshev/spline vs B-Tree/LSM/hash; `|Ψ⟩=α|True⟩+β|False⟩` dual-path cancel vs TAGE/BTB/`cmov`/Spectre; photonic catnets, `Latency=d/c_fiber`, zero buffers vs TCP/IP/BBR/Cubic.
- Batch P sources: Martin CHP/QDI, NCL dual-rail `0/1/Null`, ack tokens, isochronic forks vs 5GHz/PLL/STA/CDC; Spivak ologs `I:C→Set`, `Σ_F⊣Δ_F⊣Π_F` vs ETL/Snowflake/polyglot; Voevodsky `(A≃B)≃(A=B)`, `transport^P(p)` content-hash ASTs vs Cargo/npm/SemVer/Bazel; `Latency(x,y,z)=τ_uniform` volumetric optics vs L1/L2/L3/MESI/DOD; Ising `H(σ)=−ΣJ_ijσ_iσ_j−Σh_iσ_i`, `δH=0` relaxation vs ISA/Dijkstra/CFG.
- Repo anchors: `Morph.HIRToMIR` (`lowerProgram_WF`), `Morph.MIR`
  (`WF`/`WFCFG`/`WFParams`/`WFProg`), `.specs/02_adrs/ADR-011` (MIR lowering
  pipeline), `docs/ERA2-BACKEND-SCOPE.md` (stage gates).
