# ADR-029: Frontier Register — Batches BX–CA (E-1301–E-1350)

## Status
**Accepted** (2026-10-31). Continuation of ADR-019–028 under the same
breadth-first directive: open experiments; cuts require implementation plus
proof-burden log and execution record. Sources: incoming paradigms 301–350
(Clusters XXV–XXIX: condensed mathematics, positive geometry, shifted
symplectic geometry, chromatic homotopy, twistor/microformal/supergeometry).

## Decision — Batch BX: condensed mathematics (E-1301–E-1310)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-1301 | Condensed abelian groups (`Cond(Ab)=Shv(Pro(FinSet))`, Clausen–Scholze) | Condensed-group formalization of a discretization shim with limit/colimit audit. | Formalization, L2. | Kill iff shim behaves identically without condensed machinery. |
| E-1302 | Liquid vector spaces (`M(S)⊗^L_Z R`, analytic rings, scale `p∈(0,1]`) | Liquid-tensor PDE integrator on continuous-finance fragment with stability audit. | Integrator, L1/L2. | Kill iff integrator unstable where classical stable. |
| E-1303 | Analytic stacks over non-Archimedean bases (exact completed tensors) | Analytic-stack risk-manifold evaluator with rounding-boundary audit. | Evaluator, L1/L2. | Kill iff rounding errors persist. |
| E-1304 | Solid rings (`Z→Z^■`, exact projective limits) for CAS integers | Solid-integer arithmetic core with truncation/loss-of-significance audit. | Arithmetic core, L1/L2. | Kill iff core slower than GMP 10× at equal exactness. |
| E-1305 | Condensed local systems (`π₁^cond(X)` pro-étale sheaves) | Local-system clock-domain model with race/discontinuity audit on multi-die fragment. | Domain model, L1/L2. | Kill iff races persist undetected. |
| E-1306 | Derived condensed modules over `R` (`D(Cond(R))`, Fréchet pathologies) | Derived-category elliptic-PDE solver on risk fragment with preconditioner audit. | PDE solver, L1/L2. | Kill iff convergence fails where classical converges. |
| E-1307 | Condensed monoidal functors for real-time DSP (projective-limit-commuting actions) | Condensed-`R`-module stream processor with Nyquist/aliasing audit. | Stream processor, L1. | Kill iff aliasing persists. |
| E-1308 | Pyknotic sets and higher stacks (Barwick–Haine, compact-Hausdorff site) | Pyknotic-bridge audit between HoTT fragment and continuous plant model. | Bridge audit, L2. | Kill iff mismatch persists unarticulated. |
| E-1309 | Analytic cohomology of non-Archimedean QFT (condensed coherent sheaves) | Non-Archimedean lattice evaluator on QCD-toy fragment with divergence audit. | Evaluator, L0/L1. | Kill iff divergences persist. |
| E-1310 | Condensed Riemann–Hilbert (flat connections ≅ `π₁^cond` reps) | Connection-solver audit on linear-dynamics estimator with drift audit. | Solver audit, L1/L2. | Kill iff path drift persists. |

## Decision — Batch BY: positive geometry and the amplituhedron (E-1311–E-1320)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-1311 | Amplituhedron canonical forms (`Gr_{k,k+m}^+`, log-singularity `Ω`) | Polytope-volume amplitude evaluator on toy-scattering fragment with diagram-count audit. | Evaluator, L0/L1. | Kill iff evaluator never reproduces a known amplitude. |
| E-1312 | Associahedron planar scattering forms (`Ω=dlnX₁∧…∧dlnX_n`) | Kinematic-form evaluator on scalar-interaction fragment with series audit. | Evaluator, L0/L1. | Kill iff forms mismatch perturbative results. |
| E-1313 | Cosmological polytopes (boundary wave-function as volume, no time) | Volume-based cosmology-sim step with integrator-comparison audit. | Sim step, L0/L1. | Kill iff volume mismatches time-evolved state. |
| E-1314 | Momentum amplituhedron (no ghosts/gauge redundancy) | Gauge-redundancy-free amplitude audit on loop fragment. | Amplitude audit, L0/L1. | Kill iff redundancies persist. |
| E-1315 | Positive tropical Grassmannians (`Trop^+Gr(k,n)`) and worldsheets | Fan-based worldsheet evaluator with period-matrix audit. | Evaluator, L0/L1. | Kill iff periods mismatch numerical integration. |
| E-1316 | Permutohedral kinematic flow lattices (volume-preserving shifts) | Permutohedron flow solver on packet/fluid fragment with mesh audit. | Flow solver, L1. | Kill iff solver needs the meshes it replaces. |
| E-1317 | Cluster-polytope integrand extraction (mutation coordinates) | Mutation-coordinate extractor on multi-loop fragment with divergence audit. | Extractor, L0/L1. | Kill iff divergences persist. |
| E-1318 | Halohedron IR factorization (soft/collinear facet stratification) | Facet-mapped IR handler on scattering fragment with cutoff audit. | IR handler, L0/L1. | Kill iff cutoffs still required. |
| E-1319 | Eulerian positivity on intersection numbers (twisted de Rham, positive chambers) | Chamber-integral evaluator on wave-propagation fragment with quadrature audit. | Evaluator, L0/L1. | Kill iff quadrature wins on accuracy/cost. |
| E-1320 | Positive geometries for non-Abelian loops (color-kinematics/BCJ residues) | Residue-based color-factor evaluator with contraction audit. | Evaluator, L0/L1. | Kill iff contractions still required. |

## Decision — Batch BZ: shifted derived symplectic geometry (E-1321–E-1330)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-1321 | Shifted symplectic stacks (PTVV, `T_X≃L_X[n]`, `ω∈A²(X,n)`) | Shifted-structure optimizer prototype with multiplier/singularity audit. | Optimizer prototype, L1/L2. | Kill iff multipliers still required. |
| E-1322 | Derived critical loci (`X=Crit(f)`, (−1)-shifted forms) | Critical-locus phase-space solver with saddle/halt audit. | Solver, L1/L2. | Kill iff saddle halts persist. |
| E-1323 | Shifted Poisson + formality on derived stacks (`E_{n+1}` observables) | Deformation-quantization audit on operator-ordering fragment. | Quantization audit, L1/L2. | Kill iff ordering ambiguities persist. |
| E-1324 | Derived Lagrangian intersections (`L₁×_X^R L₂`, (−1)-shifted) | Derived-intersection engine on constraint fragment with degeneracy audit. | Intersection engine, L1/L2. | Kill iff degeneracies crash the engine. |
| E-1325 | Joyce perverse sheaves of vanishing cycles (DT-invariant categorification) | Orientation-data loss-landscape audit on learning fragment. | Landscape audit, L1. | Kill iff branch cuts persist. |
| E-1326 | Higher symplectic reduction (`μ:X→g*[n]`, `X//^R G`) | Derived-quotient physics engine with drift/gauge audit. | Engine audit, L1/L2. | Kill iff drift/gauge redundancy persists. |
| E-1327 | Derived vector-bundle moduli on CY4 (`Perf(X)`, 2-shifted, Borisov–Joyce) | Virtual-class constraint solver with explosion audit. | Solver, L1/L2. | Kill iff explosion on all real constraints. |
| E-1328 | Shifted contact structures (odd `α∈A¹(X,2n+1)`, derived Reeb) | Derived-Reeb dissipation audit on mechanical-sim fragment. | Dissipation audit, L1. | Kill iff dissipation unmodeled. |
| E-1329 | Derived Darboux theorem (local `ω=d p∧d q` quadrics) | Darboux-coordinate normalizer on sim fragment with metric-overhead audit. | Normalizer, L1. | Kill iff overhead exceeds nonlinear-metric cost. |
| E-1330 | Constructible sheaves on derived characteristic varieties (shifted microlocal `D`-modules) | Propagation-bound audit on wave-scattering fragment. | Propagation audit, L1. | Kill iff diffusion/ray failures persist. |

## Decision — Batch BZA: chromatic homotopy theory (E-1331–E-1340)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-1331 | Morava `K(n)` chromatic filtration (formal-group height `n` at prime `p`) | Height-stratified loop-termination audit on periodic-loop fragment. | Termination audit, L2. | Kill iff stratification never decides a real loop. |
| E-1332 | Devinatz–Hopkins–Smith nilpotence (`MU_*(f)=0` ⇒ nilpotent) | Cobordism-image nilpotence checker on rewrite-system fragment. | Nilpotence checker, L2. | Kill iff checker times out on all real systems. |
| E-1333 | Chromatic spectral sequence (`E₁^{s,t}=H^s(M_n)⇒π_{t−s}(S)`) over `M_FG` | Formal-group type-invariant search on state-transition fragment. | Invariant search, L2. | Kill iff search never finds an invariant. |
| E-1334 | Hopkins–Miller `S_n`-actions on Lubin–Tate spectra (`E_n`) | Stabilizer-action reconfiguration audit on distributed-crypto fragment. | Reconfiguration audit, L1/L2. | Kill iff races persist. |
| E-1335 | Topological modular forms (**TMF**, elliptic-spectrum global sections) | TMF-based partition/anomaly audit on SUSY-pipeline fragment. | Anomaly audit, L2. | Kill iff mismatches persist. |
| E-1336 | Landweber exact functor (formal-group-law homology theories) | Law-to-homology extractor with prover-overhead audit. | Extractor, L2. | Kill iff extractor never beats hand axiomatization. |
| E-1337 | Adams–Novikov SS over `(MU_*,MU_*MU)` Hopf algebroid | Stable-invariant prover on consensus-protocol fragment with explosion audit. | Prover, L2. | Kill iff explosion on all real protocols. |
| E-1338 | Hopkins–Smith thick subcategories (chromatic type `C_n`) | Type-classified exception/fault taxonomy with handling audit. | Taxonomy audit, L1. | Kill iff taxonomy never routes a real fault. |
| E-1339 | Chromatic splitting on Moore spectra (`L_{K(n)}S` monochromatic layers) | Layer-decomposed cache-miss analysis on tiered-memory fragment. | Miss analysis, L1. | Kill iff cascades unpredicted. |
| E-1340 | Bousfield localization (`L_E:Sp→Sp`) at chromatic heights | Local-failure isolator on execution-trace fragment with sync audit. | Isolator, L1/L2. | Kill iff isolation needs global sync anyway. |

## Decision — Batch CA: twistor, microformal, supergeometry (E-1341–E-1350)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-1341 | Penrose twistor transform (`H¹(PT⁺,O(2h−2))` zero-rest-mass fields) | Cohomology-based wave solver on Maxwell-fragment with FDTD/grid audit. | Wave solver, L1. | Kill iff solver mismatches FDTD on real fields. |
| E-1342 | Nonlinear-graviton twistor deformations (`H¹(PT,Θ_PT)` self-dual Einstein) | Deformation-based relativity solver with metric-drift audit. | Relativity solver, L0/L1. | Kill iff drift exceeds numerical relativity. |
| E-1343 | Voronov microformal thick morphisms (`S(x,q)` generating functions) | Nonlinear-function-map engine on control fragment with linearity-limit audit. | Map engine, L1. | Kill iff engine reduces to linear ops everywhere. |
| E-1344 | Witten twistor-string (`CP^{3|4}` D-instantons, N=4 SYM) amplitudes | Holomorphic-curve amplitude evaluator with lattice-YM audit. | Evaluator, L0/L1. | Kill iff evaluator mismatches lattice results. |
| E-1345 | Berezinian super-integration (`∫d^nx d^mθ Ber(J)`, odd symplectic P-manifolds) | Super-integral evaluator with fermionic-sign audit. | Evaluator, L1. | Kill iff sign errors persist. |
| E-1346 | Batalin–Marnelius odd first-class quantization (`{Q,Q}=0` odd charge) | Odd-charge constraint resolver on hardware-verification fragment with artifact audit. | Resolver, L1/L2. | Kill iff non-gauge artifacts persist. |
| E-1347 | Ambitwistor null-geodesic foliations (quadric in `P(T)×P(T*)`) | Null-geodesic ray tracer with pipeline/bottleneck audit vs classical ray tracer. | Ray tracer, L1. | Kill iff tracer slower than classical. |
| E-1348 | Graded `Q`-manifolds and Lie algebroids (`[Q,Q]=2Q²=0`, degree-1 `Q`) | Homological-vector-field dynamics engine with Jacobi/bracket audit. | Dynamics engine, L1/L2. | Kill iff Jacobi failures persist. |
| E-1349 | Frölicher–Nijenhuis tensor calculus (`[−,−]_FN` derivation algebras) | Intrinsic-geometry execution engine with chart-drift audit. | Geometry engine, L1. | Kill iff chart drift persists. |
| E-1350 | Berkovits pure-spinor formalism (`λγ^μλ=0` ghosts, manifest SUSY) | Pure-spinor amplitude evaluator with light-cone/covariance audit. | Evaluator, L0/L1. | Kill iff evaluator breaks covariance. |

## References

- ADR-019 (acceptance rule), ADR-020–028 (E-101–E-1300). Incoming source:
  paradigms 301–350 (Clusters XXV–XXIX). This file closes the E-1001–E-1350
  tranche; the register continues in ADR-030 (E-1351–E-1450) and ADR-031
  (E-1451–E-1550).
