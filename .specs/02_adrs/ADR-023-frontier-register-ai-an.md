# ADR-023: Frontier Register — Batches AI–AN (E-551–E-700)

## Status
**Accepted** (2026-10-31). Continuation of ADR-019–022 under the same
breadth-first directive: open experiments; cuts require implementation plus
proof-burden log and execution record.

## Decision — Batch AI: applied category theory (E-551–E-575)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-551 | Functorial query migration across E-97 schemas | Concrete `Σ/Δ/Π` migration programs on the four store shapes with round-trip tests. | Migration programs, L1/L2. | Kill iff any migration loses rows the ETL baseline preserves. |
| E-552 | Lens/prism optics for book-update code | Optic-composed book updates with law-checked optics on the depth fragment. | Optics, L1. | Kill iff optic code is slower than manual updates 2×. |
| E-553 | Profunctor optics for venue-adapter polymorphism | Profunctor adapters abstracting venue differences; test 2-venue swap. | Optics, L1. | Kill iff adapters need per-venue forks anyway. |
| E-554 | Operad-composed risk-check pipelines | Operadic composition of risk checks with arity audit. | Composition, L1. | Kill iff operad plumbing exceeds plain function composition cost. |
| E-555 | Monad-transformer stack audit (residual Haskell line) | Measured MTL-stack audit motivating E-73's inliner on the same handlers. | Audit, L1. | Kill iff MTL already meets the latency budget (then E-73 scope narrows). |
| E-556 | Freer-monad (extensible effects) performance audit | Freer-simple audit vs E-73/E-277 on the bounded effect set. | Audit, L1. | Kill iff freer already meets budget (scope finding). |
| E-557 | Tagless-final (MTL-style) encoding audit | Tagless-final audit on pricing kernels vs direct style. | Audit, L1. | Kill iff tagless wins outright (adopt, close experiment). |
| E-558 | Coalgebraic (final-semantics) testing harness (feeds E-91) | Concrete harness computing E-91 bisimulations on spec/impl pairs. | Harness, L1/L2. | Kill iff harness never scales past toy specs. |
| E-559 | Algebra-coalgebra (bialgebraic) SOS for the semantics | Bialgebraic operational rules with compositionality audit on the fragment. | SOS design, L1/L2. | Kill iff rule duplication exceeds plain SOS 3×. |
| E-560 | String-diagram rewriting for pipeline optimization | Diagrammatic rewrite engine on the signal pipeline; compare vs egg (accepted line). | Rewriting, L1. | Kill iff strictly dominated by egg on all rules. |
| E-561 | Double-pushout (DPO) graph rewriting for MIR opts | DPO rewrites on MIR graphs with dangling-condition audit. | Graph rewriting, L1/L2. | Kill iff DPO never fires safely where egg fires. |
| E-562 | Adhesive-category audit for DPO soundness | Adhesivity audit grounding E-561's conditions. | Theory audit, L2. | Kill iff audit shows conditions vacuous on MIR graphs. |
| E-563 | Traced-monoidal (feedback-loop) models for engine loops | Traced structure for feedback loops in the signal pipeline. | Modeling, L1. | Kill iff trace modeling finds no loop bug in a quarter. |
| E-564 | Compact-closed (teleportation-pattern) audit for state transfer | Compact-closed patterns for ownership transfer (feeds E-160/E-515). | Modeling, L1. | Kill iff patterns never transfer without copies. |
| E-565 | Enriched-category latency annotations | Hom-object latency grades on pipeline morphisms (feeds E-127). | Grading, L1. | Kill iff enrichment duplicates E-127 with no new verdicts. |
| E-566 | Weighted-limit (conical) aggregation for risk rollups | Weighted-limit rollups with exactness audit (feeds E-216). | Aggregation, L1. | Kill iff rollups mismatch exact aggregation once. |
| E-567 | Sheaf-condition audit for distributed config (feeds sheaf line) | Sheaf gluing audit on config fragments across nodes. | Config audit, L1/L2. | Kill iff gluing never catches a config drift. |
| E-568 | Topos-logic (internal-language) policy engine | Policy rules in the internal logic with audit-trail export. | Policy engine, L1. | Kill iff policy engine slower than direct checks 10×. |
| E-569 | Categorical-database (AQL-style) query audit | AQL-style queries on the analytics fragment vs SQL baseline. | Query audit, L1. | Kill iff AQL loses on all queries. |
| E-570 | Functorial reactive (FRP) engine audit (feeds E-144) | FRP engine on the feed pipeline with glitch audit. | FRP audit, L1/L2. | Kill iff glitches appear in any drill. |
| E-571 | Machine-learning (Para/optic) composition audit | Para-composition of learned models with audit trail. | ML composition, L1. | Kill iff composition never beats monolithic models. |
| E-572 | Game-theoretic (open-games) venue-choice audit | Open-games model of venue routing with equilibrium audit. | Game audit, L1. | Kill iff equilibria never match observed routing. |
| E-573 | Cybernetic (lens-based) control-loop audit (feeds E-59) | Lens-based controller audit on quoting loops. | Control audit, L1. | Kill iff controller oscillates in any drill. |
| E-574 | Categorical-probability (Markov-category) audit | Markov-category audit on the sampling stack. | Probability audit, L1/L2. | Kill iff audit finds no unsound composition in a quarter. |
| E-575 | DisCoPy-style diagrammatic testing harness | Diagrammatic test harness on pipeline morphisms. | Test harness, L1. | Kill iff harness never catches a pipeline bug. |

## Decision — Batch AJ: applied topology and geometry (E-576–E-600)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-576 | Persistent-homology (Rips) audit for regime detection | Rips barcodes on order-flow windows with regime-label audit. | TDA detection, L1. | Kill iff barcodes never beat E-207 toxicity on lead time. |
| E-577 | Mapper-graph audit for strategy clustering | Mapper graphs on strategy P&L with cluster-stability audit. | Clustering, L1. | Kill iff clusters never replicate out-of-sample. |
| E-578 | Discrete-Morse (Forman) audit for book-surface simplification | Morse simplification of depth surfaces with fidelity audit. | Simplification, L1. | Kill iff simplification distorts any fill decision. |
| E-579 | Spectral-geometry (Laplacian-eigenmap) venue embedding | Eigenmap embedding of venues with arb-prediction audit (feeds E-209). | Embedding, L1. | Kill iff embedding never predicts an arb. |
| E-580 | Hyperbolic-embedding (Poincaré) audit for hierarchy | Poincaré embeddings of instrument hierarchies with distortion audit. | Embedding, L1. | Kill iff distortion exceeds Euclidean baseline. |
| E-581 | Optimal-transport (Sinkhorn) audit for allocation | Sinkhorn allocation with cost audit (feeds E-19 kernel). | Transport audit, L1/L2. | Kill iff transport never beats greedy allocation. |
| E-582 | Wasserstein-barycenter audit for ensemble pricing | Barycenter ensembles with calibration audit. | Ensemble, L1. | Kill iff barycenter never beats best single model. |
| E-583 | Gromov-Wasserstein audit for cross-venue book matching | GW alignment of venue books with match audit. | Alignment, L1. | Kill iff alignment never improves fill rates. |
| E-584 | Curvature (Ollivier-Ricci) audit for network robustness | Ricci-curvature audit on the cluster graph (feeds E-343). | Robustness audit, L1. | Kill iff curvature never predicts a failure. |
| E-585 | Flow (Ricci-flow-style) audit for load smoothing | Flow-based load smoothing with oscillation audit (feeds E-62). | Smoothing, L1. | Kill iff smoothing oscillates in any drill. |
| E-586 | Minimal-surface (Plateau-solver) audit for E-22 | Numerical Plateau solver backing E-22's placement with mesh audit. | Solver audit, L1/L2. | Kill iff solver mesh never converges in budget. |
| E-587 | Mean-curvature-flow audit for surface denoising | MCF denoising on vol surfaces with arbitrage-preservation audit. | Denoising, L1. | Kill iff denoising creates any calendar arbitrage. |
| E-588 | Geodesic-regression audit for trend estimation | Geodesic trends on manifold-valued signals with error audit. | Regression, L1. | Kill iff trends lag linear baselines. |
| E-589 | Parallel-transport audit for cross-session calibration | Transport-based calibration alignment with error audit. | Calibration, L1. | Kill iff transport never beats direct recalibration. |
| E-590 | Holonomy-audit for E-43 path deformation | Numerical holonomy audit validating E-43's glitch-free paths. | Validation, L1/L2. | Kill iff holonomy audit contradicts hardware sim. |
| E-591 | Characteristic-class audit for E-55 descriptors | Cohomology-class computation backing E-55's obstruction reports. | Validation, L1/L2. | Kill iff classes never match injection outcomes. |
| E-592 | Index-theorem audit for E-43 anomaly loci | Family-index computation locating E-43's anomaly loci. | Validation, L2. | Kill iff loci never match glitch sites. |
| E-593 | Morse-Bott audit for E-62 gradient flow | Morse-Bott verification of E-62's flow convergence. | Validation, L2. | Kill iff flow stalls on any real load trace. |
| E-594 | Equivariant-cohomology audit for E-32 fixed points | Equivariance verification for E-32's symmetric kernels. | Validation, L2. | Kill iff symmetry claims fail on any kernel. |
| E-595 | Floer-style (action-functional) audit for execution paths | Action-functional ranking of execution paths with replay audit. | Path ranking, L1. | Kill iff ranking never beats cost-model ranking. |
| E-596 | Symplectic-capacity audit for buffer sizing | Capacity-based buffer bounds with overflow audit. | Sizing audit, L1. | Kill iff bounds are vacuous on real buffers. |
| E-597 | Contact-structure audit for E-12 dissipation grades | Contact-geometry audit grounding dissipation grades. | Validation, L1. | Kill iff grades never bind a real decision. |
| E-598 | Finsler-metric audit for anisotropic latency | Anisotropic latency metrics with path audit on the NoC model. | Metric audit, L1. | Kill iff anisotropy never changes a route. |
| E-599 | Sub-Riemannian (nonholonomic) audit for constrained routing | Constrained-geodesic routing with feasibility audit. | Routing audit, L1. | Kill iff constraints make all routes infeasible. |
| E-600 | Conformal-mapping audit for E-65 execution shaping | Conformal-map computation backing E-65's shaper. | Validation, L1/L2. | Kill iff maps never match replayed liquidity. |

## Decision — Batch AK: dynamical systems and control (E-601–E-625)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-601 | Lyapunov-function synthesis (SOS) for quoting loops | SOS-synthesized Lyapunov certificates on quoting dynamics. | Stability proof, L2/L3. | Kill iff synthesis fails on the production quoting loop. |
| E-602 | Barrier-certificate synthesis for risk limits | Barrier certificates proving risk limits unreachable-bad. | Safety proof, L2/L3. | Kill iff barriers need manual templates everywhere. |
| E-603 | Contraction-metric audit for E-64 Fatou claims | Contraction metrics validating E-64's pruning decisions. | Validation, L2. | Kill iff metric contradicts pruning outcomes. |
| E-604 | Koopman-operator (DMD) audit for flow prediction | DMD prediction on order-flow with error audit. | Prediction, L1. | Kill iff DMD lags naive predictors. |
| E-605 | Takens-embedding audit for latent-state reconstruction | Delay-embedding reconstruction with forecast audit. | Reconstruction, L1. | Kill iff reconstruction never improves forecasts. |
| E-606 | SINDy (sparse-identification) audit for impact dynamics | Sparse dynamics discovery with replay audit. | Discovery, L1. | Kill iff discovered dynamics never generalize. |
| E-607 | MPC (model-predictive) execution with horizon audit | MPC liquidation with horizon/robustness audit (vs E-34/E-61). | Control, L1/L2. | Kill iff MPC loses to E-34/E-61 on replay. |
| E-608 | LQR baseline audit for linear execution slices | LQR on linearizable slices with cost audit. | Baseline, L1. | Kill iff linearization never holds on real slices. |
| E-609 | H-infinity robust-control audit for adversarial flow | H∞ controllers with worst-case audit on adversarial traces. | Robust control, L1/L2. | Kill iff H∞ is always more conservative than naive. |
| E-610 | Sliding-mode control audit for fill tracking | Sliding-mode fill tracking with chatter audit. | Tracking, L1. | Kill iff chatter breaks venue rate limits. |
| E-611 | Adaptive-control (MRAC) audit for fee-regime shifts | MRAC adaptation with stability audit on fee shifts. | Adaptation, L1/L2. | Kill iff adaptation destabilizes in any drill. |
| E-612 | Extremum-seeking audit for fee-optimal routing | Extremum-seeking router with convergence audit. | Seeking, L1. | Kill iff seeking oscillates on real venues. |
| E-613 | Passivity-based control audit for market-making | Passivity certificates on quoting loops. | Control proof, L2. | Kill iff passivity fails on any loop. |
| E-614 | Hybrid-automaton (bouncing) audit for auction phases | Hybrid model of auction/continuous phases with reachability audit. | Hybrid audit, L1/L2. | Kill iff reachability never terminates. |
| E-615 | Timed-automaton audit for session timeouts | Timed models of session recovery with bound audit. | Timed audit, L1/L2. | Kill iff bounds exceed recovery budgets. |
| E-616 | Signal-temporal-logic (STL) monitoring for SLOs | STL monitors on latency SLOs with robustness audit. | Monitoring, L1. | Kill iff monitors miss any SLO breach. |
| E-617 | Control-barrier-function audit for halt triggers | CBF halt triggers with safety audit on crash replays. | Safety audit, L1/L2. | Kill iff triggers miss any historical halt. |
| E-618 | Reach-avoid (Hamilton-Jacobi) audit for arb capture | Reach-avoid sets for arb windows with capture audit. | Reachability, L1/L2. | Kill iff sets are empty on all real windows. |
| E-619 | Viability-kernel audit for inventory limits | Viability kernels for inventory constraints with breach audit. | Viability, L1/L2. | Kill iff kernel is empty under real limits. |
| E-620 | Attractor-reconstruction audit for toxic regimes | Attractor reconstruction on toxic-flow windows. | Reconstruction, L1. | Kill iff attractors never predict toxicity. |
| E-621 | Early-warning (critical-slowing) audit for crashes | Slowing-down indicators with lead-time audit (vs E-67). | Warning, L1. | Kill iff warnings lag E-67's walls everywhere. |
| E-622 | Tipping-point (bifurcation) audit for E-59 | Bifurcation audit validating E-59's Conley gate. | Validation, L1/L2. | Kill iff audit contradicts gate outcomes. |
| E-623 | Noise-induced-transition audit for thin books | Noise-transition analysis with fill audit on thin names. | Transition audit, L1. | Kill iff transitions never explain fills. |
| E-624 | Large-deviation (Freidlin-Wentzell) audit for tails | LD estimates on tail-latency with MC audit (vs E-54). | Tail audit, L1/L2. | Kill iff LD disagrees with MC beyond tolerance. |
| E-625 | Rare-event (importance-splitting) simulation audit | Splitting estimators with variance audit on crash traces. | Rare events, L1. | Kill iff splitting never beats crude MC. |

## Decision — Batch AL: logic, proof theory, and foundations (E-626–E-650)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-626 | Focused-sequent (LJF/LKF) elaborator audit | Focused elaboration with determinism audit (feeds E-130). | Elaboration audit, L1/L2. | Kill iff focusing slows elaboration 3×. |
| E-627 | Display-calculus audit for substructural logics | Display-calculus prototype for the ordered fragment (feeds E-131). | Prototype, L2. | Kill iff display rules never decide a real case. |
| E-628 | Nested-sequent audit for modal latency grades | Nested sequents for E-127 grades with proof audit. | Prototype, L2. | Kill iff nesting duplicates E-127 verdicts. |
| E-629 | Hypersequent audit for parallel composition | Hypersequents for fork/join reasoning with audit. | Prototype, L2. | Kill iff hypersequents never compose real branches. |
| E-630 | Bunched-sequent (BBI) prover audit (feeds E-132) | BBI prover on store-typing goals with success audit. | Prover audit, L1/L2. | Kill iff success rate <20%. |
| E-631 | Linear-logic programming (Lolli-style) audit | Lolli-style encoding of the borrow analysis with audit. | Encoding audit, L1/L2. | Kill iff encoding is slower than direct 10×. |
| E-632 | Concurrent-constraint (CHR) audit for propagation | CHR rules for bound propagation with confluence audit. | Propagation, L1. | Kill iff CHR never converges in budget. |
| E-633 | Answer-set (ASP) audit for config search | ASP search on config/schedule spaces with solution audit. | Search audit, L1. | Kill iff ASP never scales past toy spaces. |
| E-634 | Datalog (Soufflé-style) audit for program facts | Datalog fact extraction with fixpoint audit (feeds E-498). | Fact extraction, L1. | Kill iff Datalog never matches hand facts. |
| E-635 | Equality-saturation (egg) rule audit (accepted line) | Rule-set audit for the accepted equality-saturation line. | Rule audit, L1. | Kill iff rules never fire on the corpus. |
| E-636 | Rewrite-strategy (Stratego-style) audit | Strategy-controlled rewriting with termination audit. | Strategy audit, L1. | Kill iff strategies loop on real rules. |
| E-637 | Nominal (name-binding) audit for the surface syntax | Nominal techniques audit on binder-heavy proofs. | Binding audit, L2. | Kill iff nominal adds nothing over de Bruijn. |
| E-638 | Higher-order-abstract-syntax (HOAS) audit | HOAS encoding audit on the typing proofs. | Encoding audit, L2. | Kill iff HOAS exotic terms appear. |
| E-639 | Parametric-HOAS (PHOAS) audit for extraction | PHOAS audit on extraction code (feeds E-255). | Extraction audit, L2. | Kill iff PHOAS extraction diverges once. |
| E-640 | Definitional-interpreter (functional-big-step) audit | Functional big-step audit on HIREval correspondence. | Interpreter audit, L2. | Kill iff big-step misses any small-step behavior. |
| E-641 | Coinductive-big-step (divergence-tracking) audit | Divergence-tracking audit on server loops. | Divergence audit, L2. | Kill iff divergence tracking is vacuous. |
| E-642 | Step-indexed (Appel-style) audit for E-109 | Step-index audit validating E-109's model. | Validation, L3. | Kill iff indices never suffice on real heaps. |
| E-643 | Kripke-logical-relation audit for E-251 | Kripke-structure audit on closure conversion. | Validation, L3. | Kill iff worlds never cover real stores. |
| E-644 | Bisimulation-up-to audit for E-252/E-558 | Up-to techniques audit on CPS/endpoint proofs. | Technique audit, L3. | Kill iff up-to never closes a real proof. |
| E-645 | Compatibility-lemma generator audit | Generator for compatibility lemmas with coverage audit. | Automation, L2. | Kill iff generated lemmas never discharge goals. |
| E-646 | Adequacy-checker audit for LF encodings (feeds E-266) | Adequacy audit on the LF encoding. | Validation, L2. | Kill iff adequacy fails on any rule. |
| E-647 | Independence (axiom-need) audit for the spec | Axiom-need audit per lemma (no hidden classical axioms). | Hygiene audit, L2. | Kill iff audit is clean everywhere (then keep as CI). |
| E-648 | Consistency (model-construction) audit for new axioms | Model audit before any axiom admission. | Hygiene, L3. | Kill iff any admitted axiom lacks a model (then remove axiom). |
| E-649 | Proof-term size audit with compression study | Term-size audit with sharing/compression experiments. | Term audit, L1. | Kill iff compression never shrinks real terms. |
| E-650 | Hints-database (simp-set) audit with relevance study | Simp-set relevance audit on proof timings. | Timing audit, L1. | Kill iff audit never speeds a slow proof. |

## Decision — Batch AM: discrete math and combinatorics (E-651–E-675)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-651 | Expander-code (LDPC) audit for E-35 topologies | LDPC-on-expander audit for control-channel reliability. | Coding audit, L1. | Kill iff decoding never meets the control budget. |
| E-652 | Polar-code audit for feed retransmission | Polar-code evaluation on refresh channels (feeds E-387). | Coding audit, L1. | Kill iff polars lose to ARQ on all traces. |
| E-653 | Fountain-code (Raptor) audit for multicast repair | Fountain repair audit on multicast loss (feeds E-386). | Repair audit, L1. | Kill iff repair traffic exceeds unicast refresh. |
| E-654 | Network-coding audit for relay topologies | Coding-relay audit on microwave meshes. | Relay audit, L1. | Kill iff decoding delay breaks the arb budget. |
| E-655 | Gossip-code (random-linear) audit for dissemination | Random-linear gossip audit (feeds E-165). | Dissemination audit, L1. | Kill iff gossip never converges in budget. |
| E-656 | Spectral-partitioner (Fiedler) audit for E-22 | Fiedler-vector placement audit backing E-22. | Validation, L1. | Kill iff Fiedler never beats profile-guided placement. |
| E-657 | Multilevel-partitioner (METIS-style) audit | Multilevel partition audit on thread graphs. | Partition audit, L1. | Kill iff partitions never beat affinity defaults. |
| E-658 | Streaming-partitioner (one-pass) audit for live placement | One-pass placement audit under thread churn. | Live placement, L1. | Kill iff streaming never matches offline quality. |
| E-659 | Submodular-maximization audit for sensor/selection | Submodular selection with approximation audit. | Selection audit, L1. | Kill iff greedy never nears optimal on real sets. |
| E-660 | Matroid-audit for independence in scheduling | Matroid modeling audit on task-assignment constraints. | Modeling audit, L1. | Kill iff matroid never captures real constraints. |
| E-661 | Matching (blossom) audit for pairing problems | Blossom matching audit on hedge-pairing instances. | Matching audit, L1. | Kill iff matching never beats greedy pairing. |
| E-662 | Flow (push-relabel) audit for allocation | Max-flow allocation audit with gap audit. | Allocation audit, L1. | Kill iff flow never beats greedy allocation. |
| E-663 | Min-cost-flow audit for settlement routing | Min-cost settlement routing with cost audit (feeds E-60). | Routing audit, L1. | Kill iff min-cost never beats HN-guided routing. |
| E-664 | TSP-path audit for maintenance/rollout ordering | TSP ordering audit on rollout sequences. | Ordering audit, L1. | Kill iff TSP order never beats manual order. |
| E-665 | Vehicle-routing audit for courier-style settlement legs | VRP audit on physical-settlement legs (where applicable). | Routing audit, L1. | Kill iff VRP never applies (pure-electronic books). |
| E-666 | Bin-packing audit for batching (E-464 group commit) | Bin-packing audit on commit batches. | Batching audit, L1. | Kill iff packing never beats time-based batching. |
| E-667 | Scheduling-theory (Smith-rule) audit for queues | Dispatching-rule audit on analytics queues. | Queue audit, L1. | Kill iff rules never beat FIFO on real mixes. |
| E-668 | Online-algorithm (competitive-ratio) audit for paging | Competitive audit on buffer/page policies. | Policy audit, L1. | Kill iff ratios are vacuous on real traces. |
| E-669 | Caching-theory (Belady/FIF) audit for prefetch | Prefetch-policy audit on book scans. | Prefetch audit, L1. | Kill iff prefetch never helps. |
| E-670 | Sketch-switch (heavy-hitter) audit for flow telemetry | Heavy-hitter audit on feed telemetry. | Telemetry audit, L1. | Kill iff heavy hitters never explain anomalies. |
| E-671 | Graph-streaming (semi-streaming) audit for live graphs | Semi-streaming audit on live thread graphs. | Graph audit, L1. | Kill iff streaming never matches offline. |
| E-672 | Property-testing (graph) audit for topology claims | Graph-property tests on all topology claims. | Property tests, L1. | Kill iff tests never falsify a claim. |
| E-673 | Ramsey-type audit for unavoidable contention patterns | Ramsey analysis audit on contention traces. | Pattern audit, L0/L1. | Kill iff patterns never predict contention. |
| E-674 | Discrepancy (Beck-Fiala-style) audit for load balance | Discrepancy audit on shard balance. | Balance audit, L1. | Kill iff discrepancy never beats round-robin. |
| E-675 | Derandomization (conditional-expectation) audit | Derandomized-policy audit where randomness is used. | Derandomization, L1. | Kill iff derandomization never preserves guarantees. |

## Decision — Batch AN: statistics and experimental design (E-676–E-700)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-676 | Sequential-testing (SPRT) audit for strategy promotion | SPRT promotion gates with error-rate audit (feeds E-212). | Promotion gates, L1. | Kill iff SPRT never decides within the window. |
| E-677 | Multi-armed (best-arm) audit for config selection | Best-arm selection on engine configs with sample audit. | Config selection, L1. | Kill iff selection never beats manual tuning. |
| E-678 | Bayesian-optimization audit for parameter search | BO search on latency parameters with regret audit. | Param search, L1. | Kill iff BO never beats grid/random. |
| E-679 | Causal-inference (DID/synthetic-control) audit for changes | Causal audit on every production change. | Change audit, L1. | Kill iff causal estimates never agree with A/B. |
| E-680 | A/B (randomized) rollout audit for engine changes | Randomized rollout protocol with power audit. | Rollout audit, L1. | Kill iff randomization is infeasible on the path. |
| E-681 | Variance-reduction (common-random-numbers) audit | CRN audit on backtest comparisons. | Comparison audit, L1. | Kill iff CRN never tightens comparisons. |
| E-682 | Bootstrap-confidence audit for Sharpe claims | Bootstrap audit on all performance claims. | Claim audit, L1. | Kill iff claims never survive bootstrap. |
| E-683 | Multiple-testing (FDR) audit for signal mining | FDR control on mined signals with audit. | Mining audit, L1. | Kill iff FDR kills all signals incl. known-good. |
| E-684 | Selection-bias (winner's-curse) audit for promotions | Winner's-curse adjustment on promoted strategies. | Bias audit, L1. | Kill iff adjustment never changes a decision. |
| E-685 | Concept-drift (DDM/ADWIN) audit for live models | Drift detection with retrain audit on live detectors. | Drift audit, L1. | Kill iff drift never triggers before damage. |
| E-686 | Survival-analysis audit for order lifetimes | Survival models on order lifetimes with calibration audit. | Lifetime audit, L1. | Kill iff survival never beats empirical quantiles. |
| E-687 | Point-process (Hawkes) audit for arrival modeling | Hawkes arrival models with goodness-of-fit audit. | Arrival audit, L1/L2. | Kill iff Hawkes never beats Poisson on real feeds. |
| E-688 | State-space (regime-switching) audit for volatility | Regime models with filter audit (feeds E-411). | Regime audit, L1/L2. | Kill iff regimes never persist out-of-sample. |
| E-689 | Copula audit for cross-asset dependence | Copula dependence with tail audit (feeds E-61). | Dependence audit, L1. | Kill iff copulas never beat Gaussian on tails. |
| E-690 | Extreme-value (GPD/GEV) audit for tail risk | EVT tail fits with backtest audit (feeds E-54/E-624). | Tail audit, L1/L2. | Kill iff EVT never validates out-of-sample. |
| E-691 | Quantile-regression audit for slippage bands | Quantile bands on slippage with coverage audit. | Band audit, L1. | Kill iff coverage never holds out-of-sample. |
| E-692 | Conformal-prediction audit for fill intervals | Conformal intervals on fills with coverage audit. | Interval audit, L1. | Kill iff intervals are always vacuous. |
| E-693 | Anomaly-detection (isolation/clustering) audit | Anomaly detectors with precision audit on incidents. | Anomaly audit, L1. | Kill iff detectors never beat static thresholds. |
| E-694 | Root-cause (graphical-model) audit for incidents | Graphical root-cause with accuracy audit (feeds E-450). | RCA audit, L1. | Kill iff RCA is wrong on any root-caused incident. |
| E-695 | Reliability (Weibull) audit for hardware failures | Weibull failure models with fit audit (feeds E-343). | Failure audit, L1. | Kill iff fits never predict a failure class. |
| E-696 | Power-analysis audit for negative-result claims | Power audit before accepting any kill (no underpowered kills). | Meta-audit, L1. | Kill iff power is adequate everywhere (then keep as CI). |
| E-697 | Pre-registration audit for experiment briefs | Pre-registered briefs with deviation audit per experiment. | Meta-process, L0/L1. | Kill iff deviations never affect conclusions. |
| E-698 | Replication audit (independent re-run) for top claims | Independent replication of the top-10 execution claims. | Replication, L1. | Kill iff any top claim fails replication (claim dies). |
| E-699 | Adversarial-review audit for kill decisions | Adversarial review before any kill is finalized. | Meta-process, L1. | Kill iff reviews never overturn a kill (keep process). |
| E-700 | Living-register (this-file) maintenance audit | Quarterly audit: every row still has owner, baseline, and evidence link. | Meta-process, L0/L1. | Kill iff any row lacks all three at review (fix, not kill). |

## References

- ADR-019 (acceptance rule), ADR-020–022 (E-101–E-550). Baselines named per
  row are the kill instruments.
