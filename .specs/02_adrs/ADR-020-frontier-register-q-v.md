# ADR-020: Frontier Register — Batches Q–V (E-101–E-250)

## Status
**Accepted** (2026-10-31). Continuation of ADR-019 under the same
breadth-first directive: every entry is an open experiment; cuts require an
implementation plus its proof-burden log and execution record. Kill criteria
fire only on measured evidence.

## Decision — Batch Q: verification and proof engineering (E-101–E-125)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-101 | Proof-carrying code with LFSC certificates for MIR passes | Each lowering pass emits an LFSC-style certificate; independent checker (not the pass) validates it before the next stage runs. | Pipeline hardening, L2/L3. | Kill iff certificate-check time exceeds pass time 3× on corpus, or checker misses an injected miscompile the oracle catches. |
| E-102 | Verified mark-and-sweep collector à la CakeML | Certify a stop-the-world collector for the closure heap (ADR-012): tri-color invariant + root-set audit; test pause times vs unverified baseline. | Runtime verification, L3. | Kill iff pauses exceed 2× baseline or invariant proof stalls on the write barrier. |
| E-103 | Verified graph-coloring register allocator | Certify Briggs-style coloring + spilling for one backend target; interference-graph invariant checked per function. | Backend experiment, L2/L3. | Kill iff spill counts exceed LLVM greedy on corpus or proof burden per rule exceeds budget. |
| E-104 | Translation validation for peephole/opts passes | Per-compile alive-style validator: symbolic equivalence of pre/post MIR fragments; failed validations fall back to unoptimized code + log. | Optimizer guard, L1/L2. | Kill iff validator false-alarms on >5% of corpus or misses an injected mis-opt. |
| E-105 | Verified total lexer/parser pair (CakeML pattern) | Prove the surface lexer+parser total and sound w.r.t. the declarative grammar spec; fuzz against the existing frontend. | Frontend verification, L3. | Kill iff proof forces grammar restrictions that reject existing corpus programs. |
| E-106 | Soundness of `inferType`/`synthType` w.r.t. `HasType` | Register entry P13 from Loop 2: prove inference sound (and complete on a fragment); property-test against the typing oracle. | Typechecker proof, L3. | Kill iff soundness needs axioms beyond the spec's metatheory, or completeness fragment is trivial. |
| E-107 | Separation-logic entailment automation for store invariants | Build a small entailment solver for `HasTypeS`/store-typing spatial facts used in preservation proofs; measure auto-discharge rate. | Proof automation, L1/L2. | Kill iff auto rate <50% on the proof corpus or solver loops on cyclic heaps. |
| E-108 | Concurrent separation logic for MIR loan graphs | Extend the borrow analysis (ADR-011 stage 2) with CSL-style share accounting over loans; verify the serialization theorem under fork/join. | Concurrency proof, L2/L3. | Kill iff share accounting rejects race-free patterns the sequential analysis accepts, with no precision fix. |
| E-109 | Step-indexed (Iris-style) logic for closure-store interaction | Model the open closure-representation question (ADR-011/012) with step-indexed invariants; prove store safety for one closure layout. | Semantic model, L3. | Kill iff model admits a store escape the operational tests catch. |
| E-110 | Refinement reflection for finance kernels | Reflect pure kernel functions into the refinement logic (LiquidHaskell pattern) so SMT discharges pre/post conditions automatically. | Quant verification, L2/L3. | Kill iff reflection diverges on the kernel set or SMT timeouts dominate. |
| E-111 | Tactic-audit harness for proof scripts | Record tactic nondeterminism/flakiness across the Lean corpus: timing, backtracking counts, manual-step density per lemma. | Proof engineering, L0/L1. | Kill iff audit shows no actionable hotspots (all proofs stable/fast). |
| E-112 | Proof repair on spec change | When a `Spec.lean` changes, localize broken proofs via dependency cones and synthesize repair skeletons; measure repair acceptance. | Proof engineering, L1/L2. | Kill iff accepted-repair rate <30% on real spec edits. |
| E-113 | Differential proof testing (oracle cross-check) | Cross-check `decide`-based checks against the `HIREval`/interpreter oracle on generated programs; flag divergences as spec bugs. | Testing, L1. | Kill iff zero divergences found over 1M generated cases (then it becomes CI, not research). |
| E-114 | Verified peephole optimizer with window proofs | Each peephole rule carries a small equivalence proof over the value domain; composed by rewriting with proof terms. | Optimizer proof, L2/L3. | Kill iff rule-proof maintenance exceeds rule-authoring cost 5× with no automation fix. |
| E-115 | Verified instruction selector (BURS-style) | Tile MIR patterns to target ops with per-tile cost-correctness certificates; compare selected code quality vs heuristic selector. | Backend proof, L2/L3. | Kill iff selected code is >10% slower than heuristic on benchmarks. |
| E-116 | Verified liveness analysis (Kildall fixpoint) | Certify the backward dataflow fixpoint for one fragment; use it to justify dead-code elimination certificates. | Analysis proof, L2/L3. | Kill iff fixpoint iteration count explodes on real functions vs worklist baseline. |
| E-117 | Verified dominance frontiers and φ-placement | Prove dominance + frontier computation correct, then certify φ-insertion for the SSA stage (ADR-011 stage 3). | SSA proof, L2/L3. | Kill iff certified placement inserts >20% more φs than Cytron algorithm on corpus. |
| E-118 | Verified SSA destruction (out-of-SSA with copy folding) | Certify Sreedhar-style coalescing + copy insertion; validate against interpreter on the test suite. | SSA proof, L2/L3. | Kill iff destroyed code miscompiles any oracle test or inserts >2× copies vs baseline. |
| E-119 | Verified spill-code insertion with live-range splitting | Certify split + spill placement preserves values (location-map invariant); measure dynamic spill traffic vs LLVM. | Backend proof, L2/L3. | Kill iff traffic exceeds LLVM by >15% on benchmarks. |
| E-120 | Borrow-checker completeness on a loop-free fragment | Prove the stage-2 analysis accepts all safe programs on straight-line MIR (completeness), not just soundness; document the incompleteness boundary. | Analysis proof, L3. | Kill iff the complete fragment excludes idioms used in >10% of corpus. |
| E-121 | Verified Andersen-style inclusion alias analysis | Certify cubic inclusion-based points-to for the capability fragment; use it to sharpen loan precision. | Analysis proof, L2/L3. | Kill iff precision gain is nil on corpus or analysis time exceeds budget 10×. |
| E-122 | Verified capability points-to with strong updates | Strong-update points-to restricted to unique (`iso`) places; prove kill semantics sound; measure precision win. | Analysis proof, L2/L3. | Kill iff no precision win over Andersen on corpus. |
| E-123 | Verified generic dataflow framework (Kildall over lattices) | One certified monotone-framework engine reused by all MIR analyses; each analysis supplies lattice + transfer proofs. | Infrastructure proof, L3. | Kill iff framework overhead forces per-analysis reimplementation anyway. |
| E-124 | Verified abstract-interpretation numeric domains | Intervals + octagons with certified widening for the timing/bound passes (feeds E-06 tropical analysis). | Domain proofs, L2/L3. | Kill iff widening loses bounds the E-06 pass needs on straight-line code. |
| E-125 | Certified WCET analyzer in the aiT tradition | Abstract-interpretation + microarch model for one target; emit certified cycle upper bounds on straight-line kernels. | Timing proof, L2/L3. | Kill iff bounds are >3× measured on the target board, or model effort exceeds one engineer-quarter per target. |

## Decision — Batch R: type-system frontiers (E-126–E-150)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-126 | Linear dependent session types for venue protocols | Sessions indexed by message payloads (length-prefixed FIX fields); duality check at compile time on the 2-venue fragment. | Dialect experiment, L2/L3. | Kill iff annotation burden exceeds E-21's protocol-DSL cost with no extra faults caught. |
| E-127 | Graded modal types for latency budgets | Grades are symbolic nanosecond budgets propagated through call graphs; over-budget calls are type errors with blame paths. | Effect-adjacent typing, L1/L2. | Kill iff grade inference needs full annotations and E-28 bounds subsume it. |
| E-128 | Quantitative type theory (QTT, Idris 2 style) usage semiring | Erasure/multiplicity semiring over binders; 0-use args erased by construction in the backend. | Core typing, L2/L3. | Kill iff erasure wins are nil vs current pipeline, or semiring complicates all existing proofs. |
| E-129 | Cubical equality for layout-refinement transport | Transport layout proofs across equivalent struct shapes via cubical paths; test on SoA/AoS interop fragment. | Layout typing, L1/L2. | Kill iff transport proofs cost more than re-proving per layout. |
| E-130 | Polarized substructural logic (focusing) for the elaborator | Focusing-based elaboration for the linear fragment; measure elaborator predictability vs current implementation. | Elaborator experiment, L1/L2. | Kill iff error-message quality regresses on the test suite. |
| E-131 | Ordered linear logic for stack discipline | Ordered context enforces LIFO capture discipline for closures; test against ADR-012 layout candidates. | Closure typing, L1/L2. | Kill iff ordered discipline rejects the chosen closure layout. |
| E-132 | Bunched implications (BI) for share/separation reasoning | BI context structure for the store-typing fragment; compare proof-script length vs current `HasTypeS` style. | Logic experiment, L2. | Kill iff scripts get longer with no automation gain. |
| E-133 | Guarded recursion (Nakano-style ▷) for event loops | Later-modality types for productive server loops (feeds E-88); check one engine loop productively typed. | Totality typing, L2/L3. | Kill iff later-modality plumbing exceeds sized-types cost (E-88) with no extra coverage. |
| E-134 | Sized types for termination (Abel style) beyond E-88 | Standalone sized-type checker for the pure fragment; compare coverage vs E-88's coinductive setup. | Termination typing, L2/L3. | Kill iff it subsumes nothing E-88 misses, or inference is fully manual. |
| E-135 | Intersection types for unboxed specialization | Filter-model intersection (feeds E-90) restricted to numeric kernels; monomorphize per inhabited intersection. | Specialization, L1/L2. | Kill iff code bloat exceeds 3× for <10% speedup. |
| E-136 | Union types with flow-sensitive narrowing for parsers | Flow-narrowed unions for protocol-parser states (ITCH/MDP); exhaustiveness checked per state. | Parser typing, L1/L2. | Kill iff narrowing needs annotations at every branch. |
| E-137 | Typestate for order lifecycle (placed→acked→filled) | Typestate transitions checked on the matching-engine fragment; illegal transitions are type errors. | Domain typing, L1/L2. | Kill iff state explosion forces whole-engine annotation. |
| E-138 | Capability-based effect parametricity (confinement theorem) | Prove confinement: capabilities cannot leak across handler boundaries; test against the effect-system core. | Effect metatheory, L3. | Kill iff confinement needs runtime checks on the hot path. |
| E-139 | Region kinds with outlives inference (Rust NLL style) | Borrow regions with liveness-based inference on MIR; compare diagnostics vs Polonius-style formulation (ADR-011). | Borrow typing, L2/L3. | Kill iff diagnostics regress vs current analysis on corpus errors. |
| E-140 | Higher-rank initializer lists for arena APIs | Rank-2 arena-scoped allocation (`runST` pattern) so arenas cannot escape; test on the arena-phase allocator. | Allocator typing, L1/L2. | Kill iff rank-2 plumbing leaks into unrelated APIs. |
| E-141 | Phantom branding for venue/session identity | Brand types prevent cross-venue order confusion at zero cost; test on the 2-venue fragment. | Domain typing, L1. | Kill iff branding needs casts at every boundary (ergonomics fail). |
| E-142 | Ghost state for specification-only ledger balances | Ghost ledger variables erased at compile time but checked by SMT; test on settlement fragment. | Spec typing, L1/L2. | Kill iff ghost overhead leaks into runtime codegen. |
| E-143 | Two-level (staged) types for kernel specialization | Staged kernel DSL (both levels typed); generate venue-specific fast paths at build time. | Staging, L1/L2. | Kill iff staging wins are nil vs E-76 superoptimization on same kernels. |
| E-144 | Modal FRP types for market-data streams | Stream modalities (always/eventually) for feed handlers; check one feed pipeline. | Stream typing, L1/L2. | Kill iff modality plumbing exceeds plain iterator cost with no bugs caught. |
| E-145 | Proof-irrelevant run-time irrelevance (SProp-style) | Mark proof fields irrelevant and erased; audit binary size + runtime on proof-carrying paths. | Erasure, L1/L2. | Kill iff erasure is already complete (no measured delta). |
| E-146 | Universe-polymorphic container library | One verified container library across universes; test reuse vs duplicated monomorphic copies. | Library design, L2. | Kill iff universe plumbing confuses all downstream proofs. |
| E-147 | Layout-polymorphic struct operations | Operations generic over AoS/SoA layout with layout evidence; test on packing pass (E-42) outputs. | Layout typing, L1/L2. | Kill iff evidence passing costs runtime. |
| E-148 | Or-pattern exhaustiveness with GADT refinement | GADT-refined match checking for the HIR match fragment; test diagnostic quality. | Pattern typing, L1/L2. | Kill iff refinement needs annotations per constructor. |
| E-149 | Row types for extensible risk-check records | Row-polymorphic risk records; checks compose without subtyping hacks. | Domain typing, L1. | Kill iff row inference degrades messages vs structural subtyping (ADR-015). |
| E-150 | First-class modules with sealing for venue adapters | Sealed venue adapters with hidden invariants; test 2-venue swap without re-verification. | Modularity, L1/L2. | Kill iff sealing forces code duplication across venues. |

## Decision — Batch S: concurrency and distribution (E-151–E-175)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-151 | Structured concurrency with nurseries (Trio pattern) | Lexically scoped task trees for engine tasks; no orphaned tasks by construction on the fragment. | Runtime design, L1. | Kill iff nursery plumbing costs latency vs raw tasks on benchmarks. |
| E-152 | Work-stealing scheduler with proven deque discipline | Chase–Lev deque model + steal protocol proofs on the sim; measure throughput vs baseline scheduler. | Scheduler proof, L2/L3. | Kill iff steal contention exceeds baseline on the core counts we target. |
| E-153 | Wait-free MPSC ring with certified linearizability | One certified queue (feeds E-25/E-49); linearizability proof + hammer tests. | Primitive proof, L3. | Kill iff throughput loses to the hand-written queue by >10%. |
| E-154 | Epoch-based reclamation with certified safety | Certified EBR for the lock-free structures; test memory footprint vs hazard pointers. | Reclamation proof, L2/L3. | Kill iff footprint exceeds hazard-pointer baseline 2×. |
| E-155 | Hazard-pointer reclamation with certified protection | Certified HP variant; compare coverage + cost vs E-154 on same structures. | Reclamation proof, L2/L3. | Kill iff strictly dominated by E-154 on all metrics. |
| E-156 | Flat-combining for contended risk counters | Combining layer over hot counters; measure collapse under burst load vs sharded counters. | Contention design, L1. | Kill iff combining latency exceeds sharding tail latency. |
| E-157 | Sequence-locked market snapshots (seqlock) with tearing proofs | Certified seqlock snapshots for top-of-book; tearing-freedom proof + reader retry stats. | Snapshot proof, L2/L3. | Kill iff reader starvation appears under writer bursts. |
| E-158 | RCU for routing-table updates with grace-period proofs | Certified RCU fragment for venue tables; compare update latency vs locked tables. | Reclamation proof, L2/L3. | Kill iff grace periods stall updates past the latency budget. |
| E-159 | Deterministic scheduler for replayable engine runs | Record/replay scheduler for the matching fragment; divergences become diffable traces. | Debugging infra, L1. | Kill iff recording overhead exceeds 20% on the hot path. |
| E-160 | Message-passing ownership transfer (no shared memory) | Isolated-heap message passing on one pipeline; measure copy costs vs shared-memory baseline. | Architecture, L1. | Kill iff serialization/copy costs exceed sharing costs 3×. |
| E-161 | Actor supervision trees with certified restart semantics | Certified restart/escalation for feed actors; test recovery time vs ad-hoc restarts. | Fault tolerance, L2. | Kill iff supervision adds latency to the non-fault path. |
| E-162 | Backpressure protocols with verified boundedness | Credit/flow-control protocols with buffer-bound proofs on the feed→engine path. | Flow control proof, L2. | Kill iff verified bounds force buffers 3× larger than empirical sizing. |
| E-163 | Exactly-once delivery via idempotent handlers + dedup log | Idempotence-key discipline + dedup window; test duplicates under partition replay. | Delivery semantics, L1/L2. | Kill iff dedup state cost exceeds redelivery cost on real traces. |
| E-164 | Causal broadcast with vector-clock compression | Compressed vector clocks on the cluster fragment; measure header overhead vs wall-clock baseline. | Ordering, L1/L2. | Kill iff compression still exceeds PTP-header cost with no precision win. |
| E-165 | Gossip dissemination with proven convergence rounds | Certified round bounds for membership/price dissemination on the sim. | Dissemination proof, L2. | Kill iff rounds exceed the latency budget under churn. |
| E-166 | Anti-entropy with Merkle-tree repair proofs | Certified Merkle repair for replica divergence; measure repair traffic vs full sync. | Repair proof, L1/L2. | Kill iff repair traffic exceeds full-sync on real divergences. |
| E-167 | Single-decree Paxos model-checked on the config fragment | TLA+/model-checked Paxos for one config service; extract the verified-med core. | Consensus check, L1/L2. | Kill iff E-92's coordination-free path subsumes the fragment. |
| E-168 | Raft log with machine-checked safety (Verdi-style) | Certified Raft safety for the ledger-commit path; measure commit latency overhead. | Consensus proof, L3. | Kill iff commit latency exceeds unverified Raft by >25%. |
| E-169 | Byzantine broadcast with accountable faults | Accountable BFT broadcast on the settlement fragment with blame certificates. | BFT experiment, L1/L2. | Kill iff blame certificates cost more than E-79's synthesized protocol. |
| E-170 | Threshold signatures for settlement quorum (FROST-style) | Quorum-signed settlement batches; measure signing latency vs single-key baseline. | Crypto application, L1. | Kill iff signing latency breaks the settlement loop budget. |
| E-171 | VDF-based leader fairness for sequencer rotation | Verifiable-delay rotation for the (residual) sequencer role; test fairness vs round-robin. | Fairness, L0/L1. | Kill iff VDF delay dominates rotation interval. |
| E-172 | CRDT order-book with proven merge convergence | Operation-based CRDT book on the depth fragment; merge-convergence proof + divergence tests. | Replica design, L2. | Kill iff merge loses price-time priority vs central book. |
| E-173 | Operational-transformation for collaborative strategy editing | OT for concurrent strategy edits (feeds E-84); convergence proof on the op set. | Collaboration, L1. | Kill iff OT ops cover <80% of editor actions. |
| E-174 | Distributed deadlock detection with edge-chasing audits | Certified edge-chasing detector on the cluster sim; compare detection latency vs E-41 homology. | Detection proof, L1/L2. | Kill iff strictly dominated by E-41 on ternary cases. |
| E-175 | Priority-inheritance for risk-gate locks with bound proofs | Certified PIP with blocking-bound proofs on the gate fragment. | Realtime proof, L2. | Kill iff bounds exceed the gate budget under contention. |

## Decision — Batch T: hardware and silicon models (E-176–E-200)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-176 | Cycle-accurate NoC simulator for placement studies | One calibrated mesh/torus sim backing E-22/E-35/E-49 placement claims. | Simulation infra, L1. | Kill iff sim deviates >30% from any measured board counter we can access. |
| E-177 | Cache-coherence (MESI) executable model + litmus tests | Executable MESI + litmus suite for the fence-elision claims (E-66/E-49). | Model, L1/L2. | Kill iff model disagrees with hardware litmus outcomes. |
| E-178 | Store-buffer/LSQ model for TSO/PSO checking | Executable store-buffer model for the memory-model fragment; test fence sufficiency. | Model, L1/L2. | Kill iff model admits a forbidden outcome the architecture manual forbids. |
| E-179 | PCIe/DMA descriptor checker beyond E-55 | Extended descriptor-lifecycle checker (ownership + IOMMU mapping) on the NIC fragment. | Driver check, L1/L2. | Kill iff dominated by E-55 with no extra faults caught. |
| E-180 | IOMMU page-table walker model with fault proofs | Certified walker + fault classification for the DMA path. | I/O proof, L2. | Kill iff walker model misses a fault class from injection tests. |
| E-181 | NIC timestamping model for PTP error analysis | Error model for NIC clocks feeding E-85's sync-free comparison. | Timing model, L1. | Kill iff model cannot reproduce measured PTP jitter distribution. |
| E-182 | FPGA HLS equivalence harness (C→RTL spot checks) | Differential harness for HLS outputs on kernels; feeds E-16's checked-equivalence kernel. | Harness, L1. | Kill iff harness false-alarms on >10% of vendor HLS outputs. |
| E-183 | Systolic-array mapper for matrix kernels | Map GEMM-like kernels to a systolic model; compare utilization vs E-57 FSM flow. | Accelerator model, L1. | Kill iff utilization <50% on the kernel set. |
| E-184 | Timing-annotated mixed-signal boundary checks | Analog/digital boundary assertions for the telemetry path (feeds E-37). | Mixed-signal, L0/L1. | Kill iff assertions never fire on real traces (vacuous). |
| E-185 | Power/thermal model for dissipation-graded effects | Per-instruction energy + thermal envelope model feeding E-12's dissipation grades. | Energy model, L1. | Kill iff model error exceeds 2× on any measured workload. |
| E-186 | Row-hammer/error-injection harness for SRAM claims | Fault-injection harness backing E-68's correction claims. | Harness, L1. | Kill iff harness cannot reproduce published Row-hammer patterns on the model. |
| E-187 | Formal PCIe ordering-rule checker (producer/consumer) | Check descriptor/doorbell ordering rules on traces; emit minimal violating prefix. | Protocol check, L1/L2. | Kill iff checker misses an ordering bug the vendor tool catches. |
| E-188 | CXL memory-semantic extension model | Model CXL-attached memory semantics for E-87's persistence claims. | Memory model, L1. | Kill iff model contradicts the CXL spec on any litmus case. |
| E-189 | Deterministic replay for DMA races | Record/replay DMA + driver interleavings on the sim; diffable race traces. | Debugging, L1. | Kill iff recording perturbs timing past fidelity threshold. |
| E-190 | Hardware performance-counter validator for placement wins | Counter-backed validation (misses, crossbar stalls) for every layout claim (E-22/E-35/E-93). | Measurement, L1. | Kill iff counters show no effect where sims claimed wins (then the claim dies too). |
| E-191 | FPGA partial-reconfiguration flow harness (bitstream diffing) | Bitstream-diff + transition harness for E-43's glitch claims. | Harness, L1. | Kill iff harness cannot detect a known-glitched transition. |
| E-192 | SerDes/link-layer error model for microwave traces | Error model for the routing experiments (E-53/E-95) on microwave links. | Link model, L1. | Kill iff model cannot reproduce a recorded outage trace. |
| E-193 | Clock-domain-crossing (CDC) structural checker | Structural CDC checker for generated RTL (feeds E-78); compare vs vendor CDC tools. | RTL check, L1/L2. | Kill iff vendor tool catches a CDC bug ours misses. |
| E-194 | Reset-domain sequencing verifier | Certified reset sequencing for generated blocks. | RTL check, L1. | Kill iff reset bugs escape to sim that vendor flow catches. |
| E-195 | Scan-chain/DFT overhead auditor for generated RTL | Area/timing overhead audit for test structures on generated blocks. | DFT audit, L0/L1. | Kill iff overhead exceeds 15% with no testability win. |
| E-196 | On-chip telemetry (perf-mux) model for EP sensing | Perf-mux + sampling model backing E-37's lead-time measurements. | Telemetry model, L1. | Kill iff sampling aliasing explains away all claimed lead time. |
| E-197 | Voltage/frequency-scaling response model | DVFS response model for the energy experiments (E-185/E-96). | Power model, L1. | Kill iff model misses a measured voltage-droop fault. |
| E-198 | Radiation/SEU rate model for H-68 claims | Environment SEU-rate model grounding E-68's correction requirements. | Reliability model, L1. | Kill iff required rates are 10× above any deployment environment. |
| E-199 | Formal memory-consistency litmus suite (300+ cases) | Litmus corpus covering the memory-model fragment; all checkers must pass it. | Test corpus, L1. | Kill iff corpus duplicates vendor suites with zero new coverage. |
| E-200 | End-to-end measurement playbook (all claims reproducible) | One playbook: every execution claim re-runnable with counters + traces archived. | Process, L0/L1. | Kill iff any E-claim cannot be reproduced from its archive (then that claim dies). |

## Decision — Batch U: quantitative finance and stochastic systems (E-201–E-225)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-201 | Rough-volatility (Bergomi) pricing kernel library | Certified characteristic-function pricers for rough Bergomi on vanilla/exotic slice. | Quant library, L2/L3. | Kill iff calibration error exceeds baseline library on the same surface. |
| E-202 | Fractional-Brownian Monte Carlo with variance audit | fBm path generator (H<½) with variance accounting feeding E-23's sign-problem comparison. | Stochastics, L1/L2. | Kill iff E-23 thimbles dominate on every payoff (then merge into E-23). |
| E-203 | BSDE solver for XVA with convergence certificates | Backward-SDE solver for the XVA fragment with error certificates. | Quant solver, L2/L3. | Kill iff certificates are vacuous (bounds > notional) on real books. |
| E-204 | Almgren–Chriss frontier with impact-model plug-ins | Multi-model execution frontier (feeds E-34/E-61 comparisons); Pareto audit per model. | Execution baseline, L1. | Kill iff no model beats TWAP on replay (then baselines reset). |
| E-205 | Limit-order-book simulator with certified matching | Certified price-time matching core for all replay experiments (shared oracle). | Simulation infra, L2/L3. | Kill iff matching diverges from exchange specs on any replay case. |
| E-206 | Market-impact (propagator) estimator with confidence bands | Propagator-model fitter with honest bands; feeds execution shapers (E-65/E-59). | Estimation, L1/L2. | Kill iff bands never exclude the naive model on real data. |
| E-207 | Adverse-selection detector (markout regression suite) | Markout-based toxicity detector; feeds quoting guards (E-59/E-67). | Microstructure, L1. | Kill iff detector lags a simple spread filter with no precision win. |
| E-208 | Queue-position estimator for iceberg detection | Queue-imbalance/iceberg estimators; test fill-rate lift vs naive join. | Microstructure, L1. | Kill iff no fill lift on replay. |
| E-209 | Cross-venue latency map with arbitrage accounting | Measured latency map + fee-aware arb accounting (feeds E-60/E-63). | Measurement, L1. | Kill iff map goes stale faster than the arb loop (useless). |
| E-210 | Fee/slippage ledger with graded-effect export | Exact fee/slippage accounting exported as effect grades (feeds E-12). | Accounting, L1. | Kill iff ledger disagrees with clearing records on any day. |
| E-211 | Regulatory (MiFID II/Reg NMS) rule checker on orders | Rule checker (tick, short-sale, locked-market) on the order path; test on historical violations. | Compliance, L1/L2. | Kill iff checker misses a historical violation the manual review caught. |
| E-212 | Backtest overfitting auditor (deflated Sharpe/White reality) | Overfitting audit on every strategy change; blocks promotion on failure. | Statistics, L1. | Kill iff auditor blocks all strategies incl. known-good ones (miscalibrated). |
| E-213 | Tick-data compressor benchmark beyond E-70 | Compressor shootout (E-70 vs zstd/LZ4/Snappy) on identical feeds with latency accounting. | Benchmark, L1. | Kill iff E-70 wins everywhere (then E-70 graduates, this closes). |
| E-214 | Order-flow toxicity (VPIN/flow) with regime gating | Toxicity-gated quoting (feeds E-59/E-67); test P&L vs always-quote. | Microstructure, L1. | Kill iff gating loses P&L vs always-quote net of adverse fills. |
| E-215 | Optimal-hedge (delta/vega) engine with transaction costs | Cost-aware hedging engine; compare slippage vs naive delta on replay. | Hedging, L1/L2. | Kill iff costs erase all hedge-timing wins. |
| E-216 | Scenario (CCAR-style) risk engine with exact aggregation | Exact scenario aggregation (feeds E-32 localization comparison). | Risk engine, L1/L2. | Kill iff E-32 closed forms dominate on every scenario (merge into E-32). |
| E-217 | Margin (SPAN-style) calculator with audit trail | Margin calculator with per-position audit; test against clearing statements. | Risk/compliance, L1. | Kill iff any mismatch vs clearing margin on real portfolios. |
| E-218 | Corporate-action adjuster with certified adjustment rules | Certified split/dividend/merger adjustments for backtest integrity. | Data integrity, L1/L2. | Kill iff adjuster misses a historical action in the corpus. |
| E-219 | Symbology/venue-map resolver with conflict proofs | Certified instrument/venue mapping; conflicts become explicit errors. | Data integrity, L1. | Kill iff resolver admits a dual-mapped symbol. |
| E-220 | Latency-attribution (tick-to-trade) profiler | Per-stage tick-to-trade attribution feeding E-28 bound validation. | Profiling, L1. | Kill iff attribution disagrees with E-28's stage model structurally. |
| E-221 | Fill-probability (LOB-state-conditioned) model | Conditional fill models for router decisions (feeds E-38/E-48). | Routing model, L1/L2. | Kill iff fill lift is nil vs static routing on replay. |
| E-222 | Cancel/replace optimizer with fee-awareness | Fee-aware cancel policy; test net capture vs always-refresh. | Microstructure, L1. | Kill iff fee savings < latency cost of the policy. |
| E-223 | Auction (open/close) participation optimizer | Auction-only execution slice; compare vs continuous-session baseline. | Execution, L1. | Kill iff auction fills underperform continuous on the same names. |
| E-224 | Odd-lot/retail internalization detector | Internalization-pattern detector; test signal value vs noise. | Microstructure, L0/L1. | Kill iff signal never survives transaction costs. |
| E-225 | End-of-day reconciliation prover (ledger = clearing) | Daily proof: internal ledger equals clearing records; mismatches become tickets. | Accounting proof, L2. | Kill iff prover false-alarms >1/month on clean days. |

## Decision — Batch V: cryptography, security, and safety (E-226–E-250)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-226 | Constant-time discipline checker for crypto kernels | Certified constant-time (no secret branches/memory) on the settlement-signing path. | Side-channel check, L2. | Kill iff checker rejects the only performant implementation (then redesign, not waive). |
| E-227 | Nonce/mask misuse audit for threshold signing | Misuse detector over the E-170 signing flow; test on fault-injection traces. | Crypto audit, L1. | Kill iff detector misses an injected nonce reuse. |
| E-228 | Formal TLS/Noise handshake model for venue links | Model-checked handshake properties on the venue-link fragment. | Protocol check, L1/L2. | Kill iff model misses a machine-found attack from the literature set. |
| E-229 | Deterministic build + reproducible-binary proofs | Bit-reproducible builds with hash-equality CI gate for all artifacts. | Supply chain, L1. | Kill iff any release artifact is unreproducible after two fix attempts. |
| E-230 | SBOM + vulnerability-response pipeline | SBOM generation + response SLA tracker for the dependency set. | Supply chain, L0/L1. | Kill iff SBOM misses a shipped dependency (audit failure). |
| E-231 | Fuzzing corpus (structure-aware) for the frontend | Grammar-aware fuzzing of lexer/parser/lowerer with oracle differential vs interpreter. | Fuzzing, L1. | Kill iff 1B cases find zero divergences for a quarter (then reduce cadence, keep harness). |
| E-232 | Symbolic-execution bug hunt on the order path | Symbolic execution over bounded order-path programs; all alarms triaged. | Bug hunt, L1/L2. | Kill iff alarm precision <10% with no refinement path. |
| E-233 | Taint tracker for secret strategies → wire bytes | Taint analysis proving strategy bytes never reach wire fields; test on the gateway. | Info-flow, L1/L2. | Kill iff tracker misses an injected leak. |
| E-234 | Declassification policy with explicit release points | Release-point discipline for any intentional declassification; audit log per release. | Info-flow, L1/L2. | Kill iff any release lacks a ticketed justification (process fail). |
| E-235 | Control-flow integrity for generated binaries (software CET) | Software CET/CFI on generated code; measure overhead vs E-89 hardware tags. | Exploit mitigation, L1/L2. | Kill iff E-89 strictly dominates on all metrics (then merge). |
| E-236 | Sandboxed venue-adapter processes with capability IPC | Adapter isolation via capability IPC (feeds E-81); test escape resistance. | Isolation, L1/L2. | Kill iff sandbox adds >5% latency to the adapter path. |
| E-237 | Key-management (HSM-interface) audit for signing keys | HSM-interface audit + rotation drill for settlement keys. | Key management, L0/L1. | Kill iff a rotation drill fails (then fix, not kill — safety process). |
| E-238 | Disaster-recovery failover drill harness (feeds E-44) | Quarterly partition/kill drills measuring E-44's reconciler against RTO targets. | Resilience process, L0/L1. | Kill iff drills never find gaps for a year (then reduce cadence). |
| E-239 | Chaos-injection (latency/loss/partition) testbed | Controlled chaos suite for all distributed claims (E-79/E-92/E-165). | Testbed, L1. | Kill iff chaos finds nothing for two quarters (recalibrate, keep bed). |
| E-240 | Formal audit of randomness sources (DRBG/health) | Health-test audit for all RNG uses (nonces, jitter, VDF input). | Crypto hygiene, L1. | Kill iff any RNG use lacks a health test (fix, not kill). |
| E-241 | Memory-zeroization checker for secret buffers | Checker proving secret buffers zeroized on all paths; test on signing flow. | Hygiene check, L1/L2. | Kill iff checker misses an injected non-zeroized path. |
| E-242 | Panic-path audit (no secrets in crash dumps) | Crash-dump scrub audit for strategy material. | Hygiene audit, L0/L1. | Kill iff any drill leaks redacted material (fix, not kill). |
| E-243 | Dependency-vulnerability SLA tracker (feeds E-230) | Time-to-patch tracker with severity gating. | Process, L0/L1. | Kill iff tracker misses a published CVE in the set. |
| E-244 | Consensus-fault injection for BFT claims (feeds E-169) | Byzantine-fault injection validating E-169/E-79 blame claims. | Testbed, L1. | Kill iff injection cannot trigger any claimed detection (claims die). |
| E-245 | Side-channel (cache-timing) testbed for E-69/E-89 | Cache-timing probe suite validating fence-free claims. | Testbed, L1/L2. | Kill iff probes break a claimed-safe fragment (claim dies). |
| E-246 | Timing-side-channel audit for matching priority | Audit proving fill priority doesn't leak via timing on the gateway. | Side-channel, L1/L2. | Kill iff audit finds a leak with no fix within one iteration. |
| E-247 | Formal firewall/ACL model for venue connectivity | Model-checked ACLs for venue links; diff against deployed rules. | Network security, L1. | Kill iff deployed rules admit traffic the model denies (drift). |
| E-248 | Incident-response runbook with game-day drills | Runbooks + drills for matching-halt, data-corruption, key-compromise scenarios. | Process, L0/L1. | Kill iff any drill misses its RTO twice (rewrite runbook). |
| E-249 | Bug-bounty scope + safe-harbor for the open surface | Scoped bounty for the dialect/toolchain surface. | Process, L0/L1. | Kill iff zero valid reports in a year (rescope, keep program). |
| E-250 | Safety case (assurance-case) skeleton for the engine | GSN-style safety case linking every claim to evidence (proofs, tests, drills). | Assurance, L1. | Kill iff any top claim lacks an evidence link at review (fix, not kill). |

## References

- ADR-019 (acceptance rule, Batch 0 + A–P). Proof-engineering lineage:
  CakeML/Verdi/CompCert traditions; Kildall, Briggs, Cytron, Sreedhar,
  Chase–Lev, McSherry, Hellerstein/Bailis carried forward as cited in
  E-sets. Baselines named per row are the kill instruments.
