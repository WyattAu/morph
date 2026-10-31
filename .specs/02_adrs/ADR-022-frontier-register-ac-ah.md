# ADR-022: Frontier Register — Batches AC–AH (E-401–E-550)

## Status
**Accepted** (2026-10-31). Continuation of ADR-019/020/021 under the same
breadth-first directive: open experiments; cuts require implementation plus
proof-burden log and execution record.

## Decision — Batch AC: numerical methods and solvers (E-401–E-425)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-401 | Symplectic integrator suite beyond E-10 (higher-order Yoshida) | 4th/6th-order Yoshida compositions with proved preservation on the sim fragment. | Quant-sim library, L3. | Kill iff drift bound unprovable at required step counts. |
| E-402 | Exponential integrators for stiff market-impact ODEs | Lawson/EPI-style integrators on stiff impact models; compare vs implicit Euler. | Solver library, L1/L2. | Kill iff stiffness never appears in real impact models. |
| E-403 | IMEX splitting for multiscale feed/signal dynamics | Implicit-explicit splitting on fast/slow feed dynamics; measure step wins. | Solver library, L1/L2. | Kill iff splitting loses to fully implicit on benchmarks. |
| E-404 | Monte Carlo Greeks (pathwise/LR/malliavin-selective) | Greek estimators with variance audit per payoff class (feeds E-14 kernel). | Quant library, L1/L2. | Kill iff E-14 weights dominate everywhere (merge). |
| E-405 | Quasi-Monte Carlo (Sobol/Niederreiter) with Koksma audit | QMC pricers with star-discrepancy audit vs MC variance. | Sampling, L1. | Kill iff effective dimension kills QMC wins on real payoffs. |
| E-406 | Multilevel Monte Carlo (Giles) with level audit | MLMC telescoping with per-level variance audit on path-dependent slice. | Sampling, L1/L2. | Kill iff level-0 cost dominates (no telescoping win). |
| E-407 | Adaptive mesh (AMR) for HJB pockets | AMR HJB on transient-liquidity pockets; compare vs uniform grid (feeds E-34). | PDE solver, L1/L2. | Kill iff E-34 Lax integration dominates everywhere. |
| E-408 | Sparse-grid (Smolyak) high-dimensional interpolation | Sparse grids for multi-asset value surfaces; measure curse relief. | Interpolation, L1. | Kill iff dimensionality still explodes on real books. |
| E-409 | Spectral (Chebyshev) methods for smooth value functions | Chebyshev spectral solver on smooth payoff slice; compare vs FD. | PDE solver, L1/L2. | Kill iff payoff kinks destroy spectral convergence. |
| E-410 | Radial-basis-function meshfree interpolation for surfaces | RBF vol-surface interpolation with shape-parameter audit. | Interpolation, L1. | Kill iff conditioning fails on real surfaces. |
| E-411 | Kalman/particle filtering for latent toxicity states | Filters for latent order-flow states feeding E-214/E-207 detectors. | Filtering, L1/L2. | Kill iff filters lag naive estimators with no accuracy win. |
| E-412 | Change-point detection (CUSUM/SR) for regime shifts | Certified detection-delay bounds on regime-shift suite. | Detection, L1/L2. | Kill iff detection delay exceeds reaction budget. |
| E-413 | Online convex optimization (regret-bounded) for quoting | Regret-bounded quoting updates; compare vs E-59 Conley gate. | Online learning, L1/L2. | Kill iff regret bounds are vacuous on real traces. |
| E-414 | Bandit (UCB/Thompson) venue selection with audit | Bandit router across venues with regret audit (feeds E-38/E-221). | Routing, L1. | Kill iff bandit explores into toxic venues repeatedly. |
| E-415 | Distributionally-robust optimization for impact models | DRO execution with ambiguity-set audit; test worst-case vs nominal. | Robust opt, L1/L2. | Kill iff robust policy is always the naive policy. |
| E-416 | Stochastic-gradient Langevin dynamics for calibration | SGLD calibration with convergence audit on vol surfaces. | Calibration, L1. | Kill iff SGLD never converges within the calibration window. |
| E-417 | Automatic-differentiation-through-calibration audit | End-to-end AD through calibrator with gradient-accuracy audit. | AD application, L1. | Kill iff gradients are unusable (noisy) for optimization. |
| E-418 | Interval arithmetic (validated numerics) for margin math | Validated intervals on margin/collateral math (feeds E-217). | Validated numerics, L1/L2. | Kill iff interval blowup makes results useless. |
| E-419 | Fixed-point (integer-only) pricing fast paths | Integer-only pricers for venue FPGAs; equivalence audit vs float. | Fixed-point, L1. | Kill iff quantization breaks any conformance case. |
| E-420 | Posit/unum arithmetic evaluation vs IEEE754 | Posit evaluation on pricing kernels with accuracy/latency audit. | Arithmetic eval, L0/L1. | Kill iff posits lose to floats on both metrics. |
| E-421 | Stochastic rounding audit for low-precision accumulators | Stochastic-rounding accumulators with bias audit on reductions. | Rounding, L1. | Kill iff bias persists on real reductions. |
| E-422 | Mixed-precision (FP16/FP8) inference audit for detectors | Mixed-precision toxicity/fill models with accuracy audit. | Precision, L1. | Kill iff accuracy drops below detector thresholds. |
| E-423 | FFT-based (Carr-Madan) pricing with truncation audit | FFT pricers with truncation/aliasing audit on vanilla slice. | Quant library, L1. | Kill iff truncation error exceeds tolerance on real surfaces. |
| E-424 | PDE-constrained calibration (adjoint) with gradient audit | Adjoint calibration on local-vol models; compare vs bump-and-revalue. | Calibration, L1/L2. | Kill iff adjoint gradients mismatch finite differences. |
| E-425 | Surrogate (GP/neural) model with uncertainty gating | Surrogate pricers gated by uncertainty; fallback audit. | Surrogates, L1. | Kill iff fallback rate exceeds 50% (surrogate useless). |

## Decision — Batch AD: real-time, scheduling, and timing (E-426–E-450)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-426 | Response-time analysis (RTA) for engine task sets | Certified RTA bounds on the engine task set with blocking terms. | Schedulability proof, L2/L3. | Kill iff bounds exceed periods on the real task set (then redesign). |
| E-427 | Priority-ceiling protocol with certified blocking bounds | PCP on gate locks with bound proofs (feeds E-175). | Locking proof, L2. | Kill iff ceiling blocks a high-priority trade twice. |
| E-428 | EDF scheduler with density-test certification | Certified EDF density test on the analytics task set. | Scheduler proof, L2. | Kill iff density exceeds 1 on the real set. |
| E-429 | Mixed-criticality (Vestal) scheduling for trade vs analytics | Criticality-level scheduler isolating trade path from analytics. | Scheduling, L1/L2. | Kill iff analytics ever delays a trade in drill. |
| E-430 | Time-triggered (TTA) static schedule for the hot loop | Static TT schedule for parse→signal→risk→wire with jitter audit. | Static sched, L1. | Kill iff jitter exceeds E-28's certified bound. |
| E-431 | Cyclic executive with frame-overrun proofs | Certified frame bounds on the cyclic hot loop. | Executive proof, L2. | Kill iff any overrun in stress drill. |
| E-432 | Tickless (dynamic-tick) audit for idle power | Dynamic-tick policy with wake-latency audit (feeds E-185). | Power policy, L1. | Kill iff wake latency breaks any deadline. |
| E-433 | Interrupt-affinity planner with cache-audit | IRQ pinning planner with locality audit on the gateway. | Affinity, L1. | Kill iff pinning never beats default affinity. |
| E-434 | NAPI-polling budget audit for feed handlers | Polling-budget policy with drop audit under bursts. | I/O sched, L1. | Kill iff drops exceed interrupt-mode baseline. |
| E-435 | Real-time GC (Metronome-style) pause-bound audit | Pause-bound audit if any managed runtime enters the stack. | GC audit, L1. | Kill iff any pause exceeds the trade-path budget. |
| E-436 | Lock-free timer wheel with certified expiry order | Certified timer wheel for E-285 deadline effects. | Timer proof, L2. | Kill iff expiry misorders in any stress test. |
| E-437 | Watchdog hierarchy with certified detection latency | Watchdog tree with detection-bound proofs (feeds E-238/E-248). | Supervision proof, L2. | Kill iff detection misses any injected hang. |
| E-438 | Thermal-throttle response with deadline preservation | Throttle policy preserving trade deadlines; drill audit. | Thermal policy, L1. | Kill iff throttling drops a trade deadline in drill. |
| E-439 | Jitter (release/queuing) decomposition ledger | Per-source jitter ledger validating E-28/E-430 budgets jointly. | Measurement, L1. | Kill iff unaccounted jitter exceeds 10% of budget. |
| E-440 | End-to-end latency SLO prover (budget algebra) | Budget-algebra prover composing per-stage bounds into SLO certificates. | SLO proof, L1/L2. | Kill iff composition is unsound on any interleaving test. |
| E-441 | Graceful overload (bounded-tardiness) proofs | Tardiness bounds under transient overload on analytics tasks. | Overload proof, L2. | Kill iff tardiness is unbounded in any drill. |
| E-442 | Mode-change protocol with certified transition bounds | Certified mode transitions (open/auction/halt) with bound proofs. | Mode proof, L1/L2. | Kill iff any transition exceeds bound in drill. |
| E-443 | Fault-tolerant clock (Byzantine) audit for residual clocks | Audit where clocks remain; comparison baseline for E-85. | Clock audit, L1. | Kill iff audit shows clocks unnecessary everywhere (then E-85 graduates). |
| E-444 | Execution-time server (Deferrable/ Sporadic) audit | Server-capacity audit for aperiodic trade events. | Server audit, L1. | Kill iff capacity analysis is vacuous on real arrivals. |
| E-445 | Cache-related preemption-delay (CRPD) analysis | CRPD bounds on the trade path with measurement validation. | Cache analysis, L1/L2. | Kill iff CRPD exceeds the path budget. |
| E-446 | Memory-bandwidth regulator with isolation proofs | Bandwidth regulation isolating trade cores (feeds E-62/E-49). | Isolation proof, L1/L2. | Kill iff regulation throttles trade cores in any drill. |
| E-447 | DRAM-refresh interference audit on tail latency | Refresh-interference measurement on tail percentiles. | Interference audit, L1. | Kill iff refresh never appears in tails (moot). |
| E-448 | SMI-interrupt audit for tail-latency spikes | SMI detection/correlation audit on spike traces. | Interference audit, L1. | Kill iff SMIs never correlate with spikes. |
| E-449 | NUMA-migration cost/benefit ledger (feeds E-22) | Migration ledger validating E-22 placement decisions. | Measurement, L1. | Kill iff migrations never pay back within the window. |
| E-450 | Deadline-miss root-cause classifier with evidence log | Classifier attributing misses to budget stages; all misses ticketed. | Diagnostics, L1. | Kill iff classifier is wrong on any root-caused miss. |

## Decision — Batch AE: storage engines and persistence (E-451–E-475)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-451 | Append-only segment store with verified compaction | Certified leveled compaction on tick segments. | Store proof, L2. | Kill iff compaction write-amp exceeds 10×. |
| E-452 | Bitcask-style hint-file index with crash audit | Crash-safe hint index with pull-the-plug audit. | Crash audit, L1/L2. | Kill iff any plug test loses acknowledged writes. |
| E-453 | Log-structured state store with segment-CRC proofs | CRC-chained segments with corruption-detection proofs. | Integrity proof, L2. | Kill iff corruption escapes detection in injection. |
| E-454 | Erasure-coded (Reed-Solomon) cold tick archive | RS-coded cold archive with reconstruction drill audit. | Archive, L1. | Kill iff reconstruction misses its RTO. |
| E-455 | Deduplicating chunk store with collision audit | Content-chunked dedup with hash-collision audit on tick data. | Dedup, L1. | Kill iff dedup ratio <1.1× (not worth it). |
| E-456 | Delta-of-delta + Gorilla-style tick codec shootout | Codec shootout on timestamp/price streams with latency accounting. | Codec, L1. | Kill iff no codec beats raw + zstd on both metrics. |
| E-457 | Dictionary-of-dictionaries venue codec with version proofs | Versioned codec dicts with compatibility proofs (feeds E-336). | Codec compat, L1/L2. | Kill iff version skew breaks any decoder in drill. |
| E-458 | Zero-copy deserialization (FlatBuffers-style) audit | Access-without-parse audit on hot structs. | Serde, L1. | Kill iff access is slower than parse on hot structs. |
| E-459 | Schema-less (self-describing) fallback path audit | Fallback decoder cost audit when schemas mismatch. | Compatibility, L1. | Kill iff fallback never triggers in practice (dead). |
| E-460 | Snapshot (point-in-time) export with consistency proofs | Certified snapshot export for analytics. | Export proof, L1/L2. | Kill iff export blocks writers past budget. |
| E-461 | Incremental backup with changed-block proofs | Changed-block incremental backup with restore drill. | Backup, L1. | Kill iff restore misses RTO twice. |
| E-462 | Remote-replica shipping with lag proofs | Replica lag bounds on the DR path (feeds E-348). | Replication proof, L1/L2. | Kill iff lag exceeds RPO in any drill. |
| E-463 | Quorum-replicated journal with acknowledged-write proofs | Quorum journal with write-ack proofs on settlement path. | Journal proof, L2. | Kill iff ack latency breaks settlement budget. |
| E-464 | Single-node fsync-minimal journal with batching proofs | Batched group-commit journal with durability proofs. | Journal proof, L2. | Kill iff batching loses acknowledged writes in plug test. |
| E-465 | NVM-direct (DAX) access path with torn-write audit | Torn-write audit on DAX-mapped structures (feeds E-87). | NVM audit, L1/L2. | Kill iff torn writes appear in any plug test. |
| E-466 | Copy-on-write file clone audit for backtest datasets | Clone-based dataset provisioning with integrity audit. | Provisioning, L1. | Kill iff clone integrity fails any checksum. |
| E-467 | Tiered compaction (hot NVMe → cold object) with proofs | Tiering policy with retrieval-bound proofs (feeds E-375). | Tiering proof, L1/L2. | Kill iff cold retrieval misses SLA twice. |
| E-468 | Object-store (S3-style) multipart audit for archives | Multipart upload audit with integrity proofs. | Archive, L1. | Kill iff multipart corrupts any archive in drill. |
| E-469 | Lifecycle (retention) policy with legal-hold proofs | Retention engine with legal-hold override proofs. | Retention proof, L1. | Kill iff any held record is deleted in audit. |
| E-470 | Encryption-at-rest with key-rotation proofs | Rotation protocol with re-encryption proofs on tick archives. | Encryption, L1/L2. | Kill iff rotation leaves any unencrypted extent. |
| E-471 | Tamper-evident (hash-chained) ledger with auditor proofs | Hash-chained ledger with third-party verification path (feeds E-300). | Ledger proof, L2. | Kill iff chain verification fails on any tamper test. |
| E-472 | GDPR-style erasure with tombstone proofs | Certified erasure with tombstone propagation proofs. | Erasure proof, L1/L2. | Kill iff any erased record resurfaces in audit. |
| E-473 | Compaction-budget scheduler with write-stall proofs | Compaction scheduling with stall-bound proofs. | Scheduler proof, L1/L2. | Kill iff stalls exceed bound in any burst. |
| E-474 | Store-benchmark (YCSB-style) harness for all backends | Uniform benchmark across store backends with published numbers. | Benchmark, L1. | Kill iff harness never changes a backend choice (moot). |
| E-475 | Corruption-recovery runbook with game-day proofs | Recovery drills with RTO proofs per corruption class. | Recovery, L1. | Kill iff any class misses RTO twice. |

## Decision — Batch AF: compilers for accelerators (E-476–E-500)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-476 | GPU (PTX) backend realization (feeds E-26/E-40) | Second realization functor to PTX on matrix kernels with conformance tests. | Backend, L1/L2. | Kill iff PTX output diverges from scalar on any kernel. |
| E-477 | FPGA (HLS C) backend realization with equivalence spot-checks | HLS-C realization with differential checks vs scalar (feeds E-182). | Backend, L1/L2. | Kill iff equivalence fails on any kernel. |
| E-478 | Vector (SVE/RVV) backend with length-agnostic proofs | Length-agnostic vector codegen with predication proofs. | Backend, L1/L2. | Kill iff predicated code loses to fixed-width everywhere. |
| E-479 | Sparse-tensor (CSR) kernel library with format proofs | CSR kernels with format-invariant proofs on book-depth structures. | Sparse lib, L1. | Kill iff dense beats sparse on all real structures. |
| E-480 | Quantized (INT8) inference kernels with error audit | INT8 detector kernels with accuracy audit (feeds E-422). | Quantization, L1. | Kill iff error exceeds detector thresholds. |
| E-481 | Kernel-fusion (epilogue) pass with numerics audit | Fusion pass with numerics-equivalence audit on pricing chains. | Fusion, L1. | Kill iff fusion changes any price beyond tolerance. |
| E-482 | Autotuner (TVM-style) for kernel schedules with budget | Schedule search with tuning-time budget on matrix kernels. | Autotuning, L1. | Kill iff tuning never beats default schedule. |
| E-483 | Roofline-model audit for every kernel claim | Roofline placement for all accelerator claims. | Analysis, L1. | Kill iff any claim exceeds roofline (invalid claim). |
| E-484 | Memory-hierarchy (shared/global) placement proofs | Placement proofs for GPU memory tiers on kernels. | Placement proof, L1/L2. | Kill iff placement loses to default on all kernels. |
| E-485 | Cooperative-groups/warp-primitive audit | Warp-level primitive use with correctness audit. | GPU correctness, L1. | Kill iff any primitive use diverges across architectures. |

## Decision — Batch AG: observability and Developer experience (E-486–E-510)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-486 | Structured logging with schema proofs (feeds E-286) | Log schemas with compatibility proofs across releases. | Logging, L1. | Kill iff schema churn breaks any dashboard twice. |
| E-487 | Trace (span) propagation with sampled-tail audit | Tail-aware sampling preserving slow traces; audit capture rate. | Tracing, L1. | Kill iff sampling drops all slow traces in practice. |
| E-488 | Continuous profiling (pyroscope-style) with overhead audit | Always-on profiling with overhead audit on hot path. | Profiling, L1. | Kill iff overhead exceeds 2%. |
| E-489 | Flame-graph diffing in CI with regression gates | CI flame diffs gating performance regressions. | Perf CI, L1. | Kill iff diffs never catch a real regression in a quarter. |
| E-490 | eBPF probes for production introspection with safety audit | eBPF probes with verifier-pass audit on production hosts. | Introspection, L1. | Kill iff verifier rejects all useful probes. |
| E-491 | REPL for the kernel DSL with fidelity proofs | REPL evaluating identically to compiled kernels. | DX, L1. | Kill iff REPL diverges from compiled output once. |
| E-492 | Notebook (Jupyter-style) strategy lab with audit trail | Strategy notebooks with full audit/export trail. | DX, L0/L1. | Kill iff notebooks cannot export to production kernels. |
| E-493 | Time-travel debugger for engine replays | Deterministic replay debugger on recorded traces (feeds E-159). | Debugging, L1. | Kill iff replay diverges on any recorded trace. |
| E-494 | Data-breakpoint (watchpoint) support for book corruption | Watchpoints trapping book invariant violations with stack evidence. | Debugging, L1. | Kill iff watchpoints miss any injected corruption. |
| E-495 | Fuzz-to-minimized-case reducer with proof of minimality | Reducer producing minimal reproducers with coverage-equivalence check. | Fuzzing DX, L1. | Kill iff reduction never shrinks a real case. |

## Decision — Batch AH: program analysis extras (E-496–E-520)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-496 | Demand-driven (IDE-speed) borrow queries | On-demand borrow facts for editor integration; latency audit. | IDE analysis, L1. | Kill iff query latency exceeds 100ms on real files. |
| E-497 | Incremental analysis with verified invalidation | Incremental MIR analysis with invalidation proofs on edits. | Incrementality proof, L2. | Kill iff invalidation misses any edit class. |
| E-498 | Call-graph (RTA/VTA) construction audit | Call-graph precision audit on the engine binary. | Call graphs, L1. | Kill iff graph misses any dynamic call in tests. |
| E-499 | Reflection/dynamic-load audit for closed-world claims | Audit that no dynamic loading breaks closed-world optimizations. | Closed-world, L1. | Kill iff any plugin path violates assumptions. |
| E-500 | Dead-feature (config-gated) elimination with audit | Config-driven feature elimination with behavior-equivalence audit. | Feature opts, L1. | Kill iff elimination breaks any config in tests. |

## (Batch AH continued — analysis precision: E-501–E-525)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-501 | Path-sensitive (BFS-bounded) symbolic executor | Bounded symbolic execution on the order path; alarm triage audit. | Symbolic exec, L1/L2. | Kill iff path explosion blocks all real entry points. |
| E-502 | Under-constrained symbolic (function-level) summaries | Function summaries from under-constrained execution; reuse audit. | Summaries, L1. | Kill iff summaries never transfer across callers. |
| E-503 | Separation-logic shape analysis for book structures | Shape graphs for book/feed structures with materialization audit. | Shape analysis, L1/L2. | Kill iff shapes never stabilize on real structures. |
| E-504 | Numeric-shape (length/capacity) coupling analysis | Length/capacity coupling facts for buffer code; bounds-removal audit. | Buffer analysis, L1/L2. | Kill iff no bounds check is removed safely. |
| E-505 | String/bytes analysis for protocol fields | Field-length facts for codec code; audit on ITCH/MDP codecs. | Codec analysis, L1. | Kill iff facts never discharge a codec check. |
| E-506 | Taint-driven sink audit for order fields | Taint from venue bytes to order fields with sink audit. | Taint, L1. | Kill iff taint misses any injected field confusion. |
| E-507 | Information-flow (noninterference) audit for strategies | Noninterference audit on strategy/gateway boundary (feeds E-233). | Info-flow, L2. | Kill iff audit is vacuous (everything tainted). |
| E-508 | Side-effect summary inference for handler fusion | Effect summaries enabling handler fusion (feeds E-73/E-277). | Effect summaries, L1/L2. | Kill iff fusion never fires on real handlers. |
| E-509 | Purity-checked memoization with invalidation proofs | Memoization with purity + invalidation proofs on pricing functions. | Memoization proof, L1/L2. | Kill iff memoization never hits on real books. |
| E-510 | Concurrency-dependence (MHP) analysis for race audit | May-happen-in-parallel facts for race triage (feeds E-66). | MHP analysis, L1/L2. | Kill iff MHP is everything-parallel (useless). |
| E-511 | Lockset analysis with guarded-access audit | Lockset facts cross-checked against E-293 certificates. | Locksets, L1. | Kill iff locksets contradict certificates everywhere. |
| E-512 | Wait-graph analysis for lock-order audit | Wait-graph cycle audit on gate locks (feeds E-174). | Deadlock audit, L1. | Kill iff wait graphs never match runtime orders. |
| E-513 | Region-escape audit for arena discipline (feeds E-274) | Escape facts validating arena resets. | Escape analysis, L1/L2. | Kill iff escape forces whole-program arenas. |
| E-514 | Thread-escape audit for stack-allocation safety | Thread-escape facts for stack allocation (feeds E-313). | Escape analysis, L1/L2. | Kill iff everything escapes in practice. |
| E-515 | Ownership-transfer audit for message passing (feeds E-160) | Transfer facts validating isolation. | Isolation audit, L1/L2. | Kill iff transfers need copies everywhere. |
| E-516 | Protocol-state (typestate) inference for sessions | Inferred typestates for session code (feeds E-137). | Typestate inference, L1/L2. | Kill iff inference needs full annotations. |
| E-517 | units/dimension analysis for price/qty confusion | Dimension facts preventing price/qty mixups on order structs. | Units analysis, L1. | Kill iff analysis false-alarms on all real code. |
| E-518 | Currency-unit analysis for multi-FX confusion | Currency facts on settlement code (feeds E-60). | Units analysis, L1. | Kill iff currency is always dynamic in practice. |
| E-519 | Rounding-mode audit for pricing determinism | Rounding-mode facts ensuring deterministic pricing. | Determinism audit, L1. | Kill iff modes vary uncontrollably per target. |
| E-520 | Exception-flow analysis for unwind-table pruning | Exception-flow facts pruning unwind tables (feeds E-282). | Exception analysis, L1. | Kill iff pruning breaks any unwind test. |
| E-521 | Callback-reentrancy audit for handler safety | Reentrancy facts on venue callbacks. | Reentrancy audit, L1. | Kill iff callbacks are always reentrant (moot). |
| E-522 | Initialization-definiteness for book structs | Definite-assignment facts on hot structs. | Init analysis, L1. | Kill iff init is always dynamic. |
| E-523 | Nullability-flow audit (Option-safety) | Option-flow facts removing redundant checks. | Nullability, L1. | Kill iff checks are never redundant. |
| E-524 | Integer-overflow audit with wrapping certificates | Overflow facts with explicit wrapping certificates where intended. | Overflow audit, L1/L2. | Kill iff wrapping intent is never documented. |
| E-525 | Division-by-zero audit for price ratios | Zero-denominator facts on ratio code. | Div-zero audit, L1. | Kill iff denominators are never provable nonzero. |

## (Batch AH continued — verification of analyses: E-526–E-550)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-526 | Verified interval-domain operations | Certified interval arithmetic for E-124's domain. | Domain proof, L2/L3. | Kill iff operations are unsound on any bound test. |
| E-527 | Verified octagon-domain closure | Certified octagon closure for relational facts. | Domain proof, L2/L3. | Kill iff closure cost exceeds analysis budget 10×. |
| E-528 | Verified widening-operator convergence | Convergence proofs for widening on the analysis corpus. | Widening proof, L3. | Kill iff widening diverges on any real function. |
| E-529 | Verified narrowing (post-widening) precision audit | Narrowing precision audit on bound queries. | Narrowing audit, L1/L2. | Kill iff narrowing never recovers precision. |
| E-530 | Verified concurrent-fixpoint (chaotic iteration) engine | Certified chaotic iteration for concurrent analyses. | Engine proof, L3. | Kill iff engine is slower than sequential 5× with no precision win. |
| E-531 | Verified BDD-backed (binary-decision) domain ops | Certified BDD ops for boolean abstraction. | Domain proof, L2. | Kill iff BDDs blow up on all real predicates. |
| E-532 | Verified SAT-backed path feasibility checks | SAT-discharged path feasibility on symbolic paths (feeds E-501). | Feasibility proof, L1/L2. | Kill iff SAT time dominates execution time 100×. |
| E-533 | Verified counterexample minimization for alarms | Certified minimal counterexamples for analysis alarms. | Alarm quality, L1/L2. | Kill iff minimized cases mislead triage twice. |
| E-534 | Alarm-triage (true/false) classifier with audit | Classifier with precision audit on historical alarms. | Triage, L1. | Kill iff precision <50% after tuning. |
| E-535 | Suppression (baseline) manager with drift audit | Baseline suppressions with drift detection on new code. | Suppression mgmt, L1. | Kill iff drift reintroduces suppressed bugs. |
| E-536 | Analysis-composition (reduced product) framework | Reduced-product composition of domains with precision audit. | Composition, L1/L2. | Kill iff composition never beats single domains. |
| E-537 | Trace-partitioning (path-merging control) audit | Partitioning policy with cost/precision audit. | Partitioning, L1. | Kill iff partitioning explodes cost with no precision win. |
| E-538 | Loop-unrolling (bounded) for analysis precision | Bounded unrolling policy with audit on loop-heavy code. | Precision policy, L1. | Kill iff unrolling never changes verdicts. |
| E-539 | Function-summary (bottom-up) verification | Certified summaries for bottom-up analysis. | Summary proof, L2. | Kill iff summaries are unsound on any test. |
| E-540 | Context-sensitivity (k-CFA) tuning audit | k-tuning policy with cost/precision audit. | Sensitivity audit, L1. | Kill iff k>0 never pays off. |
| E-541 | Heap-abstraction (recency/alloc-site) shootout | Abstraction shootout on book/feed structures. | Heap abstraction, L1/L2. | Kill iff no abstraction stabilizes shapes. |
| E-542 | Numeric-trace (policy-iteration) solver audit | Policy-iteration solver with convergence audit. | Solver audit, L1/L2. | Kill iff iteration diverges on any real loop. |
| E-543 | Max-plus (tropical) policy iteration (feeds E-06) | Tropical policy iteration for timing games. | Tropical solver, L1/L2. | Kill iff dominated by E-06's direct analysis. |
| E-544 | Game-solving (minimax) for adversarial scheduling | Game solutions for adversarial packet arrivals. | Game solving, L1. | Kill iff game model never matches arrivals. |
| E-545 | Strategy-iteration for stochastic games on queues | Stochastic-game iteration on buffer models. | Game solving, L1. | Kill iff iteration never converges in budget. |
| E-546 | Predicate-abstraction (CEGAR) loop audit | CEGAR loop with refinement audit on the order path. | CEGAR audit, L1/L2. | Kill iff refinement never terminates on real code. |
| E-547 | Interpolation-based (Craig) refinement audit | Interpolant refinement audit on spurious alarms. | Refinement audit, L1/L2. | Kill iff interpolants never generalize. |
| E-548 | Horn-clause (CHC) encoding shootout for verifiers | CHC encoding comparison across solver backends. | Encoding, L1. | Kill iff no backend solves the corpus in budget. |
| E-549 | IC3/PDR reachability audit for safety properties | IC3/PDR runs on gate safety properties. | Reachability, L1/L2. | Kill iff IC3 never converges on real properties. |
| E-550 | k-induction audit for loop safety properties | k-induction runs on loop-heavy kernels. | Induction audit, L1/L2. | Kill iff k-induction needs k>depth everywhere. |

## References

- ADR-019 (acceptance rule), ADR-020/021 (E-101–E-400). Baselines named per
  row are the kill instruments.
