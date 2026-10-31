# ADR-021: Frontier Register — Batches W–AB (E-251–E-400)

## Status
**Accepted** (2026-10-31). Continuation of ADR-019/020 under the same
breadth-first directive: open experiments; cuts require implementation plus
proof-burden log and execution record.

## Decision — Batch W: semantics and metatheory (E-251–E-275)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-251 | Step-indexed logical relation for closure conversion | Logical relation over the closure pass proving contextual equivalence on a fragment. | Metatheory, L3. | Kill iff relation cannot handle the chosen ADR-012 layout. |
| E-252 | Bisimulation for CPS transform correctness | Coinductive bisimulation between direct-style and CPS fragments; tested on corpus. | Transform proof, L2/L3. | Kill iff bisimulation needs full program analysis (non-compositional). |
| E-253 | Denotational model (domain-theoretic) for the pure core | CPO model for recursion + divergence; adequacy proof on the pure fragment. | Semantics, L3. | Kill iff model cannot interpret store/capability features (then scope stands). |
| E-254 | Game-semantic model for the effect fragment | HO/N game model for effect handlers; full-abstraction check on a fragment. | Semantics, L2/L3. | Kill iff model complexity exceeds any decision payoff. |
| E-255 | Realizability model for extraction to MIR | Realizability interpretation justifying extraction of proof content to code. | Extraction, L2. | Kill iff extracted code is slower than handwritten with no trust win. |
| E-256 | Parametricity (Reynolds) free theorems as rewrite rules | Free-theorem-driven rewrites (map fusion etc.) with parametricity certificates. | Optimization, L1/L2. | Kill iff rewrite fire-rate is nil on corpus. |
| E-257 | Gradual guarantee auditing (Siek pattern) | Check the gradual guarantee holds on the E-82 boundary fragment. | Gradual metatheory, L2. | Kill iff guarantee fails (then E-82 redesigns). |
| E-258 | Blame-correctness proofs for contract boundaries | Prove blame assignment sound on the boundary calculus. | Contracts proof, L2/L3. | Kill iff blame needs runtime state the zero-cost design forbids. |
| E-259 | Coeffect-graded comonadic semantics | Categorical comonad model for graded coeffects; coherence proofs. | Semantics, L2. | Kill iff model yields no new analysis beyond E-127 grades. |
| E-260 | Call-by-push-value (CBPV) IR as polarization check | CBPV structuring of the MIR value/computation split; test backend reuse. | IR design, L1/L2. | Kill iff CBPV split complicates all passes with no payoff. |
| E-261 | Polarized focusing completeness for elaboration | Completeness proof for the E-130 focusing elaborator on the linear fragment. | Proof, L3. | Kill iff completeness needs cut rules the implementation lacks. |
| E-262 | Normalization-by-evaluation (NbE) for the kernel DSL | NbE evaluator + completeness for kernel specialization (feeds E-143). | Staging proof, L2/L3. | Kill iff NbE is slower than the existing evaluator 10×. |
| E-263 | Definitional-equality decision audit | Audit equality-check cost profile across the corpus; optimize hot paths. | Performance, L1. | Kill iff audit shows equality is never the bottleneck. |
| E-264 | Unification (Miller pattern) completeness on fragment | Pattern-unification completeness proof for the elaborator's core. | Elaboration proof, L2/L3. | Kill iff fragment excludes idioms in >20% of corpus. |
| E-265 | Higher-order unification heuristics with proof witnesses | Witness-carrying HOU heuristics; failures become informative errors. | Elaboration, L1/L2. | Kill iff witnesses never explain a real user error. |
| E-266 | Logical-framework (LF/Twelf) encoding of HasType | LF encoding of the type system for independent adequacy checking. | Mechanization, L2. | Kill iff encoding diverges from the Lean spec on any rule. |
| E-267 | Adequacy of the executable interpreter vs Spec | Prove `HIREval` adequate w.r.t. the declarative semantics on the fragment. | Semantics proof, L3. | Kill iff adequacy needs determinism the semantics lacks. |
| E-268 | Compiler-correctness diagram (CompCert-style) audit | End-to-end simulation diagram audit across stages 1–3 (ADR-011). | Pipeline proof, L3. | Kill iff any stage lacks a simulation statement (log as finding). |
| E-269 | Compositional compiler correctness (vertical + horizontal) | Separate + composed correctness for optimization vs lowering passes. | Pipeline proof, L3. | Kill iff pass interactions invalidate per-pass statements. |
| E-270 | Verified separate compilation with linking certificates | Per-module certificates composed at link time (feeds linker spec). | Linking proof, L2/L3. | Kill iff certificate size exceeds object size 5×. |
| E-271 | Fully-abstract compilation on a fragment | Full abstraction for the closure/borrow boundary; test with context attacks. | Security proof, L3. | Kill iff abstraction breaks on any capability-passing test. |
| E-272 | Secure-compilation criterion audit (robust preservation) | Audit which properties survive each pass (robust preservation mapping). | Security audit, L2. | Kill iff no security property survives stage 2 (finding, redesign). |
| E-273 | Cost-semantics (time/space) soundness for grades | Prove grade annotations bound real cost on the instrumented runtime. | Cost proof, L2/L3. | Kill iff measured cost exceeds grades on any benchmark. |
| E-274 | Space-safety (no leaks) proof for arena discipline | Prove arena reset safety for the phase allocator (feeds E-19 kernel). | Memory proof, L2/L3. | Kill iff a reset frees live data in any test (then fix, not kill). |
| E-275 | Determinism proof for the replay scheduler (E-159) | Prove record/replay determinism on the covered fragment. | Determinism proof, L2. | Kill iff nondeterminism escapes on any replay test. |

## Decision — Batch X: effects, handlers, and resources (E-276–E-300)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-276 | Effect-row inference with principal rows | Principal row inference for the bounded effect set; test inference completeness. | Effect inference, L2. | Kill iff rows need annotations at every function. |
| E-277 | Evidence-passing elaboration for handlers | Elaborate handlers to evidence-passing code; benchmark vs E-73 inlining. | Elaboration, L1/L2. | Kill iff strictly dominated by E-73 on all benchmarks. |
| E-278 | Linear continuations (one-shot) enforcement | One-shot continuation check enabling stack allocation of handlers. | Effect runtime, L1/L2. | Kill iff multishot is needed on >30% of handlers. |
| E-279 | Multi-shot continuation codegen with cloning audit | Clone-cost audit for multishot handlers; compare vs heap-frame baseline. | Codegen, L1. | Kill iff cloning exceeds heap cost 2× everywhere. |
| E-280 | Effect masking (encapsulation) proofs | Prove masked effects unobservable; test with counterexamples. | Effect proof, L2/L3. | Kill iff masking leaks on any test. |
| E-281 | Resource-tracked file/network handles as effects | Handle lifecycle as effect protocol; test on gateway fragment. | Resource effects, L1/L2. | Kill iff protocol rejects valid handle-passing patterns. |
| E-282 | Exception effects with precise stack-unwind tables | Certified unwind tables for exception effects on one target. | Exception impl, L1/L2. | Kill iff table size exceeds binary budget. |
| E-283 | Async effects with I/O-uring backend mapping | Map async effects to io_uring ops; measure vs epoll baseline. | Async runtime, L1. | Kill iff uring mapping loses to epoll on benchmarks. |
| E-284 | Structured I/O cancellation with leak proofs | Cancellation that provably releases all resources on the fragment. | Cancellation proof, L2. | Kill iff a cancelled task leaks a descriptor in any test. |
| E-285 | Timeout/deadline effects with timer-wheel mapping | Deadline effects on timer wheels; test deadline-miss rate vs ad-hoc timers. | Timing effects, L1. | Kill iff miss rate exceeds ad-hoc baseline. |
| E-286 | Logging/tracing effects with zero-cost elision | Compile-time elision of disabled log levels with proof of zero residue. | Observability, L1. | Kill iff residue remains in binary audit. |
| E-287 | Metrics effects with lock-free export | Metrics effects exported via lock-free counters (feeds E-156/E-196). | Observability, L1. | Kill iff export perturbs hot path >1%. |
| E-288 | Randomness effects with audited sourcing | Randomness as effect with DRBG-health gating (feeds E-240). | Effect hygiene, L1. | Kill iff any randomness use bypasses the effect. |
| E-289 | Nondeterminism effects with search-strategy handlers | Search strategies as handlers (DFS/BFS/best-first) on a bounded solver. | Search effects, L1/L2. | Kill iff handler overhead exceeds direct search 3×. |
| E-290 | Probabilistic-programming effects (sample/observe) | Sample/observe effects with inference-handler backends (feeds Gen/Pyro line). | PPL effects, L1/L2. | Kill iff inference handlers cover only toy models. |
| E-291 | Differentiable-programming effects (grad as handler) | Gradient handlers over the reversible core (feeds E-77). | AD effects, L1/L2. | Kill iff strictly dominated by E-77's operator. |
| E-292 | Transactional (STM) effects with contention audit | STM effects with retry-rate audit on the order-book fragment (feeds E-46). | STM effects, L1/L2. | Kill iff retry storms appear under burst load. |
| E-293 | Lock effects with deadlock-freedom certificates | Lock acquisition as effect with lock-order certificates (feeds E-41). | Lock effects, L1/L2. | Kill iff certificates reject the project's own locking patterns. |
| E-294 | GPU-offload effects with transfer-cost model | Offload effects with PCIe-transfer cost grading; test on matrix kernels. | Heterogeneous, L1. | Kill iff transfer costs erase all offload wins. |
| E-295 | SIMD-lane effects with portable lane abstraction | Lane effects abstracting AVX/SVE widths; test kernel portability. | Portability, L1. | Kill iff abstraction costs >5% vs intrinsics. |
| E-296 | Memory-order effects (fence placement as handler) | Fence selection as effect interpretation per target (feeds E-66/E-178). | Memory effects, L1/L2. | Kill iff handler picks weaker ordering than manual on any litmus. |
| E-297 | Power-state effects with DVFS interpretation | Power-state effects interpreted via DVFS model (feeds E-185/E-197). | Energy effects, L0/L1. | Kill iff interpretation never saves energy on benchmarks. |
| E-298 | Migration effects for cluster task movement | Task-migration as effect with cost grading (feeds E-62). | Cluster effects, L1. | Kill iff migration effects never fire (dead feature). |
| E-299 | Checkpoint/restore effects with verified snapshots | Snapshot effects with restore-correctness proofs (feeds E-87/E-238). | Resilience effects, L1/L2. | Kill iff restore diverges from snapshot on any test. |
| E-300 | Audit/compliance effects with tamper-evident log | Compliance effects emitting hash-chained logs (feeds E-210/E-234). | Compliance, L1. | Kill iff log verification fails on any tamper test. |

## Decision — Batch Y: compilation and optimization (E-301–E-325)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-301 | Profile-guided inlining with cost-model audit | PGO inliner with per-call-site cost audit; compare vs static heuristics. | PGO, L1. | Kill iff PGO loses to static on benchmarks. |
| E-302 | Context-sensitive cloning for venue fast paths | Clone hot venue paths per caller context; measure code-growth vs win. | Specialization, L1. | Kill iff growth exceeds 2× for <5% win. |
| E-303 | Loop-invariant code motion with certified hoisting | Certified LICM on the loop fragment; test vs baseline. | Loop opts, L1/L2. | Kill iff hoisting moves a faulting op (correctness fail). |
| E-304 | Induction-variable strength reduction + audit | Certified SR on affine loops; measure on numeric kernels. | Loop opts, L1/L2. | Kill iff no kernel wins. |
| E-305 | Loop tiling/fusion for cache behavior (feeds polyhedral) | Tiled/fused loops with reuse-distance audit vs polyhedral baseline. | Loop opts, L1. | Kill iff strictly dominated by the polyhedral pass. |
| E-306 | Auto-vectorization with legality proofs | Vectorizer with dependence-legality certificates on straight-line loops. | Vectorization, L1/L2. | Kill iff legality check rejects loops LLVM vectorizes safely. |
| E-307 | SLP vectorization for parser bit-twiddling | SLP pass on parser kernels; measure vs scalar baseline. | Vectorization, L1. | Kill iff no parser kernel wins. |
| E-308 | Software pipelining (modulo scheduling) for FPGA loops | Modulo scheduler for the HLS path; compare initiation intervals vs vendor. | HLS sched, L1/L2. | Kill iff II exceeds vendor HLS on all kernels. |
| E-309 | If-conversion/predication with mispredict audit | Convert branches to predicated code where mispredict audit favors it. | Branch opts, L1. | Kill iff predication loses to E-94's model everywhere. |
| E-310 | Tail-call + sibling-call optimization with audit | Certified tail-call elimination; measure stack use on engine loops. | Call opts, L1. | Kill iff ABI constraints block all hot tail calls. |
| E-311 | Devirtualization with guarded speculation + audit | Speculative devirtualization with guard-failure stats on the gateway. | Dispatch opts, L1. | Kill iff guard failures exceed 5% on hot paths. |
| E-312 | Inline caching for dynamic dispatch points | Polymorphic inline caches on the E-82 boundary; measure hit rates. | Dispatch, L1. | Kill iff E-82 erasure subsumes all dynamic points. |
| E-313 | Escape analysis with allocation-removal audit | Stack-allocate non-escaping objects; audit removal rate on corpus. | Analysis/opt, L1/L2. | Kill iff removal rate <10% with no precision path. |
| E-314 | Scalar replacement of aggregates with field audit | SROA with field-liveness audit; test on order structs. | Scalar opts, L1. | Kill iff replacement breaks ABI layout assumptions. |
| E-315 | Global value numbering with hash-consing audit | GVN with collision/cost audit vs baseline. | Redundancy, L1. | Kill iff no win over existing CSE. |
| E-316 | Sparse conditional constant propagation (SCCP) | Certified SCCP on MIR; measure on config/param-heavy code. | Constant opts, L1/L2. | Kill iff constants are trivial in corpus. |
| E-317 | Range analysis with overflow-exclusion certificates | Range facts excluding overflow checks; test check-removal rate. | Range opt, L1/L2. | Kill iff removal breaks any overflow test. |
| E-318 | Alignment analysis with vector-load certificates | Alignment facts certifying vector loads; test on SIMD kernels. | Alignment, L1. | Kill iff alignment unknown on all hot kernels. |
| E-319 | TBAA-style type-based aliasing with soundness proof | Certified TBAA for the capability fragment; measure disambiguation win. | Aliasing, L2. | Kill iff win is nil vs E-121/122 analyses. |
| E-320 | Function-attribute inference (pure/readonly) with audit | Infer attributes enabling call CSE/hoisting; audit precision. | Attributes, L1. | Kill iff inference marks nothing pure in corpus. |
| E-321 | Cold-code outlining with I-cache audit | Outline cold blocks; measure I-cache effects on the engine binary. | Layout, L1. | Kill iff no I-cache win on the target. |
| E-322 | Hot/cold splitting with profile audit | Profile-driven splitting; test on gateway binary. | Layout, L1. | Kill iff profiles go stale within a release. |
| E-323 | Basic-block reordering (Pettis-Hansen) with audit | Trace-layout pass; measure on the matching loop. | Layout, L1. | Kill iff no measured win on the target. |
| E-324 | Link-time optimization with certificate composition | LTO with composed per-module certificates (feeds E-270). | LTO, L1/L2. | Kill iff LTO wins are nil on the engine binary. |
| E-325 | Post-link binary optimization (BOLT-style) with audit | BOLT-style reordering on shipped binaries; measure tick-to-trade delta. | Binary opt, L1. | Kill iff no measured delta on the target. |

## Decision — Batch Z: distribution and coordination continued (E-326–E-350)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-326 | Two-phase commit with presumed-abort audit | Presumed-abort 2PC on the settlement fragment; measure blocking windows. | Commit, L1. | Kill iff E-92 subsumes the fragment coordination-free. |
| E-327 | Three-phase commit with partition audit | 3PC liveness/blocking audit under partitions on the sim. | Commit, L0/L1. | Kill iff partitions block identically to 2PC (no win). |
| E-328 | Saga orchestration with compensation proofs | Saga + compensations with forward-progress proofs on settlement flows. | Workflow, L1/L2. | Kill iff compensation coverage <100% of saga steps. |
| E-329 | Outbox pattern with relay-dedup proofs | Transactional outbox with relay dedup; test duplicate rate under crashes. | Reliability, L1. | Kill iff duplicates escape dedup in any crash test. |
| E-330 | Inbox dedup with idempotence-key proofs | Inbox dedup keyed on idempotence tokens; test on gateway replay. | Reliability, L1. | Kill iff key space exhausts or collides in practice. |
| E-331 | Change-data-capture with ordering certificates | CDC stream with per-table ordering certificates feeding E-33's log. | CDC, L1/L2. | Kill iff ordering certs fail on any interleaving the log accepts. |
| E-332 | Stream joins (temporal) with watermark proofs | Temporal joins with watermark-correctness proofs on feed joins. | Streaming, L1/L2. | Kill iff watermarks stall joins past the budget. |
| E-333 | Exactly-once streaming with checkpoint audit | Checkpointed exactly-once on the analytics path; audit overhead. | Streaming, L1. | Kill iff overhead exceeds at-least-once + dedup cost. |
| E-334 | Stateful-stream snapshots (Chandy-Lamport) with audit | Certified snapshots on the analytics fragment. | Snapshots, L1/L2. | Kill iff snapshot blocks the stream past budget. |
| E-335 | Backfill/replay planner with cost model | Costed backfill planner for analytics recomputation. | Planning, L1. | Kill iff planner picks full recompute on all real cases. |
| E-336 | Schema-registry with compatibility proofs (feeds E-97) | Compatibility-checked schema evolution on streams. | Schema, L1/L2. | Kill iff strictly dominated by E-97's functorial migration. |
| E-337 | Partition assignment (sticky/rebalance) with bound proofs | Rebalance protocol with assignment-bound proofs on the sim. | Partitioning, L1/L2. | Kill iff rebalance storms appear under membership churn. |
| E-338 | Consumer-lag autoscaler with stability proofs | Lag-driven autoscaling with oscillation-freedom proof (feeds E-62 style). | Autoscaling, L1/L2. | Kill iff scaler oscillates on bursty traces. |
| E-339 | Chaos-mesh for network partitions (feeds E-239) | Partition-fault mesh validating E-92/E-79 claims. | Testbed, L1. | Kill iff mesh cannot reproduce a historical partition incident. |
| E-340 | Clock-skew injector for sync-free validation (feeds E-85) | Skew injection proving E-85's independence from wall clocks. | Testbed, L1. | Kill iff any E-85 claim needs bounded skew (finding). |
| E-341 | Jepsen-style history checker for the ledger path | Linearizability checker on ledger histories; all anomalies triaged. | Checking, L1/L2. | Kill iff checker misses an injected anomaly. |
| E-342 | Elle-style transaction checker for settlement | Adya-style anomaly checker on settlement histories. | Checking, L1/L2. | Kill iff checker false-alarms on all real histories. |
| E-343 | Correlated-failure (rack/DC) model for placement | Failure-correlation model for replica placement decisions. | Reliability model, L1. | Kill iff model never changes a placement decision. |
| E-344 | Blast-radius limiter with verified bulkheads | Bulkhead isolation with verified blast-radius bounds on the cluster. | Isolation proof, L1/L2. | Kill iff blast radius exceeds bounds in any drill. |
| E-345 | Load-shedding policy with utility proofs | Shedding policy maximizing preserved utility under overload; test on bursts. | Overload, L1/L2. | Kill iff shedding drops high-utility traffic first in any trace. |
| E-346 | Graceful-degradation ladder with verified steps | Degradation steps with per-step latency/utility certificates. | Degradation, L1. | Kill iff any step degrades utility with no latency win. |
| E-347 | Capacity planner with queueing-model calibration | Calibrated queueing planner for the gateway; test prediction error. | Planning, L1. | Kill iff prediction error exceeds 2× on real growth. |
| E-348 | Multi-region failover with RPO/RTO proofs | Certified RPO/RTO bounds on the region-failover path (feeds E-44). | Failover proof, L1/L2. | Kill iff drill RTO exceeds bound twice. |
| E-349 | Split-brain fencing (STONITH) with correctness audit | Fencing protocol audit on partition drills. | Fencing, L1. | Kill iff fencing fails any partition drill. |
| E-350 | Reconciliation (post-partition) with convergence proofs | Post-partition merge with convergence certificates (feeds E-92). | Merge proof, L1/L2. | Kill iff merge diverges on any drill history. |

## Decision — Batch AA: data, storage, and indexing (E-351–E-375)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-351 | LSM-tree tuner with cost-model certificates | Certified compaction/size-ratio tuning on the analytics store. | Storage tuning, L1. | Kill iff E-93 subsumes the store (then merge). |
| E-352 | B-tree with verified latch-coupling (ARIES-style) | Certified concurrent B-tree on the state store. | Index proof, L2/L3. | Kill iff latch coupling deadlocks in any stress test. |
| E-353 | Lock-free skip-list index with linearizability proof | Certified skip list for the symbol-routing table. | Index proof, L2/L3. | Kill iff throughput loses to the locked tree 2×. |
| E-354 | Hash-table with verified open addressing + probes | Certified probe-sequence table for the dedup path. | Table proof, L2. | Kill iff probe storms appear at target load factors. |
| E-355 | Bloom-filter sizing with FPR certificates | Certified FPR bounds for pre-filters on the feed path. | Probabilistic, L1. | Kill iff FPR exceeds bound on any real key set. |
| E-356 | Quotient/Cuckoo filters with verified operations | Certified compact filters for membership on gateways. | Probabilistic, L1/L2. | Kill iff strictly dominated by E-355 on all metrics. |
| E-357 | Count-min/HyperLogLog audit for flow telemetry | Certified sketch error bounds on telemetry aggregates. | Sketches, L1. | Kill iff sketch error misguides any capacity decision. |
| E-358 | Columnar encoding (RLE/dictionary/FSST) shootout | Encoding shootout on tick data with decode-latency accounting. | Encoding, L1. | Kill iff no encoding beats raw on latency. |
| E-359 | Compression-dictionary trainer with drift audit | Dictionary retraining with drift detection on feeds (feeds E-70/E-213). | Compression, L1. | Kill iff drift retraining never triggers on real feeds. |
| E-360 | WAL with verified truncation/replay (feeds E-20 kernel) | Certified WAL replay + truncation on the ledger fragment. | Durability proof, L2/L3. | Kill iff replay diverges from the oracle on any crash test. |
| E-361 | Checkpoint (fuzzy) with verified restore bounds | Fuzzy checkpoints with restore-time bounds on the state store. | Durability, L1/L2. | Kill iff restore exceeds bound twice. |
| E-362 | Copy-on-write snapshot isolation with proof | Certified CoW snapshots for analytics on the store. | Isolation proof, L2. | Kill iff snapshot blocks writers past budget. |
| E-363 | MVCC with certified visibility rules | Certified MVCC visibility on the state fragment. | Concurrency proof, L2/L3. | Kill iff visibility admits a phantom the spec forbids. |
| E-364 | Serializable snapshot isolation (SSI) danger audit | SSI danger-structure audit on settlement transactions. | Isolation audit, L1/L2. | Kill iff audit aborts >20% of real transactions. |
| E-365 | Time-travel queries with retention proofs | Retention-bounded time travel on the ledger fragment. | Temporal queries, L1. | Kill iff retention costs exceed storage budget. |
| E-366 | Materialized-view maintenance with increment audit | Incremental view maintenance with staleness audit (feeds E-74). | Views, L1. | Kill iff E-74 subsumes all views (merge). |
| E-367 | Secondary-index consistency with backfill proofs | Backfilled secondary indexes with consistency certificates. | Indexing, L1/L2. | Kill iff backfill blocks writes past budget. |
| E-368 | Partition pruning with constraint-exclusion proofs | Certified pruning on the analytics store. | Query opt, L1. | Kill iff pruning never fires on real queries. |
| E-369 | Statistics (histograms) with staleness audit | Staleness-audited stats for the (residual) cost-based paths. | Statistics, L1. | Kill iff stale stats misplan every Join in the test set. |
| E-370 | Query-plan cache with invalidation proofs | Certified plan-cache invalidation on schema/data change. | Plan cache, L1/L2. | Kill iff invalidation misses any change class. |
| E-371 | Vectorized execution with batch-size audit | Batched execution with size autotuning on analytics scans. | Execution, L1. | Kill iff batching loses to row-wise on all queries. |
| E-372 | Late materialization with tuple-lifetime audit | Late-mat execution with lifetime audit on wide rows. | Execution, L1. | Kill iff gains are nil on the query set. |
| E-373 | Join-order DP with cardinality Certificates (residual) | DP join ordering where E-05-style stats genuinely exist (test corpora). | Join order, L1/L2. | Kill iff E-05's rejection stands (no stats) — then close. |
| E-374 | Spill-to-disk sort with external-merge certificates | Certified external sort for oversized analytics. | Sort, L1/L2. | Kill iff in-memory always suffices (dead feature). |
| E-375 | Tiered-storage (hot/warm/cold) with migration proofs | Certified tiering on historical tick data. | Tiering, L1. | Kill iff retrieval SLA misses twice on cold data. |

## Decision — Batch AB: networking and messaging fabric (E-376–E-400)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-376 | Kernel-bypass (DPDK/EF_VI) backend with audit | Bypass backend for the gateway with drop/latency audit vs kernel stack. | I/O backend, L1. | Kill iff bypass wins are nil on the target NIC. |
| E-377 | io_uring storage/network unified backend | Unified uring backend (feeds E-283); measure vs epoll + pread baselines. | I/O backend, L1. | Kill iff uring loses on all workloads. |
| E-378 | Busy-poll vs interrupt trade audit with power model | Polling/interrupt policy with power accounting (feeds E-185). | I/O policy, L1. | Kill iff policy never switches modes in practice. |
| E-379 | Zero-copy receive (packet → book) path with proof | Certified zero-copy path from NIC buffer to book update. | Zero-copy proof, L1/L2. | Kill iff copy remains due to alignment on all NICs. |
| E-380 | Message framing (length-prefix) with fuzz proofs | Fuzz-certified framing on venue protocols. | Framing, L1. | Kill iff fuzzer finds a framing desync the checker misses. |
| E-381 | FIX/ITCH/MDP codec with spec-conformance suite | Codec + conformance corpus for the 2-venue fragment. | Codec, L1. | Kill iff codec diverges from spec on any corpus case. |
| E-382 | Session (logon/heartbeat/gap-fill) state machine proofs | Certified session recovery on venue links. | Session proof, L1/L2. | Kill iff gap-fill loses messages in any drill. |
| E-383 | Order-entry rate limiting with token-bucket proofs | Certified rate limiting on the order path. | Rate control, L1. | Kill iff limiter throttles valid bursts twice. |
| E-384 | Cancel-on-disconnect with liveness proofs | Certified COD on gateway disconnect. | Safety proof, L1/L2. | Kill iff COD fails any disconnect drill. |
| E-385 | Drop-copy (backup session) with consistency audit | Redundant session with consistency audit on failover. | Redundancy, L1. | Kill iff drop-copy diverges from primary in any drill. |
| E-386 | Multicast (PIM) feed handling with loss audit | Multicast join/loss handling with gap stats on feeds. | Multicast, L1. | Kill iff loss exceeds unicast-refresh cost breakeven. |
| E-387 | Unicast refresh/retransmit with cost audit | Refresh protocol with cost accounting vs multicast loss. | Refresh, L1. | Kill iff refresh storms appear under bursts. |
| E-388 | Microwave-link jitter model for routing (feeds E-53) | Jitter characterization feeding E-53/E-192 routing claims. | Link model, L1. | Kill iff jitter is indistinguishable from fiber (moot). |
| E-389 | FPGA NIC timestamping with calibration proofs | Calibrated NIC timestamps feeding E-181/E-220 attribution. | Timestamping, L1/L2. | Kill iff calibration drifts past PTP accuracy. |
| E-390 | PTP servo audit for residual clocked paths | Servo audit where clocks remain (comparison baseline for E-85). | Clock audit, L1. | Kill iff servo outperforms E-85's needs everywhere (finding). |
| E-391 | Congestion (ECN/BBR-style) audit for analytics links | Congestion response audit on non-critical links. | Congestion, L1. | Kill iff response never triggers on real links. |
| E-392 | Priority queuing (strict/WFQ) with bound proofs | Certified queueing bounds on the order path. | Queueing proof, L1/L2. | Kill iff bounds exceed the path budget. |
| E-393 | Traffic-shaping for venue rate limits with proofs | Shaper certified against venue limits. | Shaping, L1. | Kill iff shaper breaches any venue limit in drill. |
| E-394 | Failover (BGP/VRRP-style) with convergence audit | Convergence audit on link failover drills. | Failover, L1. | Kill iff convergence exceeds the arb-loop budget. |
| E-395 | DDoS/throttle response with utility preservation audit | Response policy preserving trading utility under floods. | Security response, L1. | Kill iff response drops trading traffic first. |
| E-396 | Packet-capture (pcap) determinism audit for replay | Capture-fidelity audit for replay experiments. | Observability, L1. | Kill iff capture drops packets the NIC counted. |
| E-397 | Order-wire encryption (TLS/Noise) overhead audit | Encryption overhead on the order path vs plaintext baseline. | Crypto cost, L1. | Kill iff overhead breaks the path budget with no venue requiring it. |
| E-398 | Clock-sync-free sequencing audit (feeds E-85) | Prove sequencing needs no wall clock on the covered fragment. | Sync-free proof, L1/L2. | Kill iff any sequence needs timestamps (finding). |
| E-399 | Cross-connect (colo) topology audit for placement | Colo topology facts feeding E-22/E-62 placement. | Topology facts, L1. | Kill iff facts never change a placement decision. |
| E-400 | End-to-end wire-to-wire latency ledger (all stages) | Per-stage wire ledger validating every latency claim jointly. | Measurement, L1. | Kill iff any claim lacks a ledger entry at review. |

## References

- ADR-019 (acceptance rule), ADR-020 (E-101–E-250). Each row names its own
  baseline; the kill instrument is the named comparison, not taste.
