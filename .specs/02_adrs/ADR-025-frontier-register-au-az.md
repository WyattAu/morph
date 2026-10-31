# ADR-025: Frontier Register — Batches AU–AZ (E-851–E-1000)

## Status
**Accepted** (2026-10-31). Continuation of ADR-019–024 under the same
breadth-first directive: open experiments; cuts require implementation plus
proof-burden log and execution record. This file completes the 1000-entry
register (E-851–E-1000).

## Decision — Batch AU: language-runtime futures (E-851–E-875)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-851 | Region-inference (Tofte-Talpin) with effect-polymorphic reset | Effect-polymorphic regions inferring arena lifetimes; test annotation burden vs E-71. | Region inference, L2. | Kill iff inference needs annotations everywhere. |
| E-852 | Reference-counting (Perceus-style) with reuse audit | Reuse-credit RC with drop-specialization audit on engine structures. | RC audit, L1/L2. | Kill iff RC traffic exceeds tracing-GC pause cost. |
| E-853 | Bounded-lifetime (Cyclone-style) audit for legacy glue | Bounded-lifetime audit on any remaining unsafe glue. | Legacy audit, L1. | Kill iff glue is eliminated (then close). |
| E-854 | Move-semantics (C++-style) audit for interop structs | Move-audit on FFI structs with double-free tests (feeds E-80). | Interop audit, L1. | Kill iff moves ever double-free in tests. |
| E-855 | Garbage-collector (Immix-style) audit as fallback | Immix-fallback audit where arenas don't fit. | GC fallback, L1. | Kill iff fallback never triggers (arenas suffice). |
| E-856 | Stack-map (precise-root) audit for any managed path | Precise-root audit on managed paths. | Root audit, L1/L2. | Kill iff roots ever missed in a drill. |
| E-857 | Write-barrier (card-marking) audit for generational paths | Card-barrier audit with pause metrics. | Barrier audit, L1. | Kill iff barriers cost more than full collections. |
| E-858 | Finalizer (scope-guarded) audit for external resources | Scope-guarded finalizers with leak audit. | Finalizer audit, L1. | Kill iff any finalizer runs late past its scope. |
| E-859 | Weak-reference (ephemeron) audit for caches | Ephemeron audit on strategy caches with staleness metrics. | Cache audit, L1. | Kill iff weak refs never clear (leak). |
| E-860 | Thread-local (TLAB-style) allocation audit | TLAB audit with contention metrics on the engine. | Allocator audit, L1. | Kill iff TLABs never beat global arenas. |
| E-861 | Size-class (slab) audit for fixed book structs | Slab audit on fixed-size structs with waste metrics. | Slab audit, L1. | Kill iff waste exceeds 25%. |
| E-862 | Large-object (direct-map) audit for tick buffers | Large-object path audit on tick buffers. | Allocator audit, L1. | Kill iff large path fragments in a week. |
| E-863 | Defragmentation (compaction-pause) audit | Compaction audit with pause metrics (vs E-09 kernel). | Compaction audit, L1. | Kill iff pauses break any deadline. |
| E-864 | Allocator-fuzz (OOM-injection) audit | OOM-injection audit on all allocators. | Robustness audit, L1. | Kill iff any allocator crashes (not clean-fails) once. |
| E-865 | Leak-detector (reachability-diff) audit in CI | Reachability-diff leak gates in CI. | Leak gates, L1. | Kill iff gates never catch a leak in a quarter. |
| E-866 | Use-after-free (quarantine) audit for unsafe glue | Quarantine audit on unsafe paths. | UAF audit, L1. | Kill iff quarantine never triggers (then remove glue). |
| E-867 | Double-free (tombstone) audit for unsafe glue | Tombstone audit on unsafe paths. | Double-free audit, L1. | Kill iff tombstones never trigger (then remove glue). |
| E-868 | Buffer-overflow (canary-free, proof-based) audit | Proof-based bounds audit replacing canaries (feeds E-235). | Bounds audit, L1/L2. | Kill iff any overflow escapes in fuzzing. |
| E-869 | Integer-overflow (sanitizer) audit for unsafe glue | Sanitizer audit on glue arithmetic. | Overflow audit, L1. | Kill iff sanitizer never fires (then remove glue). |
| E-870 | Data-race (TSan-style) audit for unsafe glue | Race audit on glue threads. | Race audit, L1. | Kill iff races never found (then remove glue). |
| E-871 | Startup (cold-path) latency audit | Cold-start audit with budget gates. | Startup audit, L1. | Kill iff cold start exceeds budget twice. |
| E-872 | Shutdown (drain-path) audit with loss metrics | Drain audit proving no acknowledged-trade loss. | Shutdown audit, L1. | Kill iff any drain loses an acked trade. |
| E-873 | Signal-handler (async-safety) audit | Async-signal-safety audit on handlers. | Handler audit, L1. | Kill iff any handler calls non-async-safe code. |
| E-874 | Fork-safety audit for any forking path | Fork-safety audit with lock-state metrics. | Fork audit, L1. | Kill iff any fork deadlocks in drill. |
| E-875 | Daemonization (PID/supervision) audit | Supervision audit with restart metrics (feeds E-161). | Supervision audit, L0/L1. | Kill iff supervision never restarts correctly. |

## Decision — Batch AV: operating-system futures (E-876–E-900)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-876 | Scheduler (CFS/EEVDF-style) audit for analytics cores | Scheduler audit with latency metrics on analytics cores. | Scheduler audit, L1. | Kill iff audit never informs a pinning decision. |
| E-877 | Cgroup (CPU-quota) audit for analytics isolation | Quota audit isolating analytics from trade cores. | Isolation audit, L1. | Kill iff analytics ever steals trade cycles. |
| E-878 | IRQ-balance audit for feed NICs | IRQ-balance audit with drop metrics. | IRQ audit, L1. | Kill iff balance never beats manual pinning. |
| E-879 | Huge-page (THP) audit for book structures | Huge-page audit with TLB-miss metrics. | Page audit, L1. | Kill iff THP never reduces misses. |
| E-880 | NUMA-balancing audit (feeds E-449) | Auto-balance audit with migration metrics. | NUMA audit, L1. | Kill iff auto-balance migrates pathologically. |
| E-881 | Swap/OOM-killer audit for trade hosts | Swap/OOM audit proving trade hosts never swap. | OOM audit, L1. | Kill iff any trade host swaps once. |
| E-882 | Filesystem-choice (tmpfs/ext4) audit for hot paths | FS audit on hot spill paths. | FS audit, L1. | Kill iff FS choice never matters. |
| E-883 | Container (cgroup-namespace) audit for tooling | Container audit for non-trade tooling isolation. | Container audit, L0/L1. | Kill iff containers ever leak into trade cores. |
| E-884 | Seccomp-filter audit for trade binaries | Seccomp audit minimizing trade-binary syscalls. | Syscall audit, L1. | Kill iff any trade binary needs an unexpected syscall. |
| E-885 | Capabilities (Linux-cap) audit for trade binaries | Capability audit dropping all unneeded caps. | Cap audit, L1. | Kill iff any binary needs a dropped cap. |
| E-886 | SELinux/AppArmor-policy audit for gateways | MAC-policy audit with denial metrics. | MAC audit, L1. | Kill iff policy blocks valid traffic twice. |
| E-887 | Auditd (syscall-log) audit for compliance | Syscall-log audit feeding E-300/E-850 trails. | Trail audit, L1. | Kill iff logging drops events under load. |
| E-888 | Core-dump (redacted) audit (feeds E-242) | Redacted-dump audit with secret-scan metrics. | Dump audit, L0/L1. | Kill iff any dump leaks secrets. |
| E-889 | Kexec/kdump (crash-capture) audit | Crash-capture audit with capture-rate metrics. | Capture audit, L0/L1. | Kill iff capture fails twice. |
| E-890 | Firmware/BIOS-setting audit for latency | Firmware-setting audit (C-states, P-states, SMT) with latency metrics. | Firmware audit, L1. | Kill iff settings never affect tails. |
| E-891 | SMT (hyperthread) on/off audit for trade cores | SMT audit with interference metrics. | SMT audit, L1. | Kill iff SMT never interferes (then enable). |
| E-892 | CPU-isolation (isolcpus/nohz) audit for trade cores | Isolation audit with jitter metrics. | Isolation audit, L1. | Kill iff isolation never reduces jitter. |
| E-893 | RCU-boost/offload audit for kernel paths | RCU audit on kernel-involved paths. | RCU audit, L1. | Kill iff RCU stalls any path. |
| E-894 | Timer-migration audit for isolated cores | Timer-migration audit with jitter metrics. | Timer audit, L1. | Kill iff timers fire on isolated cores. |
| E-895 | Power-cap (RAPL) audit for trade hosts | RAPL audit with throttle metrics (feeds E-438). | Power audit, L1. | Kill iff caps throttle trades in drill. |
| E-896 | Fan/thermal-policy audit for colo hosts | Thermal audit with throttle correlation. | Thermal audit, L1. | Kill iff thermals never correlate with tails. |
| E-897 | Disk-health (SMART/NVMe-log) audit | Health audit with replacement metrics. | Health audit, L0/L1. | Kill iff audit never predicts a failure. |
| E-898 | NIC-firmware audit for feed NICs | NIC-firmware audit with drop metrics. | Firmware audit, L1. | Kill iff firmware never affects drops. |
| E-899 | BMC/IPMI-access audit for out-of-band | OOB-access audit with intrusion metrics. | OOB audit, L0/L1. | Kill iff OOB ever reachable from trade nets. |
| E-900 | Time-source (PTP/NTP-fallback) audit for residual clocks | Time-source audit wherever clocks remain. | Time audit, L1. | Kill iff sources disagree past tolerance twice. |

## Decision — Batch AW: silicon and device futures (E-901–E-925)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-901 | Cache-partitioning (CAT) audit for trade cores | CAT audit with miss metrics. | Partition audit, L1. | Kill iff CAT never reduces trade misses. |
| E-902 | Memory-bandwidth-allocation (MBA) audit (feeds E-446) | MBA audit with isolation metrics. | Bandwidth audit, L1. | Kill iff MBA never isolates trade cores. |
| E-903 | Prefetcher (HW) on/off audit for book scans | Prefetcher audit with scan metrics. | Prefetch audit, L1. | Kill iff prefetchers always hurt. |
| E-904 | Branch-predictor (hardware) audit for E-94 comparison | Hardware-predictor audit as E-94 baseline. | Predictor audit, L1. | Kill iff hardware already meets all jitter needs (finding). |
| E-905 | TLB-shootdown audit for shared mappings | Shootdown audit with stall metrics. | TLB audit, L1. | Kill iff shootdowns never appear in tails. |
| E-906 | IOMMU (DMA-remap) audit for descriptor paths | IOMMU audit with fault metrics (feeds E-180). | IOMMU audit, L1. | Kill iff IOMMU never faults on injection. |
| E-907 | SR-IOV (virtual-function) audit for feed NICs | SR-IOV audit with isolation metrics. | VF audit, L1. | Kill iff VFs never isolate feeds. |
| E-908 | RDMA (RoCE) audit for cluster links | RDMA audit with latency metrics vs TCP. | RDMA audit, L1. | Kill iff RDMA never beats kernel TCP. |
| E-909 | DPDK-polling (lcore) audit (feeds E-376) | Polling-lcore audit with power metrics. | Polling audit, L1. | Kill iff polling never beats uring. |
| E-910 | AF_XDP (kernel-bypass-lite) audit | AF_XDP audit with drop metrics. | XDP audit, L1. | Kill iff XDP never beats kernel stack. |
| E-911 | io_uring (registered-buffer) audit (feeds E-377) | Registered-buffer audit with copy metrics. | uring audit, L1. | Kill iff registration never removes copies. |
| E-912 | NVMe (polled-completion) audit for journals | Polled-completion audit with latency metrics (feeds E-464). | NVMe audit, L1. | Kill iff polling never beats interrupts. |
| E-913 | PMEM (app-direct) audit (feeds E-465) | App-direct audit with torn-write metrics. | PMEM audit, L1/L2. | Kill iff torn writes appear once. |
| E-914 | GPU-direct (RDMA) audit for analytics | GPU-direct audit with transfer metrics. | Transfer audit, L1. | Kill iff transfers never bypass CPU copies. |
| E-915 | FPGA-shell (PCIe) audit for HLS blocks | Shell audit with DMA metrics (feeds E-182). | Shell audit, L1. | Kill iff shell DMA corrupts once. |
| E-916 | SmartNIC (offload) audit for parsing | Offload audit with parse metrics (vs E-57/E-183). | Offload audit, L1. | Kill iff offload never beats host parse. |
| E-917 | DPU (data-processing-unit) audit for storage | DPU audit with offload metrics. | DPU audit, L1. | Kill iff DPU never beats host. |
| E-918 | TPM (measured-boot) audit for trade hosts | Measured-boot audit with attestation metrics. | Boot audit, L1. | Kill iff attestation fails twice. |
| E-919 | Secure-boot (UEFI) audit for trade hosts | Secure-boot audit with bypass metrics. | Boot audit, L1. | Kill iff any bypass in drill. |
| E-920 | BMC-firmware audit for supply-chain (feeds E-745) | BMC audit with hash metrics. | Supply-chain audit, L0/L1. | Kill iff BMC hashes drift once. |
| E-921 | JTAG/debug-port audit for trade hosts | Debug-port audit with access metrics. | Port audit, L0/L1. | Kill iff any debug port reachable in prod. |
| E-922 | Electromagnetic-interference (EMI) audit for colo | EMI audit with error metrics. | EMI audit, L0/L1. | Kill iff EMI never correlates with errors. |
| E-923 | Power-supply (redundant-PSU) audit | PSU audit with failover metrics. | PSU audit, L0/L1. | Kill iff failover fails any drill. |
| E-924 | Cooling-failure drill audit for colo | Cooling drill with throttle metrics. | Cooling drill, L0/L1. | Kill iff cooling drill never completes. |
| E-925 | Seismic/shock-mount audit for microwave gear | Shock audit with alignment metrics. | Shock audit, L0/L1. | Kill iff alignment never drifts (moot). |

## Decision — Batch AX: totality, termination, and the end of hangs (E-926–E-950)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-926 | Structural-recursion checker with lexicographic audit | Lexicographic-metric checker on pure functions. | Termination check, L2. | Kill iff checker rejects >30% of real functions. |
| E-927 | Size-change-termination (SCT) audit for tricky loops | SCT audit on loop-heavy kernels. | SCT audit, L2. | Kill iff SCT never certifies a real loop. |
| E-928 | Dependency-pair (DP) audit for rewrite termination | DP audit on optimizer rewrite rules (feeds E-635). | Rewrite audit, L2. | Kill iff DP never proves a real rule-set. |
| E-929 | Polynomial-interpretation audit for rule termination | Polynomial-interpretation audit on rewrite rules. | Interpretation audit, L2. | Kill iff interpretations never found automatically. |
| E-930 | Matrix-interpretation audit for rule termination | Matrix-interpretation audit as E-929 fallback. | Interpretation audit, L2. | Kill iff matrices never succeed where polynomials fail. |
| E-931 | Recursive-path-ordering (RPO) audit for rules | RPO audit on the rewrite corpus. | Ordering audit, L2. | Kill iff RPO never orients real rules. |
| E-932 | Knuth-Bendix-completion audit for decision rules | KB-completion audit on equational rules. | Completion audit, L2. | Kill iff completion never converges in budget. |
| E-933 | Confluence (critical-pair) audit for optimizer rules | Critical-pair audit on optimizer rules. | Confluence audit, L2. | Kill iff confluence never holds (then document, don't kill rules). |
| E-934 | Productivity-checker audit for E-88 server loops | Productivity audit on engine loops with bound evidence. | Productivity audit, L2/L3. | Kill iff audit rejects the production engine loop. |
| E-935 | Guardedness-checker audit for coinductive streams | Guardedness audit on stream definitions. | Guardedness audit, L2. | Kill iff guardedness rejects all real streams. |
| E-936 | Sized-type inference audit (feeds E-134) | Inference audit with annotation-burden metrics. | Inference audit, L2. | Kill iff inference is fully manual. |
| E-937 | Type-based-termination (Barton-style) audit | Type-based termination audit on the pure core. | Termination audit, L2/L3. | Kill iff audit needs whole-program info everywhere. |
| E-938 | Walther-recursion audit for nested calls | Walther-measure audit on nested-recursive kernels. | Recursion audit, L2. | Kill iff measures never found automatically. |
| E-939 | Cyclic-proof (infinite-descent) audit for loops | Cyclic-proof audit on loop safety. | Proof audit, L3. | Kill iff cyclic proofs never close. |
| E-940 | Ordinal-notation (below-ε₀) audit for termination strength | Ordinal audit calibrating termination strength claims. | Strength audit, L3. | Kill iff audit shows strength claims vacuous. |
| E-941 | Impredicativity audit for the spec logic | Impredicativity-need audit per proof (predicative where possible). | Logic audit, L3. | Kill iff audit is clean everywhere (keep as CI). |
| E-942 | Classical-axiom (choice/LEM) audit (feeds E-647) | Classical-axiom audit with constructive-alternative metrics. | Axiom audit, L3. | Kill iff audit is clean everywhere (keep as CI). |
| E-943 | Proof-irrelevance audit for runtime erasure (feeds E-145) | Irrelevance audit with binary-diff metrics. | Erasure audit, L1/L2. | Kill iff erasure already complete (close). |
| E-944 | Canonicity audit for closed kernel terms | Canonicity audit on kernel evaluation. | Canonicity audit, L3. | Kill iff canonicity fails once (spec bug). |
| E-945 | Normalization audit for the kernel fragment | Normalization audit with bound metrics. | Normalization audit, L3. | Kill iff normalization needs unproved axioms. |
| E-946 | Decidability audit for every new judgment | Decidability audit gating new judgments (acceptance-rule enforcement). | Meta-gate, L2. | Kill iff any admitted judgment lacks a decider (then remove). |
| E-947 | Conservativity audit for dialect extensions | Conservativity audit per dialect (no core-theorem breakage). | Dialect audit, L3. | Kill iff any dialect breaks a core theorem. |
| E-948 | Relative-consistency audit for new axioms | Relative-consistency audit before axiom admission (feeds E-648). | Consistency audit, L3. | Kill iff any axiom lacks a relative model. |
| E-949 | Independence-result audit (what can't be proved) | Independence audit documenting unprovable goals. | Meta-audit, L3. | Kill iff audit never documents a real boundary. |
| E-950 | Proof-assistant (kernel-soundness) audit for Lean itself | Kernel-soundness audit tracking upstream Lean issues. | Meta-audit, L3. | Kill iff upstream issue ever invalidates a proof silently. |

## Decision — Batch AY: the end of testing, consensus, and serialization (E-951–E-975)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-951 | Bisimulation-checker performance audit (feeds E-91) | Performance audit on E-91's checker with scaling metrics. | Perf audit, L1/L2. | Kill iff checker never scales past 1k states. |
| E-952 | Counterexample-explanation audit for E-91 divergences | Explanation-quality audit on divergence kernels. | Explanation audit, L1. | Kill iff explanations never guide a fix. |
| E-953 | Assume-guarantee (compositional) audit for E-91 | A/G decomposition audit scaling bisimulation to the engine. | Composition audit, L2. | Kill iff decomposition never covers the engine. |
| E-954 | Learning-based (L*-style) model inference audit | L* model inference audit on venue protocols. | Inference audit, L1/L2. | Kill iff L* never learns a real protocol in budget. |
| E-955 | Conformance-testing (ioco-style) audit for adapters | ioco audit on venue adapters with fault metrics. | Conformance audit, L1. | Kill iff ioco never finds an adapter fault. |
| E-956 | Model-based (spec-derived) test generation audit | Spec-derived test generation with coverage audit. | Generation audit, L1. | Kill iff generated tests never beat hand tests. |
| E-957 | Property-based (stateful-model) audit for the ledger | Stateful-model audit on ledger ops (vs E-239 chaos). | Stateful audit, L1. | Kill iff models never find a ledger bug. |
| E-958 | Metamorphic (follow-up-input) audit for matching | Metamorphic audit on matching outcomes. | Metamorphic audit, L1. | Kill iff relations never catch a matching bug. |
| E-959 | Mutation (operator-set) audit for E-739 detail | Operator-set audit with kill-rate metrics. | Mutation audit, L1. | Kill iff operators never kill surviving mutants. |
| E-960 | Flaky-test (order-dependence) detector audit | Order-dependence audit with quarantine metrics. | Flake audit, L0/L1. | Kill iff detector never finds an order-dependent test. |
| E-961 | Lattice-type (CRDT-proof) audit for new state (feeds E-92) | Lattice-type audit on every new replicated state. | Type audit, L1/L2. | Kill iff any new state is non-lattice without coordination proof. |
| E-962 | Coordination-avoidance (static-analysis) audit | Static audit flagging avoidable coordination. | Coordination audit, L1. | Kill iff audit never flags real coordination. |
| E-963 | Escrow/compensatation audit for non-I-confluent ops | Escrow audit on ops failing I-confluence. | Escrow audit, L1/L2. | Kill iff escrow never covers a real op. |
| E-964 | Calibration-free (CRDT-counter) audit for metrics | CRDT-counter audit on distributed metrics. | Counter audit, L1. | Kill iff counters ever diverge. |
| E-965 | G-counter/PN-counter audit for risk tallies | Counter audit on risk tallies with exactness metrics. | Counter audit, L1. | Kill iff tallies ever mismatch exact counts. |
| E-966 | OR-set/OR-map audit for working-order sets | OR-structure audit on working orders with convergence metrics. | Set audit, L1/L2. | Kill iff sets ever diverge across replicas. |
| E-967 | LWW-register audit with causality warnings | LWW audit with concurrent-write warnings. | Register audit, L1. | Kill iff warnings never fire on real races. |
| E-968 | RGA (replicated-growable-array) audit for logs | RGA audit on replicated logs with order metrics. | Log audit, L1/L2. | Kill iff RGA order ever contradicts causality. |
| E-969 | JSON-CRDT (Automerge-style) audit for strategy docs | Doc-CRDT audit on strategy docs (feeds E-173). | Doc audit, L1. | Kill iff docs ever diverge. |
| E-970 | Yjs-style (update-calculus) audit for collaboration | Update-calculus audit on collaborative editing. | Collab audit, L1. | Kill iff updates ever conflict irreversibly. |
| E-971 | Serialization-format (compat-matrix) audit for codecs | Compat-matrix audit across codec versions. | Compat audit, L1. | Kill iff matrix ever misses a break. |
| E-972 | Zero-copy (borrowed-slice) audit for hot structs | Borrowed-slice audit on hot paths (feeds E-972/E-80). | Zero-copy audit, L1. | Kill iff slices ever dangle in tests. |
| E-973 | Endianness (byte-order) audit for wire code | Byte-order audit on wire codecs. | Wire audit, L1. | Kill iff any codec mishandles order in tests. |
| E-974 | Alignment (ABI) audit for descriptor structs | Alignment audit on NIC descriptors (feeds E-55). | ABI audit, L1. | Kill iff any descriptor misaligns in tests. |
| E-975 | Checksum/CRC-selection audit for integrity fields | Checksum-strength audit with collision metrics. | Integrity audit, L1. | Kill iff any checksum collides in practice. |

## Decision — Batch AZ: the register itself and the road to experimentation (E-976–E-1000)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-976 | Claim-evidence linker (every row → artifacts) | Linker enforcing proof-log + execution-record links per row. | Register infra, L0/L1. | Kill iff any row resists linking at review (fix). |
| E-977 | Brief-template (one-page) generator for E-briefs | Template + completeness checker for experiment briefs. | Brief infra, L0/L1. | Kill iff briefs never meet the template twice. |
| E-978 | Kill-criterion parser (machine-checkable kills) | Parser turning kill prose into checkable predicates. | Kill infra, L1. | Kill iff kills resist formalization everywhere (then keep prose). |
| E-979 | Evidence-lake (append-only) for all measurements | Append-only store for every measurement backing a claim. | Evidence infra, L1. | Kill iff any measurement lacks lake entry at review. |
| E-980 | Leaderboard (best-known result) per claim family | Leaderboard tracking best proof/execution result per family. | Tracking, L0/L1. | Kill iff leaderboard never updates in two quarters. |
| E-981 | Reproduction (one-command) audit per claim | One-command reproduction audit for every execution claim. | Repro audit, L1. | Kill iff any claim irreproducible (claim dies). |
| E-982 | Cost-ledger (proof:code ratios) per experiment | Ledger tracking proof burden per experiment (acceptance-rule artifact). | Ledger, L0/L1. | Kill iff ledger never informs a scope cut. |
| E-983 | Compute-budget (tuning/sim) allocator audit | Budget allocator with ROI metrics per experiment. | Budget audit, L0/L1. | Kill iff budgets never bind (then cut budgets). |
| E-984 | Prioritization (expected-value) ranker for E-101–E-1000 | EV ranker ordering experiments by payoff × feasibility. | Planning, L0/L1. | Kill iff ranker never changes the build order. |
| E-985 | Dependency-graph (E-depends-on-E) mapper | Graph mapping experiment dependencies with cycle audit. | Planning, L1. | Kill iff graph never reveals a shared prerequisite. |
| E-986 | Graduation (L0→L3) promotion audit per experiment | Promotion audit with grade-evidence gates. | Promotion audit, L1. | Kill iff no experiment graduates in two quarters (replan). |
| E-987 | Sunset (kill-execution) audit (feeds E-800) | Kill-execution audit ensuring dead experiments stop. | Sunset audit, L0/L1. | Kill iff killed work continues (process fail). |
| E-988 | Resurrection (reopen-condition) watcher | Watcher re-evaluating reopen conditions on new evidence. | Reopen watch, L0/L1. | Kill iff no reopen ever triggers in a year (keep watching). |
| E-989 | New-proposal (intake) checklist enforcer | Intake checklist enforcing the acceptance rule on arrivals. | Intake gate, L0/L1. | Kill iff any proposal bypasses the checklist. |
| E-990 | Duplicate-detector (overlap) audit for the register | Overlap audit merging duplicate rows with evidence preserved. | Dedup audit, L0/L1. | Kill iff audit never finds an overlap (register clean). |
| E-991 | Coverage (domain-blindspot) audit for the register | Blindspot audit proposing the next 100 entries if needed. | Coverage audit, L0/L1. | Kill iff blindspots never found (register complete). |
| E-992 | External-benchmark (public-proof) linker | Linker tying internal claims to public benchmarks where possible. | Benchmark link, L1. | Kill iff no claim ever maps to a public benchmark. |
| E-993 | Publication (paper-per-graduation) pipeline audit | Pipeline turning graduated experiments into papers with artifact audit. | Publication, L0/L1. | Kill iff no paper in a year (replan). |
| E-994 | Patent-prior-art (defensive) audit for novel mechanisms | Defensive-publication audit on novel mechanisms. | IP audit, L0/L1. | Kill iff audit never files in a year (rescope). |
| E-995 | Hiring (skill-gap) audit for the experiment queue | Skill-gap audit mapping the queue to hiring needs. | Hiring audit, L0/L1. | Kill iff queue never informs a hire. |
| E-996 | Risk (kill-blast-radius) audit for shared-core experiments | Blast-radius audit for experiments touching the trusted core. | Risk audit, L1. | Kill iff any core-touching experiment breaks the core build. |
| E-997 | Rollback (experiment-revert) drill audit | Revert drills proving experiments detach cleanly. | Revert audit, L1. | Kill iff any experiment cannot detach in a drill. |
| E-998 | Postmortem (kill-decision) quality audit (feeds E-699) | Postmortem audit on every finalized kill. | Kill audit, L1. | Kill iff any kill lacks its proof + execution evidence. |
| E-999 | Register-completeness (1000-count) audit — this row | Count audit proving E-101–E-1000 continuity with no gaps or duplicates. | Meta-audit, L0/L1. | Kill iff any gap/duplicate found (then fix the register). |
| E-1000 | Experimentation-kickoff gate (all briefs filed) | Gate opening the experimentation phase once briefs exist per row family. | Phase gate, L0/L1. | Kill iff gate opens with missing briefs (process fail). |

## References

- ADR-019 (acceptance rule), ADR-020–024 (E-101–E-850). This file completes
  the register at E-1000. No cuts without implementation + proof + execution
  evidence; E-999 audits continuity, E-1000 gates the experimentation phase.
