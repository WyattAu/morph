# ADR-024: Frontier Register — Batches AO–AT (E-701–E-850)

## Status
**Accepted** (2026-10-31). Continuation of ADR-019–023 under the same
breadth-first directive: open experiments; cuts require implementation plus
proof-burden log and execution record.

## Decision — Batch AO: physics-inspired compute (E-701–E-725)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-701 | Quantum-annealing (Ising-embedding) audit for E-100 | Embedding audit for E-100's coupling maps on annealer sim. | Validation, L0/L1. | Kill iff embeddings never fit real instances. |
| E-702 | Coherent-Ising-machine (optical) sim audit | Optical-CIM sim audit on routing fragments. | Sim audit, L0/L1. | Kill iff CIM never beats SA on quality/time. |
| E-703 | Simulated-annealing (parallel-tempering) baseline audit | PT-SA baseline all E-100 claims must beat. | Baseline, L1. | Kill iff SA already meets all budgets (then E-100 narrows). |
| E-704 | Memristor-crossbar VMM audit for E-83 | Crossbar VMM sim audit with noise/drift modeling. | Device audit, L0/L1. | Kill iff drift destroys all mapped kernels. |
| E-705 | Photonic-MAC (MZI-mesh) audit for pricing kernels | MZI-mesh MAC audit with phase-error modeling. | Device audit, L0/L1. | Kill iff phase errors exceed kernel tolerance. |
| E-706 | Spiking-neural (LIF) audit for event detection | LIF-network audit on microburst detection (vs E-37). | Detection audit, L0/L1. | Kill iff spikes lag EP sensors everywhere. |
| E-707 | Oscillator-Ising (Kuramoto) audit for scheduling | Kuramoto-sync audit on task-assignment fragments. | Scheduling audit, L0/L1. | Kill iff sync never yields feasible schedules. |
| E-708 | Thermodynamic-computing (noise-harvest) audit | Noise-harvested sampling audit with quality metrics. | Sampling audit, L0/L1. | Kill iff samples never pass randomness health (E-240). |
| E-709 | Reversible-logic (adiabatic) audit for E-77 | Adiabatic-gate audit on the reversible core. | Device audit, L0/L1. | Kill iff adiabatic overhead exceeds tape savings. |
| E-710 | Superconducting-logic (SFQ) timing audit | SFQ timing audit on hot-loop fragments. | Device audit, L0/L1. | Kill iff SFQ never fits the loop in budget. |
| E-711 | Cryogenic-DRAM retention audit for E-99 | Cryo-retention audit on the volumetric model. | Memory audit, L0/L1. | Kill iff retention never meets refresh budgets. |
| E-712 | DNA-storage (codec) audit for cold archives | DNA-codec audit on tick archives with cost modeling. | Archive audit, L0/L1. | Kill iff cost exceeds tape 100× with no density need. |
| E-713 | Microfluidic-latency audit (physical transport) | Transport-latency audit for any physical-leg claims. | Transport audit, L0/L1. | Kill iff transport never enters the critical path. |
| E-714 | MEMS-oscillator stability audit for timestamping | MEMS-stability audit feeding E-389 calibration. | Stability audit, L1. | Kill iff MEMS never meets PTP-grade stability. |
| E-715 | Atomic-clock (chip-scale) audit for residual sync | Chip-scale-clock audit as E-85 comparison baseline. | Clock audit, L1. | Kill iff chip clocks already meet all sync needs (finding). |
| E-716 | Quantum-key-distribution (QKD) audit for venue links | QKD-link audit with key-rate modeling. | Link audit, L0/L1. | Kill iff key rates never support session rotation. |
| E-717 | Post-quantum (ML-KEM/Dilithium) migration audit | PQC migration audit on venue handshakes (feeds E-228). | Migration audit, L1. | Kill iff PQC handshake breaks the session budget. |
| E-718 | Homomorphic-encryption (BFV/CKKS) audit for analytics | FHE audit on outsourced analytics with cost modeling. | Crypto audit, L0/L1. | Kill iff FHE overhead exceeds 1000× with no threat need. |
| E-719 | MPC (garbled-circuit) audit for joint settlement | MPC audit on two-party settlement with round audit. | Crypto audit, L0/L1. | Kill iff rounds exceed the settlement budget. |
| E-720 | Zero-knowledge (plonk-style) audit for compliance proofs | ZK audit on compliance statements with prover-time audit. | Crypto audit, L0/L1. | Kill iff prover time exceeds reporting windows. |
| E-721 | Trusted-execution (SGX/SEV) audit for strategy secrecy | TEE audit on strategy isolation with side-channel audit. | Isolation audit, L1. | Kill iff TEE side channels leak in any probe test. |
| E-722 | Photonic-interconnect (co-packaged) audit for E-95 | Co-packaged-optics audit with loss modeling. | Interconnect audit, L0/L1. | Kill iff losses exceed the link budget. |
| E-723 | 3D-stacked (HBM-adjacent) compute audit for kernels | Near-memory compute audit on pricing kernels. | Placement audit, L1. | Kill iff near-memory never beats GPU on kernels. |
| E-724 | Wafer-scale (Cerebras-style) mapping audit | Wafer-mapping audit on dataflow kernels. | Mapping audit, L0/L1. | Kill iff mapping never fits real kernels. |
| E-725 | Analog-in-memory (PCM) drift-compensation audit | Drift-compensation audit on analog-mapped kernels. | Compensation audit, L0/L1. | Kill iff drift defeats all compensation in a week. |

## Decision — Batch AP: advanced logic and proof technology (E-726–E-750)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-726 | Higher-order-unification (pattern-fragment) tuning audit | Tuning audit on elaborator HOU with success metrics (feeds E-264). | Tuning audit, L1. | Kill iff tuning never improves success rates. |
| E-727 | E-matching (quantifier-instantiation) audit for SMT | E-matching audit on finance verification goals. | SMT audit, L1/L2. | Kill iff instantiation loops on all real goals. |
| E-728 | MBQI (model-based-instantiation) audit | MBQI audit on quantified risk invariants. | SMT audit, L1/L2. | Kill iff MBQI never discharges a real invariant. |
| E-729 | CHC (Spacer-style) audit for E-548 shootout detail | Spacer-run audit on gate safety properties. | Solver audit, L1/L2. | Kill iff Spacer never converges in budget. |
| E-730 | PDR (property-directed) audit for E-549 detail | PDR-run audit on ledger safety. | Solver audit, L1/L2. | Kill iff PDR diverges on all real properties. |
| E-731 | Bounded-model-checking (CBMC-style) audit for C-ABI glue | BMC audit on any remaining C-ABI glue (feeds E-80). | Glue audit, L1/L2. | Kill iff glue is eliminated entirely (then close). |
| E-732 | Abstract-interpretation (Apron-style) audit for E-124 | Apron-domain audit on bound queries. | Domain audit, L1/L2. | Kill iff Apron never beats hand domains. |
| E-733 | Symbolic-execution (KLEE-style) audit for E-501 detail | KLEE-run audit on parser entry points. | Executor audit, L1/L2. | Kill iff executor never reaches depth on real parsers. |
| E-734 | Concolic (DART-style) audit for gateway paths | Concolic-run audit on gateway branches. | Executor audit, L1. | Kill iff concolic never flips a real branch. |
| E-735 | Fuzzing (AFL++-style) audit for E-231 detail | AFL++-run audit on codec entry points. | Fuzzer audit, L1. | Kill iff fuzzer never covers new edges in a week. |
| E-736 | Grammar-aware (protobuf-style) fuzz audit | Structured-input fuzz audit on session messages. | Fuzzer audit, L1. | Kill iff structured fuzz never beats byte fuzz. |
| E-737 | Differential (cross-impl) fuzz audit for codecs | Cross-impl differential audit on FIX/ITCH codecs. | Differential audit, L1. | Kill iff impls never disagree in a quarter. |
| E-738 | Metamorphic-relation audit for pricing oracles | Metamorphic relations on pricers (symmetry/scale) with violation audit. | Oracle audit, L1. | Kill iff relations never catch a pricer bug. |
| E-739 | Mutation-testing audit for the test suite | Mutation-score audit on engine tests with kill-rate gates. | Test-quality audit, L1. | Kill iff mutation score stays <50% after effort. |
| E-740 | Coverage (MC/DC) audit for gate safety code | MC/DC audit on risk-gate code. | Coverage audit, L1. | Kill iff coverage cannot reach targets. |
| E-741 | Flakiness (quarantine) audit for CI reliability | Flake-rate audit with quarantine policy. | CI audit, L0/L1. | Kill iff flakes never reproduce (then keep quarantine). |
| E-742 | Performance-regression (benchmark-guard) audit | Benchmark-guard audit on hot paths (feeds E-489). | Perf audit, L1. | Kill iff guards never catch a regression. |
| E-743 | Documentation (doc-test) audit for specs | Doc-test audit keeping spec examples executable. | Doc audit, L0/L1. | Kill iff examples rot within a release (then fix). |
| E-744 | Changelog (semantic-diff) audit for releases | Semantic-diff audit on release notes vs behavior. | Release audit, L0/L1. | Kill iff diffs never match behavior twice. |
| E-745 | Dependency (SBOM-diff) audit per release (feeds E-230) | SBOM-diff audit gating releases. | Supply-chain audit, L0/L1. | Kill iff diffs never flag a risk. |
| E-746 | License-compatibility audit for the dependency set | License audit with incompatibility tickets. | License audit, L0/L1. | Kill iff audit is clean for a year (keep as CI). |
| E-747 | Secret-scanning audit for the repo surface | Secret-scan audit on every commit. | Secret audit, L0/L1. | Kill iff scans never find a true positive in a year (keep). |
| E-748 | SAST (static-appsec) audit for gateway code | SAST-run audit with precision metrics. | SAST audit, L1. | Kill iff precision <10% after tuning. |
| E-749 | DAST (dynamic-appsec) audit for venue endpoints | DAST-run audit on test endpoints. | DAST audit, L1. | Kill iff DAST never reaches authenticated surface. |
| E-750 | Threat-model (STRIDE) audit per release | STRIDE audit with mitigations tracked to evidence. | Threat audit, L0/L1. | Kill iff audit never adds a mitigation in two releases. |

## Decision — Batch AQ: AI compilers and ML systems (E-751–E-775)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-751 | Graph-lowering (StableHLO-style) audit for models | StableHLO-lowering audit on toxicity/fill models. | ML lowering, L1. | Kill iff lowering never preserves model accuracy. |
| E-752 | Layout (NCHW/transpose) audit for model latency | Layout audit on detector inference. | Layout audit, L1. | Kill iff layouts never change latency. |
| E-753 | Fusion (clamp/gemm-bias) audit for detectors | Fusion audit on detector graphs. | Fusion audit, L1. | Kill iff fusion never fires on real graphs. |
| E-754 | Quantization-aware-training audit (feeds E-480) | QAT audit with accuracy-recovery metrics. | QAT audit, L1. | Kill iff QAT never recovers accuracy. |
| E-755 | Distillation (teacher-student) audit for tick models | Distillation audit on microstructure models. | Distillation, L1. | Kill iff students never match teachers. |
| E-756 | Pruning (magnitude/structured) audit for detectors | Pruning audit with latency/accuracy metrics. | Pruning audit, L1. | Kill iff pruning never preserves accuracy. |
| E-757 | NAS (once-for-all) audit for feed models | NAS audit with search-cost accounting. | NAS audit, L1. | Kill iff search never beats hand models. |
| E-758 | Feature-store (point-in-time) audit for signals | Point-in-time correctness audit on signal features. | Feature audit, L1. | Kill iff leakage appears in any backtest. |
| E-759 | Label (fill-outcome) audit for supervised models | Label-correctness audit on fill labels. | Label audit, L1. | Kill iff labels disagree with fills twice. |
| E-760 | Train/serve-skew audit for live detectors | Skew audit with PSI metrics on live features. | Skew audit, L1. | Kill iff skew never explains a degradation. |
| E-761 | Drift-triggered retrain audit (feeds E-685) | Retrain audit with rollback on regression. | Retrain audit, L1. | Kill iff retrains never improve live metrics. |
| E-762 | Shadow-deployment audit for model promotion | Shadow audit with promotion gates. | Promotion audit, L1. | Kill iff shadow never disagrees with prod. |
| E-763 | Explainability (SHAP-style) audit for risk models | SHAP audit on risk-model decisions. | Explainability, L1. | Kill iff explanations never satisfy audit. |
| E-764 | Fairness (venue-neutrality) audit for routers | Neutrality audit on venue routing. | Fairness audit, L1. | Kill iff audit never finds a bias. |
| E-765 | Robustness (adversarial-fill) audit for models | Adversarial audit on detector inputs. | Robustness audit, L1. | Kill iff models break on every probe. |
| E-766 | Calibration (reliability-diagram) audit for probabilities | Calibration audit on fill/toxicity probabilities. | Calibration, L1. | Kill iff calibration never holds out-of-sample. |
| E-767 | Uncertainty (ensemble/MC-dropout) audit for gating | Uncertainty-gated quoting with P&L audit. | Uncertainty audit, L1. | Kill iff gating never improves P&L. |
| E-768 | Active-learning (label-query) audit for regimes | Active queries on uncertain regimes with cost audit. | Active learning, L1. | Kill iff queries never beat random labels. |
| E-769 | Semi-supervised (pseudo-label) audit for tick data | Pseudo-label audit with accuracy metrics. | SSL audit, L1. | Kill iff pseudo-labels never help. |
| E-770 | Self-supervised (contrastive) audit for feed embeddings | Contrastive-embedding audit on feeds. | SSL audit, L1. | Kill iff embeddings never transfer. |
| E-771 | Transfer-learning audit across venue pairs | Transfer audit with negative-transfer detection. | Transfer audit, L1. | Kill iff transfer always hurts. |
| E-772 | Multi-task (shared-trunk) audit for signal heads | Shared-trunk audit with interference metrics. | MTL audit, L1. | Kill iff heads always interfere. |
| E-773 | Continual-learning (EWC-style) audit for regime memory | Continual audit with forgetting metrics. | Continual audit, L1. | Kill iff forgetting is catastrophic everywhere. |
| E-774 | Federated-learning audit for cross-desk signals | Federated audit with privacy accounting. | Federated audit, L1. | Kill iff federation never beats local models. |
| E-775 | Inference-server (Triton-style) latency audit | Server audit with SLO metrics on detectors. | Serving audit, L1. | Kill iff server never meets SLOs. |

## Decision — Batch AR: programming environments and tooling (E-776–E-800)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-776 | Language-server (go-to-def/hover) with proof-fact audit | LSP surfacing analysis facts (feeds E-496). | LSP, L1. | Kill iff facts never display correctly twice. |
| E-777 | Inlay-hint (grade/invariant) display audit | Inlay hints for grades/invariants with readability audit. | Hints, L1. | Kill iff hints confuse in user study. |
| E-778 | Quick-fix (apply-certificate) action audit | Code actions applying certified fixes with audit. | Actions, L1. | Kill iff actions never apply cleanly. |
| E-779 | Refactoring (extract/rename) with proof-preservation audit | Refactorings preserving proofs with breakage audit. | Refactoring, L1/L2. | Kill iff any refactoring breaks a proof silently. |
| E-780 | Formatter (canonical-print) with idempotence proofs | Canonical printer with idempotence + round-trip proofs. | Formatting proof, L1/L2. | Kill iff printer ever non-idempotent on corpus. |
| E-781 | Import (dependency-cone) minimizer with audit | Import minimization with build-time audit. | Imports, L1. | Kill iff minimization breaks any build. |
| E-782 | Build (incremental) with verified staleness | Incremental build with staleness proofs (feeds E-497). | Build proof, L1/L2. | Kill iff stale artifacts ever ship. |
| E-783 | Remote-cache (content-addressed) audit for builds | Remote cache with hit-rate + correctness audit. | Build cache, L1. | Kill iff cache serves any stale artifact. |
| E-784 | Hermetic-toolchain (pinned) audit for releases | Hermetic toolchain with drift audit (feeds E-229). | Toolchain audit, L1. | Kill iff drift breaks reproducibility once. |
| E-785 | Cross-compilation (multi-target) audit | Cross builds with per-target test audit. | Cross builds, L1. | Kill iff any target's tests never run. |
| E-786 | Playground (wasm) kernel evaluator with parity audit | Wasm playground with parity vs native kernels. | Playground, L0/L1. | Kill iff parity breaks once. |
| E-787 | Error-message (diagnostic) quality audit | Diagnostic audit with fix-rate metrics on corpus errors. | Diagnostics, L1. | Kill iff fix-rate never improves. |
| E-788 | Telemetry (opt-in-usage) audit for DX decisions | Usage telemetry with privacy audit informing DX work. | Telemetry, L0/L1. | Kill iff telemetry never informs a decision. |
| E-789 | Crash-report (minidump) audit for toolchain | Minidump pipeline with symbolication audit. | Crash reporting, L0/L1. | Kill iff reports never symbolicate. |
| E-790 | bisect (regression-hunt) automation audit | Automated bisection with accuracy audit. | Bisection, L1. | Kill iff bisection never finds a culprit. |
| E-791 | Benchmark (criterion-style) harness audit | Benchmark harness with noise audit (feeds E-474/E-698). | Benchmarking, L1. | Kill iff noise exceeds effect sizes always. |
| E-792 | Coverage-guided (engineering) dashboard audit | Dashboard tracking every E-claim's evidence state. | Dashboard, L0/L1. | Kill iff dashboard rots (stale >1 quarter). |
| E-793 | Onboarding (tutorial-track) audit for new engineers | Tutorial audit with time-to-first-proof metrics. | Onboarding, L0/L1. | Kill iff onboarding never completes in a week. |
| E-794 | Style-guide (lint-set) audit for the codebase | Lint-set audit with violation-trend metrics. | Style, L0/L1. | Kill iff violations grow unboundedly. |
| E-795 | Review (checklist) audit for proof changes | Review checklists with defect-escape metrics. | Review, L0/L1. | Kill iff escapes never traced to checklist gaps. |
| E-796 | Pairing (driver/navigator) audit for hard proofs | Pairing audit on stuck-proof throughput. | Pairing, L0/L1. | Kill iff pairing never unblocks a stuck proof. |
| E-797 | Knowledge-base (decision-log) audit | Decision-log audit with retrieval metrics. | Knowledge, L0/L1. | Kill iff log never answers a real question. |
| E-798 | Postmortem (blameless) audit for incidents | Postmortem audit with action-completion metrics. | Postmortem, L0/L1. | Kill iff actions never complete. |
| E-799 | Roadmap (quarterly) audit for register progress | Roadmap audit tracking E-claim graduation rates. | Planning, L0/L1. | Kill iff no claim graduates in two quarters (replan). |
| E-800 | Deprecation (sunset) audit for killed experiments | Sunset audit ensuring killed experiments actually stop consuming effort. | Sunset, L0/L1. | Kill iff killed work continues (process fail). |

## Decision — Batch AS: finance-specific execution microstructure (E-801–E-825)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-801 | Tick-rule (uptick) compliance audit | Uptick-rule checker with violation audit. | Compliance, L1. | Kill iff checker misses any historical violation. |
| E-802 | Locked/crossed-market detector with halt audit | Lock/cross detector with halt-decision audit. | Market-state, L1. | Kill iff detector lags exchange halts. |
| E-803 | Circuit-breaker (limit-up/down) handler audit | Breaker handler with drill audit. | Breaker audit, L1. | Kill iff handler misprices through a breaker. |
| E-804 | Opening/closing-auction imbalance predictor audit | Imbalance predictor with fill audit (feeds E-223). | Auction, L1. | Kill iff predictor never beats naive. |
| E-805 | Hidden/iceberg (reserve) detector audit (feeds E-208) | Reserve detector with fill-lift audit. | Microstructure, L1. | Kill iff no lift on replay. |
| E-806 | Odd-lot (retail) flow separator audit (feeds E-224) | Separator audit with signal-value metrics. | Flow audit, L1. | Kill iff separator never isolates signal. |
| E-807 | Payment-for-order-flow (PFOF) routing audit | PFOF-routing audit with execution-quality metrics. | Routing audit, L1. | Kill iff audit never changes routing. |
| E-808 | Best-execution (RTS-27-style) report prover | Best-execution reports with proof artifacts. | Reporting proof, L1/L2. | Kill iff reports fail any venue audit. |
| E-809 | Transaction-cost-analysis (TCA) with benchmark audit | TCA engine with benchmark-selection audit. | TCA, L1. | Kill iff TCA never selects the right benchmark. |
| E-810 | Implementation-shortfall attribution audit | Shortfall attribution with decision audit. | Attribution, L1. | Kill iff attribution never informs a change. |
| E-811 | Slippage-vs-arrival audit per algorithm | Per-algo slippage audit with algorithm-selection metrics. | Algo selection, L1. | Kill iff selection never beats default algo. |
| E-812 | Participation-rate (POV) controller audit | POV controller with impact audit. | Participation, L1. | Kill iff controller never tracks targets. |
| E-813 | Dark-pool (ATS) routing audit with information-leak metrics | Dark routing with leak audit. | Dark routing, L1. | Kill iff leakage exceeds lit savings. |
| E-814 | Midpoint-peg audit with adverse-selection metrics | Midpoint strategy audit with markout metrics. | Peg audit, L1. | Kill iff adverse selection dominates savings. |
| E-815 | Primary-peg audit with queue-risk metrics | Primary-peg audit with fill/queue metrics. | Peg audit, L1. | Kill iff queue risk exceeds spread savings. |
| E-816 | Discretionary (D-peg) audit for venue pairs | D-peg audit on the 2-venue fragment. | Peg audit, L1. | Kill iff D-peg never fills better than limit. |
| E-817 | Stop/stop-limit handler audit with trigger metrics | Stop handling with trigger-accuracy audit. | Order-type audit, L1. | Kill iff triggers misfire in any drill. |
| E-818 | Trailing-stop audit with ratchet metrics | Trailing logic with ratchet audit. | Order-type audit, L1. | Kill iff ratchets never track. |
| E-819 | OCO (one-cancels-other) atomicity audit | OCO atomicity with partial-fill audit. | Order-type audit, L1/L2. | Kill iff OCO leaks a leg in any test. |
| E-820 | Bracket-order (TP/SL) audit with trigger metrics | Bracket audit with trigger metrics. | Order-type audit, L1. | Kill iff brackets misfire in any drill. |
| E-821 | Time-in-force (IOC/FOK/AON) handler audit | TIF handling with conformance audit. | Order-type audit, L1. | Kill iff any TIF mishandled in tests. |
| E-822 | Post-only (maker) audit with fee-capture metrics | Post-only audit with fee-capture metrics. | Fee audit, L1. | Kill iff taker fees leak in any test. |
| E-823 | Reduce-only (risk) audit with breach metrics | Reduce-only audit with breach metrics. | Risk audit, L1. | Kill iff reduce-only ever increases position. |
| E-824 | Close-position audit with residual metrics | Close handling with residual audit. | Position audit, L1. | Kill iff residuals persist after close. |
| E-825 | Position-limit (hard/soft) enforcer with breach proofs | Limit enforcer with breach-freedom proofs. | Limit proof, L1/L2. | Kill iff any breach in stress drill. |

## Decision — Batch AT: cross-cutting risk and limits (E-826–E-850)

| ID | Concept | Implementation shape (computable core) | Scope / grade | Kill criterion (post-implementation only) |
|----|---------|----------------------------------------|---------------|-------------------------------------------|
| E-826 | Pre-trade risk (credit/position/price) gate proofs | Certified pre-trade gates with bypass-freedom proofs. | Gate proof, L2/L3. | Kill iff any gate bypass in drill. |
| E-827 | Fat-finger (notional/qty) guard audit | Notional guards with drill audit. | Guard audit, L1. | Kill iff guards block valid block trades twice. |
| E-828 | Price-collar (reasonability) guard audit | Collar guards with override audit. | Guard audit, L1. | Kill iff collars block valid fast-market trades twice. |
| E-829 | Message-rate (burst) guard audit | Burst guards with throttle audit. | Guard audit, L1. | Kill iff guards throttle valid bursts twice. |
| E-830 | Self-match (wash-trade) prevention proofs | Certified self-match prevention on the matching fragment. | Prevention proof, L2. | Kill iff any self-match in tests. |
| E-831 | Restricted-symbol (hard-to-borrow) gate audit | Restriction gates with list-freshness audit. | Gate audit, L1. | Kill iff any restricted trade passes. |
| E-832 | Short-sale (locate) gate audit (feeds E-211) | Locate-gate audit with fail metrics. | Gate audit, L1. | Kill iff any naked short passes. |
| E-833 | Corporate-action (ex-date) gate audit (feeds E-218) | Ex-date gates with adjustment audit. | Gate audit, L1. | Kill iff any unadjusted trade passes. |
| E-834 | Currency-holiday (settlement) gate audit | Holiday gates with calendar audit. | Gate audit, L1. | Kill iff any holiday settlement passes. |
| E-835 | Counterparty-limit enforcer with breach proofs | Counterparty limits with proofs on settlement flows. | Limit proof, L2. | Kill iff any breach in drill. |
| E-836 | Concentration-limit enforcer with breach proofs | Concentration limits with proofs on books. | Limit proof, L2. | Kill iff any breach in drill. |
| E-837 | Drawdown-circuit (kill-switch) with drill proofs | Kill-switch with activation-drill proofs. | Safety proof, L1/L2. | Kill iff switch fails any drill. |
| E-838 | Manual-override (four-eyes) protocol audit | Four-eyes override with audit trail. | Override audit, L1. | Kill iff any solo override in audit. |
| E-839 | Post-trade (T+1) reconciliation proofs (feeds E-225) | Certified T+1 reconciliation with break metrics. | Recon proof, L2. | Kill iff any break unexplained at EOD. |
| E-840 | Fee-accrual (daily) reconciliation proofs | Certified fee accrual with clearing-match metrics. | Recon proof, L2. | Kill iff any mismatch vs clearing. |
| E-841 | Dividend/coupon (entitlement) reconciliation proofs | Certified entitlements with custodian-match metrics. | Recon proof, L2. | Kill iff any mismatch vs custodian. |
| E-842 | Stock-loan (borrow-cost) reconciliation proofs | Certified borrow costs with lender-match metrics. | Recon proof, L2. | Kill iff any mismatch vs lender. |
| E-843 | FX-settlement (CLS-style) reconciliation proofs | Certified FX settlement with CLS-match metrics. | Recon proof, L2. | Kill iff any mismatch vs CLS records. |
| E-844 | Collateral (margin-call) workflow proofs | Certified margin-call workflow with dispute metrics. | Workflow proof, L2. | Kill iff any call disputed successfully. |
| E-845 | Liquidation (default) drill with shortfall audit | Default drills with shortfall metrics. | Drill audit, L1. | Kill iff shortfall exceeds prefunded resources. |
| E-846 | Insurance/guarantee-fund adequacy audit | Fund-adequacy audit with stress metrics. | Adequacy audit, L1. | Kill iff fund inadequate under stress. |
| E-847 | Recovery (living-will) plan audit | Recovery-plan audit with feasibility metrics. | Plan audit, L1. | Kill iff plan infeasible in any drill. |
| E-848 | Resolution (wind-down) drill with position audit | Wind-down drills with flattening metrics. | Drill audit, L1. | Kill iff wind-down exceeds its window. |
| E-849 | Regulatory-report (MiFID/EMIR) generator proofs | Certified reports with acceptance metrics. | Reporting proof, L1/L2. | Kill iff any report rejected by the venue/regulator. |
| E-850 | Audit-trail (immutable) completeness proofs | Certified completeness of the audit trail (feeds E-300/E-471). | Trail proof, L2. | Kill iff any trade lacks a trail entry. |

## References

- ADR-019 (acceptance rule), ADR-020–023 (E-101–E-700). Baselines named per
  row are the kill instruments.
