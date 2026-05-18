# Morph Detailed Roadmap

Lean 4 v4.27.0 | Lake 5.0.0 | mathlib4 + batteries + aesop

---

## Baseline (2026-05-15)

| Metric | Value |
|---|---|
| `lake build Morph` | 328 jobs, 0 errors, 2 sorry warnings |
| `lake build Morph.Tests` | 186 jobs, 0 errors |
| Python spec-tools | 735 tests, 93.29% coverage |
| `.lean` files | 155 |
| Lines of Lean | ~16,165 |
| Spec modules | 43 |
| Real theorems/lemmas | 787 total; 550+ in Specs/ |
| `sorry` declarations | 6 (all Preservation.lean, 0 in Lemmas.lean) |
| `example : True := trivial` stubs | 0 |
| Pre-commit hook | 7-step gate |
| CI/CD | 4 GitHub Actions + GitLab CI + Jenkins |
| Broken cross-references | 26 (nonexistent targets) |
| Documentation site | Landing page + 5 doc pages (GitHub Pages) |

---

## Dependency Graph

```
[1.1 Fix sorries]--------+--[2.1 Zero-warning gate]--[2.3 Pre-commit hardening]
                         +--[2.2 Sorry-free gate]
                         |
[2.4 Resolve billing]----+--[4.2 Regression snapshots]
                         +--[5.2 API docs]
                         +--[4.3 Cache optimization]
                         |
[3.1 Fix 26 links]       |
[3.2 Normalize numbering]|
[3.3 SlimCheck]          |
[3.4 Python coverage]    +--[5.3 Spec status tracking]
                         |
[1.2 Tier 1 proofs]------+--[1.3 Tier 2]--[1.4 Tier 3]--[1.5 Tier 4]
                         |
                         +--[6.1 Compiler frontend]--[6.2 Type checker]--[6.3 Runtime (Rust/C++)]--[6.4 Stdlib]
                         |
[7.1-7.5 Research]       |
                         |
[8.1-8.5 Production]-----+--[6.3 Runtime]
```

---

## Phase 1: Immediate (Weeks 1-2)

### 1.1 Fix 6 sorry declarations

**Preservation.lean (6 sorries):**

| Line | Context | Required Lemma | Effort |
|---|---|---|---|
| 116 | `HasType_subst` bvar_type | `lift_preserves_type`: lifting by 0 preserves typing | 2-3 days |
| 156 | `HasType_subst` lam_type | Generalized subst at depth > 0 | 3-5 days |
| 171 | `HasType_subst` let_type | Generalized subst at depth 1 | 2-3 days |
| 175 | `HasType_subst` for_type | Generalized subst at depth 1 | 2-3 days |
| 288 | `preservation` for_exec | `substAll_preserves_type` | 3-5 days |
| 359 | `preservation` app_lam | `substAll_preserves_type` | 2-3 days |

**Lemmas.lean:** All 4 sorries resolved -- no remaining work.

**Proof strategy:**
1. Prove `lift_preserves_type` (unblocks sorry #1)
2. Prove `subst'_preserves_type` for arbitrary depth (unblocks sorries #2-4)
3. Prove `substAll_preserves_type` (unblocks sorries #5-6)

| Attribute | Detail |
|---|---|
| Total effort | 1-2 weeks |
| Dependencies | None |
| Blocks | 2.1, 2.2, 2.3 |
| Risk | Medium -- substitution lemmas require careful de Bruijn index reasoning |
| Success gate | `lake build Morph` produces 0 sorry warnings |

### 1.2 Resolve GitHub billing

| Attribute | Detail |
|---|---|
| Effort | Account-level action (hours) |
| Dependencies | None |
| Blocks | 2.1, 2.2, 2.3, 4.2, 5.2, 5.3 |
| Risk | Low -- workflows are verified correct |
| Success gate | All 4 GitHub Actions execute green on push |

### 1.3 Fix 26 broken cross-references

| Category | Count | Action |
|---|---|---|
| Nonexistent top-level files | 16 | Create stub files or remove links |
| Typo in filename (`lexical_strcutre`) | 2 | Fix link targets |
| `docs/conventions/` path from `spec/` | 3 | Fix relative paths |
| Line-reference format (`:2.6`) | 2 | Remove or fix format |
| Stray single-char link | 1 | Remove |

| Attribute | Detail |
|---|---|
| Effort | 2-3 hours |
| Dependencies | None |
| Blocks | Spec integrity |
| Risk | Low |
| Success gate | `spec-tools check-links` reports 0 broken references |

---

## Phase 2: Short-term (Weeks 3-12)

### 2.1 CI hardening

| Task | Effort | Deps | Gate |
|---|---|---|---|
| Zero-warning CI gate (Morph source) | 1 hour | 1.1, 1.2 | Build log has 0 warnings in `Morph/` |
| Sorry-free CI gate (hard failure) | 30 min | 1.1 | Exit 1 if `sorry` count > 0 |
| Pre-commit hook: sorry as blocking | 15 min | 1.1 | Commit blocked if sorry present |
| Pre-commit hook: warning as blocking | 15 min | 1.1 | Commit blocked if warnings present |

### 2.2 Tier 1 proof completion (runtime foundation)

| Module | Target Proofs | Effort | Notes |
|---|---|---|---|
| MemoryModel | 3-5 additional lemmas | 2-3 days | Heap invariants, allocation bounds |
| SecurityFlow | 5-8 lemmas | 1-2 weeks | Taint tracking, non-interference |
| MorphLanguage | 5-8 additional | 1 week | Substitution properties |
| ConcurrencyProcessAlgebra | 5-10 lemmas | 1-2 weeks | Deadlock-free, channel safety |
| TypeSystem | 3-5 additional | 3-5 days | Uniqueness of types |
| ModuleSystem | 5-8 lemmas | 1 week | Hash determinism |
| GLOSSARY | 3-5 examples | 2-3 days | Well-formed instances |

| Attribute | Detail |
|---|---|
| Total effort | 4-6 weeks (parallelizable) |
| Dependencies | None |
| Blocks | Tier 2, compiler frontend |
| Risk | Low-Medium -- SecurityFlow and ConcurrencyProcessAlgebra are the hardest |
| Success gate | Each module passes `lake build` with 0 new sorries |

### 2.3 Tier 2 proof completion (compiler/runtime support)

| Module | Target | Effort |
|---|---|---|
| ScopingLambdaCalculus | Scope rules, alpha-equivalence | 1-2 weeks |
| DialectProjection | Multi-stage compilation | 1-2 weeks |
| MonadicEffect | Effect handler semantics | 1-2 weeks |
| OperatorNullCoalescing | Operator semantics | 3-5 days |
| LexicalStructureSyntax | Token/literal specs | 3-5 days |
| ExecutionModel | Step relation | 1 week |
| AbiAlignmentAlgebra | ABI struct layout | 3-5 days |
| BackendTiling | Tiling correctness | 1 week |

| Attribute | Detail |
|---|---|
| Total effort | 5-8 weeks |
| Dependencies | Tier 1 complete |
| Blocks | Tier 3, Tier 4 |
| Risk | Low |
| Success gate | All 8 modules pass with 0 new sorries |

### 2.4 SlimCheck property testing

| Target | Properties | File |
|---|---|---|
| MemoryModel | `allocate` produces fresh `BlockId`; `readByte` after `writeByte` returns written value | `Morph/Tests/Memory.lean` |
| TypeSoundness | Random closed terms are either well-typed or rejected | `Morph/Tests/Typing.lean` |
| Semantics | Evaluation is deterministic for pure expressions | `Morph/Tests/Semantics.lean` |

| Attribute | Detail |
|---|---|
| Effort | 1-2 weeks |
| Dependencies | SlimCheck in `lakefile.lean` |
| Risk | Low |
| Success gate | 50+ property tests pass; integrated into CI |

### 2.5 Python spec-tools coverage to 90%

Priority areas:
- `spec_tools/validation/checks/` (70-73% each)
- `spec_tools/cli/commands/check_all.py` (43%)
- `spec_tools/utils/file_utils.py` (71%)

| Attribute | Detail |
|---|---|
| Effort | 3-5 days |
| Dependencies | None |
| Risk | Low |
| Success gate | `pytest --cov` reports >= 90% |

---

## Phase 3: Medium-term (Months 3-5)

### 3.1 Tier 3 proof completion (domain-specific)

| Module | Effort |
|---|---|
| BuildLattice | 3-5 days |
| DualOptimization | 3-5 days |
| LayeredConcurrency | 5 days |
| SchedulerRandomizedStealing | 5 days |
| SchedulingModes | 3-5 days |
| SecurityOCap | 1 week |
| MemoryAcyclicity | 5 days |
| MemoryAffineLogic | 1 week |
| LinkerLogic | 3-5 days |
| ArcAffineIntegration | 5 days |
| ModuleExistential | 5 days |
| InfrastructureSafetyContracts | 3-5 days |
| Financial | 3-5 days |
| Maths | 3-5 days |

| Attribute | Detail |
|---|---|
| Total effort | 6-9 weeks |
| Dependencies | Tier 1 |
| Risk | Medium -- MemoryAffineLogic and SecurityOCap require careful formalization |
| Success gate | All 14 modules pass with 0 new sorries |

### 3.2 Tier 4 proof completion (auxiliary)

| Module | Effort |
|---|---|
| Licensing | 2-3 days |
| LicenseDeonticLogic | 2-3 days |
| DependencySat | 2-3 days |
| UnidirectionalDataFlow | 2-3 days |
| StrictStateUnidirectional | 2-3 days |
| StorageDAWG | 2-3 days |
| RegistryConsensus | 2-3 days |
| VersionCompatibility | 2-3 days |
| SyntaxTranslation | 2-3 days |
| UnitGroupTheory | 2-3 days |
| TerminologyStandardization | 2-3 days |
| ASTGraph | 2-3 days |
| AbiDataRefinement | 2-3 days |
| README | 1 day |

| Attribute | Detail |
|---|---|
| Total effort | 3-4 weeks |
| Dependencies | Tier 1 |
| Risk | Low |
| Success gate | All 14 modules pass with 0 new sorries |

### 3.3 Spec status automation

Script to auto-generate `SPEC_STATUS.md` from Lean source by scanning each `Morph/Specs/*/` directory for spec lines, lemma counts, and sorry counts.

| Attribute | Detail |
|---|---|
| Effort | 3-4 hours |
| Dependencies | None |
| Success gate | `SPEC_STATUS.md` regenerates correctly; diff against committed version in CI |

### 3.4 Regression snapshots

Capture build metrics per push (errors, warnings, sorries, stubs). Store in `.reports/regression/`. Fail CI on metric regression.

| Attribute | Detail |
|---|---|
| Effort | 3-4 hours |
| Dependencies | CI running (1.2) |
| Success gate | CI fails if any metric regresses from previous baseline |

### 3.5 Section numbering normalization

3868 warnings across 87 spec files. Preferred approach: hierarchical numbering (1, 1.1, 1.2, 2, 2.1...).

| Attribute | Detail |
|---|---|
| Effort | 1-2 days |
| Dependencies | None |
| Risk | Medium -- may break existing cross-references |
| Success gate | `spec-tools lint` reports 0 numbering warnings |

---

## Phase 4: Implementation (Months 6-14)

### 4.1 Compiler frontend (Lean 4)

| Component | Description | Effort |
|---|---|---|
| Lexer | Tokenize Morph source into `Morph.Syntax.Token` | 2-3 weeks |
| Parser | Recursive descent producing `Morph.Syntax.AST` | 3-4 weeks |
| Name resolution | Resolve identifiers, build symbol table | 2-3 weeks |
| HIR lowering | AST to `Morph.HIR.Expr` | 1-2 weeks |

| Attribute | Detail |
|---|---|
| Total effort | 8-12 weeks |
| Dependencies | Tier 1 complete, zero-warning CI |
| Blocks | Type checker extraction |
| Risk | Medium -- parser error recovery is non-trivial |
| Success gate | Round-trip: parse Morph source, reconstruct equivalent source |

### 4.2 Type checker extraction

Extract type checking rules from proof layer into certified executable.

| Step | Description | Effort |
|---|---|---|
| Type synthesis | `synthType : Expr -> TypEnv -> Option Typ` | 2-3 weeks |
| Type checking | `checkType : Expr -> TypEnv -> Typ -> Bool` | 1-2 weeks |
| Unification | Pattern unification for type variables | 2-3 weeks |
| Error reporting | Human-readable type error messages | 1 week |

| Attribute | Detail |
|---|---|
| Total effort | 6-9 weeks |
| Dependencies | Tier 1, compiler frontend |
| Blocks | Runtime integration |
| Risk | Medium -- unification may require extensions beyond HM |
| Success gate | Type checker agrees with Lean 4 proofs on all test cases |

### 4.3 Runtime (Rust/C++)

Per `impl/roadmap.md`:

| Phase | Description | Timeline |
|---|---|---|
| Phase 0 | Infrastructure: Cargo workspace, ABI bridge, Docker CI | Weeks 1-4 |
| Phase 1 | Runtime core: Memory subsystem, M:N scheduler, I/O poller | Months 2-4 |
| Phase 2 | Compiler frontend: Parser (chumsky), semantic analysis, comptime | Months 5-7 |
| Phase 3 | Backend: LLVM lowering (inkwell), MCP server, optimization | Months 8-10 |
| Phase 4 | Extensions: UI backend (wgpu), stdlib bootstrap, training data | Months 11-12 |

| Attribute | Detail |
|---|---|
| Total effort | 12 months |
| Dependencies | Compiler frontend, type checker (for Lean-to-Rust extraction) |
| Risk | High -- LLVM integration and scheduler correctness are the main risks |
| Mitigation | ASan/TSan in CI for every commit; benchmark scheduler early |
| Success gate | `hello_world.morph` compiles and runs; scheduler passes 1M-fiber stress test |

### 4.4 Standard library

| Component | Effort |
|---|---|
| Core types (Int, String, Bool, List, Option) | 2-3 weeks |
| Collections (Map, Set, Array) | 2-3 weeks |
| I/O primitives | 1-2 weeks |
| Concurrency primitives (spawn, send, recv) | 2-3 weeks |

| Attribute | Detail |
|---|---|
| Total effort | 7-11 weeks |
| Dependencies | Runtime (Phase 1) |
| Success gate | All stdlib tests pass; fuzzer runs 24h without crashes |

---

## Phase 5: Research Directions (Ongoing)

### 5.1 Dependent types for runtime

Extract dependent type information from Lean 4 proofs for runtime use (array bounds, nullable tracking).

| Attribute | Detail |
|---|---|
| Milestone | Proof of concept in 3 months |
| Dependencies | Lean 4 code extraction pipeline |
| Risk | High -- extraction gap between proof-level and runtime-level types |

### 5.2 Linear types for resource management

Extend type system with affine/linear qualifiers. Formalize in `Morph/Specs/MemoryAffineLogic/`.

| Attribute | Detail |
|---|---|
| Milestone | Spec.lean definitions in 2 months |
| Dependencies | None |
| Risk | Medium |

### 5.3 Capability-based security enforcement

Extend `Morph/Specs/SecurityOCap/` with formal capability model. Prove noninterference.

| Attribute | Detail |
|---|---|
| Milestone | Noninterference theorem in 3 months |
| Dependencies | SecurityOCap spec module |
| Risk | Medium-High -- noninterference proofs are complex |

### 5.4 Multi-stage compilation (dialect system)

Extend `Morph/Specs/DialectProjection/` with verified multi-stage pipeline. Prove dialect lowering preserves semantics.

| Attribute | Detail |
|---|---|
| Milestone | Dialect soundness theorem in 4 months |
| Dependencies | DialectProjection spec module |
| Risk | Medium |

### 5.5 Verified compiler extraction

Investigate extracting a verified compiler from Lean 4 proofs directly, bypassing the Rust/C++ runtime for the core calculus.

| Attribute | Detail |
|---|---|
| Milestone | Feasibility study in 2 months |
| Dependencies | None |
| Risk | High -- Lean 4 extraction tooling is immature |

---

## Phase 6: Production Readiness (Months 15-18)

### 6.1 Performance benchmarks

| Benchmark | Target | Notes |
|---|---|---|
| `http_server` | Within 10% of Rust/Go | Per impl/roadmap.md DoD |
| Scheduler throughput | >= 1M fibers, correct final count | Race detection validation |
| Compilation time | < 10s for 10k LOC | Cold and warm builds |
| Memory usage | Bounded arena growth | No unbounded leaks |

| Attribute | Detail |
|---|---|
| Effort | 2-3 weeks |
| Dependencies | Runtime (Phase 3) |
| Success gate | All benchmarks within target; results published in CI |

### 6.2 WCET analysis

Worst-case execution time analysis for real-time use cases (HFT, embedded).

| Attribute | Detail |
|---|---|
| Effort | 2-4 weeks |
| Dependencies | Runtime stable, benchmarks complete |
| Risk | Medium -- requires tooling for static analysis |
| Success gate | WCET bounds documented for core runtime primitives |

### 6.3 Security audit

| Area | Scope |
|---|---|
| Memory safety | ASan/TSan/UBSan clean on full test suite |
| Capability enforcement | No capability violations in adversarial test suite |
| Supply chain | All dependencies audited; lock files pinned |
| Fuzzing | 24h continuous fuzz with no crashes |

| Attribute | Detail |
|---|---|
| Effort | 3-4 weeks |
| Dependencies | Runtime + stdlib complete |
| Success gate | 0 critical/high findings |

### 6.4 Documentation complete

| Deliverable | Status |
|---|---|
| API reference (`lake exe doc-gen4`) | Auto-generated |
| Spec status page | Auto-generated from CI |
| Tutorials (getting started, language tour) | Written |
| Architecture deep-dive | Updated |
| ADRs | Complete (11+) |

| Attribute | Detail |
|---|---|
| Effort | 2-3 weeks |
| Dependencies | All phases substantially complete |
| Success gate | New contributor can build and run `hello_world.morph` from docs alone |

### 6.5 Beta release

| Attribute | Detail |
|---|---|
| Effort | 1-2 weeks (release engineering) |
| Dependencies | All above |
| Success gate | Self-hosting build system; agent can query semantic tree and install libraries |

---

## Master Timeline

```
Week   1-2:  [1.1] [1.2] [1.3]                    -- sorries, billing, broken links
Week   3-4:  [2.1] [2.4]                          -- CI hardening, SlimCheck start
Week   5-8:  [2.2] [2.5]                          -- Tier 1 proofs, Python coverage
Week   9-12: [2.3] [3.3] [3.4] [3.5]             -- Tier 2, regression, numbering
Month  3-4:  [3.1]                                -- Tier 3 proofs
Month  4-5:  [3.2]                                -- Tier 4 proofs
Month  6-8:  [4.1] [4.2]                          -- Compiler frontend, type checker
Month  8-14: [4.3]                                -- Runtime (Rust/C++)
Month 12-14: [4.4]                                -- Standard library
Ongoing:      [5.1-5.5]                           -- Research directions
Month 15-18: [6.1-6.5]                            -- Production readiness, beta
```

---

## Risk Summary

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| Substitution lemma proofs stall | Blocks CI hardening | Medium | Consult mathlib4 community; consider alternative encoding |
| GitHub billing unresolved | Blocks all CI | Low | Escalate; GitLab/Jenkins as fallback |
| LLVM integration complexity | Delays Phase 3 | Medium-High | Use `inkwell`; start with O0 builds |
| Runtime scheduler bugs | Correctness | Medium | ASan/TSan in CI; 1M-fiber stress test |
| Lean 4 extraction immaturity | Blocks verified compiler | High | Maintain manual Rust implementation as primary path |
| Proof effort exceeds estimates | Timeline slip | Medium | Tier system allows partial completion per tier |

---

## Success Criteria Summary

| Criterion | Target | Current |
|---|---|---|
| `lake build Morph` errors | 0 | 0 |
| `lake build Morph` warnings | 0 | 2 (sorry-related) |
| `sorry` in `Morph/` | 0 | 6 (all in Preservation.lean) |
| `example : True := trivial` stubs | 0 | 0 |
| Broken cross-references | 0 | 26 |
| CI passes on every push | Yes | Partial (billing was resolved) |
| Python spec-tools coverage | >= 90% | 93.29% |
| Pre-commit blocks on sorry | Yes | Warns only |
| Regression snapshot tracking | Active | Script exists, not in CI |
| Spec status page | Auto-generated | Manual |
| Tier 1-4 proofs complete | 43 modules | In progress |
| Runtime compiles hello_world | Yes | Not started |
| Beta release | Shipped | Not started |
