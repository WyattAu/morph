# Morph Consolidated Roadmap

Lean 4 v4.27.0 | Lake 5.0.0 | mathlib4 + batteries + aesop

---

## Post-Audit Baseline (2026-05-18)

| Metric | Value |
|---|---|
| `lake build Morph` | 328 jobs, 0 errors, 2 sorry warnings |
| `lake build Morph.Tests` | 186 jobs, 0 errors |
| Python spec-tools | 735 tests, 93.29% coverage |
| `.lean` files | 155 |
| Lines of Lean | ~16,165 |
| Spec modules | 43 |
| Theorems/lemmas (total) | 787 |
| `sorry` declarations | 6 (all in Preservation.lean) |
| `example : True := trivial` stubs | 0 |
| Pre-commit hook | 7-step gate (lake build, sorry scan, stub scan, tests, pytest, ruff/mypy, spec-tools lint) |
| CI/CD | 4 GitHub Actions (lean-build, spec-validation, nightly, pages) + GitLab CI + Jenkins |
| Broken cross-refs (spec/) | 367 (mostly internal section anchors in spec markdown) |
| Documentation site | Landing page + 5 doc pages on GitHub Pages |
| ruff | 0 errors, 0 warnings, 66 files formatted |
| mypy | 0 errors, 66 source files |

### Issues Resolved This Audit

| Category | Fix |
|---|---|
| CI/CD: YAML indentation | Fixed step alignment in lean-build.yml |
| CI/CD: pip cache miss | Added `cache-dependency-path` to spec-validation.yml |
| CI/CD: PR comment permission | Added `pull-requests: write` to spec-validation.yml |
| CI/CD: warning grep pattern | Fixed to `Morph/.*warning:` matching Lean output format |
| CI/CD: GitLab safety check | Fixed to use `pip freeze` output |
| CI/CD: Jenkinsfile error handling | Added `set -e` and conditional venv creation |
| CI/CD: nightly build log | Added artifact upload and sorry counting |
| Pre-commit: comment filter | Changed `/--` to `^\s*--` for Lean comments |
| Pre-commit: temp files | Changed hardcoded `/tmp/` to `mktemp` |
| Docs: stale metrics | Updated 735 tests, 93.29% coverage, 6 sorries, ~16,165 LoC |
| Docs: Lemmas.lean references | Removed all 4 Lemmas.lean sorry references (resolved) |
| Docs: Chinese characters | Replaced batch labels in PATH_FORWARD.md |
| Docs: theorem count | Unified to 787 total across all files |
| Docs: cross-refs | Added 6 missing specs to SPECIFICATION_INDEX, fixed GLOSSARY links |

### Outstanding Issues

| ID | Category | Description | Severity |
|---|---|---|---|
| O-1 | Spec cross-refs | 367 broken internal section anchors across `spec/` markdown | Medium |
| O-2 | CI/CD | spec-validation.yml uses `continue-on-error: true` on all checks | Medium |
| O-3 | CI/CD | Actions pinned to major tags only, not full SHAs | Low |
| O-4 | CI/CD | elan installed via `curl | sh` without hash verification | Low |
| O-5 | Docs | ROADMAP.md, ROADMAP_DETAILED.md, PATH_FORWARD.md are 90%+ duplicated | Low |
| O-6 | Docs | Duplicate ADR numbering in `.specs/02_adrs/` | Low |
| O-7 | Docs | spec/README.md directory tree shows wrong subdirectory structure | Low |
| O-8 | Site | No HTML validation or link checking in pages deployment | Low |

---

## Dependency Graph

```
[1.1 Fix 6 sorries]--------+--[2.1 Zero-warning gate]--[2.3 Pre-commit hardening]
                           +--[2.2 Sorry-free gate]
                           |
[1.2 Fix spec cross-refs]--+--[3.1 Spec status automation]
                           +--[2.4 Regression snapshots]
                           |
[2.5 Python coverage 95%]--+--[3.2 SlimCheck]
                           |
[3.3 Section numbering]----+
                           |
[4.1 Compiler frontend]----+--[4.2 Type checker]--[4.3 Runtime (Rust/C++)]--[4.4 Stdlib]
                           |
[5.1-5.5 Research]--------+
                           |
[6.1-6.5 Production]------+--[4.3 Runtime]
```

---

## Phase 1: Immediate (Weeks 1-2)

### 1.1 Fix 6 sorry declarations in Preservation.lean

All 6 sorries are in `Morph/Proofs/TypeSoundness/Preservation.lean`:

| Line | Context | Required Lemma | Effort |
|---|---|---|---|
| 116 | `HasType_subst` bvar_type | `lift_preserves_type`: lifting by 0 preserves typing | 2-3 days |
| 156 | `HasType_subst` lam_type | Generalized subst at depth > 0 | 3-5 days |
| 171 | `HasType_subst` let_type | Generalized subst at depth 1 | 2-3 days |
| 175 | `HasType_subst` for_type | Generalized subst at depth 1 | 2-3 days |
| 288 | `preservation` for_exec | `substAll_preserves_type` | 3-5 days |
| 359 | `preservation` app_lam | `substAll_preserves_type` | 2-3 days |

**Proof strategy:**
1. Prove `lift_preserves_type` (unblocks sorry #1)
2. Prove `subst'_preserves_type` for arbitrary depth (unblocks sorries #2-4)
3. Prove `substAll_preserves_type` (unblocks sorries #5-6)

| Attribute | Detail |
|---|---|
| Total effort | 1-2 weeks |
| Dependencies | None |
| Blocks | 2.1, 2.2, 2.3 |
| Risk | Medium -- de Bruijn index substitution reasoning |
| Gate | `lake build Morph` produces 0 sorry warnings |

### 1.2 Fix spec cross-references (367 broken anchors)

| Category | Count | Action |
|---|---|---|
| Internal section anchors | ~340 | Normalize section headings to match link targets |
| File path mismatches | ~20 | Fix relative paths |
| Orphaned sections | ~7 | Create target sections or remove links |

| Attribute | Detail |
|---|---|
| Effort | 3-5 days |
| Dependencies | None |
| Gate | `spec-tools check-links spec/` reports < 10 broken links |

---

## Phase 2: Short-term (Weeks 3-12)

### 2.1 CI hardening

| Task | Effort | Deps | Gate |
|---|---|---|---|
| Zero-warning CI gate (Morph source) | 1 hour | 1.1 | Build log has 0 warnings in `Morph/` |
| Sorry-free CI gate (hard failure) | 30 min | 1.1 | Exit 1 if `sorry` count > 0 |
| Pre-commit: sorry as blocking | 15 min | 1.1 | Commit blocked if sorry present |
| Remove `continue-on-error: true` from spec-validation | 1 hour | None | Validation failures block CI |

### 2.2 Tier 1 proof completion (runtime foundation)

| Module | Target Proofs | Effort |
|---|---|---|
| MemoryModel | 3-5 additional lemmas | 2-3 days |
| SecurityFlow | 5-8 lemmas | 1-2 weeks |
| MorphLanguage | 5-8 additional | 1 week |
| ConcurrencyProcessAlgebra | 5-10 lemmas | 1-2 weeks |
| TypeSystem | 3-5 additional | 3-5 days |
| ModuleSystem | 5-8 lemmas | 1 week |

| Attribute | Detail |
|---|---|
| Total effort | 4-6 weeks (parallelizable) |
| Dependencies | None |
| Risk | Low-Medium |

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

### 2.4 SlimCheck property testing

| Target | Properties |
|---|---|
| MemoryModel | `allocate` produces fresh `BlockId`; `readByte` after `writeByte` returns written value |
| TypeSoundness | Random closed terms are either well-typed or rejected |
| Semantics | Evaluation is deterministic for pure expressions |

| Attribute | Detail |
|---|---|
| Effort | 1-2 weeks |
| Gate | 50+ property tests pass; integrated into CI |

### 2.5 Python spec-tools coverage to 95%

Priority areas:
- `spec_tools/cli/main.py` (80%)
- `spec_tools/verification/compilation.py` (80%)
- `spec_tools/validation/validator.py` (77%)
- `spec_tools/linting/rules/sections.py` (92%)

| Attribute | Detail |
|---|---|
| Effort | 3-5 days |
| Gate | `pytest --cov` reports >= 95% |

---

## Phase 3: Medium-term (Months 3-5)

### 3.1 Tier 3 proof completion (domain-specific)

14 modules: BuildLattice, DualOptimization, LayeredConcurrency, SchedulerRandomizedStealing, SchedulingModes, SecurityOCap, MemoryAcyclicity, MemoryAffineLogic, LinkerLogic, ArcAffineIntegration, ModuleExistential, InfrastructureSafetyContracts, Financial, Maths.

| Attribute | Detail |
|---|---|
| Total effort | 6-9 weeks |
| Dependencies | Tier 1 |

### 3.2 Tier 4 proof completion (auxiliary)

14 modules: Licensing, LicenseDeonticLogic, DependencySat, UnidirectionalDataFlow, StrictStateUnidirectional, StorageDAWG, RegistryConsensus, VersionCompatibility, SyntaxTranslation, UnitGroupTheory, TerminologyStandardization, ASTGraph, AbiDataRefinement, README.

| Attribute | Detail |
|---|---|
| Total effort | 3-4 weeks |
| Dependencies | Tier 1 |

### 3.3 Spec status automation

Script to auto-generate `SPEC_STATUS.md` from Lean source.

| Attribute | Detail |
|---|---|
| Effort | 3-4 hours |
| Gate | `SPEC_STATUS.md` regenerates correctly; diff in CI |

### 3.4 Regression snapshots

Capture build metrics per push. Store in `.reports/regression/`. Fail CI on regression.

### 3.5 Section numbering normalization

3868 warnings across 87 spec files. Preferred: hierarchical numbering (1, 1.1, 1.2, 2, 2.1...).

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
| Gate | Round-trip: parse Morph source, reconstruct equivalent source |

### 4.2 Type checker extraction

| Step | Description | Effort |
|---|---|---|
| Type synthesis | `synthType : Expr -> TypEnv -> Option Typ` | 2-3 weeks |
| Type checking | `checkType : Expr -> TypEnv -> Typ -> Bool` | 1-2 weeks |
| Unification | Pattern unification for type variables | 2-3 weeks |
| Error reporting | Human-readable type error messages | 1 week |

| Attribute | Detail |
|---|---|
| Total effort | 6-9 weeks |
| Gate | Type checker agrees with Lean 4 proofs on all test cases |

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
| Risk | High -- LLVM integration and scheduler correctness |
| Mitigation | ASan/TSan in CI; 1M-fiber stress test |
| Gate | `hello_world.morph` compiles and runs |

### 4.4 Standard library

Core types (Int, String, Bool, List, Option), Collections (Map, Set, Array), I/O primitives, Concurrency primitives (spawn, send, recv).

| Attribute | Detail |
|---|---|
| Total effort | 7-11 weeks |
| Dependencies | Runtime Phase 1 |
| Gate | All stdlib tests pass; fuzzer runs 24h without crashes |

---

## Phase 5: Research Directions (Ongoing)

### 5.1 Dependent types for runtime
Extract dependent type information from Lean 4 proofs for runtime use (array bounds, nullable tracking).
| Milestone | Proof of concept in 3 months | Risk: High |

### 5.2 Linear types for resource management
Extend type system with affine/linear qualifiers in `Morph/Specs/MemoryAffineLogic/`.
| Milestone | Spec.lean definitions in 2 months | Risk: Medium |

### 5.3 Capability-based security enforcement
Extend `Morph/Specs/SecurityOCap/` with formal capability model. Prove noninterference.
| Milestone | Noninterference theorem in 3 months | Risk: Medium-High |

### 5.4 Multi-stage compilation (dialect system)
Extend `Morph/Specs/DialectProjection/` with verified multi-stage pipeline.
| Milestone | Dialect soundness theorem in 4 months | Risk: Medium |

### 5.5 Verified compiler extraction
Investigate extracting a verified compiler from Lean 4 proofs directly.
| Milestone | Feasibility study in 2 months | Risk: High |

---

## Phase 6: Production Readiness (Months 15-18)

### 6.1 Performance benchmarks
| Benchmark | Target |
|---|---|
| `http_server` | Within 10% of Rust/Go |
| Scheduler throughput | >= 1M fibers, correct final count |
| Compilation time | < 10s for 10k LOC |
| Memory usage | Bounded arena growth |

### 6.2 WCET analysis
Worst-case execution time analysis for real-time use cases (HFT, embedded).

### 6.3 Security audit
Memory safety (ASan/TSan/UBSan), capability enforcement, supply chain, 24h fuzzing.

### 6.4 Documentation complete
API reference, spec status page, tutorials, architecture deep-dive, ADRs (11+).

### 6.5 Beta release
Self-hosting build system; agent can query semantic tree and install libraries.

---

## Master Timeline

```
Week   1-2:  [1.1] [1.2]                    -- sorries, broken links
Week   3-4:  [2.1] [2.4] [2.5]             -- CI hardening, SlimCheck, coverage
Week   5-8:  [2.2]                          -- Tier 1 proofs
Week   9-12: [2.3] [3.3] [3.4] [3.5]      -- Tier 2, regression, numbering
Month  3-4:  [3.1]                          -- Tier 3 proofs
Month  4-5:  [3.2]                          -- Tier 4 proofs
Month  6-8:  [4.1] [4.2]                   -- Compiler frontend, type checker
Month  8-14: [4.3]                          -- Runtime (Rust/C++)
Month 12-14: [4.4]                         -- Standard library
Ongoing:      [5.1-5.5]                    -- Research directions
Month 15-18: [6.1-6.5]                    -- Production readiness, beta
```

---

## Risk Summary

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| Substitution lemma proofs stall | Blocks CI hardening | Medium | Consult mathlib4 community; alternative encoding |
| LLVM integration complexity | Delays Phase 4 | Medium-High | Use inkwell; start with O0 builds |
| Runtime scheduler bugs | Correctness | Medium | ASan/TSan in CI; 1M-fiber stress test |
| Lean 4 extraction immaturity | Blocks verified compiler | High | Manual Rust implementation as primary path |
| Proof effort exceeds estimates | Timeline slip | Medium | Tier system allows partial completion |
| Spec cross-ref normalization | Breaks existing links | Medium | Automated tooling; batch fix with validation |

---

## Success Criteria

| Criterion | Target | Current |
|---|---|---|
| `lake build Morph` errors | 0 | 0 |
| `lake build Morph` warnings | 0 | 2 (sorry-related) |
| `sorry` in `Morph/` | 0 | 6 |
| `example : True := trivial` stubs | 0 | 0 |
| Broken cross-references | < 10 | 367 |
| CI passes on every push | Yes | Yes |
| Python spec-tools coverage | >= 95% | 93.29% |
| Pre-commit blocks on sorry | Yes | Warns only |
| Regression snapshot tracking | Active | Script exists, not in CI |
| Spec status page | Auto-generated | Manual |
| Tier 1-4 proofs complete | 43 modules | In progress |
| Runtime compiles hello_world | Yes | Not started |
| Beta release | Shipped | Not started |
