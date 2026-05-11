# Morph Specification Quality Roadmap

Lean 4 formal verification layer -- immediate next steps after build fix (commit 65341e5).

**Build baseline:** `lake build Morph` -- 323 jobs, 0 errors, 11 warnings
**Lean:** v4.27.0 | **Lake:** 5.0.0 | **Deps:** mathlib4, batteries, aesop

---

## 1. Warning Elimination

### 1.1 Fix 3 `sorry` in Preservation.lean (requires theorem restructure)
- **File:** `Morph/Proofs/TypeSoundness/Preservation.lean` lines 281, 294, 308
- **Problem:** Non-capture substitution cases for `lam_type`, `let_type`, and `for_type`. The `subst_preserves_type` theorem lacks a freshness precondition (`x not in freeVars v`), which is needed to weaken `hV : HasType Gamma v tau1` into the extended typing environment after swapping bindings via `extendTypEnv_swap`.
- **Root cause:** `subst_preserves_type` signature is `(Gamma) (e) (x) (v) (tau1) (tau) ...` with no freshness precondition. Adding one requires restructuring the entire mutual block (subst_preserves_type + substList_preserves_type_all) and updating all call sites in the `preservation` theorem.
- **Approach:** Add `hFresh : x not in freeVars v` parameter to both `subst_preserves_type` and `substList_preserves_type_all`. Update all recursive calls. In the `preservation` theorem, derive freshness from the evaluation context (beta-reduction guarantees the argument is closed with respect to the binder).
- **Priority:** P0 | **Effort:** 3-5 days | **Deps:** none
- **Blocks:** sorry-free CI gate

### 1.2 Fix 2 unused `simp` arguments [DONE]
- Removed unused `h1` hypotheses from `simp only` calls at former lines 121, 127.

### 1.3 Fix 8 unused variable warnings [DONE]
- Prefixed unused parameters with `_` in CommonTypes.lean.

### 1.4 Zero-warning CI gate
- **Target:** `lake build Morph` with 0 errors, 0 warnings
- **Priority:** P0 | **Effort:** part of #1.1-1.3 | **Deps:** all above

---

## 2. Proof Restoration -- Spec Modules

42 Lemmas.lean + 42 Examples.lean files contain only `example : True := trivial` stubs across 21 spec modules. Real proofs needed in priority order.

### 2.1 Tier 1: Runtime Foundation Modules (do first)

| Module | Lemmas | Examples | Why |
|---|---|---|---|
| **MemoryModel** | stub | stub | Heap, allocation, layout -- runtime memory subsystem spec |
| **TypeSoundness** | stub (Proofs/ has real content) | stub | Preservation + Progress -- type system correctness |
| **SecurityFlow** | stub | stub | Information flow, taint tracking -- security guarantees |
| **MorphLanguage** | stub | stub | Core syntax/semantics -- language definition |
| **ConcurrencyProcessAlgebra** | stub | stub | Process calculus, scheduling -- runtime concurrency model |

**Priority:** P0 | **Effort:** 2-4 weeks per module | **Deps:** none (can parallelize)

### 2.2 Tier 2: Compiler/Runtime Support Modules

| Module | Why |
|---|---|
| **ScopingLambdaCalculus** | Scope rules, alpha-equivalence for parser |
| **DialectProjection** | Dialect system for multi-stage compilation |
| **MonadicEffect** | Effect system for async/io semantics |
| **OperatorNullCoalescing** | Operator semantics for codegen |
| **LexicalStructureSyntax** | Token/literal specs for lexer |
| **ModuleSystem** | Import resolution for compiler frontend |
| **ExecutionModel** | Step relation, evaluation contexts |
| **AbiAlignmentAlgebra** | ABI struct layout for FFI bridge |

**Priority:** P1 | **Effort:** 1-2 weeks per module | **Deps:** Tier 1 complete

### 2.3 Tier 3: Domain-Specific Modules

| Module | Why |
|---|---|
| **BuildLattice** | Build dependency ordering |
| **DualOptimization** | Optimization search for OSE |
| **LayeredConcurrency** | Layered threading model |
| **SchedulerRandomizedStealing** | Work-stealing scheduler spec |
| **SchedulingModes** | `@critical` vs cooperative scheduling |
| **SecurityOCap** | Object capability security |
| **MemoryAcyclicity** | Acyclic heap invariant |
| **MemoryAffineLogic** | Affine type reasoning |
| **LinkerLogic** | Linker symbol resolution |
| **ArcAffineIntegration** | ARC integration spec |

**Priority:** P2 | **Effort:** 1 week each | **Deps:** Tier 1

### 2.4 Tier 4: Auxiliary Modules

| Module | Why |
|---|---|
| **Licensing** | License compatibility DSL |
| **LicenseDeonticLogic** | Deontic logic for licenses |
| **DependencySat** | Dependency satisfiability |
| **ModuleExistential** | Existential module types |
| **UnidirectionalDataFlow** | Data flow direction |
| **StrictStateUnidirectional** | State transition linearity |
| **StorageDAWG** | Merkle DAG storage |
| **RegistryConsensus** | Package registry consensus |
| **VersionCompatibility** | Semver compatibility |
| **SyntaxTranslation** | Source-to-source transforms |
| **UnitGroupTheory** | Algebraic unit groups |
| **TerminologyStandardization** | Glossary consistency |
| **ASTGraph** | AST traversal properties |
| **AbiDataRefinement** | ABI data refinement |
| **TypeSystem** | Core type system (overlaps TypeSoundness) |
| **README / GLOSSARY** | Meta-modules |

**Priority:** P2 | **Effort:** 2-3 days each | **Deps:** Tier 1

### Proof Restoration Strategy

For each module:
1. Read the `Spec.lean` to understand definitions, types, inductives
2. Write 3-5 `theorem`/`lemma` declarations in `Lemmas.lean` proving non-trivial properties
3. Write 2-3 `example` declarations in `Examples.lean` demonstrating concrete instances
4. Each proof should use `aesop`, `simp`, or manual tactics -- never `sorry`
5. Run `lake build Morph` after each module

---

## 3. CI/CD

### 3.1 GitHub Actions -- Build + Warning Check
- **File:** `.github/workflows/build.yml` (new)
- **Triggers:** push to main, PRs to main
- **Steps:**
  1. Checkout + Lean 4 / Lake cache
  2. `lake build Morph`
  3. Fail if any error
  4. Fail if `Morph/` source emits warnings (filter out `.lake/packages/`)
  5. Fail if any `sorry` in `Morph/` source (grep check)
- **Priority:** P0 | **Effort:** 4-6 hours | **Deps:** none
- **Note:** Existing workflows (`spec-validation.yml`, `specification_tests.yml`) already exist but may need updating

### 3.2 Lean toolchain caching
- Use `leanprover/lean4:stable` Docker image or `cachix` for `.lake/` oleans
- **Priority:** P1 | **Effort:** 2-3 hours | **Deps:** #3.1

### 3.3 Nightly full build
- Cron job running `lake build` + `lake env lean --make` for full compilation
- Track build time trends, catch incremental breakage
- **Priority:** P2 | **Effort:** 2 hours | **Deps:** #3.1

---

## 4. Documentation Accuracy

### 4.1 Fix false claims [DONE]
- Updated README.md, impl/roadmap.md, impl/overview.md, ADR-007, DESIGN-001, DESIGN-003, design/index.md
- **Files needing updates:**
  - `README.md:154` -- claims "all proofs are complete (no sorry)"
  - `.specs/04_future_state/design/index.md:236` -- same claim
  - `.specs/02_adrs/ADR-007-ci-cd-integration.md:11` -- same claim
  - `impl/roadmap.md:27` -- "All proofs are complete (no sorry)"
- **Update to:** "Proofs in progress -- 1 sorry in Preservation.lean, 84 stub Lemmas/Examples files"
- **Priority:** P0 | **Effort:** 30 min | **Deps:** none

### 4.2 Add spec module status table
- In README or a dedicated `SPEC_STATUS.md`
- Track: module name, Spec done (Y/N), Lemmas done (Y/N), Examples done (Y/N), sorries
- Auto-generate from a script that greps for `example : True := trivial` and `sorry`
- **Priority:** P1 | **Effort:** 3-4 hours | **Deps:** none

---

## 5. Python Spec-Tools

### 5.1 Fix PEP 668 venv issue
- **Problem:** System Python blocks `pip install` due to externally-managed-environment (PEP 668)
- **Fix:** Use `python -m venv .venv` + activate, or add `pyproject.toml` with `[tool.spec-tools]`
- **Priority:** P2 | **Effort:** 2-3 hours | **Deps:** none

### 5.2 Unblock spec-tools tests
- Once venv works, run test suite and fix any failures
- **Priority:** P2 | **Effort:** 2-4 hours | **Deps:** #5.1

---

## 6. Testing Infrastructure

### 6.1 Lean test framework
- Current: 6 test files in `Morph/Tests/` (Core, Memory, Typing, Semantics, AST, Executable)
- Verify all pass with `lake build Morph.Tests` (or equivalent)
- **Priority:** P1 | **Effort:** 2 hours | **Deps:** none

### 6.2 Property-based tests
- Use Lean 4 `Lean.Data.RBMap`/`HashMap` for random generation, or `SlimCheck` (from mathlib)
- Target: MemoryModel (heap operations), TypeSoundness (random typing derivations)
- **Priority:** P2 | **Effort:** 1-2 weeks | **Deps:** Tier 1 proofs started

### 6.3 Regression tests
- Script that snapshots `lake build` output (error count, warning count, sorry count)
- Run in CI to catch regressions
- **Priority:** P1 | **Effort:** 3-4 hours | **Deps:** #3.1

---

## Execution Order

```
Week 1:  [1.2] [1.3] [4.1] [3.1]          -- quick wins, CI gate, doc fix
Week 2:  [1.1] [1.2]                      -- Preservation.lean sorry + simp fixes
Week 3:  [2.1 MemoryModel proofs]          -- first real module
Week 4:  [2.1 MorphLanguage proofs]        -- core language spec
Week 5:  [2.1 TypeSoundness lemmas]        -- align with Proofs/ layer
Week 6:  [2.1 SecurityFlow proofs]         -- security guarantees
Week 7:  [2.1 ConcurrencyProcessAlgebra]   -- concurrency spec
Week 8+: [2.2] [6.1] [6.3] [3.2]           -- Tier 2, tests, CI caching
```

---

## Success Criteria

- [ ] `lake build Morph` -- 0 errors, 0 warnings
- [ ] Zero `sorry` in `Morph/` source
- [ ] Zero `example : True := trivial` stubs in Tier 1 modules
- [ ] CI passes on every push (build + sorry check + warning check)
- [ ] Documentation accurately reflects current proof status
- [ ] All existing tests pass
