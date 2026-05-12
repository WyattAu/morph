# Morph Roadmap

Lean 4 v4.27.0 | Lake 5.0.0 | mathlib4 + batteries + aesop

---

## Baseline

| Metric | Value |
|---|---|
| `lake build Morph` | 323 jobs, 0 errors, 1 warning |
| `lake build Morph.Tests` | 186 jobs, 0 errors |
| Python spec-tools | 636 tests, 86% coverage |
| `.lean` files | 151 |
| Lines of Lean | ~14,878 |
| Spec modules | 43 |
| Real theorems/lemmas (Specs/) | 485 |
| `sorry` declarations | 3 (`Preservation.lean`, documented) |
| `example : True := trivial` stubs | 0 |
| Real proof modules | 7 (TypeSystem, SecurityFlow, GLOSSARY, MorphLanguage, ConcurrencyProcessAlgebra, MemoryModel, ModuleSystem) |

---

## 1. Formal Verification Completion [P0]

### 1.1 Fix 3 sorries in Preservation.lean

**File:** `Morph/Proofs/TypeSoundness/Preservation.lean:284,296,309`

All three sorries occur in non-capture substitution cases (`lam_type`, `let_type`, `for_type`). Each requires weakening `hV : HasType Gamma v tau1` into an extended typing environment `HasType (extendTypEnv Gamma x'.name tau') v tau1`. This demands proving `x'.name not in freeVars v` (beta-reduction guarantees the argument is closed w.r.t. the binder).

**Approach:**
1. Add a weakening lemma: `theorem weakening {Gamma Gamma' tau e} : Gamma <= Gamma' -> HasType Gamma e tau -> HasType Gamma' e tau`
2. Alternatively, add freshness preconditions to `subst_preserves_type` and `substList_preserves_type_all`, restructuring the mutual block
3. In each `sorry` branch, derive `x'.name notin freeVars v` from the evaluation context, then apply weakening

**Effort:** 3-5 days | **Deps:** none | **Blocks:** sorry-free CI gate

### 1.2 Eliminate stubs -- Tier 1 (runtime foundation)

These modules have real definitions in `Spec.lean` but only `example : True := trivial` in `Lemmas.lean`/`Examples.lean`.

| Module | Current stubs | Target proofs | Effort | Notes |
|---|---|---|---|---|
| **MemoryModel** | 0 (already has 6 real lemmas) | 3-5 additional | 2-3 days | Heap invariants, allocation bounds, layout soundness |
| **SecurityFlow** | 1 (Examples) | 5-8 lemmas | 1-2 weeks | Taint tracking, non-interference, lattice join properties |
| **MorphLanguage** | 0 (already has real lemmas) | 5-8 additional | 1 week | Substitution properties, evaluation determinism |
| **ConcurrencyProcessAlgebra** | 1 (Examples) | 5-10 (non-trivial) | 1-2 weeks | 31 existing theorems are mostly `trivial`; need deadlock-free proofs, channel safety |
| **TypeSystem** | 0 (already has real lemmas) | 3-5 additional | 3-5 days | Uniqueness of types, subtyping transitivity |
| **ModuleSystem** | 2 (Lemmas+Examples) | 5-8 lemmas | 1 week | Hash determinism, version constraint soundness |
| **GLOSSARY** | 2 (Lemmas+Examples) | 3-5 examples | 2-3 days | Concrete well-formed glossary instances |

**Total Tier 1:** 4-6 weeks | **Deps:** none (parallelizable)

### 1.3 Eliminate stubs -- Tier 2 (compiler/runtime support)

| Module | Stubs | Effort | Notes |
|---|---|---|---|
| **ScopingLambdaCalculus** | 0 | 1-2 weeks | Scope rules, alpha-equivalence |
| **DialectProjection** | 0 | 1-2 weeks | Dialect system for multi-stage compilation |
| **MonadicEffect** | 0 | 1-2 weeks | Effect handler semantics |
| **OperatorNullCoalescing** | 0 | 3-5 days | Operator semantics |
| **LexicalStructureSyntax** | 0 | 3-5 days | Token/literal specs |
| **ExecutionModel** | 0 | 1 week | Step relation, evaluation contexts |
| **AbiAlignmentAlgebra** | 2 | 3-5 days | ABI struct layout |
| **BackendTiling** | 0 | 1 week | Tiling correctness proofs |

**Total Tier 2:** 5-8 weeks | **Deps:** Tier 1 complete

### 1.4 Eliminate stubs -- Tier 3 (domain-specific)

| Module | Stubs | Effort |
|---|---|---|
| **BuildLattice** | 0 | 3-5 days |
| **DualOptimization** | 0 | 3-5 days |
| **LayeredConcurrency** | 2 | 5 days |
| **SchedulerRandomizedStealing** | 2 | 5 days |
| **SchedulingModes** | 2 | 3-5 days |
| **SecurityOCap** | 2 | 1 week |
| **MemoryAcyclicity** | 2 | 5 days |
| **MemoryAffineLogic** | 2 | 1 week |
| **LinkerLogic** | 0 | 3-5 days |
| **ArcAffineIntegration** | 2 | 5 days |
| **ModuleExistential** | 2 | 5 days |
| **InfrastructureSafetyContracts** | 0 | 3-5 days |
| **Financial** | 0 | 3-5 days |
| **Maths** | 0 | 3-5 days |

**Total Tier 3:** 6-9 weeks | **Deps:** Tier 1

### 1.5 Eliminate stubs -- Tier 4 (auxiliary)

| Module | Stubs | Effort |
|---|---|---|
| **Licensing** | 0 | 2-3 days |
| **LicenseDeonticLogic** | 2 | 2-3 days |
| **DependencySat** | 0 | 2-3 days |
| **UnidirectionalDataFlow** | 0 | 2-3 days |
| **StrictStateUnidirectional** | 0 | 2-3 days |
| **StorageDAWG** | 0 | 2-3 days |
| **RegistryConsensus** | 0 | 2-3 days |
| **VersionCompatibility** | 2 | 2-3 days |
| **SyntaxTranslation** | 2 | 2-3 days |
| **UnitGroupTheory** | 2 | 2-3 days |
| **TerminologyStandardization** | 0 | 2-3 days |
| **ASTGraph** | 2 | 2-3 days |
| **AbiDataRefinement** | 2 | 2-3 days |
| **README** | 0 | 1 day |

**Total Tier 4:** 3-4 weeks | **Deps:** Tier 1

---

## 2. Proof Infrastructure [P0]

### 2.1 Zero-warning CI gate

**File:** `.github/workflows/lean-build.yml`

Current `lean-build.yml` warns on sorries but does not block. The remaining 1 warning is the known sorry in `Preservation.lean`. Once 1.1 is resolved, make warnings fail the build:

```yaml
- name: Check for warnings in Morph source
  run: |
    MORPH_WARNINGS=$(grep "warning: Morph/" build.log || true)
    if [ -n "$MORPH_WARNINGS" ]; then
      echo "::error::Build contains warnings in Morph source"
      exit 1
    fi
```

**Effort:** 1 hour | **Deps:** 1.1

### 2.2 Sorry-free CI gate

Current `lean-build.yml:67-76` warns but does not fail. Change to hard failure:

```yaml
if [ "$SORRY_COUNT" -gt 0 ]; then
  echo "::error::$SORRY_COUNT sorry declaration(s) found"
  exit 1
fi
```

**Effort:** 30 min | **Deps:** 1.1, 1.2

### 2.3 Stub detection in CI

Add a check for `example : True := trivial` in `Morph/Specs/`:

```yaml
- name: Check for spec stubs
  run: |
    STUB_COUNT=$(grep -r "example : True := trivial" Morph/Specs/ --include="*.lean" | wc -l)
    echo "Stub count: $STUB_COUNT"
    # Warn for now, fail after Tier 1 deadline
```

**Effort:** 30 min | **Deps:** none

### 2.4 Pre-commit hook hardening

**File:** `.githooks/pre-commit`

The current hook warns on sorries but allows the commit (line 50). After 1.1 resolves, change to `exit 1`:

```bash
if [ "$SORRY_COUNT" -gt 0 ]; then
    echo "Commit blocked. Fix sorry declarations."
    exit 1
fi
```

**Effort:** 15 min | **Deps:** 1.1

---

## 3. Testing Infrastructure [P1]

### 3.1 Lean property-based testing (SlimCheck)

Add SlimCheck dependency and write property tests for:

| Target | Properties | File |
|---|---|---|
| MemoryModel | `allocate` always produces fresh `BlockId`; `readByte` after `writeByte` returns written value | `Morph/Tests/Memory.lean` |
| TypeSoundness | Random closed terms are either well-typed or rejected | `Morph/Tests/Typing.lean` |
| Semantics | Evaluation is deterministic for pure expressions | `Morph/Tests/Semantics.lean` |

**Effort:** 1-2 weeks | **Deps:** SlimCheck added to `lakefile.lean`

### 3.2 Regression test snapshots

Script to capture and diff build metrics:

```bash
#!/usr/bin/env bash
# scripts/regression-snapshot.sh
lake build Morph 2>&1 | tee build.log
echo "errors: $(grep -c 'error:' build.log || echo 0)"
echo "warnings: $(grep -c 'warning:' build.log || echo 0)"
echo "sorries: $(grep -r 'sorry' Morph/ --include='*.lean' | grep -v '/--' | wc -l)"
echo "stubs: $(grep -r 'example : True := trivial' Morph/Specs/ --include='*.lean' | wc -l)"
```

Store snapshots in `.reports/regression/`. Fail CI if any metric increases.

**Effort:** 3-4 hours | **Deps:** none

### 3.3 Python spec-tools coverage improvement

Current: 256 tests, 48% coverage. Target: 70%.

Priority areas for new tests:
- `scripts/spec_tools/validation/` -- constraint validation paths
- `scripts/spec_tools/link_checker/` -- edge cases (relative links, anchors)
- `scripts/spec_tools/formatting/` -- nested list formatting, table alignment

**Effort:** 1 week | **Deps:** none

### 3.4 Fix ghost CI references

Multiple CI configs reference nonexistent files:

| Config | Ghost reference | Fix |
|---|---|---|
| `.gitlab-ci.yml:25` | `tests/requirements.txt` | Point to `scripts/` or remove job |
| `.gitlab-ci.yml:27` | `tests/specification_test_suite.py` | Point to `scripts/tests/` |
| `.github/workflows/specification_tests.yml:36` | `tests/requirements.txt` | Point to `scripts/` or remove matrix job |
| `.github/workflows/specification_tests.yml:56` | `tests/specification_test_suite.py` | Point to `scripts/tests/` |
| `.github/workflows/specification_tests.yml:104` | `scripts/spec_linter.py` | Remove (replaced by `spec-tools lint`) |
| `.github/workflows/specification_tests.yml:108` | `scripts/spec_link_checker.py` | Remove (replaced by `spec-tools check-links`) |
| `.github/workflows/specification_tests.yml:112` | `scripts/spec_version_validator.py` | Remove (replaced by `spec-tools validate`) |
| `Jenkinsfile` | `tests/requirements.txt`, `tests/specification_test_suite.py` | Update paths or deprecate |

**Effort:** 2-3 hours | **Deps:** none

---

## 4. CI/CD Consolidation [P1]

### 4.1 Unify pre-commit systems

Two overlapping pre-commit systems exist:
- `.githooks/pre-commit` -- bash, runs `lake build` + sorry scan + pytest
- `.pre-commit-config.yaml` -- Python framework, runs `spec-tools format/lint/validate/check-links`

Consolidate into one. Recommended approach: keep the bash hook as primary (it runs `lake build`), call `spec-tools` from within it, and remove `.pre-commit-config.yaml`.

**Effort:** 3-4 hours | **Deps:** 3.4

### 4.2 Consolidate GitHub Actions workflows

Three workflows exist with overlapping scope:

| Workflow | Purpose | Status |
|---|---|---|
| `lean-build.yml` | `lake build Morph`, error/warning/sorry checks | Working, needs hardening (2.1, 2.2) |
| `spec-validation.yml` | `spec-tools format/lint/validate/check-links` | Working |
| `specification_tests.yml` | Python pytest on ghost files | Broken (3.4) |

Plan:
1. Fix `specification_tests.yml` per 3.4, or remove and fold into `spec-validation.yml`
2. Add `Morph.Tests` build step to `lean-build.yml`
3. Add regression snapshot step to `lean-build.yml`

**Effort:** 4-6 hours | **Deps:** 3.4

### 4.3 Lean toolchain caching

Current `lean-build.yml` caches `.lake/build` and `.lake/packages`. Verify the cache key includes `lake-manifest.json`. Consider adding elan toolchain caching:

```yaml
- uses: actions/cache@v4
  with:
    path: ~/.elan
    key: elan-${{ runner.os }}-${{ hashFiles('lean-toolchain') }}
```

**Effort:** 1 hour | **Deps:** none

### 4.4 Nightly full build

Add to `lean-build.yml` or create `.github/workflows/nightly.yml`:

```yaml
on:
  schedule:
    - cron: '0 6 * * *'  # 06:00 UTC daily
jobs:
  full-build:
    steps:
      - run: lake build Morph
      - run: lake build Morph.Tests
      - run: lake exe morph test  # if executable tests exist
```

Track build time in a GitHub Actions artifact. Alert on regression > 20%.

**Effort:** 2-3 hours | **Deps:** 4.2

---

## 5. Documentation [P1]

### 5.1 Spec module status tracking

Create `SPEC_STATUS.md` with a machine-generated table:

| Module | Spec.lean | Lemmas.lean | Examples.lean | Sorries | Stubs |
|---|---|---|---|---|---|

Generate via `scripts/gen-spec-status.sh`:

```bash
for d in Morph/Specs/*/; do
  name=$(basename "$d")
  spec_lines=$(wc -l < "$d/Spec.lean" 2>/dev/null || echo "N/A")
  real_lemmas=$(grep -c 'theorem\|lemma ' "$d/Lemmas.lean" 2>/dev/null | head -1 || echo 0)
  stubs=$(grep -c 'example : True := trivial' "$d/Lemmas.lean" "$d/Examples.lean" 2>/dev/null || echo 0)
  echo "$name|$spec_lines|$real_lemmas|$stubs"
done
```

Run in CI to detect drift.

**Effort:** 3-4 hours | **Deps:** none

### 5.2 API documentation generation

Use `lake doc` (Lean 4 doc-gen) or `lake exe doc-gen4` to generate HTML documentation from Lean source. Target: `docs/api/`.

```bash
lake exe doc-gen4 Morph --output docs/api/
```

Add to `lean-build.yml` as a non-blocking step (warnings acceptable during doc-gen transition).

**Effort:** 1 day | **Deps:** none

### 5.3 Cross-reference validation

Script to verify that:
- Every `import Morph.Specs.X` resolves to an existing `Spec.lean`
- Every theorem referenced in markdown (`spec/`) links to a real Lean declaration
- Every ADR in `.specs/02_adrs/` referenced from code exists

**Effort:** 4-6 hours | **Deps:** 5.1

---

## 6. Implementation Phase [P2]

### 6.1 Morph compiler frontend

| Component | Description | Effort | File(s) |
|---|---|---|---|
| **Lexer** | Tokenize Morph source into `Morph.Syntax.Token` stream | 2-3 weeks | `Morph/Frontend/Lexer.lean` |
| **Parser** | Recursive descent or combinator parser producing `Morph.Syntax.AST` | 3-4 weeks | `Morph/Frontend/Parser.lean` |
| **Name resolution** | Resolve identifiers, build symbol table | 2-3 weeks | `Morph/Frontend/NameResolution.lean` |
| **HIR lowering** | AST -> `Morph.HIR.Expr` | 1-2 weeks | `Morph/Frontend/HIR.lean` |

**Total:** 8-12 weeks | **Deps:** 1.2 (Tier 1 complete), 2.1

### 6.2 Type checker extraction

Extract the type checking rules from the Lean 4 proof layer into a certified executable:

| Step | Description | Effort |
|---|---|---|
| Type synthesis | `synthType : Expr -> TypEnv -> Option Typ` | 2-3 weeks |
| Type checking | `checkType : Expr -> TypEnv -> Typ -> Bool` | 1-2 weeks |
| Unification | Pattern unification for type variables | 2-3 weeks |
| Error reporting | Human-readable type error messages | 1 week |

**Total:** 6-9 weeks | **Deps:** 1.2, 6.1

### 6.3 Runtime

| Component | Description | Effort | Spec reference |
|---|---|---|---|
| **Memory model** | Heap allocation, GC, layout | 3-4 weeks | `Morph/Specs/MemoryModel/` |
| **Concurrency** | Actor scheduler, channels | 4-6 weeks | `Morph/Specs/ConcurrencyProcessAlgebra/` |
| **FFI bridge** | C ABI calling convention | 2-3 weeks | `Morph/Specs/AbiAlignmentAlgebra/` |

**Total:** 9-13 weeks | **Deps:** 6.1, 6.2, Tier 1 proofs

### 6.4 Standard library

| Component | Effort |
|---|---|
| Core types (Int, String, Bool, List, Option) | 2-3 weeks |
| Collections (Map, Set, Array) | 2-3 weeks |
| I/O primitives | 1-2 weeks |
| Concurrency primitives (spawn, send, recv) | 2-3 weeks |

**Total:** 7-11 weeks | **Deps:** 6.3

---

## 7. Research Directions [P3]

### 7.1 Dependent types for runtime

Investigate extracting dependent type information from Lean 4 proofs for use at runtime (e.g., array bounds verified at compile time, nullable tracking). Requires Lean 4 code extraction pipeline.

**Effort:** Ongoing research | **Milestone:** Proof of concept in 3 months

### 7.2 Linear types for resource management

Extend the type system with affine/linear type qualifiers to enforce unique ownership of file handles, network connections, and memory regions. Formalize in `Morph/Specs/MemoryAffineLogic/`.

**Effort:** Ongoing research | **Milestone:** Spec.lean definitions in 2 months

### 7.3 Capability-based security enforcement

Extend `Morph/Specs/SecurityOCap/` with a formal capability model. Prove that unprivileged code cannot access protected resources. Connect to the `SecurityFlow` information-flow analysis.

**Effort:** Ongoing research | **Milestone:** Noninterference theorem in 3 months

### 7.4 Multi-stage compilation (dialect system)

Extend `Morph/Specs/DialectProjection/` with a verified multi-stage compilation pipeline. Each dialect (core, unsafe, ffi) is a well-defined subset. Prove that dialect lowering preserves semantics.

**Effort:** Ongoing research | **Milestone:** Dialect soundness theorem in 4 months

---

## Execution Timeline

```
Week  1:  [1.1] [2.3] [3.4]                   -- sorries, stub detection, fix ghost CI
Week  2:  [1.1 cont] [2.1] [2.2] [2.4]        -- finish sorries, harden CI gates
Week  3:  [1.2 MemoryModel] [3.3]              -- first Tier 1 module, Python tests
Week  4:  [1.2 SecurityFlow] [3.1]             -- SlimCheck setup
Week  5:  [1.2 MorphLanguage] [3.2]            -- regression snapshots
Week  6:  [1.2 ConcurrencyProcessAlgebra]       -- process algebra proofs
Week  7:  [1.2 TypeSystem + ModuleSystem]       -- remaining Tier 1
Week  8:  [1.2 GLOSSARY] [4.1] [4.2]           -- Tier 1 done, CI consolidation
Week  9:  [5.1] [5.2] [4.3] [4.4]              -- docs, caching, nightly
Week 10: [1.3 ScopingLambdaCalculus]            -- begin Tier 2
Week 11-18: [1.3 remaining] [5.3]              -- Tier 2 modules, cross-refs
Week 19-26: [1.4] [1.5]                        -- Tier 3 + Tier 4
Week 27+:  [6.1] [6.2] [6.3] [6.4]             -- implementation phase
Ongoing:   [7.x]                                -- research directions
```

---

## Success Criteria

| Criterion | Target | Current |
|---|---|---|
| `lake build Morph` errors | 0 | 0 |
| `lake build Morph` warnings | 0 | 1 |
| `sorry` in `Morph/` | 0 | 3 |
| `example : True := trivial` stubs (Tier 1) | 0 | 0 |
| `example : True := trivial` stubs (all) | 0 | 0 |
| CI passes on every push | Yes | Partial (ghost refs) |
| Python spec-tools coverage | >= 80% | 86% |
| Lean tests pass | All | All |
| Pre-commit blocks on sorry | Yes | Warns only |
| Regression snapshot tracking | Active | None |
| Spec status page | Auto-generated | None |

---

## Dependencies Graph

```
[1.1 Preservation sorries]
  |
  +---> [2.1 Zero-warning gate] ---> [2.4 Pre-commit hardening]
  +---> [2.2 Sorry-free gate]
  |
[1.2 Tier 1 proofs] ---> [1.3 Tier 2 proofs] ---> [1.4 Tier 3] ---> [1.5 Tier 4]
  |                                                                   |
  +---> [6.1 Compiler frontend] ---> [6.2 Type checker] ---> [6.3 Runtime] ---> [6.4 Stdlib
  |                                                                   |
  +---> [7.1-7.4 Research]                                          |
                                                                      |
[3.4 Fix ghost CI] ---> [4.1 Unify pre-commit] ---> [4.2 Consolidate workflows]
                            |
[3.3 Python coverage]          +---> [4.3 Caching] ---> [4.4 Nightly]
[3.1 SlimCheck]               |
[3.2 Snapshots]               +---> [5.1 Spec status] ---> [5.3 Cross-refs]
[2.3 Stub detection]          |
                               +---> [5.2 API docs]
```
