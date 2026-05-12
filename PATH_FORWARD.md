# Morph: Path Forward and Detailed Roadmap

Lean 4 v4.27.0 | Lake 5.0.0 | mathlib4 + batteries + aesop

---

## Current Baseline (post-audit, 2026-05-12)

| Metric | Value | Status |
|--------|-------|--------|
| `lake build Morph` | 323 jobs, 0 errors, 1 warning (sorry) | PASS |
| `lake build Morph.Tests` | 186 jobs, 0 errors | PASS |
| Python spec-tools | 405 tests, 71% coverage | PASS |
| ruff lint | 0 errors, 0 warnings | PASS |
| ruff format | 0 unformatted files | PASS |
| mypy strict | 0 errors across 66 source files | PASS |
| `.lean` files | 150 | -- |
| Lines of Lean | 13,029 | -- |
| Spec modules | 43 | -- |
| Real theorems/lemmas (Specs/) | 376 | -- |
| `sorry` declarations | 3 (`Preservation.lean:284,296,309`) | KNOWN |
| `example : True := trivial` stubs | 15 across 12 directories | WARNING |
| Lean test files | 6 (`Morph/Tests/`) | -- |
| ADRs | 11 | -- |
| CI workflows | 3 GitHub Actions + GitLab CI + Jenkins | -- |
| Pre-commit hook | 7-step gate (lake build, sorry, stubs, tests, ruff, mypy, lint) | ACTIVE |
| Documentation emojis | 0 | CLEAN |

---

## Phase 1: Formal Verification Completion [P0 -- 4-6 weeks]

### 1.1 Eliminate 3 sorries in Preservation.lean

**File:** `Morph/Proofs/TypeSoundness/Preservation.lean:284,296,309`

All three sorries are in non-capture substitution cases (`lam_type`, `let_type`, `for_type`). Each requires a weakening lemma to extend the typing environment.

**Approach:**
1. Prove `theorem weakening : Gamma <= Gamma' -> HasType Gamma e tau -> HasType Gamma' e tau`
2. In each sorry branch, derive `x'.name notin freeVars v` from the evaluation context
3. Apply weakening to carry the type through the extended environment

**Effort:** 3-5 days | **Deps:** none | **Blocks:** sorry-free CI gate

### 1.2 Eliminate 15 spec stubs

Current stubs across 12 directories. Each requires replacing `example : True := trivial` with real lemmas or examples that exercise the module's definitions.

| Module | Stubs | Target | Effort |
|--------|-------|--------|--------|
| AbiAlignmentAlgebra | 2 | Layout soundness lemmas | 3-5 days |
| AbiDataRefinement | 2 | Refinement relation proofs | 3-5 days |
| ArcAffineIntegration | 2 | Integration correctness | 5 days |
| ASTGraph | 2 | Graph traversal properties | 3-5 days |
| GLOSSARY | 2 | Well-formed glossary instances | 2-3 days |
| LayeredConcurrency | 2 | Layer composition safety | 5 days |
| LicenseDeonticLogic | 2 | Deontic logic properties | 2-3 days |
| MemoryAcyclicity | 2 | Acyclicity preservation | 5 days |
| MemoryAffineLogic | 2 | Affine reasoning lemmas | 5 days |
| ModuleExistential | 2 | Existential packaging | 5 days |
| ModuleSystem | 2 | Hash determinism, versioning | 1 week |
| SchedulerRandomizedStealing | 2 | Stealing correctness | 5 days |
| SchedulingModes | 2 | Mode transition safety | 3-5 days |
| SecurityOCap | 2 | Capability non-interference | 1 week |
| VersionCompatibility | 2 | Semver constraint soundness | 2-3 days |
| SyntaxTranslation | 2 | Round-trip preservation | 3-5 days |
| UnitGroupTheory | 2 | Group axiom verification | 2-3 days |

**Total:** 6-9 weeks | **Deps:** none (parallelizable)

### 1.3 Add real proofs to Tier 2 modules with zero lemmas

19 Tier 2 modules have real `Spec.lean` content (>50 lines) but zero real lemmas. Priority order by dependency depth:

1. **BackendTiling** (188 lines) -- Tiling correctness, no-overlap
2. **BuildLattice** (175 lines) -- Lattice join/meet properties
3. **TerminologyStandardization** (129 lines) -- Term equivalence
4. **DependencySat** (108 lines) -- SAT constraint soundness

**Effort:** 4-6 weeks | **Deps:** 1.1

---

## Phase 2: Proof Infrastructure Hardening [P0 -- 1-2 weeks]

### 2.1 Zero-warning CI gate

Once 1.1 resolves the 3 sorries, the single remaining warning disappears. Update `lean-build.yml` to fail on any warning:

```yaml
- name: Check for warnings
  run: |
    if grep "warning:" build.log; then
      echo "::error::Build contains warnings"
      exit 1
    fi
```

**Effort:** 30 min | **Deps:** 1.1

### 2.2 Sorry-free CI gate

Change `lean-build.yml:67-76` from warning to hard failure once Preservation.lean sorries are resolved.

**Effort:** 15 min | **Deps:** 1.1

### 2.3 Stub regression detection

Add to CI: track stub count, fail if it increases.

```bash
STUB_COUNT=$(grep -rc "example : True := trivial" Morph/Specs/ --include="*.lean" | grep -v ":0" | wc -l)
echo "stub_count=$STUB_COUNT" >> $GITHUB_OUTPUT
```

**Effort:** 1 hour | **Deps:** none

### 2.4 Pre-commit hook: block on sorry after Phase 1

Update `.githooks/pre-commit` step 2: change from warning to `exit 1` once all sorries are resolved.

**Effort:** 15 min | **Deps:** 1.1, 1.2

---

## Phase 3: Testing Infrastructure [P1 -- 2-3 weeks]

### 3.1 Lean property-based testing (SlimCheck)

Add SlimCheck dependency to `lakefile.lean`. Write property tests for:

| Target | Properties | File |
|--------|-----------|------|
| MemoryModel | `allocate` produces fresh `BlockId`; `readByte` after `writeByte` returns written value | `Morph/Tests/Memory.lean` |
| TypeSoundness | Well-typed terms do not get stuck | `Morph/Tests/Typing.lean` |
| Semantics | Evaluation is deterministic for pure expressions | `Morph/Tests/Semantics.lean` |
| ConcurrencyProcessAlgebra | Process algebra equivalences hold | `Morph/Tests/Concurrency.lean` |

**Effort:** 2-3 weeks | **Deps:** SlimCheck added to lakefile

### 3.2 Regression test snapshots

The `scripts/regression-snapshot.sh` script already exists. Integrate into CI:

- Store snapshots in `.reports/regression/`
- Fail CI if error count, warning count, sorry count, or stub count increases
- Track build time; alert on >20% regression

**Effort:** 3-4 hours | **Deps:** none

### 3.3 Python spec-tools coverage improvement

Current: 405 tests, 71% coverage (up from 48%). Target: 80%.

Priority areas for new tests:
- `scripts/spec_tools/cli/commands/` -- CLI integration tests (currently 13-19% coverage)
- `scripts/spec_tools/verification/` -- Verification module tests (currently 0% coverage)
- `scripts/spec_tools/utils/file_utils.py` -- Edge cases (currently 71%)

**Effort:** 1-2 weeks | **Deps:** none

### 3.4 Fix ghost CI references

Multiple CI configs reference nonexistent files (documented in ROADMAP section 3.4):

| Config | Ghost reference | Fix |
|--------|----------------|-----|
| `.gitlab-ci.yml:25` | `tests/requirements.txt` | Point to `scripts/pyproject.toml` |
| `.gitlab-ci.yml:27` | `tests/specification_test_suite.py` | Point to `scripts/tests/` |
| `.github/workflows/specification_tests.yml` | Multiple ghost paths | Fold into `spec-validation.yml` |
| `Jenkinsfile` | `tests/requirements.txt` | Update paths |

**Effort:** 2-3 hours | **Deps:** none

---

## Phase 4: CI/CD Consolidation [P1 -- 1 week]

### 4.1 Consolidate GitHub Actions workflows

Three overlapping workflows exist:

| Workflow | Purpose | Action |
|----------|---------|--------|
| `lean-build.yml` | Lake build + quality gates | Keep, harden |
| `spec-validation.yml` | spec-tools format/lint/validate | Keep |
| `specification_tests.yml` | Python pytest on ghost files | Remove, fold into `spec-validation.yml` |

Add `Morph.Tests` build step and regression snapshot to `lean-build.yml`.

**Effort:** 4-6 hours | **Deps:** 3.4

### 4.2 Lean toolchain caching

Verify `.lake/build` and `.lake/packages` cache keys include `lake-manifest.json`. Add elan toolchain caching:

```yaml
- uses: actions/cache@v4
  with:
    path: ~/.elan
    key: elan-${{ runner.os }}-${{ hashFiles('lean-toolchain') }}
```

**Effort:** 1 hour | **Deps:** none

### 4.3 Nightly full build

Add scheduled workflow for daily full build with build time tracking.

**Effort:** 2-3 hours | **Deps:** 4.1

---

## Phase 5: Specification Deepening [P1 -- 6-10 weeks]

### 5.1 Fill Tier 4 empty modules (16 modules)

These modules have no `Spec.lean` content at all:

| Module | Domain | Effort |
|--------|--------|--------|
| DialectProjection | Multi-stage compilation | 1-2 weeks |
| DualOptimization | Optimization theory | 1 week |
| ExecutionModel | Operational semantics | 1-2 weeks |
| Financial | Financial domain types | 3-5 days |
| InfrastructureSafetyContracts | Safety invariants | 1 week |
| LexicalStructureSyntax | Lexer specification | 3-5 days |
| Licensing | License types | 2-3 days |
| LinkerLogic | Linker semantics | 3-5 days |
| Maths | Mathematical foundations | 1 week |
| MonadicEffect | Effect handlers | 1-2 weeks |
| OperatorNullCoalescing | Operator semantics | 3-5 days |
| RegistryConsensus | Distributed consensus | 1 week |
| ScopingLambdaCalculus | Scope rules | 1-2 weeks |
| StorageDAWG | DAWG data structure | 3-5 days |
| StrictStateUnidirectional | Unidirectional state | 3-5 days |
| UnidirectionalDataFlow | Data flow analysis | 3-5 days |

**Total:** 8-12 weeks | **Deps:** Phase 1 complete

### 5.2 Spec module status automation

Create `scripts/gen-spec-status.sh` to auto-generate `SPEC_STATUS.md`. Run in CI to detect drift.

**Effort:** 3-4 hours | **Deps:** none

### 5.3 Cross-reference validation

Script to verify:
- Every `import Morph.Specs.X` resolves to an existing `Spec.lean`
- Every theorem referenced in markdown links to a real Lean declaration
- Every ADR referenced from code exists in `.specs/02_adrs/`

**Effort:** 4-6 hours | **Deps:** 5.2

---

## Phase 6: Implementation Phase [P2 -- 6-9 months]

### 6.1 Morph compiler frontend

| Component | Description | Effort |
|-----------|-------------|--------|
| Lexer | Tokenize Morph source into token stream | 2-3 weeks |
| Parser | Recursive descent parser producing AST | 3-4 weeks |
| Name resolution | Resolve identifiers, build symbol table | 2-3 weeks |
| HIR lowering | AST to High-level IR | 1-2 weeks |

**Total:** 8-12 weeks | **Deps:** Phase 1 complete

### 6.2 Type checker extraction

Extract type checking rules from the Lean 4 proof layer into a certified executable:

| Step | Description | Effort |
|------|-------------|--------|
| Type synthesis | `synthType : Expr -> TypEnv -> Option Typ` | 2-3 weeks |
| Type checking | `checkType : Expr -> TypEnv -> Typ -> Bool` | 1-2 weeks |
| Unification | Pattern unification for type variables | 2-3 weeks |
| Error reporting | Human-readable type error messages | 1 week |

**Total:** 6-9 weeks | **Deps:** 6.1

### 6.3 Runtime

| Component | Description | Effort |
|-----------|-------------|--------|
| Memory model | Heap allocation, GC, layout | 3-4 weeks |
| Concurrency | Actor scheduler, channels | 4-6 weeks |
| FFI bridge | C ABI calling convention | 2-3 weeks |

**Total:** 9-13 weeks | **Deps:** 6.1, 6.2

### 6.4 Standard library

| Component | Effort |
|-----------|--------|
| Core types (Int, String, Bool, List, Option) | 2-3 weeks |
| Collections (Map, Set, Array) | 2-3 weeks |
| I/O primitives | 1-2 weeks |
| Concurrency primitives (spawn, send, recv) | 2-3 weeks |

**Total:** 7-11 weeks | **Deps:** 6.3

---

## Phase 7: Research Directions [P3 -- Ongoing]

### 7.1 Dependent types for runtime

Extract dependent type information from Lean 4 proofs for runtime use (array bounds, nullable tracking). Requires Lean 4 code extraction pipeline.

**Milestone:** Proof of concept in 3 months

### 7.2 Linear types for resource management

Extend the type system with affine/linear type qualifiers. Formalize in `Morph/Specs/MemoryAffineLogic/`.

**Milestone:** Spec.lean definitions in 2 months

### 7.3 Capability-based security enforcement

Extend `Morph/Specs/SecurityOCap/` with formal capability model. Prove noninterference theorem.

**Milestone:** Noninterference theorem in 3 months

### 7.4 Multi-stage compilation (dialect system)

Extend `Morph/Specs/DialectProjection/` with verified multi-stage compilation pipeline. Prove dialect lowering preserves semantics.

**Milestone:** Dialect soundness theorem in 4 months

---

## Execution Timeline

```
Week  1-2:  [1.1] [2.3] [3.4] [5.2]          -- sorries, stub detection, fix ghost CI, status script
Week  3-4:  [1.2第一批] [2.1] [2.2] [3.2]     -- first stub batch, harden CI gates, snapshots
Week  5-6:  [1.2第二批] [3.1] [3.3]            -- stub batch 2, SlimCheck, Python coverage
Week  7-8:  [1.2第三批] [1.3] [4.1]            -- stub batch 3, Tier 2 lemmas, CI consolidation
Week  9-10: [1.2第四批] [4.2] [4.3] [5.3]     -- remaining stubs, caching, nightly, cross-refs
Week 11-14:[1.2第五批] [5.1第一批]             -- final stubs, Tier 4 modules begin
Week 15-22:[5.1第二批]                          -- remaining Tier 4 modules
Week 23+:  [6.1] [6.2] [6.3] [6.4]            -- implementation phase
Ongoing:   [7.x]                                -- research directions
```

---

## Dependency Graph

```
[1.1 Preservation sorries]
  |
  +---> [2.1 Zero-warning gate] ---> [2.4 Pre-commit hardening]
  +---> [2.2 Sorry-free gate]
  |
[1.2 Eliminate stubs] ---> [1.3 Tier 2 proofs] ---> [5.1 Tier 4 modules]
  |                                                                   |
  +---> [6.1 Compiler frontend] ---> [6.2 Type checker] ---> [6.3 Runtime] ---> [6.4 Stdlib
  |                                                                   |
  +---> [7.1-7.4 Research]                                          |
                                                                      |
[3.4 Fix ghost CI] ---> [4.1 Consolidate workflows] ---> [4.3 Nightly]
                             |
[3.3 Python coverage]          +---> [4.2 Caching]
[3.1 SlimCheck]               |
[3.2 Snapshots]               +---> [5.2 Spec status] ---> [5.3 Cross-refs
[2.3 Stub detection]          |
                              +---> [5.1 Tier 4]
```

---

## Success Criteria

| Criterion | Current | Target | Priority |
|-----------|---------|--------|----------|
| `lake build Morph` errors | 0 | 0 | P0 |
| `lake build Morph` warnings | 1 | 0 | P0 |
| `sorry` in `Morph/` | 3 | 0 | P0 |
| Spec stubs (all tiers) | 15 | 0 | P0 |
| CI passes on every push | Partial | Yes | P1 |
| ruff lint errors | 0 | 0 | PASS |
| ruff format issues | 0 | 0 | PASS |
| mypy errors | 0 | 0 | PASS |
| Python test count | 405 | 500+ | P1 |
| Python coverage | 71% | 80%+ | P1 |
| Pre-commit blocks on sorry | Warns | Blocks | P0 |
| Regression snapshot tracking | None | Active | P1 |
| Tier 4 empty modules | 16 | 0 | P1 |
| Documentation emojis | 0 | 0 | PASS |
