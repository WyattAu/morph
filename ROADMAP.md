# Morph Roadmap

> Companion to `PATH_FORWARD.md` (execution view) — this file is the
> status view. Live progress lands in `docs/RESEARCH-LOOPS-*.md`;
> generated proof counts in `.reports/spec-status.md` (CI-checked for drift).

Lean 4 v4.27.0 | Lake 5.0.0 | mathlib4 + batteries + aesop

---

## Baseline (Post-Audit, 2026-05-15)

| Metric | Value |
|---|---|
| `lake build Morph Morph.Tests` | green, 0 errors, 0 warnings (measured 2026-11-25) |
| Python spec-tools | 836 tests, 96% coverage (as of 2026-10-30) |
| `.lean` files | 309 in `Morph/` (311 with root files; measured 2026-11-25) |
| Lines of Lean | ~105,000 (measured 2026-11-25) |
| Spec modules | 68 (measured 2026-11-25) |
| Real theorems/lemmas | 2549 repo-wide / 1635 in `Specs/` (measured 2026-11-25) |
| `sorry` declarations | **0** (measured 2026-11-25) |
| `example : True := trivial` stubs | 0 |
| Pre-commit hook | 6-step gate: lake build, `scripts/check-gates.sh` (warnings, `sorry`, stubs, cross-refs, spec links), test build, pytest, ruff+mypy, spec-tools lint |
| CI/CD | 4 GitHub Actions + GitLab CI + Jenkins |
| Cross-reference integrity | repo gate `scripts/cross-ref-validate.sh` 2021/2021 PASS and `spec-tools check-links spec/` 0 broken — both blocking in CI and pre-commit via `scripts/check-gates.sh` (measured 2026-11-25); 12 malformed link-syntax sites and 31 wrong tooling paths repaired |
| Documentation site | Landing page + 5 doc pages (specs, architecture, tools, ADRs) |

### Audit Findings (Resolved)

| Finding | Resolution |
|---|---|
| `psutil` imported but not declared in pyproject.toml | Added to `dependencies` |
| Pre-commit hook used system `ruff`/`mypy` instead of `.venv/` | Fixed: prefer `.venv/bin/` |
| spec-validation CI failed on 1857 lint warnings | Changed to non-blocking with reporting |
| 735 broken cross-references in spec/ | Fixed systematic path resolution |
| spec-tools CLI called with multiple positional args | Fixed: iterate files individually |
| GitHub Pages not deployed | Blocked by GitHub billing; workflow correct |
| 6 `sorry` declarations (audit-era) | Was blocking zero-warning CI gate | §1.1 done 2026-10-30; still 0, verified 2026-11-25 |
| 12 malformed spec link-syntax sites (rendered as text, broken under every resolver) | Brackets repaired 2026-11-25 (GLOSSARY ×8, README, memory_model ×2, type_system) |
| `spec-tools check-links` disagreed with the repo gate (107 vs 0): results were cached by URL alone, so one directory's failure leaked into every other directory using the same name, and bare `.md` prose mentions counted as links | Fixed 2026-11-25: cache keyed by referring directory, resolution falls back to enclosing roots, prose mentions opt-in (`--check-file-refs`); 31 wrong `../tooling/…` paths repaired; both gates report 0 and are blocking in CI + pre-commit |
| Warnings and broken links were not gated locally | `scripts/check-gates.sh` (build warnings, `sorry`, stubs, cross-refs, spec links) is now blocking in `.githooks/pre-commit` and CI |

### Audit Findings (Outstanding)

| Finding | Impact | Resolution Path |
|---|---|---|
| CI/CD not running (GitHub billing) | No automated verification | Resolve billing |
| Section numbering warnings in specs (3868) | Lint noise | Normalize numbering or suppress |
| `impl/roadmap.md` describes Rust/C++ runtime not yet started | Future work | Section 6 |
| `.gitlab-ci.yml` and `Jenkinsfile` reference Python 3.11 only | Minor | No action needed (Python 3.8+ compatible) |

---

## 1. Formal Verification Completion [P0]

### 1.1 Fix 6 sorries in Preservation.lean — DONE (0 `sorry` verified 2026-10-30)

Unblocks §2.1/§2.3 (zero-warning gate, pre-commit hardening).

**Preservation.lean (6 sorries, all resolved — row statuses below are the pre-fix plan, retained for history):**

| Line | Location | Required Lemma | Status |
|---|---|---|---|
| 116 | `HasType_subst` bvar_type | `lift_preserves_type`: lifting by 0 preserves typing | Needs proof |
| 156 | `HasType_subst` lam_type | Substitution at depth > 0 (crossing lambda binders) | Needs generalized subst lemma |
| 171 | `HasType_subst` let_type | Substitution at depth 1 (crossing let binder) | Needs generalized subst lemma |
| 175 | `HasType_subst` for_type | Substitution at depth 1 (crossing for-loop binder) | Needs generalized subst lemma |
| 288 | `preservation` for_exec | Simultaneous substitution for loop body | Needs `substAll_preserves_type` |
| 359 | `preservation` app_lam | Simultaneous substitution for lambda args | Needs `substAll_preserves_type` |

**Lemmas.lean sorries resolved (all 4 fixed).**

**Approach:**
1. Prove `lift_preserves_type : HasType bvs Gamma v tau -> HasType bvs Gamma (lift k v) tau` (fixes sorry #1)
2. Generalize `HasType_subst` to handle arbitrary depth: `subst'_preserves_type : HasType (tau1 :: bvs) Gamma e tau -> HasType bvs Gamma v tau1 -> HasType bvs Gamma (subst' k e v) tau` (fixes sorries #2-4)
3. Prove `substAll_preserves_type` for simultaneous substitution (fixes sorries #5-6)

**Effort:** 1-2 weeks | **Deps:** none | **Blocks:** sorry-free CI gate

> **Loop 119 note:** §1.2–§1.5 below are spent. All `example : True :=
> trivial` stubs are eliminated repo-wide (0 remaining, CI-gated), and
> every one of the 68 spec modules in `SPEC_STATUS.md` ships real
> `theorem`/`lemma` declarations (1408 total, 0 sorries) — including
every
> module these tables list with nonzero stub counts. The per-module
> tables are retained as the historical work plan, not current state.
> Current proof inventory: `SPEC_STATUS.md` (regenerated loop 114).

### 1.2 Eliminate stubs -- Tier 1 (runtime foundation) — DONE

| Module | Current stubs | Target proofs | Effort | Notes |
|---|---|---|---|---|
| **MemoryModel** | 0 (6 real lemmas) | 3-5 additional | 2-3 days | Heap invariants, allocation bounds |
| **SecurityFlow** | 1 (Examples) | 5-8 lemmas | 1-2 weeks | Taint tracking, non-interference |
| **MorphLanguage** | 0 (real lemmas) | 5-8 additional | 1 week | Substitution properties |
| **ConcurrencyProcessAlgebra** | 1 (Examples) | 5-10 | 1-2 weeks | Deadlock-free proofs, channel safety |
| **TypeSystem** | 0 (real lemmas) | 3-5 additional | 3-5 days | Uniqueness of types |
| **ModuleSystem** | 2 (Lemmas+Examples) | 5-8 lemmas | 1 week | Hash determinism |
| **GLOSSARY** | 2 (Lemmas+Examples) | 3-5 examples | 2-3 days | Well-formed glossary instances |

**Total Tier 1:** 4-6 weeks | **Deps:** none (parallelizable)

### 1.3 Eliminate stubs -- Tier 2 (compiler/runtime support) — DONE

| Module | Stubs | Effort | Notes |
|---|---|---|---|
| **ScopingLambdaCalculus** | 0 | 1-2 weeks | Scope rules, alpha-equivalence |
| **DialectProjection** | 0 | 1-2 weeks | Multi-stage compilation |
| **MonadicEffect** | 0 | 1-2 weeks | Effect handler semantics |
| **OperatorNullCoalescing** | 0 | 3-5 days | Operator semantics |
| **LexicalStructureSyntax** | 0 | 3-5 days | Token/literal specs |
| **ExecutionModel** | 0 | 1 week | Step relation |
| **AbiAlignmentAlgebra** | 2 | 3-5 days | ABI struct layout |
| **BackendTiling** | 0 | 1 week | Tiling correctness |

**Total Tier 2:** 5-8 weeks | **Deps:** Tier 1 complete

### 1.4 Eliminate stubs -- Tier 3 (domain-specific) — DONE

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

### 1.5 Eliminate stubs -- Tier 4 (auxiliary) — DONE

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

> Loop 81 status: §2.1 done (89 warnings cleared, gate blocking), §2.2
> already blocking, §2.3 sorry-check already blocking (stub check flipped
> to blocking in loop 81). CI itself still blocked on billing (§2.4).

### 2.1 Zero-warning CI gate — DONE (loop 81)

Once 1.1 resolves, change `lean-build.yml` warning check from advisory to error:

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

Change `lean-build.yml` sorry check from warning to hard failure:

```yaml
if [ "$SORRY_COUNT" -gt 0 ]; then
  echo "::error::$SORRY_COUNT sorry declaration(s) found"
  exit 1
fi
```

**Effort:** 30 min | **Deps:** 1.1, 1.2

### 2.3 Pre-commit hook hardening

After 1.1 resolves, change sorry check from warning to blocking:

```bash
if [ "$SORRY_COUNT" -gt 0 ]; then
    echo "Commit blocked. Fix sorry declarations."
    exit 1
fi
```

**Effort:** 15 min | **Deps:** 1.1

### 2.4 Resolve GitHub billing

CI/CD workflows are correct but not executing due to GitHub account spending limit. Resolve billing to enable:
- Lean Build workflow
- Specification Validation workflow
- Nightly Full Build (Nix)
- GitHub Pages deployment

**Effort:** Account-level action | **Deps:** none

---

## 3. Specification Quality [P1]

### 3.1 Fix 26 remaining broken cross-references — DONE (0 broken; `cross-ref-validate.sh` 1704 pass / 0 fail, loop 112–113; re-verified loop 118)

| Category | Count | Action |
|---|---|---|
| Nonexistent top-level files (SPEC_CONTRADICTIONS.md, etc.) | 16 | Create stub files or remove links |
| Typo in filename (lexical_strcutre -> lexical_structure) | 2 | Fix link targets |
| docs/conventions/ path from spec/ | 3 | Fix relative paths |
| Line-reference format (`:2.6`) | 2 | Remove or fix format |
| Stray single-char link | 1 | Remove |

**Effort:** 2-3 hours | **Deps:** none

### 3.2 Normalize section numbering — DISPOSITIONED (loop 120, no bulk edit)

The "3868 warnings" figure is stale. Machine-measured breakdown of the
106 lint warnings (via the linter API): 74 `header-validation` (files
missing the File/Version/Status/Author/Last Modified block), 31
`change-log` (files missing a change log section), 1
`section-structure` (numbering decrease 2.7.2 → 2.2.8 in
`execution_model_spec.md` — a false positive on an intentional,
changelog-recorded series return, now waived; 105 warnings / 19
waived). The sections rule contributes zero real warnings, so options
1–3 are closed: no renumbering. The remaining 105 are
missing-boilerplate warnings, accepted baseline (zero-warning gate
covers Lean only).

### 3.3 Lean property-based testing (Plausible, not SlimCheck) — DELIVERED (loop 80)

No lakefile change was needed (`Plausible` arrives via the mathlib
closure); see `Morph/Tests/Property.lean`. The original per-target plan:

| Target | Properties | File |
|---|---|---|
| MemoryModel | `allocate` produces fresh `BlockId`; `readByte` after `writeByte` returns written value | `Morph/Tests/Memory.lean` |
| TypeSoundness | Random closed terms are either well-typed or rejected | `Morph/Tests/Typing.lean` |
| Semantics | Evaluation is deterministic for pure expressions | `Morph/Tests/Semantics.lean` |

**Effort:** 1-2 weeks | **Deps:** SlimCheck in lakefile.lean

### 3.4 Python spec-tools coverage improvement

Current: 96% coverage as of 2026-10-30 (target 95% met).

Priority areas:
- `spec_tools/validation/checks/` (70-73% each)
- `spec_tools/cli/commands/check_all.py` (43%)
- `spec_tools/utils/file_utils.py` (71%)

**Effort:** 3-5 days | **Deps:** none

---

## 4. CI/CD Consolidation [P1]

### 4.1 Current CI/CD state

| Workflow | Platform | Scope | Status |
|---|---|---|---|
| `lean-build.yml` | GitHub Actions | Lake build, sorry/stub scan, error check | Correct, blocked by billing |
| `spec-validation.yml` | GitHub Actions | spec-tools format/lint/validate/check-links | Correct, blocked by billing; format+validate advisory since loop 118 (were red-on-arrival), lint error-gate blocking |
| `nightly.yml` | GitHub Actions | Nix-based full build at 06:00 UTC | Correct, blocked by billing |
| `pages.yml` | GitHub Actions | Deploy site/ to GitHub Pages | Correct, blocked by billing |
| `.gitlab-ci.yml` | GitLab CI | pytest, bandit, safety | Correct for GitLab |
| `Jenkinsfile` | Jenkins | pytest, spec-tools format/lint/validate | Aligned loop 118 (was red-on-arrival: `--strict` + hard format/validate); lint error-gate blocking, rest advisory |

### 4.2 Regression test snapshots

Capture and diff build metrics per push:

```bash
#!/usr/bin/env bash
lake build Morph 2>&1 | tee build.log
echo "errors: $(grep -c 'error:' build.log || echo 0)"
echo "warnings: $(grep -c 'warning:' build.log || echo 0)"
echo "sorries: $(grep -r 'sorry' Morph/ --include='*.lean' | grep -v '/--' | wc -l)"
echo "stubs: $(grep -r 'example : True := trivial' Morph/Specs/ --include='*.lean' | wc -l)"
```

Store in `.reports/regression/`. Fail CI on metric regression.

**Effort:** 3-4 hours | **Deps:** 2.4 (CI running)

### 4.3 Lean toolchain caching optimization

Verified loop 120 in `lean-build.yml`: Lake cache key includes
`lake-manifest.json` and elan caching is present (keyed on
`lean-toolchain`). No change needed. Monitor cache hit rates after
billing resolved.

**Effort:** 1 hour (verification, spent) | **Deps:** 2.4

---

## 5. Documentation [P1]

### 5.1 Current documentation state

| Resource | Location | Status |
|---|---|---|
| Landing page | `site/index.html` | Complete, dark theme, responsive |
| Documentation hub | `site/docs/index.html` | Complete |
| Spec modules index | `site/docs/specs.html` | Complete (60+ modules) |
| Architecture docs | `site/docs/architecture.html` | Complete |
| Tools reference | `site/docs/tools.html` | Complete |
| ADR index | `site/docs/adr.html` | Complete (11 ADRs) |
| README | `README.md` | Complete |
| Roadmap | `ROADMAP.md` | This file |
| Path Forward | `PATH_FORWARD.md` | Complete |
| Spec status | `SPEC_STATUS.md` | Exists |
| Implementation plan | `impl/roadmap.md` | Complete (Rust/C++ runtime plan) |

### 5.2 API documentation generation

Use `lake exe doc-gen4` to generate HTML from Lean source:

```bash
lake exe doc-gen4 Morph --output docs/api/
```

Add as non-blocking CI step.

**Effort:** 1 day | **Deps:** doc-gen4 compatibility with Lean 4.27.0

> **Loop 121:** still open. `doc-gen4` is not in `.lake/packages/` —
> adding it is a new dependency (network fetch + `lakefile.lean` +
> `lake-manifest.json` change), needs maintainer approval. Not attempted.

### 5.3 Automated spec status tracking

Create script to generate `SPEC_STATUS.md` from Lean source:

```bash
for d in Morph/Specs/*/; do
  name=$(basename "$d")
  spec_lines=$(wc -l < "$d/Spec.lean" 2>/dev/null || echo "N/A")
  real_lemmas=$(grep -c 'theorem\|lemma ' "$d/Lemmas.lean" 2>/dev/null | head -1 || echo 0)
  sorries=$(grep -c 'sorry' "$d/Lemmas.lean" 2>/dev/null || echo 0)
  echo "$name | $spec_lines | $real_lemmas | $sorries"
done
```

**Effort:** 3-4 hours | **Deps:** none

---

## 6. Implementation Phase [P2]

### 6.1 Morph compiler frontend (Lean 4)

| Component | Description | Effort | File(s) |
|---|---|---|---|
| **Lexer** | Tokenize Morph source into `Morph.Syntax.Token` | 2-3 weeks | `Morph/Frontend/Lexer.lean` — **delivered (total, proven)** |
| **Parser** | Recursive descent producing `Morph.Syntax.AST` | 3-4 weeks | `Morph/Frontend/Parser.lean` — **delivered (fuel-monotone, full surface)** |
| **Name resolution** | Resolve identifiers, build symbol table | 2-3 weeks | `Morph/Frontend/NameResolution.lean` — **delivered as its own pass (loop 82: `resolveIdent` + `resolveExpr`, idempotence + fixed-point proofs; parser calls it)** |
| **HIR lowering** | AST to `Morph.HIR.Expr` | 1-2 weeks | `Morph/Frontend/HIRLower.lean` — **delivered for the HIR-representable fragment (loop 82: `toHIR`, supported↔`some`/rejected↔`none` contract; semantic preservation awaits HIR evaluation semantics)** |

**Total:** 8-12 weeks | **Deps:** 1.2 (Tier 1), 2.1

### 6.2 Type checker extraction

Extract type checking rules from proof layer into certified executable:

| Step | Description | Effort |
|---|---|---|
| Type synthesis | `synthType : Expr -> TypEnv -> Option Typ` | 2-3 weeks | **delivered with soundness proof** |
| Type checking | `checkType : Expr -> TypEnv -> Typ -> Bool` | 1-2 weeks | **delivered with soundness proof** |
| Unification | Pattern unification for type variables | 2-3 weeks | **delivered (`unify`/`unifyFuel`)** |
| Error reporting | Human-readable type error messages | 1 week | **delivered at the CLI (loop 82: `morph check` surfaces `formatTypeError`; `Driver.checkSource` + `Outcome.typeError`)** |

**Total:** 6-9 weeks | **Deps:** 1.2, 6.1

### 6.3 Runtime (Rust/C++)

Per `impl/roadmap.md`:

| Phase | Description | Timeline |
|---|---|---|
| Phase 0 | Infrastructure: Cargo workspace, ABI bridge, Docker CI | Weeks 1-4 |
| Phase 1 | Runtime core: Memory subsystem, M:N scheduler, I/O poller | Months 2-4 |
| Phase 2 | Compiler frontend: Parser (chumsky), semantic analysis, comptime | Months 5-7 |
| Phase 3 | Backend: LLVM lowering (inkwell), MCP server, optimization | Months 8-10 |
| Phase 4 | Extensions: UI backend (wgpu), stdlib bootstrap, training data | Months 11-12 |

**Total:** 12 months | **Deps:** 6.1, 6.2 for Lean-to-Rust extraction

> **Loop 121 measured state:** the Cargo workspace builds clean — `cargo
> fmt --check` 0, `clippy --all-targets -- -D warnings` 0 (2 lints fixed
> in `compiler/src/lexer/mod.rs`), `cargo test --workspace` 218 passed
> (30 + 133 + 55). Crates present: `compiler` (lexer/parser/ast/codegen/
> diagnostic/typeck), `runtime` (actor/memory/scheduler/sync/io/...),
> `cli`. Coverage of `impl/roadmap.md` phases is a maintainer/Era-2
> assessment, not a sprint task.

### 6.4 Standard library

| Component | Effort |
|---|---|
| Core types (Int, String, Bool, List, Option) | 2-3 weeks |
| Collections (Map, Set, Array) | 2-3 weeks |
| I/O primitives | 1-2 weeks |
| Concurrency primitives (spawn, send, recv) | 2-3 weeks |

**Total:** 7-11 weeks | **Deps:** 6.3

> **Loop 121 measured state:** seed exists — `Morph/Stdlib.lean` (187
> lines: `checkedAdd` with i64 bounds, core-type/collection/IO/concurrency
> sections per ADR-012) — but it is unwired: nothing imports it
> (`Morph.lean`/`Main.lean` don't reference it). Era-2 track (G-5); not a
> current-core defect. Wiring it in is a maintainer call, not taken here.

---

## 7. Research Directions [P3]

### 7.1 Dependent types for runtime

Extract dependent type information from Lean 4 proofs for runtime use (array bounds, nullable tracking). Requires Lean 4 code extraction pipeline.

**Milestone:** Proof of concept in 3 months

### 7.2 Linear types for resource management

Extend type system with affine/linear qualifiers. Formalize in `Morph/Specs/MemoryAffineLogic/`.

**Milestone:** Spec.lean definitions in 2 months

### 7.3 Capability-based security enforcement

Extend `Morph/Specs/SecurityOCap/` with formal capability model. Prove noninterference.

**Milestone:** Noninterference theorem in 3 months

### 7.4 Multi-stage compilation (dialect system)

Extend `Morph/Specs/DialectProjection/` with verified multi-stage pipeline. Prove dialect lowering preserves semantics.

**Milestone:** Dialect soundness theorem in 4 months

### 7.5 Verified compiler extraction

Investigate extracting a verified compiler from Lean 4 proofs directly, bypassing the Rust/C++ runtime for the core calculus. Lean 4's own compiler can serve as a bootstrap target.

**Milestone:** Feasibility study in 2 months

---

## Execution Timeline

```
Week  1-2:  [1.1] [3.1] [2.4]                 -- sorries, fix 26 broken links, resolve billing
Week  3-4:  [1.1 cont] [2.1] [2.2] [2.3]      -- finish sorries, harden CI gates
Week  5-6:  [1.2 MemoryModel+SecurityFlow] [3.3] -- Tier 1 start, SlimCheck
Week  7-8:  [1.2 MorphLanguage+Concurrency] [3.4] -- Tier 1 continue, Python coverage
Week  9-10: [1.2 TypeSystem+ModuleSystem+GLOSSARY] -- Tier 1 complete
Week 11-12: [4.2] [5.2] [5.3] [3.2]          -- regression, API docs, spec status, numbering
Week 13-18: [1.3]                              -- Tier 2 compiler/runtime support
Week 19-26: [1.4] [1.5]                        -- Tier 3 + Tier 4
Week 27-38: [6.1] [6.2]                        -- compiler frontend + type checker
Week 39-50: [6.3]                              -- runtime (Rust/C++)
Week 51-58: [6.4]                              -- standard library
Ongoing:   [7.x]                               -- research directions
```

---

## Success Criteria

| Criterion | Target | Current |
|---|---|---|
| `lake build Morph` errors | 0 | 0 |
| `lake build Morph` warnings | 0 | 0 |
| `sorry` in `Morph/` | 0 | 0 (was 6 at audit; resolved by 2026-10-30) |
| `example : True := trivial` stubs | 0 | 0 (all §1.2–§1.5 tiers; CI-gated) |
| Broken cross-references | 0 | 0 (§3.1 done loop 118 audit; `cross-ref-validate.sh` 1704/0) |
| CI passes on every push | Yes | Blocked by billing |
| Python spec-tools coverage | >= 95% | 96% |
| Lean tests pass | All | All |
| Pre-commit blocks on sorry | Yes | Blocks (`.githooks/pre-commit` step 2 exits 1) |
| Regression snapshot tracking | Active | Active (Era-1 baseline 2026-10-30) |
| Spec status page | Auto-generated | Auto-generated (SPEC_STATUS.md + CI-tracked .reports/spec-status.md) |
| Documentation site | Complete | Complete (landing + 5 pages) |

---

## Dependencies Graph

```
[1.1 Preservation sorries]
  |
  +---> [2.1 Zero-warning gate] ---> [2.3 Pre-commit hardening]
  +---> [2.2 Sorry-free gate]
  |
[1.2 Tier 1 proofs] ---> [1.3 Tier 2] ---> [1.4 Tier 3] ---> [1.5 Tier 4]
  |                                                                   |
  +---> [6.1 Compiler frontend] ---> [6.2 Type checker] ---> [6.3 Runtime] ---> [6.4 Stdlib
  |                                                                   |
  +---> [7.1-7.5 Research]                                          |
                                                                      |
[3.1 Fix 26 broken links]                                           |
[3.2 Normalize numbering]                                           |
[3.3 SlimCheck]          +---> [4.2 Regression snapshots]           |
[3.4 Python coverage]     +---> [5.3 Spec status tracking]          |
[2.4 Resolve billing]     +---> [5.2 API docs]                      |
                          +---> [4.3 Cache optimization]
```
