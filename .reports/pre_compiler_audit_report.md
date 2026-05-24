# Morph Pre-Compiler Audit Report

Date: 2026-05-24
Scope: Full codebase (Lean specs, Lean proofs, Markdown specs, tests, CI/CD)
Purpose: Identify every problem before starting Rust/C++ compiler implementation

---

## 0. Executive Summary

| Metric | Value |
|--------|-------|
| Lean files | 157 |
| Lean LOC | 17,477 |
| Markdown spec files | 87 |
| Markdown LOC | 66,695 |
| Real theorems (proven) | 567 |
| Stub theorems (`True := trivial`) | 9 |
| Stub examples (`True := trivial`) | 8 |
| `sorry` count | 0 |
| `partial` definitions | 10 |
| `unsafe` definitions | 0 |
| `noncomputable` definitions | 0 |
| Custom axioms | 0 |
| Python tests | 803 (96.04% coverage) |
| Lean test jobs | 342 (0 errors) |
| Type soundness | PROVEN (progress + preservation) |

**Bottom line:** The formal core (type soundness for a minimal lambda calculus) is mechanically verified with zero sorries. However, the formalized language covers approximately 10% of what the Markdown specs describe. The remaining 90% -- capability types, effects, ADTs, generics, traits, actors, pattern matching, error handling -- has zero Lean formalization and zero machine-checked proofs.

---

## 1. PROVEN CORRECT (No Action Needed)

These items are mechanically verified and require no changes:

1. **Type soundness for the core expression language** -- `progress`, `preservation`, `type_safety`, `not_stuck`, `multi_step_preservation` all proven with zero sorries
2. **Simultaneous substitution lemma** -- `HasType_substAll` / `HasTypeAll_substAll` (generalized prefix-parameterized)
3. **Inversion lemmas** -- 18 inversion lemmas for all core expression forms
4. **Weakening lemmas** -- `weakening_at_depth`, `weakening_many_at_depth`, `weakening_all`, `weakening_insert`
5. **Operator classification disjointness** -- All operator categories proven disjoint (arith/comp/logic/bitwise)
6. **Evaluation completeness** -- All operator evaluators proven total for valid operators
7. **Property-based tests** -- 4 `#test` properties + 15 proven examples pass
8. **CI/CD pipeline** -- 6 pipelines passing (4 GitHub Actions, GitLab CI, Jenkins)
9. **Pre-commit hook** -- 7-step gate (lake build, sorry scan, stub scan, tests build, pytest, ruff/mypy, spec lint)
10. **Well-typed values classification** -- `WellTypedValue` inductive with 6 constructors, `value_is_well_typed` theorem

---

## 2. SPEC CONTRADICTIONS (Must Resolve)

### C-001: Duplicate Requirement ID LANG-REQ-071
**Location:** `spec/language/morph_language_spec.md`
**Problem:** LANG-REQ-071 is used for both "Input Normalization" (Sec 9.4) and "Error Type Enumeration" (Sec 15.1.2).
**Fix:** Renumber one of them.

### C-002: `async` Keyword Contradiction
**Location:** `spec/language/morph_language_spec.md` LANG-REQ-023 vs `spec/language/lexical_structure_syntax_spec.md` Sec 2.1
**Problem:** LANG-REQ-023 says "There are no `async`/`await` keywords." But `lexical_structure_syntax_spec.md` lists `async` as keyword #14 and uses `async let` syntax.
**Fix:** Clarify that `async` exists only as a modifier for `let` (dataflow), not as a standalone keyword.

### C-003: Effect Category Mismatch
**Location:** `spec/language/morph_language_spec.md` LANG-REQ-040 vs `spec/type/type_system_spec.md` Sec 2.6.1
**Problem:** Language spec defines effects as {Pure, IO, Net, Sys} (4 categories). Type system spec defines {Pure, IO, Net, Time, System} (5 categories). The language spec omits `Time`.
**Fix:** Reconcile to one canonical list.

### C-004: Affine vs Linear Semantics
**Location:** `spec/memory/memory_model_spec.md` Sec 2.4.1 vs `spec/type/type_system_spec.md` Sec 5.1.2
**Problem:** Memory spec defines affine types as "used at most once" (`uses(x) <= 1`). Type system spec proof sketch says "each resource is used exactly once" (linear, `uses(x) = 1`). These are different properties.
**Fix:** Choose one semantics (affine is more flexible) and update both documents to match.

### C-005: Keyword Count Off-by-One
**Location:** `spec/language/morph_language_spec.md` LANG-REQ-006
**Problem:** States "22 keywords" but if `async` is excluded per LANG-REQ-023, the count is 21.
**Fix:** Recount after resolving C-002.

### C-006: Version Drift in Examples
**Location:** `spec/conventions/version_compatibility_spec.md`
**Problem:** Examples reference type_system v2.0.0 (actual: 2.1.0), memory_model v2.0.0 (actual: 3.3.0), execution_model v2.0.0 (actual: 2.2.0).
**Fix:** Update examples to match actual versions.

---

## 3. FORMALIZATION GAPS (Lean vs Markdown)

### 3.1 Type System: What Lean Has vs What Specs Promise

The Lean `Typ` inductive defines 7 constructors:
```
intType | boolType | stringType | pointerType | unitType | arrayType(T, n) | functionType([T], T)
```

The Markdown specs promise the following types that have **ZERO** Lean formalization:

| Specified Feature | Spec Location | Lean Status |
|-------------------|--------------|-------------|
| Iso / Val / Ref / Weak capabilities | type_system_spec Sec 2.3 | MISSING |
| Option type (T?) | type_system_spec Sec 2.4 | MISSING |
| Effect types (Pure, IO, Net, Time, System) | type_system_spec Sec 2.6 | MISSING |
| Generic type parameters (T) | type_system_spec Sec 2.5 | MISSING |
| Algebraic Data Types (sum types) | type_system_spec Sec 2.2 | MISSING |
| Pattern matching (`fix`) | morph_language_spec Sec 3.5 | MISSING |
| Unit types (Meter, USD, etc.) | morph_language_spec Sec 3.4 | MISSING |
| Float types (f32, f64) | morph_language_spec Sec 3.1 | MISSING |
| Signed/unsigned integer widths (i8..i64, u8..u64) | morph_language_spec Sec 3.1 | MISSING |
| String/Bytes distinction | morph_language_spec Sec 3.1 | MISSING |
| Trait types | type_system_spec Sec 3.3 | MISSING |
| Result / Error types | morph_language_spec Sec 15 | MISSING |
| Never type (bottom) | implicit in effect system | MISSING |
| Type inference variables | type_unification_spec | MISSING |

### 3.2 Expression Language: What Lean Has vs What Specs Promise

The Lean `Expr` inductive defines 11 constructors:
```
bvar | fvar | lit | unop | binop | app | lam | let_ | ifThenElse | forLoop | block
```

Missing expression forms that the specs describe:

| Specified Feature | Spec Location | Lean Status |
|-------------------|--------------|-------------|
| Pattern match (`match e with patterns`) | HIR has it, Syntax does not | MISSING from Syntax.Expr |
| Struct/record literals | morph_language_spec Sec 3.2 | MISSING |
| Field access (`e.field`) | morph_language_spec Sec 3.2 | MISSING |
| Method call (`obj.method(args)`) | morph_language_spec Sec 3.3 | MISSING |
| Pipeline operator (`e \|> f`) | morph_language_spec Sec 2.4 | MISSING |
| Null coalescing (`e ?? default`) | operator_null_coalescing_spec | MISSING |
| Walrus operator (`x := e`) | morph_language_spec Sec 2.4 | MISSING |
| Await / async let | execution_model_spec | MISSING |
| Error propagation (`e?`) | morph_language_spec Sec 15 | MISSING |
| Actor spawn (`act { ... }`) | execution_model_spec | MISSING |
| Message send / receive | execution_model_spec | MISSING |
| Comptime blocks | morph_language_spec Sec 5.1 | MISSING |
| Type ascription (`e : T`) | type_system_spec | MISSING |

### 3.3 Operational Semantics: What Lean Has vs What Specs Promise

The Lean `Step` inductive has 23 constructors covering binary/unary ops, conditionals, let, for, blocks, and function application.

**Missing semantic rules:**

| Missing Rule | Severity |
|-------------|----------|
| Pointer arithmetic (ptrAdd, ptrSub) | HIGH -- operators exist but no Step rules |
| Pointer load/store (ptrLoad, ptrStore) | HIGH -- operators exist but no Step rules |
| Pattern matching reduction | HIGH -- not in surface Expr at all |
| Error propagation | HIGH -- no error values in the semantics |
| Division by zero as defined behavior | MEDIUM -- currently just no-step (stuck) |
| Overflow behavior for arithmetic | MEDIUM -- no overflow semantics |
| Actor creation and message passing | HIGH -- core concurrency missing |
| String operations | MEDIUM -- string type exists but no string ops |
| Array indexing | MEDIUM -- arrayType exists but no index operation |
| Type casting / coercion | MEDIUM |
| Reference capability transitions | HIGH -- Iso->Val etc. are the safety guarantee |
| Effect checking during reduction | HIGH -- effects claimed but not mechanized |

### 3.4 Specifications with NO Lean Formalization (43 Markdown files)

**Critical (core language features):**
- `type/effect_system_spec.md` (1194 lines) -- effect system, zero formalization
- `type/pure_type_spec.md` (848 lines) -- type purity, zero formalization
- `type/type_unification_spec.md` (529 lines) -- type inference, zero formalization
- `tooling/operational_semantics_spec.md` (711 lines) -- full semantics, zero formalization
- `tooling/metaprogramming_spec.md` (1444 lines) -- comptime, zero formalization

**High (memory/concurrency):**
- `memory/memory_petri_net_spec.md` (625 lines) -- Petri net model, zero formalization
- `distributed_vector_clock_spec.md` (817 lines) -- distributed causality, zero formalization

**Medium (29 tooling specs):**
agent_planning_mdp, analysis_abstract_interp, compiler_bisimulation, comptime_partial_eval, context_comonad, context_temporal_logic, deterministic_time, diagnose_protocol, distributed_crdt, fuzzing_combinatorial, graph_rewriting, history_persistent_tree, hot_reload_projection, learning_theory, meta_modal_logic, parsing_island_grammar, pattern_coverage_matrix, protocol_session_types, reactive_frp, realtime_mtl, registry_merkle, semantic_trie, semantic_vector, serialization_isomorphism, symbolic_execution_fuzz, synthesis_inhabitation

**Low (UI/optimization):**
semantic_accessibility, ui_constraint_algebra, ui_event_topology, optimization_bayesian, optimization_manifold, optimization_search_engine, selective_monomorphization, stdlib_amortized, unproven_assumptions

---

## 4. PROOF GAPS

### 4.1 Proofs That Exist (Complete)

| Proof | File | Status |
|-------|------|--------|
| Progress | `Progress.lean` (386 lines) | COMPLETE |
| Preservation | `Preservation.lean` (707 lines) | COMPLETE |
| Type Safety | `Soundness.lean` (141 lines) | COMPLETE |
| Not Stuck | `Soundness.lean` | COMPLETE |
| Multi-step Preservation | `Soundness.lean` | COMPLETE |
| Value Well-typedness | `Soundness.lean` | COMPLETE |
| Closed No Bvar | `Soundness.lean` | COMPLETE |
| Substitution lemma | `Preservation.lean` | COMPLETE |
| Weakening | `Lemmas.lean` | COMPLETE |

### 4.2 Proofs That DON'T Exist (Required for C++/Rust Replacement)

| Required Proof | Priority | Status |
|---------------|----------|--------|
| Memory safety (no use-after-free, no double-free) | CRITICAL | NOT STARTED |
| Capability type safety (Iso/Val/Ref transitions) | CRITICAL | NOT STARTED |
| Actor isolation (no data races) | CRITICAL | NOT STARTED |
| Effect system soundness | HIGH | NOT STARTED |
| Information flow non-interference | HIGH | NOT STARTED |
| Type inference completeness (principal types) | HIGH | NOT STARTED |
| Trait coherence | HIGH | NOT STARTED |
| Pattern match exhaustiveness | HIGH | NOT STARTED |
| Concurrency safety (work-stealing scheduler) | MEDIUM | NOT STARTED |
| Weak reference cycle breaking correctness | MEDIUM | NOT STARTED |
| Monomorphization termination | MEDIUM | NOT STARTED |
| ABI layout stability | MEDIUM | NOT STARTED |
| Hot reload type safety | LOW | NOT STARTED |

### 4.3 Stub Theorems (Proclaim properties without proof)

| File | Theorem | Problem |
|------|---------|---------|
| `Specs/ModuleSystem/Spec.lean` | `moduleIdUnique` | `True := trivial` |
| `Specs/ModuleSystem/Spec.lean` | `linkTableConsistent` | `True := trivial` |
| `Specs/ModuleSystem/Spec.lean` | `workspaceRootValid` | `True := trivial` |
| `Specs/ModuleSystem/Spec.lean` | `registrySearchCorrect` | `True := trivial` |
| `Specs/ModuleSystem/Spec.lean` | `registryTagSearchCorrect` | `True := trivial` |
| `Specs/ModuleSystem/Spec.lean` | `symbolManglingInjective` | `True := trivial` |
| `Specs/ModuleSystem/Spec.lean` | `functionManglingInjective` | `True := trivial` |
| `Specs/SecurityOCap/Spec.lean` | 2 theorems | `True := trivial` |

These claim properties (uniqueness, consistency, injectivity) but prove nothing.

---

## 5. CODE QUALITY ISSUES

### 5.1 `partial` Definitions (10 total)

All `partial` definitions are recursion without a proven termination measure:

| File | Definition | Risk |
|------|-----------|------|
| `TypeChecker.lean` | `unify` | Low -- structural recursion on types |
| `Frontend/Parser.lean` | `parseExpr` | Low -- recursive descent consuming tokens |
| `Frontend/Lexer.lean` | `advanceWhile` | Low -- character consumption |
| `Frontend/Lexer.lean` | `skipWhitespaceAndComments` | Low -- character consumption |
| `Frontend/Lexer.lean` | `scanString` | Low -- until closing quote |
| `Frontend/Lexer.lean` | `nextToken` | Low -- token iteration |
| `Frontend/Lexer.lean` | `tokenizeLoop` | Low -- input iteration |
| `Specs/Maths/Spec.lean` | `gcd` | Low -- standard Euclidean |
| `Specs/StrictStateUnidirectional/Spec.lean` | `reachable` | Medium -- graph reachability, may loop on cyclic graphs |
| `Specs/DependencySat/Spec.lean` | `addTransitiveDependencies` | Medium -- may not terminate on cyclic dependencies |
| `Specs/DependencySat/Spec.lean` | `hasCycle` | Medium -- cycle detection via DFS |

### 5.2 Functional Bugs (Lean Code)

| File | Bug | Severity |
|------|-----|----------|
| `Stdlib.lean:17` | `checkedAdd` always returns `some`, never checks overflow | HIGH |
| `Stdlib.lean:21` | `checkedSub` always returns `some`, never checks overflow | HIGH |
| `Runtime.lean` | `marshal` returns `ByteArray.empty` for int/bool/pointer | HIGH |
| `Runtime.lean` | `unmarshal` returns dummy values | HIGH |
| `Runtime.lean` | `stepActor` is a stub ("deferred to Phase 6.3") | MEDIUM |
| `Stdlib.lean` | `print` returns input string, does no I/O | MEDIUM (by design in Lean) |
| `Stdlib.lean` | `readLine` returns empty string | MEDIUM (by design in Lean) |
| `Stdlib.lean` | `asyncSpawn`, `asyncSend`, `asyncRecv` are stubs | MEDIUM |
| `Executable.lean` | Entire module is empty (TODO) | HIGH |

### 5.3 Empty/Stub Modules

| Module | Lines | Content |
|--------|-------|---------|
| `Morph/Executable.lean` | 15 | Empty stub with TODO |
| `Morph/Specs/UnidirectionalDataFlow/Spec.lean` | 16 | Empty stub with TODO |
| `Morph/Tests/Executable.lean` | 71 | 8 `True := trivial` stubs |

---

## 6. CRITICAL MISSING FEATURES (for C++/Rust Replacement)

### 6.1 Language Features Required for C++/Rust Parity

| Feature | C++ | Rust | Morph Spec | Morph Lean | Morph Compiler |
|---------|-----|------|-----------|-----------|---------------|
| Parametric generics | Templates | Generics | Specified | MISSING | MISSING |
| Traits / Concepts | Concepts | Traits | Specified | MISSING | MISSING |
| ADTs (sum types) | std::variant | enum | Specified | MISSING | MISSING |
| Pattern matching | switch/pattern | match | Specified | MISSING | MISSING |
| Ownership / borrowing | -- | Ownership | Specified | MISSING | MISSING |
| Lifetimes | -- | Lifetimes | Mentioned | MISSING | MISSING |
| Error handling | exceptions | Result<T,E> | Specified | MISSING | MISSING |
| Concurrency | threads/std::async | async/tokio | Specified | MISSING | MISSING |
| Trait/method dispatch | virtual/templates | dyn/impl | Specified | MISSING | MISSING |
| Float types | float/double | f32/f64 | Specified | MISSING | MISSING |
| Integer widths | intNN_t | iNN/uNN | Specified | MISSING | MISSING |
| Platform abstraction | Preprocessor | cfg(target) | Specified | MISSING | MISSING |
| Module system | Modules (C++20) | mod | Partial | Stub | MISSING |
| Standard library | STL | std | Specified | Stub | MISSING |
| Linkage / ABI | extern "C" | extern "C" | Specified | MISSING | MISSING |

### 6.2 Compiler Pipeline Gaps

The compiler pipeline is defined as:
```
Source -> Lexer -> Parser -> Surface AST -> HIR -> MIR -> LLVM IR
```

Current state:

| Stage | Lean Code | Rust/C++ Code | Tests |
|-------|-----------|---------------|--------|
| Lexer | `Frontend/Lexer.lean` (209 lines) | MISSING | MISSING |
| Parser | `Frontend/Parser.lean` (288 lines) | MISSING | MISSING |
| Surface-to-HIR lowering | MISSING | MISSING | MISSING |
| HIR type checking | `TypeChecker.lean` (120 lines) | MISSING | MISSING |
| HIR-to-MIR lowering | MISSING | MISSING | MISSING |
| MIR optimization | MISSING | MISSING | MISSING |
| MIR-to-LLVM codegen | MISSING | MISSING | MISSING |
| Runtime (libmorphrt) | `Runtime.lean` (211 lines, stubs) | MISSING | MISSING |

### 6.3 Spec-to-Implementation Traceability Gaps

No formal traceability exists between:
- Markdown requirement IDs (LANG-REQ-XXX, TYP-REQ-XXX, MMS-INV-XXX) and Lean definitions
- Lean definitions and future Rust/C++ implementation
- Test cases and specific requirements

The `TRACEABILITY_MATRIX.md` file mentioned in project conventions does not exist.

---

## 7. UNDERSPECIFIED AREAS

### 7.1 Critically Vague

| Area | Problem |
|------|---------|
| `??` (optimization hole) semantics | Is it a type? A value? How does it interact with inference? |
| `comptime` execution model | What operations are allowed? Can it do I/O? Memory model? |
| Actor mailbox ordering | FIFO? Arbitrary? Between senders? |
| `flow` vs `act` enforcement | How does the compiler verify UDF/SSUS constraints? |
| `min`/`hum` isomorphism | Claimed isomorphic but no formal proof |
| Inter-actor memory model | Sequential consistency? Relaxed? Acquire-release? |
| Undefined behavior catalog | What happens on integer overflow? Stack overflow? OOM? |
| Pointer provenance semantics | ProvenanceId exists in Lean but no semantic rules use it |
| Division by zero behavior | Currently stuck (no step) -- is this a panic? UB? |

### 7.2 Moderately Vague

| Area | Problem |
|------|---------|
| Supervision tree strategies | No restart/escalation policies specified |
| Hot reload consistency | In-flight messages, running fibers during reload |
| GC boundary | "No GC" claimed but cycle detection exists |
| `performs` effect syntax | Both `performs IO` and `performs [Pure]` used |
| Trait derivation rules | Auto-derive claimed but customization not specified |
| Weak reference lifecycle | When checked during deallocation? |

---

## 8. SPEC VOLUME VS SUBSTANCE

### 8.1 The Imbalance

| Category | Markdown Lines | Lean Lines | Formalized |
|----------|---------------|------------|------------|
| Type system | ~4,200 | ~1,800 | ~15% |
| Memory model | ~4,500 | ~374 | ~10% |
| Concurrency | ~2,500 | ~400 | ~5% |
| Security | ~3,400 | ~300 | ~5% |
| Tooling | ~15,000 | 0 | 0% |
| Build system | ~3,000 | ~600 | ~10% |
| UI | ~2,100 | 0 | 0% |
| Optimization | ~3,400 | ~200 | ~3% |
| Stdlib | ~1,300 | ~169 | ~5% |
| Financial | ~1,100 | ~120 | ~5% |
| **Total** | **~66,700** | **~3,963** | **~6%** |

### 8.2 Specs at Risk of Irrelevance

These 29 tooling specs (15,000+ lines) describe advanced concepts with zero implementation path:

- Bayesian optimization, MDPs, CRDTs, FRP, modal logic, temporal logic, comonads, abstract interpretation, symbolic execution, synthesis via inhabitation, persistent trees, semantic vectors, semantic tries, island grammars, graph rewriting, protocol session types, deterministic time, real-time MTL

These are aspirational research topics, not blocking requirements for a compiler. They should be deprioritized until the core language is formalized.

---

## 9. PRIORITIZED ACTION ITEMS

### Phase 1: Fix Before Compiler Work (1-2 weeks)

| ID | Item | Effort | Impact |
|----|------|--------|--------|
| A-001 | Resolve 6 spec contradictions (C-001 through C-006) | 2 days | Traceability |
| A-002 | Fix `checkedAdd`/`checkedSub` overflow checking in Stdlib | 1 hour | Correctness |
| A-003 | Add pointer operator Step rules to Semantics | 2 days | Completeness |
| A-004 | Add pattern match to Syntax.Expr and Step rules | 3 days | Core feature |
| A-005 | Prove or remove 9 stub theorems in ModuleSystem/SecurityOCap | 1 day | Integrity |
| A-006 | Implement `Morph.Executable` reference interpreter | 3 days | Testing foundation |
| A-007 | Add `FloatType`, integer width types to `Typ` | 1 day | C++ parity |

### Phase 2: Extend Formalization (2-4 months, parallel with compiler)

| ID | Item | Effort | Impact |
|----|------|--------|--------|
| B-001 | Formalize capability types (Iso/Val/Ref/Weak) in Lean | 3 weeks | Memory safety proof |
| B-002 | Formalize ADTs and pattern matching in Lean | 2 weeks | Core feature |
| B-003 | Formalize effect system in Lean | 3 weeks | Effect safety proof |
| B-004 | Formalize generics in Lean | 2 weeks | Core feature |
| B-005 | Prove memory safety (no UAF, no double-free) | 4 weeks | Safety guarantee |
| B-006 | Prove actor isolation (no data races) | 3 weeks | Concurrency guarantee |
| B-007 | Formalize error handling (Result type) | 1 week | Core feature |
| B-008 | Formalize trait system and coherence | 3 weeks | Core feature |

### Phase 3: Deprioritize (Post-Compiler)

| ID | Item | Reason |
|----|------|--------|
| C-001 | 29 tooling specs (Bayesian, MDP, CRDT, etc.) | Aspirational, not blocking |
| C-002 | 3 UI specs | Not core language |
| C-003 | Financial spec | Domain-specific |
| C-004 | Full denotational semantics | Not blocking for compiler |

---

## 10. RISK ASSESSMENT

### 10.1 Risks to 5-Year Publication Timeline

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Type system extension breaks soundness proof | High | Critical | Extend proof incrementally, one feature at a time |
| Capability types too complex to formalize | Medium | High | Start with subset, expand later |
| Effect system interferes with capability system | Medium | High | Design interaction upfront |
| Spec contradictions cause compiler rework | Medium | Medium | Resolve contradictions now (Phase 1) |
| 66K lines of specs become unmaintainable | High | Medium | Freeze non-core specs, focus on proven core |
| No reference interpreter to validate compiler against | High | High | Implement `Morph.Executable` first |
| Rust/C++ compiler diverges from Lean spec | High | Critical | Use Lean spec as test oracle for compiler |

### 10.2 Technical Debt

| Item | Location | Severity |
|------|----------|----------|
| 10 `partial` definitions without termination proofs | Multiple files | Medium |
| 8 stub tests in Executable | `Tests/Executable.lean` | High |
| 9 stub theorems | `Specs/ModuleSystem`, `Specs/SecurityOCap` | Medium |
| Runtime marshal/unmarshal are no-ops | `Runtime.lean` | High |
| Stdlib I/O is all stubs | `Stdlib.lean` | Medium (by design in Lean) |
| No lowering passes (Surface->HIR, HIR->MIR) | Missing entirely | Critical |
| No code generation pass (MIR->LLVM) | Missing entirely | Critical |

---

## 11. RECOMMENDATIONS

1. **Do not start the Rust/C++ compiler until Phase 1 is complete.** The spec contradictions, missing semantic rules, and absent reference interpreter will cause constant redesign.

2. **Implement `Morph.Executable` first.** A reference interpreter in Lean gives us a test oracle for the compiler. Without it, we cannot verify compiler correctness.

3. **Extend the Lean formalization incrementally alongside the compiler.** Do not try to formalize everything before coding. Instead, formalize one feature, implement it, test against the proof, then move to the next feature.

4. **Freeze the 29 tooling specs.** They are aspirational and consuming maintenance effort. Mark them as "future research" and focus on the core language.

5. **Establish traceability now.** Create a `TRACEABILITY_MATRIX.md` mapping requirement IDs (LANG-REQ-XXX) to Lean definitions and future Rust implementations. Without this, the spec and compiler will drift apart.

6. **Choose affine over linear.** The spec contradiction between affine and linear semantics (C-004) should be resolved in favor of affine (at most once), as it is more practical and aligns with the memory model spec.

7. **Define the undefined behavior catalog before writing the compiler.** Every operation must have a defined semantic outcome, even for programmer errors. This is the single biggest differentiator from C++.
