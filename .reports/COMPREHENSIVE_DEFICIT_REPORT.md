# Morph Language: Comprehensive Deficit Report

**Date:** 2026-05-29  
**Scope:** Full monorepo — specs, proofs, compiler prototype, runtime, CLI, tooling, CI/CD  
**Purpose:** Enumerate every known problem, gap, contradiction, and missing artifact to inform the 5-year publication roadmap

---

## 0. Executive Dashboard

| Category | Total Items | Complete | In Progress / Stub | Missing / Not Started |
|----------|------------|----------|--------------------|-----------------------|
| Markdown spec files | 87 | ~75 | ~8 stubs | ~4 missing coverage |
| Lean spec modules | 44 | 44 compile | 9 stub theorems | 0 empty (all built) |
| Lean type system types (formal) | 15+ spec'd | 7 | 0 | **8+ missing** |
| Lean expression forms (formal) | 24+ spec'd | 11 | 0 | **13+ missing** |
| Critical proofs required | 13 | 3 (progress/preservation/soundness) | 0 | **10 not started** |
| Compiler pipeline stages | 8 | 2 (lexer, parser) | 2 partial (typeck, codegen) | **4 missing** |
| Compiler requirements (compliance matrix) | 297 | 0 | 0 | **297 TODO** |
| Runtime components | 12 modules | 12 implemented | 0 stubs | **0 VM / interpreter** |
| Integration tests (Rust) | 30 | 30 | 0 | Coverage limited |
| Spec contradictions | 6 known | 0 fixed | 0 | **6 unresolved** |
| Unproven assumptions | 5 | 3 validated | 1 under review | **1 assumed, no proof** |
| Spec cross-ref broken links | 367 | 0 fixed | 0 | **367 broken anchors** |

**Bottom line:** The project has a mechanically verified type safety proof for a minimal lambda calculus (the best-in-class artifact) and a functional Rust compiler prototype that can lex, parse, type-check, and emit bytecode. However, **94% of the specification has no formal Lean verification**, **100% of the 297 compiler compliance requirements are unimplemented**, **no bytecode interpreter exists** to execute the compiler's output, and the Rust prototype and Lean spec **diverge significantly** in type system expressiveness.

---

## Part I: Specification Problems

### I.1 Spec Contradictions (6 items, ALL UNRESOLVED)

| ID | Contradiction | Files Affected | Severity |
|----|--------------|----------------|----------|
| C-001 | Duplicate requirement ID `LANG-REQ-071` used for both "Input Normalization" and "Error Type Enumeration" | `morph_language_spec.md` | Medium |
| C-002 | `async` keyword: `morph_language_spec` says "no async/await keywords" (LANG-REQ-023), but `lexical_structure_syntax_spec` lists `async` as keyword #14 and uses `async let` syntax | `morph_language_spec.md`, `lexical_structure_syntax_spec.md` | High |
| C-003 | Effect categories: language spec defines 4 (Pure, IO, Net, Sys); type system spec defines 5 (adds Time) | `morph_language_spec.md`, `type_system_spec.md` | High |
| C-004 | Affine vs Linear: memory spec says "at most once" (affine, `uses(x) <= 1`); type system spec says "exactly once" (linear, `uses(x) = 1`) | `memory_model_spec.md`, `type_system_spec.md` | Critical |
| C-005 | Keyword count: spec claims 22 keywords, but if `async` is excluded per LANG-REQ-023, count is 21 | `morph_language_spec.md` | Low |
| C-006 | Version drift in examples: type_system referenced as v2.0.0 (actual 2.1.0), memory_model as v2.0.0 (actual 3.3.0), execution_model as v2.0.0 (actual 2.2.0) | `version_compatibility_spec.md` | Low |

### I.2 Spec Gaps (5 items)

| ID | Area | Gap Description | Priority |
|----|------|----------------|----------|
| SG-001 | Syntax Translation | No formal semantics for cross-dialect translation (min ↔ hum isomorphism unproven) | Medium |
| SG-002 | Memory Model | No formal bounds on heap allocation growth | High |
| SG-003 | Security Flow | No taint tracking specification across dialect boundaries | High |
| SG-004 | Concurrency | No deadlock-freedom proof for the actor system | Medium |
| SG-005 | Type System | No decidability proof for subtyping relations | High |

### I.3 Unproven Assumptions (2 items unresolved)

| ID | Assumption | Status |
|----|-----------|--------|
| GA-003 | Projectional editing can express all syntactic forms | Under Review — no proof or disproof |
| GA-005 | Type system is decidable for all Morph programs | Assumed — no proof exists; **this is foundational** |

### I.4 Stub / Minimal Specifications (8 files)

These specs are too thin to serve as implementation references:

| File | Lines | Problem |
|------|-------|---------|
| `spec/concurrency/monadic_effect_spec.md` | 55 | Only monad structure definition; no requirements, invariants, examples, design rationale |
| `spec/type/type_category_spec.md` | 56 | Extremely brief; no requirements, examples, or theorems |
| `spec/tooling/diagnose_protocol_spec.md` | 99 | JSON schema only; no formal definitions, theorems, or examples |
| `spec/ui/semantic_accessibility_spec.md` | 119 | No proper header (missing version, status, change log); no theorems |
| `spec/licensing/licensing_spec.md` | 73 | Very short; no formal proofs or theorems |
| `spec/security/infrastructure_safety_contracts_spec.md` | 168 | Short; covers Hoare logic but no concrete enforcement specification |
| `spec/optimization/optimization_search_engine_specification.md` | 183 | Describes `??` holes but less formal than other specs |
| `spec/math/maths_spec.md` | 215 | Mostly syntax; delegates all formalism to `unit_group_theory_spec.md` |

### I.5 Organizational Inconsistencies

1. **File location mismatch:** `spec/README.md` references organizational subdirectories (`distributed/`, `scheduler/`, `storage/`, `module/`) that don't exist as physical directories — 5 spec files sit at `spec/` root instead of their documented locations
2. **Review status:** Every single spec file lists reviewers as "Pending" — **zero specs have been formally reviewed**
3. **367 broken internal section anchors** across all markdown specs (link checker finds them all)
4. **Legacy typo:** Historical reference to `lexical_strcutre_syntax_spec.md` (fixed filename, but may persist in references)
5. **Duplicate ADR numbering** in `.specs/02_adrs/`

---

## Part II: Proof Deficits

### II.1 What IS Proven (Complete, Verified)

| Proof | Lean File | Lines | Status |
|-------|-----------|-------|--------|
| Progress (well-typed closed terms are values or step) | `Proofs/TypeSoundness/Progress.lean` | 468 | COMPLETE, 0 sorry |
| Preservation (stepping preserves types) | `Proofs/TypeSoundness/Preservation.lean` | 781 | COMPLETE, 0 sorry |
| Type Safety (progress + preservation) | `Proofs/TypeSoundness/Soundness.lean` | 142 | COMPLETE, 0 sorry |
| Not Stuck | `Soundness.lean` | — | COMPLETE |
| Multi-step Preservation | `Soundness.lean` | — | COMPLETE |
| Value Well-typedness | `Soundness.lean` | — | COMPLETE |
| Closed No Bvar | `Soundness.lean` | — | COMPLETE |
| 36 type system lemmas (inversion, weakening, lift, substitution) | `Specs/TypeSystem/Lemmas.lean` | 596 | COMPLETE |
| ~200+ spec module lemmas across 30+ specs | Various `Specs/*/Lemmas.lean` | — | ALL COMPLETE |
| 400+ test examples/properties | `Tests/*.lean` | — | ALL COMPLETE |

**Total verified theorems: ~787 (567 in Specs/ + core proofs + tests). Zero `sorry`.**

### II.2 What IS NOT Proven (10 Critical/High Required Proofs)

| Required Proof | Why Needed | Priority | Status |
|---------------|-----------|----------|--------|
| **Memory safety** (no use-after-free, no double-free) | Core safety guarantee; replaces Rust's borrow checker | CRITICAL | NOT STARTED |
| **Capability type safety** (Iso/Val/Ref transition correctness) | Core type system feature; safety guarantee | CRITICAL | NOT STARTED |
| **Actor isolation** (no data races across actor boundaries) | Core concurrency guarantee | CRITICAL | NOT STARTED |
| **Effect system soundness** | Effect annotations must correspond to actual effects | HIGH | NOT STARTED |
| **Information flow non-interference** | Security guarantee for taint tracking | HIGH | NOT STARTED |
| **Type inference completeness** (principal types exist) | Type inference must terminate with correct result | HIGH | NOT STARTED |
| **Trait coherence** (no overlapping impls) | Type system integrity | HIGH | NOT STARTED |
| **Pattern match exhaustiveness** | No runtime match failures | HIGH | NOT STARTED |
| **Concurrency safety** (work-stealing scheduler correctness) | Runtime correctness | MEDIUM | NOT STARTED |
| **Weak reference cycle breaking** | Memory management correctness | MEDIUM | NOT STARTED |
| **Monomorphization termination** | Compilation must terminate | MEDIUM | NOT STARTED |
| **ABI layout stability** | Cross-module compatibility | MEDIUM | NOT STARTED |
| **Hot reload type safety** | Dynamic code replacement safety | LOW | NOT STARTED |

### II.3 Stub Theorems (Claim Properties Without Proof)

9 theorems use `True := trivial`, proving nothing:

| File | Theorem | Claimed Property |
|------|---------|-----------------|
| `Specs/ModuleSystem/Spec.lean` | `moduleIdUnique` | Module ID uniqueness |
| `Specs/ModuleSystem/Spec.lean` | `linkTableConsistent` | Link table consistency |
| `Specs/ModuleSystem/Spec.lean` | `workspaceRootValid` | Workspace root validity |
| `Specs/ModuleSystem/Spec.lean` | `registrySearchCorrect` | Registry search correctness |
| `Specs/ModuleSystem/Spec.lean` | `registryTagSearchCorrect` | Tag search correctness |
| `Specs/ModuleSystem/Spec.lean` | `symbolManglingInjective` | Symbol mangling injectivity |
| `Specs/ModuleSystem/Spec.lean` | `functionManglingInjective` | Function mangling injectivity |
| `Specs/SecurityOCap/Spec.lean` | 2 theorems | OCap safety properties |

### II.4 Formalization Coverage (Lean vs Markdown)

| Category | Markdown Lines | Lean Lines | % Formalized |
|----------|---------------|------------|-------------|
| Type system | ~4,200 | ~1,800 | **~15%** |
| Memory model | ~4,500 | ~374 | **~10%** |
| Concurrency | ~2,500 | ~400 | **~5%** |
| Security | ~3,400 | ~300 | **~5%** |
| Tooling (29 specs) | ~15,000 | 0 | **0%** |
| Build system | ~3,000 | ~600 | **~10%** |
| UI (3 specs) | ~2,100 | 0 | **0%** |
| Optimization | ~3,400 | ~200 | **~3%** |
| Stdlib | ~1,300 | ~169 | **~5%** |
| **Total** | **~66,700** | **~3,963** | **~6%** |

### II.5 Lean Type System vs Spec Promises

The Lean `Typ` inductive has **7 constructors**:
```
intType | boolType | stringType | pointerType | unitType | arrayType(T, n) | functionType([T], T)
```

The specs promise **15+ type features** with ZERO Lean formalization:

| Missing Type Feature | Spec Location |
|---------------------|---------------|
| Iso / Val / Ref / Weak capabilities | `type_system_spec` §2.3 |
| Option type (T?) | `type_system_spec` §2.4 |
| Effect types (Pure, IO, Net, Time, System) | `type_system_spec` §2.6 |
| Generic type parameters (T) | `type_system_spec` §2.5 |
| Algebraic Data Types (sum types) | `type_system_spec` §2.2 |
| Pattern matching | `morph_language_spec` §3.5 |
| Unit types (Meter, USD, etc.) | `morph_language_spec` §3.4 |
| Float types (f32, f64) | `morph_language_spec` §3.1 |
| Signed/unsigned integer widths (i8..i64, u8..u64) | `morph_language_spec` §3.1 |
| String/Bytes distinction | `morph_language_spec` §3.1 |
| Trait types | `type_system_spec` §3.3 |
| Result / Error types | `morph_language_spec` §15 |
| Never type (bottom) | Implicit in effect system |
| Type inference variables | `type_unification_spec` |
| Lifetime annotations | Mentioned but underspecified |

### II.6 Lean Expression Language vs Spec Promises

The Lean `Expr` inductive has **11 constructors**:
```
bvar | fvar | lit | unop | binop | app | lam | let_ | ifThenElse | forLoop | block
```

**13+ expression forms** specified but missing from Lean:

| Missing Expression | Spec Location |
|-------------------|---------------|
| Pattern match (`match e with patterns`) | HIR has it, Syntax.Expr does not |
| Struct/record literals | `morph_language_spec` §3.2 |
| Field access (`e.field`) | `morph_language_spec` §3.2 |
| Method call (`obj.method(args)`) | `morph_language_spec` §3.3 |
| Pipeline operator (`e |> f`) | `morph_language_spec` §2.4 |
| Null coalescing (`e ?? default`) | `operator_null_coalescing_spec` |
| Walrus operator (`x := e`) | `morph_language_spec` §2.4 |
| Await / async let | `execution_model_spec` |
| Error propagation (`e?`) | `morph_language_spec` §15 |
| Actor spawn (`act { ... }`) | `execution_model_spec` |
| Message send / receive | `execution_model_spec` |
| Comptime blocks | `morph_language_spec` §5.1 |
| Type ascription (`e : T`) | `type_system_spec` |

### II.7 Missing Operational Semantics Rules

| Missing Rule | Severity | Impact |
|-------------|----------|--------|
| Pointer arithmetic (ptrAdd, ptrSub) | HIGH | Operators exist in Lean but no Step rules |
| Pointer load/store (ptrLoad, ptrStore) | HIGH | Operators exist but no Step rules |
| Pattern matching reduction | HIGH | Not in surface Expr at all |
| Error propagation reduction | HIGH | No error values in semantics |
| Actor creation and message passing | HIGH | Core concurrency missing |
| Reference capability transitions | HIGH | Iso→Val etc. are the safety guarantee |
| Effect checking during reduction | HIGH | Effects claimed but not mechanized |
| Division by zero behavior | MEDIUM | Currently stuck (no step) — panic? UB? |
| Overflow behavior for arithmetic | MEDIUM | No overflow semantics |
| String operations | MEDIUM | String type exists but no string ops |
| Array indexing | MEDIUM | arrayType exists but no index operation |
| Type casting / coercion | MEDIUM | No coercion semantics |

### II.8 `partial` Definitions Without Termination Proofs (10 items)

| File | Definition | Risk Level |
|------|-----------|------------|
| `TypeChecker.lean` | `unify` | Low — structural recursion |
| `Frontend/Parser.lean` | `parseExpr` | Low — recursive descent |
| `Frontend/Lexer.lean` | `advanceWhile` | Low — character consumption |
| `Frontend/Lexer.lean` | `skipWhitespaceAndComments` | Low — character consumption |
| `Frontend/Lexer.lean` | `scanString` | Low — until closing quote |
| `Frontend/Lexer.lean` | `nextToken` | Low — token iteration |
| `Frontend/Lexer.lean` | `tokenizeLoop` | Low — input iteration |
| `Specs/Maths/Spec.lean` | `gcd` | Low — standard Euclidean |
| `Specs/StrictStateUnidirectional/Spec.lean` | `reachable` | Medium — may loop on cyclic graphs |
| `Specs/DependencySat/Spec.lean` | `addTransitiveDependencies` | Medium — may not terminate on cyclic deps |
| `Specs/DependencySat/Spec.lean` | `hasCycle` | Medium — cycle detection via DFS |

### II.9 Functional Bugs in Lean Code

| File | Bug | Severity |
|------|-----|----------|
| `Stdlib.lean:17` | `checkedAdd` always returns `some`, never checks overflow | HIGH |
| `Stdlib.lean:21` | `checkedSub` always returns `some`, never checks overflow | HIGH |
| `Runtime.lean` | `marshal` returns `ByteArray.empty` for int/bool/pointer | HIGH |
| `Runtime.lean` | `unmarshal` returns dummy values | HIGH |
| `Runtime.lean` | `stepActor` is a stub ("deferred to Phase 6.3") | MEDIUM |
| `Stdlib.lean` | `print` returns input string, does no I/O | MEDIUM (by design) |
| `Stdlib.lean` | `readLine` returns empty string | MEDIUM (by design) |
| `Stdlib.lean` | `asyncSpawn`, `asyncSend`, `asyncRecv` are stubs | MEDIUM |
| `Executable.lean` | Entire module is empty (TODO) | HIGH |
| `Tests/Executable.lean` | 8 `True := trivial` stub tests | MEDIUM |

---

## Part III: Compiler Prototype Deficits (Rust)

### III.1 Compiler Pipeline Status

| Stage | Rust Implementation | Tests | Status |
|-------|-------------------|-------|--------|
| Lexer | `compiler/src/lexer/` (1,364 lines) | 27 | **FULLY IMPLEMENTED** |
| Parser | `compiler/src/parser/` (2,062 lines) | 40 | **FULLY IMPLEMENTED** |
| AST definitions | `compiler/src/ast/` (755 lines) | 4 | **FULLY IMPLEMENTED** |
| Type checker | `compiler/src/typeck/` (2,159 lines) | 47 | **PARTIALLY IMPLEMENTED** |
| Code generator | `compiler/src/codegen/` (1,816 lines) | 12 | **PARTIALLY IMPLEMENTED** |
| Diagnostics | `compiler/src/diagnostic/` (176 lines) | 3 | **FULLY IMPLEMENTED** |
| **HIR → MIR lowering** | — | — | **MISSING** |
| **MIR optimization** | — | — | **MISSING** |
| **MIR → LLVM codegen** | — | — | **MISSING** |
| **Bytecode interpreter / VM** | — | — | **MISSING** |

### III.2 Type Checker Gaps

| Issue | Location | Severity |
|-------|----------|----------|
| `check_type_decl()` has empty body | `checker.rs:268` | HIGH |
| `check_trait_decl()` has empty body | `checker.rs:337` | HIGH |
| Constructor pattern checking discards field patterns | `checker.rs:858-865` | HIGH |
| `check_expr()` bidirectional helper exists but is `#[allow(dead_code)]` | `checker.rs:416-432` | MEDIUM |
| Type alias bodies stored as `()` instead of resolved types | `checker.rs:45` | HIGH |
| Pattern exhaustiveness: only checks `arm_count > 0` | checker | HIGH |
| Trait resolution: traits parsed but no method resolution | checker | HIGH |
| Generic monomorphization: generics parsed but not resolved | checker + codegen | HIGH |

### III.3 Code Generator Gaps

| Issue | Location | Severity |
|-------|----------|----------|
| `break`/`continue` compile to no-ops | codegen | HIGH |
| `defer` compiles expression but no defer semantics | codegen | HIGH |
| `LoadUpvalue`/`StoreUpvalue` defined but never emitted | `morph_ir.rs` | HIGH |
| Index expression compilation falls through without emitting | `compiler.rs:570-574` | HIGH |
| No `for` loop / iterator support in AST or parser | parser + codegen | MEDIUM |
| No string interpolation | lexer + parser | MEDIUM |

### III.4 Completely Missing Compiler Features

| Feature | C++ Has | Rust Has | Spec Says | Compiler Has |
|---------|---------|----------|-----------|-------------|
| Parametric generics | Templates | Generics | Specified | **MISSING** |
| Traits / Concepts | Concepts | Traits | Specified | **MISSING** |
| ADTs (sum types) | std::variant | enum | Specified | **MISSING** |
| Pattern matching | switch/pattern | match | Specified | **MISSING** |
| Ownership / borrowing | — | Ownership | Specified | **MISSING** |
| Lifetimes | — | Lifetimes | Mentioned | **MISSING** |
| Error handling | exceptions | Result<T,E> | Specified | **MISSING** |
| Concurrency | threads | async/tokio | Specified | **MISSING** |
| Trait/method dispatch | virtual | dyn/impl | Specified | **MISSING** |
| Float types | float/double | f32/f64 | Specified | **MISSING** |
| Integer widths | intNN_t | iNN/uNN | Specified | **MISSING** |
| Module system | Modules (C++20) | mod | Partial | **MISSING** |
| Standard library | STL | std | Specified | **MISSING** |
| Linkage / ABI | extern "C" | extern "C" | Specified | **MISSING** |

### III.5 Spec-to-Compiler Divergence

The Rust compiler prototype and the Lean spec define **fundamentally different type systems**:

| Aspect | Lean Spec (Typ) | Rust Compiler (Ty) |
|--------|-----------------|-------------------|
| Integer types | 1 (`intType`) | 10 (`I8`..`I64`, `U8`..`U64`, `ISize`, `USize`) |
| Float types | 0 | 2 (`F32`, `F64`) |
| Capabilities | 0 | 3 (`Iso`, `Val`, `Ref`) |
| Effects | 0 | 5 (`IO`, `Net`, `Time`, `System`, + `Pure`) |
| Generics | 0 | 0 (both missing) |
| ADTs | 0 | 0 (both missing) |
| Pattern match | Not in Syntax.Expr | In HIR only |
| Null coalescing | 0 | Present in AST |
| Walrus operator | 0 | Present in AST |
| Pipeline operator | 0 | Present in AST |
| Error propagation | 0 | Present in AST |
| Spawn / async | 0 | Present in AST |

The Rust compiler is **ahead** of the Lean spec in some areas (integer widths, capabilities, effects, null coalescing, pipeline, walrus) but **behind** the spec in formal verification. This divergence will cause correctness problems if not reconciled.

---

## Part IV: Runtime Deficits

### IV.1 What Exists

The `morph-runtime` crate provides 12 modules (55 tests) of real infrastructure:
- `MorphValue` (16 variants), `Fiber` with suspend/resume, `WorkStealingScheduler`, `DeterministicScheduler`, `ArenaAllocator`, `GlobalAllocator`, `Actor` with mailbox/supervision, `WaitGroup`/`Once`/`RwLock`, IO `Reactor` (epoll/iocp), `MorphArc`/`MorphWeak`, `ChaseLevDeque`, `MpscQueue`

### IV.2 Critical Missing Pieces

| Missing Component | Impact | Severity |
|------------------|--------|----------|
| **Bytecode interpreter / VM** — nothing consumes `MorphIRModule` output | No execution possible | CRITICAL |
| **Module-to-runtime bridge** — compiler output cannot be loaded into runtime | No end-to-end compilation | CRITICAL |
| **Chase-Lev deque uses Mutex** — not truly lock-free | Performance ceiling | MEDIUM |
| **No FFI bridge** — `Runtime.lean` defines FFI but Rust has no FFI layer | No C interop | HIGH |
| **No garbage collection interface** — specs say "no GC" but no ARC implementation in Rust | Memory management incomplete | HIGH |

---

## Part V: CLI / Tooling Deficits

### V.1 CLI Gaps

| Command | Status | Problem |
|---------|--------|---------|
| `morph build` | Works | Compiles to MorphIR bytecode |
| `morph check` | Works | Type-checks without codegen |
| `morph run` | **STUB** | Prints "interpreter not yet integrated" |
| `morph fmt` | **STUB** | Naive `println!` of items, no formatting |
| `morph doc` | **STUB** | Prints success message, no doc generation |

### V.2 Missing Tooling

| Tool | Status |
|------|--------|
| LSP server | NOT STARTED |
| Debugger | NOT STARTED |
| Package manager | NOT STARTED |
| Build system (make/cargo equivalent) | NOT STARTED |
| Formatter (proper) | NOT STARTED |
| Documentation generator | NOT STARTED |
| REPL | NOT STARTED |
| Profiler | NOT STARTED |
| Fuzzer integration | NOT STARTED |

---

## Part VI: Traceability and Infrastructure Deficits

### VI.1 Traceability Matrix

**The `TRACEABILITY_MATRIX.md` file does not exist.** There is no mapping between:
- Markdown requirement IDs (`LANG-REQ-XXX`, `TYP-REQ-XXX`, `MMS-INV-XXX`) and Lean definitions
- Lean definitions and Rust implementations
- Test cases and specific requirements
- Spec contradictions and their resolution status

### VI.2 Compliance Matrix

The compliance matrix tracks **297 requirements** across 8 compiler phases:

| Phase | P0 | P1 | P2 | P3 | Total |
|-------|----|----|----|----|-------|
| Lexer | 22 | 7 | 4 | 3 | 39 |
| Parser | 17 | 15 | 15 | 7 | 53 |
| Type Checker | 34 | 32 | 13 | 7 | 87 |
| Code Gen | 5 | 13 | 12 | 8 | 38 |
| Runtime | 16 | 15 | 10 | 3 | 42 |
| AST Graph | 6 | 5 | 2 | 0 | 15 |
| Security | 0 | 2 | 4 | 3 | 10 |
| Build System | 0 | 4 | 4 | 0 | 10 |
| **Total** | **101** | **95** | **64** | **31** | **297** |

**Every single requirement is marked "TODO".** None have been implemented. 101 P0 (MVP must-have) requirements are unaddressed.

### VI.3 CI/CD Issues

| ID | Issue | Severity |
|----|-------|----------|
| O-1 | 367 broken internal section anchors across spec/ markdown | Medium |
| O-2 | `spec-validation.yml` uses `continue-on-error: true` on all checks | Medium |
| O-3 | GitHub Actions pinned to major tags only, not full commit SHAs | Low |
| O-4 | `elan` installed via `curl | sh` without hash verification | Low |
| O-5 | `ROADMAP.md`, `ROADMAP_DETAILED.md`, `PATH_FORWARD.md` are 90%+ duplicated content | Low |
| O-6 | Duplicate ADR numbering in `.specs/02_adrs/` | Low |
| O-7 | `spec/README.md` directory tree shows wrong subdirectory structure | Low |
| O-8 | No HTML validation or link checking in pages deployment | Low |
| O-9 | `rust-ci.yml` exists but targets Rust code that doesn't exist yet | Low |

---

## Part VII: Underspecified Areas

### VII.1 Critically Vague

| Area | Problem |
|------|---------|
| `??` (optimization hole) semantics | Is it a type? A value? How does it interact with type inference? |
| `comptime` execution model | What operations are allowed? Can it do I/O? What's its memory model? |
| Actor mailbox ordering | FIFO? Arbitrary? Between senders? |
| `flow` vs `act` enforcement | How does the compiler verify UDF/SSUS constraints? |
| `min`/`hum` isomorphism | Claimed isomorphic but no formal proof |
| Inter-actor memory model | Sequential consistency? Relaxed? Acquire-release? |
| Undefined behavior catalog | What happens on integer overflow? Stack overflow? OOM? |
| Pointer provenance semantics | `ProvenanceId` exists in Lean but no semantic rules use it |
| Division by zero behavior | Currently stuck (no step) — is this a panic? UB? |

### VII.2 Moderately Vague

| Area | Problem |
|------|---------|
| Supervision tree strategies | No restart/escalation policies specified |
| Hot reload consistency | In-flight messages, running fibers during reload |
| GC boundary | "No GC" claimed but cycle detection exists in specs |
| `performs` effect syntax | Both `performs IO` and `performs [Pure]` used in examples |
| Trait derivation rules | Auto-derive claimed but customization not specified |
| Weak reference lifecycle | When are weak refs checked during deallocation? |

---

## Part VIII: Spec Volume vs. Substance Imbalance

### VIII.1 The Aspirational Spec Problem

29 tooling specs (~15,000 lines) describe advanced concepts with **zero implementation path** and **zero Lean formalization**:

| Spec | Lines | Category |
|------|-------|----------|
| agent_planning_mdp_spec.md | — | AI/ML |
| analysis_abstract_interp_spec.md | — | Static analysis |
| compiler_bisimulation_spec.md | — | Verification |
| comptime_partial_eval_spec.md | — | Metaprogramming |
| context_comonad_spec.md | — | Type theory |
| context_temporal_logic_spec.md | — | Logic |
| deterministic_time_spec.md | — | Semantics |
| diagnose_protocol_spec.md | 99 | Tooling |
| distributed_crdt_spec.md | — | Distributed systems |
| fuzzing_combinatorial_spec.md | — | Testing |
| graph_rewriting_spec.md | — | Refactoring |
| history_persistent_tree_spec.md | — | Data structures |
| hot_reload_projection_spec.md | — | DX |
| learning_theory_spec.md | — | AI/ML |
| meta_modal_logic_spec.md | — | Logic |
| metaprogramming_spec.md | 1,444 | Metaprogramming |
| operational_semantics_spec.md | 711 | Semantics |
| parsing_island_grammar_spec.md | — | Parsing |
| pattern_coverage_matrix_spec.md | — | Testing |
| protocol_session_types_spec.md | — | Protocols |
| reactive_frp_spec.md | — | UI |
| realtime_mtl_spec.md | — | Logic |
| registry_merkle_spec.md | — | Security |
| semantic_trie_spec.md | — | Data structures |
| semantic_vector_spec.md | — | AI/ML |
| serialization_isomorphism_spec.md | — | Serialization |
| symbolic_execution_fuzz_spec.md | — | Testing |
| synthesis_inhabitation_spec.md | — | Type theory |

These are **research papers**, not implementable specifications. They should be frozen as "future research" and excluded from the compiler development critical path.

---

## Part IX: Risk Assessment for 5-Year Timeline

### IX.1 Critical Risks

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Type system extension breaks soundness proof | HIGH | CRITICAL | Extend incrementally, one feature at a time, re-prove after each |
| Rust compiler diverges from Lean spec | HIGH | CRITICAL | Use Lean as test oracle; establish traceability now |
| Capability types too complex to formalize in Lean | MEDIUM | HIGH | Start with subset (Val only), expand |
| Effect system interferes with capability system | MEDIUM | HIGH | Design interaction upfront before implementation |
| 66K lines of specs become unmaintainable | HIGH | MEDIUM | Freeze non-core specs immediately |
| No reference interpreter to validate compiler | HIGH | HIGH | Implement `Morph.Executable` first |
| LLVM integration complexity exceeds estimates | MEDIUM-HIGH | HIGH (delays) | Use inkwell crate; start with O0 builds |
| Proof effort for memory safety exceeds 6 months | MEDIUM | HIGH | Tier system allows partial completion |

### IX.2 Effort Estimates for Key Work Items

| Item | Estimated Effort | Prerequisite |
|------|-----------------|-------------|
| Resolve 6 spec contradictions | 2-3 days | None |
| Implement reference interpreter in Lean | 3-5 days | None |
| Add missing expression forms to Lean | 2-3 weeks | None |
| Formalize capability types in Lean | 3-4 weeks | Add expression forms |
| Prove memory safety | 4-6 weeks | Formalize capabilities |
| Prove actor isolation | 3-4 weeks | Formalize capabilities |
| Build bytecode VM in Rust | 4-6 weeks | Reference interpreter |
| Implement full compiler pipeline (HIR→MIR→LLVM) | 6-12 months | VM + type system extensions |
| Implement standard library | 3-6 months | Compiler pipeline |
| **Total minimum for alpha** | **18-24 months** | — |

---

## Part X: Prioritized Recommendations

### Phase A: Immediate (Weeks 1-2) — Stop the Bleeding

1. **Resolve all 6 spec contradictions** (C-001 through C-006)
2. **Fix `checkedAdd`/`checkedSub`** overflow checking in Stdlib.lean
3. **Add pointer operator Step rules** to Semantics.lean
4. **Add pattern match** to Syntax.Expr and Step rules
5. **Prove or remove 9 stub theorems** in ModuleSystem/SecurityOCap
6. **Implement `Morph.Executable`** reference interpreter in Lean
7. **Add `FloatType`, integer width types** to Lean `Typ`
8. **Create `TRACEABILITY_MATRIX.md`** mapping requirement IDs → Lean → Rust

### Phase B: Core Formalization (Months 1-4) — Prove the Language

1. **Formalize capability types** (Iso/Val/Ref/Weak) in Lean
2. **Formalize ADTs and pattern matching** in Lean
3. **Formalize effect system** in Lean
4. **Formalize generics** in Lean
5. **Prove memory safety** (no UAF, no double-free)
6. **Prove actor isolation** (no data races)
7. **Prove effect system soundness**
8. **Extend the Rust compiler** to match Lean extensions incrementally

### Phase C: Compiler Construction (Months 3-14) — Build the Machine

1. **Build bytecode VM** that consumes MorphIR output
2. **Implement HIR → MIR lowering** pass
3. **Implement MIR optimization** passes
4. **Implement MIR → LLVM codegen** (via inkwell)
5. **Implement module system** (imports, resolution)
6. **Implement closures with upvalues**
7. **Implement standard library** (core types, collections, I/O)
8. **Build LSP server**

### Phase D: Freeze Aspirational Specs

1. Mark 29 tooling specs as "Future Research — Not Blocking"
2. Remove them from compliance matrix tracking
3. Focus all effort on core language formalization and compiler

### Phase E: Validate Against Competition

Before publication, Morph must demonstrate:
- A verified type safety proof covering **all** type features (not just the minimal core)
- A working compiler that can compile non-trivial programs
- Performance competitive with Rust/C++ on at least 3 benchmarks
- Memory safety guarantees with no runtime GC
- Concurrency safety with no data races
- A standard library covering at least basic I/O, collections, networking
- At least 1 real-world application written in Morph

---

## Appendix A: File Inventory Summary

| Category | Files | Lines |
|----------|-------|-------|
| Markdown specs (`spec/`) | 87 | ~66,700 |
| Lean source (`Morph/`, root `.lean`) | ~95 | ~17,500 |
| Rust compiler (`compiler/src/`) | 16 | ~7,500 |
| Rust runtime (`runtime/src/`) | 12 | ~1,900 |
| Rust CLI (`cli/src/`) | 4 | ~490 |
| Python spec-tools (`scripts/`) | ~30 | ~5,000 |
| Reports (`.reports/`) | ~30 | ~5,000 |
| CI/CD configs | 8 | ~500 |
| **Total** | **~282** | **~104,000** |

## Appendix B: Test Coverage Summary

| Test Suite | Count | Status |
|-----------|-------|--------|
| Lean compile-time tests (examples + theorems) | ~400+ | ALL PASS |
| Lean `#test` properties | 4 | ALL PASS |
| Rust compiler unit tests | 133 | ALL PASS |
| Rust runtime unit tests | 55 | ALL PASS |
| Rust CLI integration tests | 30 | ALL PASS |
| Python spec-tools tests | 803 (96.04% coverage) | ALL PASS |
| **Total** | **~1,425** | **ALL PASS** |

## Appendix C: Compliance Matrix Summary

| Metric | Value |
|--------|-------|
| Total requirements tracked | 297 |
| Requirements implemented | 0 |
| P0 (MVP must-have) unaddressed | 101 |
| P1 (correctness) unaddressed | 95 |
| P2 (important) unaddressed | 64 |
| P3 (nice-to-have) unaddressed | 31 |

---

*End of report. This document should be treated as a living artifact and updated as deficits are resolved.*
