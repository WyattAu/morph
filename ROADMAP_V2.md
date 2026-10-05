# Morph Master Roadmap

**Version:** 2.1.0  
**Date:** 2026-06-11  
**Source:** `.reports/COMPREHENSIVE_DEFICIT_REPORT.md`  
**Target:** Publication-ready language by 2031  
**Status:** ACTIVE  

---

## 0. Current State Snapshot

| Metric | Value | Verdict |
|--------|-------|---------|
| Lean proofs | 800+ theorems, 0 sorry, 344 jobs | STRONG |
| Type safety proof (core lambda calc) | Progress + Preservation = Soundness | COMPLETE |
| Formalization coverage of specs | ~12% (expanded: 17 Typ, 23 Expr, 67 Step) | GROWING |
| Spec contradictions | 0 (all 6 resolved) | RESOLVED |
| Compliance requirements (P0) | ~15 implemented (type system core) | IN PROGRESS |
| Compiler pipeline (Rust) | Lexer + Parser + Typeck (synced) + Codegen + CLI driver | FUNCTIONAL |
| Runtime (Rust) | 12 modules, 55 tests — VM pending (Phase 2) | FRAGMENTARY |
| `morph run` | Prints "interpreter not yet integrated" | BLOCKED |
| Traceability matrix | Created and maintained | EXISTS |
| Aspirational spec bloat | 29 tooling specs frozen, excluded from critical path | FROZEN |
| Store model | Scaffold in Morph/Store.lean + Morph/LinearContext.lean | SCAFFOLD |

### The Core Problem in One Sentence

> Phase 0 is complete: 0 spec contradictions, 29 aspirational specs frozen, traceability matrix exists. Phase 1 is ~80% complete: Lean spec now **exceeds** the Rust compiler's type coverage (17 Typ constructors, 23 Expr forms, 67 Step rules, 0 sorry). Soundness proof holds. Array formalization complete. Store model scaffold created (ADR-010). Linear context scaffold created. Remaining: match_ HasType, capability HasType, store model migration, and VM (Phase 2).

### Guiding Principle

**Every feature must follow this cycle:** Spec → Lean proof → Rust implementation → Lean as test oracle → Lean extended. No feature enters the compiler without first being proven in Lean.

---

## 0.5 Team Structure

| Team | Focus | Size | Deliverables |
|------|-------|------|-------------|
| Team Formal | Lean proofs, spec, store model | 3-4 | Store migration, capability proofs, memory safety |
| Team Compiler | Rust compiler pipeline | 3-4 | Type checker sync, codegen, generics, closures |
| Team Runtime | VM, scheduler, actors | 2-3 | Bytecode VM, fiber scheduler, actor system |
| Team DX | Stdlib, tooling, demos | 2-3 | LSP, formatter, stdlib, demo applications |

All team members are mathematicians capable of writing Lean proofs.

---

## 1. Phase 0 — Spec Integrity (Weeks 1–2)

> **Goal:** Eliminate all contradictions, fix functional bugs, and establish traceability before any feature work begins.
>
> **Exit gate:** 0 contradictions, 0 functional bugs in Lean, traceability matrix created, 29 aspirational specs frozen.

### 0.1 Resolve 6 Spec Contradictions

| ID | Contradiction | Resolution Decision | Effort |
|----|--------------|---------------------|--------|
| C-001 | Duplicate LANG-REQ-071 | Renumber to LANG-REQ-072 | 30 min |
| C-002 | `async` keyword contradiction | `async` is a contextual keyword, only valid as `async let` modifier; update morph_language_spec LANG-REQ-023 to clarify | 2 hours |
| C-003 | Effect category mismatch (4 vs 5) | Canonical: {Pure, IO, Net, Time, System} (5 categories from type_system_spec); update morph_language_spec LANG-REQ-040 | 2 hours |
| C-004 | Affine vs Linear semantics | **Choose affine** (`uses(x) <= 1`); update type_system_spec §5.1.2 to match memory_model_spec §2.4.1 | 4 hours |
| C-005 | Keyword count off-by-one | Recount after C-002 resolution; update morph_language_spec LANG-REQ-006 | 30 min |
| C-006 | Version drift in examples | Script: find-and-replace all version references in version_compatibility_spec to current values | 2 hours |

### 0.2 Fix Functional Bugs in Lean Code

| Bug | Fix | Effort |
|-----|-----|--------|
| `Stdlib.lean:checkededAdd` always returns `some` | Implement actual overflow check using `Int64.size` comparison | 1 hour |
| `Stdlib.lean:checkededSub` always returns `some` | Implement actual overflow check using `Int64.size` comparison | 1 hour |
| `Runtime.lean:marshal/unmarshal` return dummy values | Implement basic serialization for int/bool/string/pointer | 4 hours |
| `Executable.lean` empty | Implement reference evaluator (see §0.4) | 3–5 days |

### 0.3 Clean Up Lean Codebase

| Item | Action | Effort |
|------|--------|--------|
| 9 stub theorems (`True := trivial`) in ModuleSystem/SecurityOCap | Prove or formally remove with justification | 2 days |
| 8 stub tests in Tests/Executable.lean | Replace with real tests after 0.4 | 1 day |
| 3 medium-risk `partial` definitions (reachable, addTransitiveDependencies, hasCycle) | Add well-foundedness proofs | 2 days |

### 0.4 Implement Morph.Executable Reference Interpreter

This is the **single most important deliverable** of Phase 0. Without a reference interpreter, we have no oracle to validate the Rust compiler against.

**Scope:** Extend `Morph/Executable.lean` (currently empty) to evaluate the existing Lean `Syntax.Expr`:
1. Big-step evaluator for all 11 existing expression forms
2. Memory model integration (load/store from `Morph.Memory`)
3. Environment management (de Bruijn indices)
4. Print/repl output for basic expressions

**Not in scope:** New expression forms, new type constructors, actors, concurrency.

**Gate:** `lake build Morph` passes; evaluator produces correct results for 20+ test programs.

### 0.5 Establish Traceability Matrix

Create `TRACEABILITY_MATRIX.md` with three columns:

| Requirement ID | Lean Definition | Rust Implementation |
|----------------|-----------------|-------------------|
| LANG-REQ-001 | `Morph.Core.*` | `compiler/src/lexer/token.rs` |
| ... | ... | ... |

**Gate:** All 297 compliance matrix requirements have at least a "→ Lean" or "→ TODO" mapping.

### 0.6 Freeze 29 Aspirational Specs

Move `spec/tooling/{agent_planning_mdp,analysis_abstract_interp,...,synthesis_inhabitation}_spec.md` (29 files) to `spec/tooling/_future_research/`. Update SPECIFICATION_INDEX.md and COMPLIANCE_MATRIX.md to exclude them from the critical path.

### 0.7 CI/CD Housekeeping

| ID | Fix | Effort |
|----|-----|--------|
| O-2 | Remove `continue-on-error: true` from spec-validation.yml | 30 min |
| O-5 | Consolidate ROADMAP.md, ROADMAP_DETAILED.md, PATH_FORWARD.md into this file | 1 hour |
| O-6 | Fix duplicate ADR numbering | 2 hours |

---

## 2. Phase 1 — Core Formalization (Months 1–4)

> **Goal:** Extend the Lean formalization to cover all type features the Rust compiler already recognizes, so the spec becomes the verified oracle for the compiler.
>
> **Exit gate:** Lean type system matches or exceeds Rust compiler's `Ty` inductive; soundness proof re-verified after each extension.

### 1.1 Extend Lean Type System

Order matters — each extension requires re-proving progress + preservation.

| Step | Add to Lean `Typ` | Status | Effort |
|------|-------------------|--------|--------|
| 1a | `floatType(f32 \| f64)` | ✅ COMPLETE | 2–3 days |
| 1b | `intWidthType(i8..i64, u8..u64, isize, usize)` | ✅ COMPLETE | 2–3 days |
| 1c | `optionType(T)` | ✅ COMPLETE | 1 week |
| 1d | `resultType(T, E)` | ✅ COMPLETE | 1 week |
| 1e | `neverType` | ✅ COMPLETE | 2 days |
| 1f | `refType(cap, T)` (3 caps: iso/val/ref) | ✅ COMPLETE | 2–3 weeks |
| 1g | `effectFunctionType(effs, T)` | ✅ COMPLETE | 2 weeks |
| 1h | `typeVar(n)` | ✅ COMPLETE | 2 weeks |
| 1i | `tupleType(List Typ)` | ✅ COMPLETE | 1 week |
| 1j | `structType(String, List (String × Typ))` | ✅ COMPLETE | 1 week |

### 1.2 Extend Lean Expression Language

| Step | Add to Lean `Expr` | Status | Effort |
|------|-------------------|--------|--------|
| 2a | `match scrut arms` | ⏳ HasType pending | 3 weeks |
| 2b | `structLit fields` | ❌ BLOCKED (termination) | 1 week |
| 2c | `fieldAccess(e, name)` | ✅ COMPLETE | 1 week |
| 2d | `errorPropagate(e)` | ❌ DESUGARED (parser sugar → match) | — |
| 2e | `nullCoalesce(e, default)` | ✅ COMPLETE (5 Step rules) | 1 week |
| 2f | `pipeline(e, f)` | ✅ COMPLETE | 3 days |
| 2g | `walrus(x, e)` | ⏳ DEFERRED Phase 2 (ADR-008) | — |
| 2h | `typeAsc(e, T)` | ✅ COMPLETE | 2 days |
| 2i | `some_/none_/ok_/err_` | ✅ COMPLETE | 1 week |
| 2j | `tuple_(List Expr)` | ✅ COMPLETE (HasTypeAll) | 1 week |
| 2k | `arrayLit(elems)` | ✅ COMPLETE | 1 week |
| 2l | `arrayIndex(arr, idx)` | ✅ COMPLETE | 1 week |

### 1.2a Phase 1 Actual Progress (as of 2026-06-11)

| Metric | ROADMAP Target | Actual | Status |
|--------|---------------|--------|--------|
| Typ constructors | 15+ | **17** | ✅ EXCEEDS |
| Expr constructors | 19+ | **23** | ✅ EXCEEDS |
| Step rules | — | **67** | NEW |
| IsValue constructors | — | **7** | NEW |
| HasType constructors | — | **40+** | NEW |
| sorry count | 0 | **0** | ✅ |
| Build jobs | — | **344** | — |
| Rust tests | — | **55** | — |
| Soundness proof | Progress + Preservation | **Complete (0 sorry)** | ✅ |

**Remaining Phase 1 work:**
- `match_` HasType (typing rule for pattern matching) — 2-3 weeks
- Capability HasType (substructural modalities) — 3-4 weeks
- `structInit` in Expr (blocked by Lean 4 termination checker) — needs workaround
- Store model migration (ADR-010 Phase 1-3) — 6-8 weeks

**Deferred to Phase 2:**
- Walrus operator (`x := e`) — requires store semantics (ADR-008)
- Array values — requires `Value.array` constructor

### 1.3 Extend Operational Semantics

| Missing Rule | Add to `Step` | Effort |
|-------------|---------------|--------|
| Division by zero | Define as `panic("division by zero")` — no UB | 2 days |
| Integer overflow | Define as wrapping (matching Rust's `wrapping_add`) | 3 days |
| Pointer arithmetic | `PtrAdd(ptr, offset)` and `PtrSub(ptr, offset)` | 1 week |
| Pointer load/store | `PtrLoad(ptr)` and `PtrStore(ptr, val)` | 1 week |
| String concatenation | `StrConcat(s1, s2)` | 3 days |
| Array indexing | `ArrayGet(arr, idx)` with bounds check | ✅ COMPLETE (5 Step rules) |
| Array length | `ArrayLen(arr)` | 1 day |

### 1.4 Add Missing Semantic Features to Rust Compiler (Sync)

After each Lean extension, update the Rust compiler to match:

| Lean Extension | Rust Compiler Sync |
|---------------|-------------------|
| 1a–1b Float/int widths | Already in Rust — validate against Lean |
| 1c Option type | Add `Option` variant to `Ty` enum; implement `?` operator type checking |
| 1d Result type | Add `Result` variant; implement error propagation type checking |
| 1e Never type | Add `Never` variant; implement type bottoming |
| 1f Capabilities | Already in Rust — validate against Lean; implement transfer checking |
| 1g Effects | Already in Rust — validate against Lean; implement effect inference |
| 1h Generics | Implement generic parameter resolution and monomorphization |
| 2a Pattern matching | Implement exhaustiveness checking (Maranget's algorithm) |
| 2b–2h Expression forms | Already in Rust AST — validate semantics against Lean Step rules |

### 1.5 Prove Memory Safety (CRITICAL)

**Prerequisite:** 1f (capability types) must be in Lean first.

| Theorem | Statement | Effort |
|--------|-----------|--------|
| `no_use_after_free` | Affine-typed values cannot be accessed after move | 3 weeks |
| `no_double_free` | ARC release can never decrement below 0 for affine values | 2 weeks |
| `capability_transition_safe` | Iso→Val→Ref→Weak transitions preserve memory safety invariants | 2 weeks |
| `acyclicity_theorem` | Strong reference graph is always a DAG under affine types | 2 weeks |

### 1.6 Prove Actor Isolation (CRITICAL)

**Prerequisite:** 1f (capability types) + actor Step rules.

| Theorem | Statement | Effort |
|--------|-----------|--------|
| `no_data_races` | Actor state is only accessible from within the owning actor | 3 weeks |
| `message_safety` | Messages are deep-copied (Val capability) when crossing actor boundaries | 1 week |
| `mailbox_integrity` | Messages are never lost, duplicated, or reordered within a single actor | 1 week |

### 1.7 Prove Type System Decidability (HIGH)

**This addresses GA-005, the foundational unproven assumption.**

| Theorem | Statement | Effort |
|--------|-----------|--------|
| `type_inference_terminates` | `inferType` always terminates (no infinite loops in unification) | 2 weeks |
| `subtyping_decidable` | Subtyping relation is decidable for all Morph types | 2 weeks |
| `principal_types` | When inference succeeds, it produces a most-general type | 3 weeks |

### 1.8 Store Model Migration (ADR-010)

> **Goal:** Integrate the store into the operational semantics, enabling memory safety proofs.
> 
> **Exit gate:** Step carries Store, Progress + Preservation proven with Store, Value.loc constructor exists.

| Phase | Description | Status | Effort |
|-------|-------------|--------|--------|
| 1.8a | Value.loc constructor in Core.lean | ✅ DONE | 1 day |
| 1.8b | Step signature: `Store → Expr → Store → Expr → Prop` | ✅ DONE | 1 week |
| 1.8c | Existing rules carry σ unchanged | ✅ DONE | 1 week |
| 1.8d | Expr.refCreate/refLoad/refStore/refFree | ✅ DONE | 2 weeks |
| 1.8e | HasType for reference operations | ✅ DONE | 2 weeks |
| 1.8f | Store-typed Progress + Preservation (`progressS`, `preservationS`) | ✅ DONE | 3 weeks |
| 1.8g | LinearContext integration into HasType (α: carried, β-1: threaded, β-2: bvar consumes) | ✅ DONE | 3 weeks |
| 1.8h | Memory safety proofs (`safety_load/store/free_not_stuck`, `safety_no_use_after_free`, `safety_freed_not_dereferenceable`) | ✅ DONE | 6 weeks |

**Deliberate limitation.** 1.8g landed enforcement that is sound but *strict*:
a program that consumes a linear binding is currently **rejected** rather than
accepted unchecked. The binder rules (`lam_type`, `let_type`, `for_type`,
`ArmsTyped.cons`) still demand the body return the context it was given. Opening
consumption requires a consumption-aware substitution lemma for `let_subst` /
`app_lam`; `LinCtx.drop` and `value_does_not_consume` are in place as enablers.
See ADR-010 "Implementation Status" for the exact remaining statements.

**Ownership checking proper is not here.** Path-sensitive checking needs an
explicit CFG and belongs in the MIR borrow checker (ADR-011), not in `HasType`.
What Phase 1 supplies is the discipline that feeds it: which bindings are linear,
and that each may be consumed at most once.

### 1.9 MIR Pipeline (ADR-011)

> **Goal:** Verified compilation to LLVM and Cranelift, one verified front end.

| Phase | Description | Status | Effort |
|-------|-------------|--------|--------|
| 1.9a | MIR data type (CFG + SSA value graph) | ⏳ PENDING | 2 weeks |
| 1.9b | ADR-012: closure representation | ⏳ PENDING | 1 week |
| 1.9c | Stage 1 — lambda lifting, `lowering_correct` | ⏳ PENDING | 8 weeks |
| 1.9d | Stage 2 — borrow checker, `analysis_sound` | ⏳ PENDING | 12 weeks |
| 1.9e | Stage 3 — SSA construction, `ssa_correct` | ⏳ PENDING | 4 weeks |
| 1.9f | Stage 4a — LLVM backend | ⏳ PENDING | 6 weeks |
| 1.9g | Stage 4b — Cranelift backend | ⏳ PENDING | 4 weeks |

1.9d is the critical path for the whole project: it is where consumption under
control flow is discharged, and therefore where the 1.8g limitation is finally
lifted.

### Phase 1 Effort Summary

| Component | Effort |
|-----------|--------|
| Lean type system extension | 10–12 weeks |
| Lean expression language extension | 6–8 weeks |
| Operational semantics | 3–4 weeks |
| Rust compiler sync | 4–6 weeks |
| Memory safety proofs | 8 weeks |
| Actor isolation proofs | 5 weeks |
| Type system decidability proofs | 7 weeks |
| **Total (parallelizable)** | **16–20 weeks** |

---

## 3. Phase 2 — Execution Engine (Months 3–6)

> **Goal:** Build a bytecode VM that can execute MorphIR output, creating the first end-to-end `morph run` pipeline.
>
> **Exit gate:** `morph run hello.morph` prints "Hello, World!"

### 2.1 MorphIR Bytecode VM (Rust)

| Component | Description | Effort |
|-----------|-------------|--------|
| Instruction decoder | Decode `MorphIR::Instruction` from bytecode stream | 1 week |
| Value stack | Push/pop MorphValue onto a stack-based VM | 1 week |
| Frame management | Call frames with locals, upvalues, return addresses | 1 week |
| Instruction dispatch | Match on all 40 opcodes in `MorphIR::Instruction` | 2 weeks |
| GC integration | Arc retain/release on every value transition | 1 week |
| Error handling | Try/catch/throw via exception table | 1 week |

**Gate:** All 40 MorphIR opcodes dispatch correctly; VM executes simple arithmetic and control flow programs.

### 2.2 Compiler-to-VM Bridge

| Component | Description | Effort |
|-----------|-------------|--------|
| Module loader | Load `MorphIRModule` from bytecode file | 3 days |
| Function resolution | Resolve call targets by name | 2 days |
| String interning | Share string table between compiler and VM | 2 days |
| Type info table | Pass struct/enum layout info to VM | 3 days |

### 2.3 Fix Compiler Codegen Gaps

| Gap | Fix | Effort |
|-----|-----|--------|
| `break`/`continue` compile to no-ops | Implement via jump patching (like if/else) | 1 week |
| `defer` has no semantics | Defer stack: push defer expression, execute on block exit | 1 week |
| Index expression falls through | Emit `ArrayGet` instruction | 3 days |
| `LoadUpvalue`/`StoreUpvalue` never emitted | Implement closure capture via upvalue chains | 2 weeks |
| No `for` loop | Desugar `for` to `while` + iterator or add iterator protocol | 1 week |

### 2.4 Implement Closures

1. Add closure type to Lean formalization (function + captured environment)
2. Prove closure type safety
3. Implement in Rust compiler: capture analysis → upvalue creation → `LoadUpvalue`/`StoreUpvalue` emission
4. Implement in VM: closure creation, upvalue resolution

**Effort:** 3 weeks

### 2.5 Type Checker Completion

| Gap | Fix | Effort |
|-----|-----|--------|
| `check_type_decl()` empty | Implement struct/enum body validation (field types, variants) | 2 weeks |
| `check_trait_decl()` empty | Implement trait method signatures, supertraits | 2 weeks |
| Constructor pattern checking discards fields | Implement pattern-to-struct/enum type checking | 1 week |
| Type alias stored as `()` | Store actual target type, resolve on use | 3 days |
| Trait resolution | Method resolution via trait impl lookup | 3 weeks |
| Generic monomorphization | Instantiate generic functions at call sites | 4 weeks |

### 2.6 Module System

| Component | Description | Effort |
|-----------|-------------|--------|
| `use` resolution | Resolve `use path::to::module::Item;` to file-based modules | 2 weeks |
| Content-addressable imports | Hash-based module identification (per spec) | 1 week |
| Cyclic import detection | Build import graph, reject cycles | 3 days |
| Hermetic compilation | Each module compiled independently with explicit imports | 1 week |

**Gate:** Multi-file programs compile; `use std::io;` resolves to stdlib module.

### Phase 2 Effort Summary

| Component | Effort |
|-----------|--------|
| VM implementation | 7–8 weeks |
| Compiler-VM bridge | 1–2 weeks |
| Codegen fixes | 3–4 weeks |
| Closures | 3 weeks |
| Type checker completion | 12 weeks |
| Module system | 5 weeks |
| **Total (parallelizable)** | **14–18 weeks** |

---

## 4. Phase 3 — Native Backend (Months 5–9)

> **Goal:** Generate native machine code via LLVM so Morph programs run at native speed.
>
> **Exit gate:** `hello_world.morph` compiles to a native binary that runs; performance within 2x of equivalent Rust program.

### 3.1 HIR → MIR Lowering Pass

| Component | Description | Effort |
|-----------|-------------|--------|
| Surface AST → HIR | Lower `compiler::ast::Expr` to `MorphHIR` representation | 2 weeks |
| HIR desugaring | Desugar match, for, defer, pipeline into core forms | 2 weeks |
| HIR → MIR | Lower HIR to MIR basic blocks + terminators | 3 weeks |

### 3.2 MIR Optimization Passes

| Pass | Description | Effort |
|------|-------------|--------|
| Constant folding | Evaluate compile-time constants | 1 week |
| Dead code elimination | Remove unreachable blocks | 1 week |
| Inlining | Inline small functions (< 10 instructions) | 2 weeks |
| Affine dead-variable | Promote dead Val to mutable (per arc_affine_integration_spec) | 2 weeks |

### 3.3 MIR → LLVM Codegen

| Component | Description | Effort |
|-----------|-------------|--------|
| inkwell setup | LLVM context, module, builder | 1 week |
| Type lowering | Map MorphIR types to LLVM IR types | 2 weeks |
| Function lowering | Map MIR functions to LLVM functions | 2 weeks |
| Instruction lowering | Map all 40 MorphIR opcodes to LLVM IR | 4 weeks |
| Struct/enum layout | Match `layout.rs` ABI calculations to LLVM struct types | 2 weeks |
| Calling convention | Morph calling convention (matches C ABI per abi_alignment spec) | 1 week |
| Linkage | `extern` functions, symbol visibility | 1 week |

**Gate:** `morph build --emit=native hello.morph` produces an executable binary.

### 3.4 FFI / C Interop

| Component | Description | Effort |
|-----------|-------------|--------|
| `extern "C"` declarations | Parse and type-check C FFI declarations | 2 weeks |
| ABI bridge | Marshalling between Morph and C types | 2 weeks |
| Header generation | Generate C-compatible header files from Morph types | 1 week |

### 3.5 Selective Monomorphization

| Component | Description | Effort |
|-----------|-------------|--------|
| Cost-benefit analysis | Decide which generics to monomorphize (per selective_monomorphization_spec) | 2 weeks |
| Code deduplication | Merge identical monomorphizations | 1 week |
| VTable generation | Generate vtables for dynamically dispatched generics | 2 weeks |
| Binary size budget | Enforce configurable binary size limits | 1 week |

### Phase 3 Effort Summary

| Component | Effort |
|-----------|--------|
| HIR → MIR | 7 weeks |
| MIR optimization | 6 weeks |
| LLVM codegen | 12 weeks |
| FFI | 5 weeks |
| Monomorphization | 6 weeks |
| **Total (parallelizable)** | **18–22 weeks** |

---

## 5. Phase 4 — Standard Library & Concurrency (Months 8–14)

> **Goal:** A usable standard library and verified concurrency model.
>
> **Exit gate:** Morph can write a multi-actor HTTP server, an HTTP client, and a command-line tool.

### 4.1 Core Standard Library

| Module | Contents | Effort |
|--------|----------|--------|
| `morph::core` | Int, Float, Bool, String, Bytes, Unit, Never | 2 weeks |
| `morph::option` | Option type, `?` operator, `isSome`, `unwrap`, `map`, `flatMap` | 1 week |
| `morph::result` | Result type, `ok`, `err`, `map`, `flatMap`, `recover` | 1 week |
| `morph::collections` | Vec, Map, Set, Array (with amortized analysis per stdlib_amortized_spec) | 4 weeks |
| `morph::iter` | Iterator trait, for loop desugaring, map/filter/collect | 2 weeks |
| `morph::fmt` | String formatting, Display trait | 1 week |
| `morph::io` | File I/O, stdin/stdout, buffered reader/writer | 3 weeks |
| `morph::fs` | File system operations | 2 weeks |
| `morph::net` | TCP/UDP sockets (effect: Net) | 4 weeks |
| `morph::time` | Time/duration, sleep (effect: Time) | 2 weeks |
| `morph::json` | JSON serialization/deserialization | 2 weeks |
| `morph::test` | Built-in test framework with `@test` attribute | 2 weeks |

### 4.2 Trait System

| Component | Description | Effort |
|-----------|-------------|--------|
| Trait definitions | `trait Display { fn toString() -> String; }` | 2 weeks |
| Impl blocks | `impl Display for Int { ... }` | 2 weeks |
| Trait bounds | `fn sort<T: Ord>(arr: Vec<T>)` | 2 weeks |
| Dynamic dispatch | `dyn Display` vtable dispatch | 3 weeks |
| Trait coherence | Compile-time check: no overlapping impls (prove in Lean) | 3 weeks |
| Auto-derive | `@derive(Debug, Clone, Eq)` for ADTs | 2 weeks |

### 4.3 Concurrency Runtime

| Component | Description | Effort |
|-----------|-------------|--------|
| Actor system integration | Connect VM actors to runtime scheduler | 3 weeks |
| Async I/O | Integrate IO reactor with fiber scheduler | 3 weeks |
| Channel types | `Chan<T>` — multi-producer multi-consumer | 2 weeks |
| Select / choose | `select { msg1 => ..., msg2 => ..., timeout => ... }` | 2 weeks |
| Supervision trees | One-for-one, one-for-all, rest-for-one restart strategies | 2 weeks |
| Deterministic testing | `morph test --deterministic` runs fibers in fixed order | 2 weeks |

### 4.4 Concurrency Proofs

| Theorem | Statement | Effort |
|--------|-----------|--------|
| `deadlock_freedom` | Actor system is deadlock-free under structured supervision | 3 weeks |
| `message_delivery` | Messages are eventually delivered in live systems | 2 weeks |
| `scheduler_correctness` | Work-stealing scheduler preserves program semantics | 2 weeks |
| `no_starvation` | No fiber is indefinitely preempted under fair scheduling | 1 week |

### Phase 4 Effort Summary

| Component | Effort |
|-----------|--------|
| Standard library | 26 weeks |
| Trait system | 14 weeks |
| Concurrency runtime | 14 weeks |
| Concurrency proofs | 8 weeks |
| **Total (parallelizable)** | **24–30 weeks** |

---

## 6. Phase 5 — Tooling & Developer Experience (Months 12–18)

> **Goal:** Morph is pleasant and productive to use.
>
> **Exit gate:** A developer can write, debug, test, and format Morph code in VS Code.

### 5.1 LSP Server

| Feature | Description | Effort |
|---------|-------------|--------|
| Diagnostics | Type errors, warnings, info from compiler pipeline | 2 weeks |
| Go-to-definition | Navigate to definitions across modules | 2 weeks |
| Hover | Show type information on hover | 1 week |
| Autocomplete | Context-aware completions for identifiers, keywords, types | 3 weeks |
| Code actions | Quick fixes for common errors | 2 weeks |
| Semantic highlighting | Token types from type checker | 1 week |

### 5.2 Formatter

| Feature | Description | Effort |
|---------|-------------|--------|
| Opinionated formatting | Consistent indentation, line breaks, spacing | 3 weeks |
| min ↔ hum projection | Format to either dialect (per dialect_projection_spec) | 4 weeks |
| Format on save | VS Code extension integration | 1 week |

### 5.3 Testing Infrastructure

| Feature | Description | Effort |
|---------|-------------|--------|
| Built-in test runner | `morph test` discovers and runs `@test` functions | 2 weeks |
| Property-based testing | `@fuzz` attribute integrates with compiler fuzzing | 3 weeks |
| Coverage reporting | Branch coverage from Lean proof coverage + compiler instrumentation | 4 weeks |
| Snapshot testing | `@snapshot` attribute for golden-file tests | 1 week |

### 5.4 Package Manager

| Feature | Description | Effort |
|---------|-------------|--------|
| `morph.toml` manifest | Package name, version, dependencies, targets | 2 weeks |
| Registry | Content-addressable package registry (per registry_merkle_spec) | 4 weeks |
| Version resolution | SemVer constraint solving (per dependency_sat_spec) | 2 weeks |
| Build caching | Incremental compilation with content-addressed cache | 3 weeks |

### Phase 5 Effort Summary

| Component | Effort |
|-----------|--------|
| LSP server | 11 weeks |
| Formatter | 8 weeks |
| Testing infrastructure | 10 weeks |
| Package manager | 11 weeks |
| **Total (parallelizable)** | **18–22 weeks** |

---

## 7. Phase 6 — Hardening & Validation (Months 16–20)

> **Goal:** Morph is safe, fast, and ready for external scrutiny.
>
> **Exit gate:** All 297 compliance requirements implemented; 0 P0 gaps; security audit passed.

### 6.1 Compliance Matrix Closure

| Priority | Count | Target |
|----------|-------|--------|
| P0 (MVP must-have) | 101 | 100% implemented |
| P1 (correctness) | 95 | 90%+ implemented |
| P2 (important) | 64 | 70%+ implemented |
| P3 (nice-to-have) | 31 | 50%+ implemented |

**Strategy:** Each sprint, pick 5–10 requirements from the compliance matrix, implement, test against Lean oracle, mark done.

### 6.2 Performance Benchmarks

| Benchmark | Target | Comparison |
|-----------|--------|------------|
| `http_server` | >= 80% of Rust equivalent | vs Actix/Hyper |
| `json_parse` | >= 70% of Rust equivalent | vs serde_json |
| `fibonacci(45)` | >= 90% of Rust equivalent | vs rustc -O2 |
| Compilation time | < 10s for 10K LOC | vs rustc |
| Memory usage | <= 2x of Rust equivalent | vs rustc runtime |
| Scheduler throughput | >= 1M concurrent fibers | Stress test |

### 6.3 Security Audit

| Scope | Method |
|-------|--------|
| Memory safety | ASan/TSan/UBSan on all runtime code; 24h fuzzing |
| Capability enforcement | Formal proof (Phase 1) + runtime assertions |
| Supply chain | SBOM generation, dependency scanning, lockfile verification |
| Information flow | Prove non-interference for taint tracking (Lean proof) |
| Undefined behavior | Catalog all UB; verify none exists in safe Morph |

### 6.4 Effect System Soundness Proof

| Theorem | Statement | Effort |
|--------|-----------|--------|
| `effect_soundness` | If a function is typed with `performs [IO]`, it cannot perform Net or System effects | 3 weeks |
| `effect_inference_correct` | Effect inference infers the minimal effect set | 2 weeks |
| `effect_subtyping` | Effect set subtyping is sound | 1 week |

### 6.5 Pattern Match Proofs

| Theorem | Statement | Effort |
|--------|-----------|--------|
| `exhaustiveness` | If the type checker accepts a match, all cases are covered | 3 weeks |
| `redundancy` | If a pattern is unreachable, the type checker warns | 1 week |

---

## 8. Phase 7 — Publication Preparation (Months 20–24+)

> **Goal:** Morph is publishable — papers submitted, documentation complete, community ready.
>
> **Exit gate:** At least 1 peer-reviewed paper accepted; documentation site complete; 3 real-world demo applications.

### 7.1 Academic Publications

| Paper | Target Venue | Content |
|-------|-------------|---------|
| "Morph: A Verified Type System for the LLM Age" | POPL / ICFP | Core type system, soundness proof, capability types |
| "Affine Types + ARC: Verified Memory Safety Without GC" | PLDI / OOPSLA | Memory model, acyclicity theorem, ARC integration |
| "Actor Isolation via Capability Types" | CONCUR / ECOOP | Actor model, isolation proof, supervision trees |
| "Projectional Editing for Agent-First Programming" | VL / HCI | Dialect system, min/hum, LSP integration |

### 7.2 Documentation

| Artifact | Content | Effort |
|----------|---------|--------|
| Language specification | Complete, single-document spec based on frozen core specs | 4 weeks |
| Standard library reference | API docs for every stdlib function | 3 weeks |
| Tutorials | "Getting Started", "Types & Capabilities", "Concurrency", "FFI" | 4 weeks |
| Architecture guide | Compiler pipeline, runtime architecture, proof structure | 2 weeks |
| ADR consolidation | All architecture decisions documented | 1 week |

### 7.3 Demo Applications

| Application | Demonstrates | Effort |
|-------------|-------------|--------|
| HTTP server | Networking, concurrency, error handling, actors | 3 weeks |
| CLI tool (e.g., grep clone) | I/O, pattern matching, stdlib, argument parsing | 2 weeks |
| JSON parser | String processing, ADTs, traits, error handling | 2 weeks |

### 7.4 Real-World Validation

| Target | Requirement |
|--------|-------------|
| Performance | Within 2x of Rust on 3+ benchmarks |
| Memory safety | 24h fuzzing with 0 crashes |
| Concurrency | 1M concurrent fibers, correct final state |
| Compilation | < 10s for 10K LOC project |
| Standard library | Covers I/O, collections, networking, JSON, testing |

---

## 9. Phase 8 — Ecosystem & Growth (Months 24–60)

> **Goal:** Morph has a growing community, ecosystem packages, and a path to production use.
>
> **This phase is beyond the current planning horizon and will be detailed after Phase 7.**

### Tentative Milestones

| Milestone | Target Date |
|-----------|-------------|
| v0.1.0 Alpha (internal) | Month 18 |
| v0.5.0 Beta (public) | Month 24 |
| v1.0.0 Stable | Month 36 |
| v2.0.0 Production features | Month 48 |
| Academic publication cycle | Months 24–36 |
| Conference talks (POPL, RustConf, etc.) | Months 30–48 |

### Future Research Directions (Post-1.0)

| Direction | Status |
|-----------|--------|
| Dependent types extracted from Lean proofs | Research (Phase 5.1 in old roadmap) |
| Multi-stage compilation / comptime | Frozen spec exists |
| Distributed CRDTs | Frozen spec exists |
| Semantic vector RAG for agent coding | Frozen spec exists |
| Hot reload | Frozen spec exists |
| UI constraint algebra | Frozen spec exists |
| Financial domain (fixed-point, HFT) | Frozen spec exists |

---

## 10. Dependency Graph

```
Phase 0 (Spec Integrity) ✅
  ├─→ Phase 1 (Core Formalization) ← 80% COMPLETE
  │     ├─→ Phase 1.8 (Store Migration) ← STARTING NOW
  │     │     └─→ Phase 1.5 (Memory Safety Proofs)
  │     │           └─→ Phase 1.6 (Actor Isolation Proofs)
  │     └─→ Phase 2 (Execution Engine) ← can start in parallel
  │           ├─→ Phase 3 (Native Backend)
  │           └─→ Phase 4 (Stdlib & Concurrency)
  └─→ Phase 5 (Tooling)
```

### Critical Path

```
TRACK A — Team Formal (Lean proofs):
Week 1-2:     Phase 0 (spec integrity) ✅
Week 3-10:    Phase 1.1–1.3 (extend Lean types + expressions) ✅
Week 10-18:   Phase 1.8 (store model migration)
Week 18-26:   Phase 1.5 (memory safety proofs)
Week 26-32:   Phase 1.6 (actor isolation proofs)
Week 32-38:   Phase 1.7 + Phase 6.4–6.5 (decidability, effect soundness, pattern match proofs)

TRACK B — Team Compiler (Rust pipeline):
Week 3-10:    Phase 1.4 (Rust compiler sync with Lean extensions)
Week 10-22:   Phase 2.3–2.5 (codegen fixes, closures, type checker)
Week 22-28:   Phase 2.6 (module system)
Week 28-38:   Phase 3.1–3.3 (HIR→MIR→LLVM)
Week 38-44:   Phase 3.4–3.5 (FFI, monomorphization)

TRACK C — Team Runtime (VM, scheduler, actors):
Week 10-18:   Phase 2.1 (VM implementation)
Week 18-22:   Phase 2.2 (compiler-to-VM bridge)
Week 22-34:   Phase 4.3 (concurrency runtime)
Week 34-38:   Phase 4.4 (concurrency proofs)

TRACK D — Team DX (stdlib, tooling, demos):
Week 22-34:   Phase 4.1–4.2 (stdlib, trait system)
Week 38-44:   Phase 4.2 completion + Phase 5.1 (LSP server)
Week 44-50:   Phase 5.2–5.4 (formatter, tests, package manager)
Week 50-56:   Phase 5 completion + Phase 6 (hardening, benchmarks, security audit)

TRACK E — Integration & Publication:
Week 56-60:   Phase 7 (publications, documentation, demos)
```

---

## 11. Risk Register

| Risk | Probability | Impact | Mitigation | Owner |
|------|------------|--------|------------|-------|
| Extending Lean types breaks soundness proof | HIGH | CRITICAL | Extend one type at a time, re-prove after each | Lean team |
| Rust compiler diverges from Lean spec | HIGH | CRITICAL | Traceability matrix; Lean as test oracle; weekly sync reviews | Compiler team |
| Capability types too complex to formalize | MEDIUM | HIGH | Start with Val only (simplest), add Iso/Ref/Weak incrementally | Lean team |
| Effect system conflicts with capability system | MEDIUM | HIGH | Design interaction matrix upfront; prove no interference | Lean team |
| LLVM integration exceeds estimates | MEDIUM-HIGH | HIGH (delays) | Use inkwell; start with O0; fallback to Cranelift | Backend team |
| Memory safety proof effort exceeds 6 months | MEDIUM | HIGH | Tiered approach: prove for subset, expand | Lean team |
| 66K lines of specs become unmaintainable | HIGH | MEDIUM | Freeze 29 aspirational specs now; focus on ~12 core specs | Spec team |
| No one uses the language | MEDIUM | HIGH | Build compelling demos early; target LLM-agent use case | Community team |

---

## 12. Success Metrics by Phase

| Metric | Phase 0 | Phase 1 | Phase 2 | Phase 3 | Phase 4 | Phase 5 | Phase 6 | Phase 7 |
|--------|---------|---------|---------|---------|---------|---------|---------|---------|
| Spec contradictions | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Lean `sorry` count | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Stub theorems (`True := trivial`) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Lean type constructors | 17 | 17 | 17 | 17 | 17 | 17 | 17 | 17 |
| Lean expression forms | 21 | 23+ | 23+ | 23+ | 23+ | 23+ | 23+ | 23+ |
| Proven safety theorems | 7 | 20+ | 20+ | 20+ | 28+ | 28+ | 35+ | 35+ |
| Build jobs | — | 344 | — | — | — | — | — | — |
| Compliance P0 done | 0 | 10 | 40 | 70 | 90 | 95 | 101 | 101 |
| `morph run` works | No | No | **Yes** | Yes | Yes | Yes | Yes | Yes |
| Native binary output | No | No | No | **Yes** | Yes | Yes | Yes | Yes |
| Stdlib modules | 0 | 0 | 0 | 0 | **12+** | 12+ | 12+ | 12+ |
| LSP server | No | No | No | No | No | **Yes** | Yes | Yes |
| Perf vs Rust | — | — | — | within 2x | within 2x | within 1.5x | within 1.2x | **within 1.1x** |
| Fuzzing (hours crash-free) | 0 | 0 | 1 | 24 | 100 | 100 | 1000 | 10000 |
| Papers submitted | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **4** |

---

## 13. Effort Totals

| Phase | Duration | Team Size (est.) | Key Deliverable |
|-------|----------|-----------------|-----------------|
| 0 — Spec Integrity | 2 weeks | 1–2 | Contradictions resolved, traceability matrix |
| 1 — Core Formalization | 16–20 weeks | 2–3 | Extended Lean type system, memory safety proof |
| 2 — Execution Engine | 14–18 weeks | 2–3 | Bytecode VM, `morph run`, closures, modules |
| 3 — Native Backend | 18–22 weeks | 2–3 | LLVM codegen, native binaries |
| 4 — Stdlib & Concurrency | 24–30 weeks | 3–4 | Stdlib, traits, actor runtime, concurrency proofs |
| 5 — Tooling & DX | 18–22 weeks | 2–3 | LSP, formatter, test runner, package manager |
| 6 — Hardening | 14–18 weeks | 2–3 | Compliance closure, benchmarks, security audit |
| 7 — Publication | 16–20 weeks | 2–3 | Papers, docs, demos |
| **Total to v0.5.0 Beta** | **~24 months** | **2–4** | Publishable language |

---

## Appendix A: Files This Roadmap Supersedes

This file consolidates and supersedes the following roadmap documents:

| File | Status |
|------|--------|
| `ROADMAP.md` | **SUPPLANTED** — 90%+ duplicate content |
| `ROADMAP_DETAILED.md` | **SUPPLANTED** — 90%+ duplicate content |
| `PATH_FORWARD.md` | **SUPPLANTED** — 90%+ duplicate content |
| `ROADMAP_CONSOLIDATED.md` | **SUPPLANTED** — subsumed into this file |

These files should be archived (not deleted) and replaced with a redirect to this file.

## Appendix B: Frozen Spec List

The following 29 spec files are moved to `spec/tooling/_future_research/` and excluded from the critical path:

1. `agent_planning_mdp_spec.md`
2. `analysis_abstract_interp_spec.md`
3. `compiler_bisimulation_spec.md`
4. `comptime_partial_eval_spec.md`
5. `context_comonad_spec.md`
6. `context_temporal_logic_spec.md`
7. `deterministic_time_spec.md`
8. `diagnose_protocol_spec.md`
9. `distributed_crdt_spec.md`
10. `fuzzing_combinatorial_spec.md`
11. `graph_rewriting_spec.md`
12. `history_persistent_tree_spec.md`
13. `hot_reload_projection_spec.md`
14. `learning_theory_spec.md`
15. `meta_modal_logic_spec.md`
16. `metaprogramming_spec.md`
17. `operational_semantics_spec.md`
18. `parsing_island_grammar_spec.md`
19. `pattern_coverage_matrix_spec.md`
20. `protocol_session_types_spec.md`
21. `reactive_frp_spec.md`
22. `realtime_mtl_spec.md`
23. `registry_merkle_spec.md`
24. `semantic_trie_spec.md`
25. `semantic_vector_spec.md`
26. `serialization_isomorphism_spec.md`
27. `symbolic_execution_fuzz_spec.md`
28. `synthesis_inhabitation_spec.md`
29. `distributed_vector_clock_spec.md` (root-level)

## Appendix C: Active Spec List (Critical Path)

The following ~12 specs are the **core language specification** that drives all compiler and proof work:

| Spec | Role |
|------|------|
| `morph_language_spec.md` | Language keywords, operators, syntax |
| `lexical_structure_syntax_spec.md` | Lexer specification |
| `type_system_spec.md` | Type system design |
| `effect_system_spec.md` | Effect algebra and inference |
| `type_unification_spec.md` | Type inference algorithm |
| `memory_model_spec.md` | Memory management, ARC, affine types |
| `arc_affine_integration_spec.md` | ARC + affine integration |
| `memory_affine_logic_spec.md` | Affine type formalism |
| `security_flow_spec.md` | Information flow, taint tracking |
| `security_ocap_spec.md` | Object capability model |
| `concurrency_process_algebra_spec.md` | Actor model, pi-calculus |
| `execution_model_spec.md` | Fibers, scheduler, actors |
| `module_system_spec.md` | Module resolution, namespaces |
| `build_lattice_spec.md` | Build dependency management |
| `abi_alignment_algebra_spec.md` | Struct layout, ABI |

---

*Maintained by: Morph core team  
Last updated: 2026-06-11  
Next review: End of Phase 0 (2026-06-12)*
