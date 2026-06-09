# Morph Traceability Matrix

Generated: 2026-05-29  
Source: Compliance Matrix (COMPLIANCE_MATRIX.md) + Lean source + Rust source

## Legend
- ✅ = Implemented and verified
- 🔶 = Partially implemented
- ❌ = Not started / TODO
- ➖ = Not applicable

---

## Section 1: Lean Core → Spec Requirements

| Lean Module | Spec Source | Status |
|-------------|-------------|--------|
| `Morph.Core` | morph_language_spec, lexical_structure_syntax_spec | ✅ Core types defined |
| `Morph.Syntax` | morph_language_spec | ✅ 11 Expr constructors, de Bruijn indices |
| `Morph.Semantics` | morph_language_spec | ✅ 23 Step constructors |
| `Morph.Memory` | memory_model_spec | ✅ Heap block model |
| `Morph.HIR` | — | ✅ High-level IR |
| `Morph.MIR` | — | ✅ Mid-level IR |
| `Morph.Executable` | morph_language_spec | ✅ Big-step evaluator (195 lines) |
| `Morph.Stdlib` | — | ✅ Checked arithmetic, collections |
| `Morph.Runtime` | execution_model_spec | 🔶 Actor system, heap, FFI (stub marshal) |
| `Morph.TypeChecker` | type_system_spec | 🔶 Type inference, unification |

## Section 2: Lean Proofs → Spec Claims

| Proof | File | Spec Claim | Status |
|------|------|-----------|--------|
| Progress | Proofs/TypeSoundness/Progress.lean | Type soundness (morph_language_spec) | ✅ Proven |
| Preservation | Proofs/TypeSoundness/Preservation.lean | Type soundness | ✅ Proven |
| Type Safety | Proofs/TypeSoundness/Soundness.lean | Well-typed programs don't get stuck | ✅ Proven |
| Not Stuck | Proofs/TypeSoundness/Soundness.lean | No stuck well-typed terms | ✅ Proven |
| Memory Safety | — | memory_model_spec MMS-INV-008 | ❌ NOT STARTED |
| Capability Safety | — | memory_model_spec + type_system_spec | ❌ NOT STARTED |
| Actor Isolation | — | execution_model_spec EMS-INV-xxx | ❌ NOT STARTED |
| Effect Soundness | — | effect_system_spec EFF-REQ-001 | ❌ NOT STARTED |
| Information Flow | — | security_flow_spec SEC-REQ-xxx | ❌ NOT STARTED |
| Type Decidability | — | type_system_spec TYP-REQ-xxx | ❌ NOT STARTED |

## Section 3: Rust Compiler → Spec Requirements (Compliance Matrix)

### Lexer (39 requirements)

| Requirement | Spec Source | Rust File | Status |
|-------------|-------------|-----------|--------|
| LEX-001 (UTF-8, NFC) | lexical_structure_syntax_spec | compiler/src/lexer/mod.rs | ❌ TODO |
| LEX-002 ({, }, ; delimiters) | morph_language_spec | compiler/src/lexer/mod.rs | 🔶 Partial (no ; mandatory check) |
| LEX-003 (min dialect whitespace) | lexical_structure_syntax_spec | compiler/src/lexer/mod.rs | ❌ TODO (no dialect support) |
| LEX-004-005 (Comments) | lexical_structure_syntax_spec | compiler/src/lexer/mod.rs | ✅ Implemented |
| LEX-007 (22 keywords) | morph_language_spec | compiler/src/lexer/token.rs | 🔶 Partial (has keywords, no cap sigils) |
| LEX-010-011 (Int/Float literals) | lexical_structure_syntax_spec | compiler/src/lexer/mod.rs | ✅ Implemented |
| LEX-013 (String literals) | lexical_structure_syntax_spec | compiler/src/lexer/mod.rs | 🔶 Partial (no fenced code strings) |
| LEX-015-016 (Bool/Null) | morph_language_spec | compiler/src/lexer/mod.rs | 🔶 Partial (no null literal) |
| LEX-019 (??) | operator_null_coalescing_spec | compiler/src/lexer/token.rs | ✅ Implemented |

### Parser (53 requirements)

| Requirement | Spec Source | Rust File | Status |
|-------------|-------------|-----------|--------|
| PAR-001 (Compilation unit) | lexical_structure_syntax_spec | compiler/src/parser/mod.rs | 🔶 Partial (no use declarations resolved) |
| PAR-005 (fn declarations) | lexical_structure_syntax_spec | compiler/src/parser/mod.rs | ✅ Implemented |
| PAR-006 (type declarations) | lexical_structure_syntax_spec | compiler/src/parser/mod.rs | 🔶 Partial (parsed but not body-checked) |
| PAR-013 (generics) | type_system_spec | compiler/src/parser/mod.rs | 🔶 Partial (parsed but not resolved) |
| PAR-016 (expression grammar) | syntax_translation_spec | compiler/src/parser/mod.rs | ✅ Implemented |
| PAR-018 (match/fix) | lexical_structure_syntax_spec | compiler/src/parser/mod.rs | ✅ Implemented |

### Type Checker (87 requirements)

| Requirement | Spec Source | Rust File | Status |
|-------------|-------------|-----------|--------|
| TYP-001 (Hindley-Milner) | type_system_spec | compiler/src/typeck/ | ✅ Implemented |
| TYP-002 (Occurs check) | type_unification_spec | compiler/src/typeck/unification.rs | ✅ Implemented |
| TYP-080 (Affine checking) | arc_affine_integration_spec | compiler/src/typeck/ | ❌ TODO |
| TYP-081 (DAG acyclicity) | arc_affine_integration_spec | compiler/src/typeck/ | ❌ TODO |
| TYP-082 (Iso cycle-free) | arc_affine_integration_spec | compiler/src/typeck/ | ❌ TODO |

### Code Gen (38 requirements)

| Requirement | Spec Source | Rust File | Status |
|-------------|-------------|-----------|--------|
| CG-001 (MorphIR generation) | — | compiler/src/codegen/compiler.rs | ✅ Implemented (40 opcodes) |
| CG-002 (Type layout) | abi_alignment_algebra_spec | compiler/src/codegen/layout.rs | ✅ Implemented |
| CG-031 (Monomorphization) | selective_monomorphization_spec | — | ❌ TODO |

### Runtime (42 requirements)

| Requirement | Spec Source | Rust File | Status |
|-------------|-------------|-----------|--------|
| RT-001 (Value types) | memory_model_spec | runtime/src/value.rs | ✅ Implemented (16 variants) |
| RT-002 (Fibers) | execution_model_spec | runtime/src/fiber.rs | ✅ Implemented |
| RT-003 (Scheduler) | scheduling_modes_spec | runtime/src/scheduler.rs | ✅ Implemented (both modes) |
| RT-004 (Actor system) | execution_model_spec | runtime/src/actor.rs | ✅ Implemented |
| RT-005 (Memory allocators) | memory_model_spec | runtime/src/memory.rs | ✅ Implemented |
| RT-043 (ARC O(1)) | arc_affine_integration_spec | runtime/src/arc.rs | 🔶 Partial (wraps std::Arc) |
| RT-XXX (Bytecode VM) | — | — | ❌ MISSING (CRITICAL) |

## Section 4: Cross-Reference Gaps

| Gap | Impact | Priority |
|-----|--------|----------|
| No Lean formalization for Iso/Val/Ref capabilities | Cannot prove memory safety | CRITICAL |
| No Lean formalization for effects | Cannot prove effect soundness | CRITICAL |
| No Lean formalization for ADTs/pattern match | Cannot prove exhaustiveness | CRITICAL |
| No Lean formalization for generics | Cannot prove monomorphization termination | HIGH |
| Rust compiler has integer widths (10 types), Lean has 1 (intType) | Spec-compiler divergence | HIGH |
| Rust compiler has capabilities (3), Lean has 0 | Spec-compiler divergence | HIGH |
| Rust compiler has effects (5), Lean has 0 | Spec-compiler divergence | HIGH |
| No MorphIR → VM bridge | Cannot execute compiled code | CRITICAL |
| No module import resolution | Cannot compile multi-file programs | HIGH |
| No trait resolution | Cannot implement trait-based dispatch | HIGH |

## Section 5: Compliance Matrix Summary

| Phase | P0 | P1 | P2 | P3 | Total | Implemented |
|-------|----|----|----|----|-------|-------------|
| Lexer | 22 | 7 | 4 | 3 | 39 | ~15 (38%) |
| Parser | 17 | 15 | 15 | 7 | 53 | ~30 (57%) |
| Type Checker | 34 | 32 | 13 | 7 | 87 | ~15 (17%) |
| Code Gen | 5 | 13 | 12 | 8 | 38 | ~5 (13%) |
| Runtime | 16 | 15 | 10 | 3 | 42 | ~20 (48%) |
| AST Graph | 6 | 5 | 2 | 0 | 15 | ~5 (33%) |
| Security | 0 | 2 | 4 | 3 | 10 | 0 (0%) |
| Build System | 0 | 4 | 4 | 0 | 10 | 0 (0%) |
| **Total** | **101** | **95** | **64** | **31** | **297** | **~90 (30%)** |
