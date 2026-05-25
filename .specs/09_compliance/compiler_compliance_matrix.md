# Morph Compiler Compliance Matrix

Generated from 50 specification files (26 directly read: specs 1-16 primary + 10 secondary). Every numbered requirement is mapped to a compiler phase and priority.

**Specs read:** language (morph_language, lexical_structure, type_system, pure_type, type_category, effect_system, type_unification, module_system, scoping, syntax_translation, operator_null_coalescing, strict_state_unidirectional, unidirectional_data_flow, dialect_projection, ast_graph, dual_optimization), concurrency (execution_model, monadic_effect, scheduling_modes, concurrency_process_algebra), architecture (layered_concurrency), memory (memory_model, arc_affine_integration), security (security_flow), optimization (selective_monomorphization), build (build_lattice).

**Priority Key:** P0=MVP must-have, P1=correctness, P2=important features, P3=nice-to-have, P4=future/post-MVP

---

## Phase 1: Lexer (Tokenization)

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| LEX-001 | UTF-8 source encoding; NFC normalization for identifiers; case-sensitive | lexical_structure_syntax_spec.md §1.1 | P0 | TODO |
| LEX-002 | Explicit delimiters: `{`, `}`, `;` mandatory for all blocks and statements | morph_language_spec §2.1 LANG-REQ-005 | P0 | TODO |
| LEX-003 | Strip non-functional whitespace in `min` dialect (insignificant except between alphanumerics) | lexical_structure_syntax_spec.md §1.2 | P0 | TODO |
| LEX-004 | Line comments `//` (terminated by newline) | lexical_structure_syntax_spec.md §1.3 | P0 | TODO |
| LEX-005 | Block comments `/* ... */` (nestable) | lexical_structure_syntax_spec.md §1.3 | P0 | TODO |
| LEX-006 | Semantic doc comments `///` (extracted for vector embedding/RAG) | lexical_structure_syntax_spec.md §1.3 | P2 | TODO |
| LEX-007 | 22 compressed keywords: `fn`, `ret`, `use`, `pub`, `mut`, `type`, `act`, `state`, `event`, `on`, `spawn`, `async`, `fix`, `if`, `else`, `loop`, `defer`, `const`, `void`, `in`, `is`, `as` | morph_language_spec §2.2 LANG-REQ-006 | P0 | TODO |
| LEX-008 | Contextual keyword `async` (only as `let` modifier) | morph_language_spec §2.2 LANG-REQ-006 | P1 | TODO |
| LEX-009 | Capability sigils as tokens: `^` (Iso), `#` (Val), `&` (Ref), `?` (Opt) | lexical_structure_syntax_spec.md §2.2 | P0 | TODO |
| LEX-010 | Integer literals: decimal, hex (`0xFF`), binary (`0b101`) | lexical_structure_syntax_spec.md §3.1 | P0 | TODO |
| LEX-011 | Float literals: `1.0`, scientific `1e-10` | lexical_structure_syntax_spec.md §3.1 | P0 | TODO |
| LEX-012 | Optimization hole literal: `??` | lexical_structure_syntax_spec.md §3.1 | P2 | TODO |
| LEX-013 | Standard string literal `"..."` with escapes `\n`, `\t`, `\"`, `\u{...}` | lexical_structure_syntax_spec.md §3.2.1 | P0 | TODO |
| LEX-014 | Fenced code string ``` with optional semantic tag; 3+ backticks; raw content (no escapes) | lexical_structure_syntax_spec.md §3.2.2 | P1 | TODO |
| LEX-015 | Boolean literals: `true`, `false` | lexical_structure_syntax_spec.md §3 (implicit) | P0 | TODO |
| LEX-016 | Null literal: `null` | syntax_translation_spec.md §3.1.8 | P0 | TODO |
| LEX-017 | Walrus operator `:=` token | lexical_structure_syntax_spec.md §4.1 | P0 | TODO |
| LEX-018 | Pipe operator `|>` token | lexical_structure_syntax_spec.md §4.2 | P0 | TODO |
| LEX-019 | Error propagation operator `?` (postfix) | morph_language_spec §2.4 LANG-REQ-011 | P0 | TODO |
| LEX-020 | Null-coalescing operator `??` | operator_null_coalescing_spec.md §2.1 | P0 | TODO |
| LEX-021 | Arrow token `->` for return types | syntax_translation_spec.md §4.3 | P0 | TODO |
| LEX-022 | Fat arrow `=>` for match arms | lexical_structure_syntax_spec.md §5.4 | P0 | TODO |
| LEX-023 | Attribute prefix `@` (e.g., `@gpu`, `@simd`, `@fuzz`, `@critical`, `@auditable`) | morph_language_spec §5.4 LANG-REQ-036 | P1 | TODO |
| LEX-024 | All binary operators: `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `&&`, `||` | lexical_structure_syntax_spec.md §4.3 | P0 | TODO |
| LEX-025 | Unary operators: `!`, `-` (negation), `^` (bitwise not) | lexical_structure_syntax_spec.md §4.3 | P0 | TODO |
| LEX-026 | Access/call/index operators: `.`, `()`, `[]` | lexical_structure_syntax_spec.md §4.3 | P0 | TODO |
| LEX-027 | Assignment operator `=` | lexical_structure_syntax_spec.md §4.3 | P0 | TODO |
| LEX-028 | `hum` dialect keyword set: `function`, `return`, `import`, `actor`, `match`, `case`, `let` (as alternative forms) | syntax_translation_spec.md §4.1 | P1 | TODO |
| LEX-029 | `hum` dialect type names: `Int8`..`Int64`, `Float32`, `Float64`, `String`, `Boolean`, `Void` | syntax_translation_spec.md §4.2 | P1 | TODO |
| LEX-030 | Generic delimiters `<` `>` for type parameters | syntax_translation_spec.md §3.1.3 | P0 | TODO |
| LEX-031 | Effect annotation keyword `performs` | morph_language_spec §6.2 LANG-REQ-040 | P1 | TODO |
| LEX-032 | Contract keywords: `requires`, `ensures`, `invariant` | morph_language_spec §6.1 LANG-REQ-038 | P2 | TODO |
| LEX-033 | Constraint keywords: `where`, `requires` (value constraints) | morph_language_spec §5.1 LANG-REQ-030 | P1 | TODO |
| LEX-034 | `comptime` keyword for compile-time blocks | morph_language_spec §5.2 LANG-REQ-031 | P2 | TODO |
| LEX-035 | `unit` keyword for dimensional analysis | morph_language_spec §3.4 LANG-REQ-019 | P3 | TODO |
| LEX-036 | `flow` keyword for unidirectional data flow constructs | unidirectional_data_flow_spec.md §2.2 | P2 | TODO |
| LEX-037 | Operator precedence levels 1-7: access/call/index/propagate > bitwise not > multiplicative > additive > pipeline > relational > declaration/assignment | lexical_structure_syntax_spec.md §4.3 | P0 | TODO |
| LEX-038 | Membership operators: `in`, `is`, `as` | lexical_structure_syntax_spec.md §2.1 | P1 | TODO |
| LEX-039 | Variants for `msg` keyword in actor event handlers (contextual) | morph_language_spec §4.1 LANG-REQ-022 | P1 | TODO |

---

## Phase 2: Parser (AST Construction)

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| PAR-001 | Compilation unit: `{UseDecl} {TopLevelDecl}` | lexical_structure_syntax_spec.md §5.1 | P0 | TODO |
| PAR-002 | Use declarations: `use` Identifier [`as` Identifier] `;` | lexical_structure_syntax_spec.md §5.1 | P0 | TODO |
| PAR-003 | Selective imports: `use std.math::{sin, cos, PI}` | module_system_spec.md §3.2 | P1 | TODO |
| PAR-004 | Re-exports: `pub use .internal.deep_logic.User` | module_system_spec.md §3.3 | P2 | TODO |
| PAR-005 | Function declarations: `fn` Name [Generics] Params [`->` Type] Block | lexical_structure_syntax_spec.md §5.2 | P0 | TODO |
| PAR-006 | Type declarations (ADTs): `type` Name [Generics] `=` TypeBody `;` — both Product (struct) and Sum (enum) | lexical_structure_syntax_spec.md §5.2 | P0 | TODO |
| PAR-007 | Constant declarations: `const` Name `=` (Expr \| `??`) `;` | lexical_structure_syntax_spec.md §5.2 | P0 | TODO |
| PAR-008 | Variable declarations: `:=` (inferred) or `:` Type `=` (explicit) | lexical_structure_syntax_spec.md §5.2 | P0 | TODO |
| PAR-009 | Actor declarations: `act` Name `{` {StateBlock \| EventDecl \| HandlerDecl} `}` | lexical_structure_syntax_spec.md §5.3 | P1 | TODO |
| PAR-010 | Actor state block: `state` `{` {Name `:` Type [`=` Expr] `;`} `}` | lexical_structure_syntax_spec.md §5.3 | P1 | TODO |
| PAR-011 | Actor event declaration: `event` Name Params `;` | lexical_structure_syntax_spec.md §5.3 | P1 | TODO |
| PAR-012 | Actor handler: `on` Name Params Block | lexical_structure_syntax_spec.md §5.3 | P1 | TODO |
| PAR-013 | Generic parameters: `<` GenericList `>` with optional type constraints | syntax_translation_spec.md §3.1.3 | P0 | TODO |
| PAR-014 | Generic syntax validation: non-empty, comma-separated, no trailing comma, valid identifiers | type_system_spec.md §2.5.1 TYP-INV-015 | P0 | TODO |
| PAR-015 | Type grammar: primitives, identifiers with generics, `T?` (optional), `^T` (iso), `#T` (val), `&T` (ref), tuples | syntax_translation_spec.md §3.1.4 | P0 | TODO |
| PAR-016 | Expression grammar: literals, identifiers, calls, field access, index, `?` propagate, `??` coalesce, `\|>` pipe, binary/unary ops, parenthesized | syntax_translation_spec.md §3.1.5 | P0 | TODO |
| PAR-017 | Statement grammar: VarDecl, `ret`, `fix` (match), `if`/`else`, `loop`, `defer`, expression statements | lexical_structure_syntax_spec.md §5.4 | P0 | TODO |
| PAR-018 | Pattern matching: `fix` Expr `{` {MatchArm} `}` with patterns (literal, identifier, constructor, struct) | lexical_structure_syntax_spec.md §5.4 | P0 | TODO |
| PAR-019 | `if` requires braces (no dangling else possible) | lexical_structure_syntax_spec.md §6.2 | P0 | TODO |
| PAR-020 | `Name { ... }` in expression position = struct init; in statement position = invalid | lexical_structure_syntax_spec.md §6.1 | P0 | TODO |
| PAR-021 | Walrus `:=` introduces new binding in current scope (shadowing allowed with warning in `hum`) | lexical_structure_syntax_spec.md §6.3 | P0 | TODO |
| PAR-022 | `async let x = foo()` as dataflow statement (spawns task, wait-by-necessity) | lexical_structure_syntax_spec.md §5.4, morph_language_spec §4.1 LANG-REQ-024 | P1 | TODO |
| PAR-023 | Effect annotations on functions: `performs [EffectList]` or `performs IO` | morph_language_spec §6.2 LANG-REQ-040-041 | P1 | TODO |
| PAR-024 | Trait declarations and `impl` blocks | type_system_spec.md §2.5.2 | P1 | TODO |
| PAR-025 | Generic constraints: `where T: Trait` (type) vs `requires { val > 0 }` (value) — mixing is compile error | morph_language_spec §5.1 LANG-REQ-030 | P1 | TODO |
| PAR-026 | `comptime { ... }` blocks | morph_language_spec §5.2 LANG-REQ-031 | P2 | TODO |
| PAR-027 | `meta.fields(T)` introspection expressions | morph_language_spec §5.2 LANG-REQ-032 | P3 | TODO |
| PAR-028 | `?? optimize for speed/size` optimization hole syntax | morph_language_spec §5.3 LANG-REQ-033-034 | P3 | TODO |
| PAR-029 | Attribute syntax `@name` on functions/types | morph_language_spec §5.4 LANG-REQ-036 | P1 | TODO |
| PAR-030 | Contract clauses: `requires`, `ensures`, `invariant` | morph_language_spec §6.1 LANG-REQ-038 | P2 | TODO |
| PAR-031 | `unit Name;` dimensional analysis declarations | morph_language_spec §3.4 LANG-REQ-019 | P3 | TODO |
| PAR-032 | `flow` construct with `in`, `state`, `reduce` (UDF pattern) or `update`+`command` (SSUS pattern) | unidirectional_data_flow_spec.md §2.2, strict_state_unidirectional_spec.md §2.2 | P2 | TODO |
| PAR-033 | Polarity types: `<T` (Source), `>T` (Sink) in flow declarations | unidirectional_data_flow_spec.md §2.4 | P2 | TODO |
| PAR-034 | `feedback` delay buffer for explicit cycles in flow graphs | unidirectional_data_flow_spec.md §2.3.2 | P2 | TODO |
| PAR-035 | `impl From<A> for B` error conversion blocks | morph_language_spec §15.2 LANG-REQ-075 | P1 | TODO |
| PAR-036 | `panic!` macro/expression syntax | morph_language_spec §15.3 LANG-REQ-076 | P1 | TODO |
| PAR-037 | `routing` declarative block for external signal mapping | morph_language_spec §6.3 LANG-REQ-043 | P3 | TODO |
| PAR-038 | `defer` block for scope-exit cleanup | lexical_structure_syntax_spec.md §5.4 | P1 | TODO |
| PAR-039 | `with rounding(...)` blocks for financial division | morph_language_spec §8.1 LANG-REQ-052 | P3 | TODO |
| PAR-040 | `hum` dialect alternative grammar: `function`, `return`, `import`, `match()`, `case`, `let x =` | syntax_translation_spec.md §3.2 | P1 | TODO |
| PAR-041 | Struct field visibility: private by default, `pub` for public | module_system_spec.md §4.2 | P1 | TODO |
| PAR-042 | Visibility modifiers: none (private), `pub` (package), `pub(global)` (public) | module_system_spec.md §4.1, scoping_lambda_calculus_spec.md §2.3.1 | P1 | TODO |
| PAR-043 | `routing` block for URL/Socket to actor event mapping | morph_language_spec §6.3 LANG-REQ-043 | P3 | TODO |
| PAR-044 | `pure fn` function modifier | pure_type_spec.md §6.1 | P1 | TODO |
| PAR-045 | `spawn` expression for task creation | lexical_structure_syntax_spec.md §2.1 | P1 | TODO |
| PAR-046 | FFI declaration syntax (implicit blocking, `trait [NonBlocking]`) | morph_language_spec §4.3 LANG-REQ-027-028 | P2 | TODO |
| PAR-047 | `tensor<T, Dims>` type for scientific computing | morph_language_spec §8.2 LANG-REQ-055 | P4 | TODO |
| PAR-048 | `grad(f)` operator for automatic differentiation | morph_language_spec §8.2 LANG-REQ-056 | P4 | TODO |
| PAR-049 | `#[scheduling_mode(deterministic\|randomized)]` attribute for main function | scheduling_modes_spec.md §2.2.1 SCHED-REQ-003 | P2 | TODO |
| PAR-050 | `@monomorphize` attribute to force generic specialization | selective_monomorphization_spec.md §4.2.1 SMS-INV-009 | P2 | TODO |
| PAR-051 | `@generic` attribute to force dynamic dispatch | selective_monomorphization_spec.md §4.2.1 SMS-INV-010 | P2 | TODO |
| PAR-052 | `@optimize(performance\|size\|balanced)` optimization mode attribute | selective_monomorphization_spec.md §4.2.2 SMS-INV-011 | P2 | TODO |
| PAR-053 | `@monomorphize(T1, T2, ...)` selective specialization syntax | selective_monomorphization_spec.md §4.2.1 | P3 | TODO |

---

## Phase 3: Type Checker

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| TYP-001 | Scalar primitives: `bool`, `u8`..`u64`, `i8`..`i64`, `f32`, `f64`, `usize`, `isize`, `void` with fixed bit widths and OIR mappings | type_system_spec.md §2.1.1 TYP-INV-001 | P0 | TODO |
| TYP-002 | `str` (UTF-8, immutable, non-null) vs `Bytes` (^Bytes, raw u8 array) strict separation | type_system_spec.md §2.1.2 TYP-INV-002 | P0 | TODO |
| TYP-003 | `BigInt` with Small-Object Optimization (SOO): inline for register-fit, heap spill | morph_language_spec §3.1 LANG-REQ-014 | P2 | TODO |
| TYP-004 | Product types (structs) with value semantics, C-compatible layout | type_system_spec.md §2.2.1 TYP-REQ-001 | P0 | TODO |
| TYP-005 | Sum types (enums) with discriminant + max variant size; exhaustive `fix` matching required | type_system_spec.md §2.2.2 TYP-REQ-002 | P0 | TODO |
| TYP-006 | Auto-derive `Equality`, `Hash`, `Serialization` for all `type` definitions | type_system_spec.md §2.2.3 TYP-INV-004, morph_language_spec §3.2 LANG-REQ-016 | P1 | TODO |
| TYP-007 | `Result<T, E>` type as sum type `Ok \| Err` | type_system_spec.md §6.2 | P0 | TODO |
| TYP-008 | `Option<T>` / `T?` as tagged union `Some \| None` | type_system_spec.md §2.4.2 TYP-INV-007 | P0 | TODO |
| TYP-009 | Non-nullable by default: `let x: String = null` is compile error | type_system_spec.md §2.4.1 TYP-INV-006, TYP-REQ-011 | P0 | TODO |
| TYP-010 | Flow-sensitive smart casts: after `if (s != null)`, `s` promoted from `T?` to `T` | type_system_spec.md §2.4.3 TYP-REQ-005 | P1 | TODO |
| TYP-011 | Reference capabilities: `^T` (Iso/unique/move-only), `#T` (Val/shared/immutable), `&T` (Ref/local/mutable) | type_system_spec.md §2.3.1 TYP-INV-005 | P0 | TODO |
| TYP-012 | Capability transition: Freeze (`^T` → `#T`) one-way; Borrow (`^T` → `&T`) temporary | type_system_spec.md §2.3.2 TYP-REQ-003 | P0 | TODO |
| TYP-013 | Send safety: `ref` types cannot cross actor boundaries; `iso` consumed on send | morph_language_spec §3.3 LANG-REQ-018, type_system_spec.md §2.3.3 TYP-REQ-004 | P0 | TODO |
| TYP-014 | Zero-copy message passing: only Sendable types (primitives, `#Val`, consumed `^Iso`) | type_system_spec.md §2.3.3 | P0 | TODO |
| TYP-015 | Generic monomorphization: specialized code per concrete type | type_system_spec.md §2.5.1 TYP-INV-008, morph_language_spec §5.1 LANG-REQ-029 | P1 | TODO |
| TYP-016 | Trait constraints required for public generic APIs | type_system_spec.md §2.5.2 TYP-REQ-006 | P1 | TODO |
| TYP-017 | Static dispatch by default (no virtual methods) | type_system_spec.md §2.5.3 TYP-INV-009 | P1 | TODO |
| TYP-018 | Bidirectional type inference (top-down + bottom-up) | type_system_spec.md §2.7.1 TYP-INV-011 | P0 | TODO |
| TYP-019 | `:=` infers type from RHS: `x := 10` → `i32` | type_system_spec.md §2.7.1 | P0 | TODO |
| TYP-020 | Return type inference from body expressions | type_system_spec.md §2.7.1 | P1 | TODO |
| TYP-021 | Literal coercion: `let x: u8 = 10` infers `10` as `u8` | type_system_spec.md §2.7.1 | P1 | TODO |
| TYP-022 | Affine type inference optimization: dead `val` vars promoted to mutable in backend | type_system_spec.md §2.7.2 TYP-REQ-009 | P3 | TODO |
| TYP-023 | Type unification via Robinson's algorithm: decomposition, orientation, elimination | type_unification_spec.md §2.3 | P0 | TODO |
| TYP-024 | Occurs check: prevent infinite types (`α = List<α>`) | type_unification_spec.md §2.5 TYPUNI-REQ-002/004 | P0 | TODO |
| TYP-025 | Most General Unifier (MGU) computation; uniqueness modulo variable renaming | type_unification_spec.md §2.4 TYPUNI-THM-001/003 | P1 | TODO |
| TYP-026 | Acyclic type definitions: no circular type definitions | type_system_spec.md §5.2.2 TYP-INV-013 | P0 | TODO |
| TYP-027 | `void` as terminal object (unit type) | type_category_spec.md §1.1 | P0 | TODO |
| TYP-028 | `??` as placeholder type for optimization search | type_system_spec.md §2.1.3 TYP-INV-003 | P3 | TODO |
| TYP-029 | Type safety theorem: type-checked programs are type-safe (structural induction) | type_system_spec.md §5.1.1 TYP-THM-001 | P0 | TODO |
| TYP-030 | Memory safety theorem: capability-checked programs are memory-safe | type_system_spec.md §5.1.2 TYP-THM-002 | P0 | TODO |
| TYP-031 | Iso variables are unique (no aliases) | type_system_spec.md §5.2.2 TYP-INV-015 | P0 | TODO |
| TYP-032 | Ref variables are local (non-sendable) | type_system_spec.md §5.2.2 TYP-INV-016 | P0 | TODO |
| TYP-033 | Val variables are immutable | type_system_spec.md §5.2.2 TYP-INV-017 | P0 | TODO |
| TYP-034 | All variables have valid types | type_system_spec.md §5.2.1 TYP-INV-012 | P0 | TODO |
| TYP-035 | Generic constraints are satisfied at instantiation sites | type_system_spec.md §5.2.1 TYP-INV-014 | P1 | TODO |
| TYP-036 | `??` null-coalescing operator: `T? ?? T → T` type rule | operator_null_coalescing_spec.md §2.3 NCO-REQ-001/004 | P0 | TODO |
| TYP-037 | `??` short-circuit: RHS not evaluated when LHS non-null | operator_null_coalescing_spec.md §2.6 NCO-REQ-002/003 | P0 | TODO |
| TYP-038 | `??` type inference: result type = RHS base type | operator_null_coalescing_spec.md §2.3.3 NCO-REQ-005 | P1 | TODO |
| TYP-039 | `??` flow-sensitive narrowing after non-null result | operator_null_coalescing_spec.md §2.5.3 NCO-REQ-007 | P2 | TODO |
| TYP-040 | `??` nested/right-associative: `a ?? b ?? c` = `a ?? (b ?? c)` | operator_null_coalescing_spec.md §2.1 NCO-REQ-008 | P1 | TODO |
| TYP-041 | `??` effect tracking: effect = effect of evaluated operand (short-circuit) | operator_null_coalescing_spec.md §2.4 NCO-REQ-006 | P1 | TODO |
| TYP-042 | Effect taxonomy: Pure (capability), IO, Net, Time, System (lattice) | morph_language_spec §6.2 LANG-REQ-040, effect_system_spec.md §2.2 EFF-REQ-001 | P0 | TODO |
| TYP-043 | Effect lattice: IO ⊆ Net ⊆ Time ⊆ System (complete lattice) | effect_system_spec.md §2.3 EFF-REQ-002 | P1 | TODO |
| TYP-044 | Pure is a capability (not an effect), orthogonal to effect lattice | pure_type_spec.md §2.1, §2.4 | P0 | TODO |
| TYP-045 | Pure functions: referential transparency, no side effects, deterministic | pure_type_spec.md §2.2 PURE-REQ-001/002/003 | P0 | TODO |
| TYP-046 | Pure functions cannot call effectful functions | pure_type_spec.md §5.2 PURE-INV-004 | P0 | TODO |
| TYP-047 | Pure function cannot perform I/O, mutate external state, access network/clock/system | pure_type_spec.md §5.2 PURE-INV-005-009 | P0 | TODO |
| TYP-048 | Effect inference: auto-derive effect sets from function bodies | effect_system_spec.md §4.4 EFF-REQ-005 | P1 | TODO |
| TYP-049 | Effect propagation: calling IO function adds IO to caller's effect set | type_system_spec.md §2.6.2 TYP-REQ-007 | P0 | TODO |
| TYP-050 | Effect bounds enforcement: `performs [Pure]` body cannot call IO | type_system_spec.md §2.6.3 TYP-REQ-008 | P0 | TODO |
| TYP-051 | Effect algebra operations: union (∪), intersection (∩), difference (\) | effect_system_spec.md §2.4 EFF-REQ-003 | P1 | TODO |
| TYP-052 | Effect subtyping: E1 ⊆ E2 ⟹ safe substitution | effect_system_spec.md §2.3.1 EFF-REQ-004 | P1 | TODO |
| TYP-053 | Effect polymorphism: universal/existential quantification over effect variables | effect_system_spec.md §2.6 EFF-REQ-006 | P2 | TODO |
| TYP-054 | Effect-based security level mapping: IO→Internal, Net→Confidential, Time→Secret, System→TopSecret | effect_system_spec.md §4.5 EFF-REQ-008 | P3 | TODO |
| TYP-055 | Effect monotonicity: effects never decrease during inference | effect_system_spec.md §5.2.1 EFF-INV-004 | P1 | TODO |
| TYP-056 | Scoping: nested environments with parent chain; innermost binding wins | scoping_lambda_calculus_spec.md §2.1-2.2 SC-REQ-001/002 | P0 | TODO |
| TYP-057 | Visibility enforcement: Private (module), Pub (package), Pub(Global) (always) | scoping_lambda_calculus_spec.md §2.3 SC-REQ-003/004 | P1 | TODO |
| TYP-058 | Shadowing via `:=` creates new environment binding; outer binding preserved | scoping_lambda_calculus_spec.md §2.4 SC-REQ-005, SC-THM-003 | P0 | TODO |
| TYP-059 | `use` statements build implicit dependency graph from AST (no build scripts) | morph_language_spec §7.1 LANG-REQ-045 | P1 | TODO |
| TYP-060 | Content-addressable linking by AST hash, not file name | module_system_spec.md §2.1 | P2 | TODO |
| TYP-061 | Diamond dependencies: both versions included with symbol mangling | module_system_spec.md §5.2 | P2 | TODO |
| TYP-062 | `?` error propagation: desugars to match on Result, early return on Err | morph_language_spec §15.2 LANG-REQ-116, monadic_effect_spec.md §3.1 | P0 | TODO |
| TYP-063 | `From<A> for B` trait for automatic error conversion | morph_language_spec §15.2 LANG-REQ-075 | P1 | TODO |
| TYP-064 | Error context/backtrace preservation during propagation | morph_language_spec §15.2 LANG-REQ-074 | P1 | TODO |
| TYP-065 | Actor isolation: panics don't cross actor boundaries by default | morph_language_spec §15.3 LANG-REQ-079 | P1 | TODO |
| TYP-066 | Unit algebra: `unit Name;` defines dimension; `f64<Meter>` erased to `f64` at runtime | morph_language_spec §3.4 LANG-REQ-019/020/021 | P3 | TODO |
| TYP-067 | `@gpu` attribute bans System I/O in function scope | morph_language_spec §5.4 LANG-REQ-037 | P3 | TODO |
| TYP-068 | `@critical` attribute enforces zero-allocation, thread-pinned execution | morph_language_spec §8.1 LANG-REQ-053 | P3 | TODO |
| TYP-069 | `flow` reducer must be pure (effect system enforcement) | unidirectional_data_flow_spec.md §2.3.3 UDF-REQ-003 | P2 | TODO |
| TYP-070 | `flow` update/command functions must be pure | strict_state_unidirectional_spec.md §2.4 SSUS-REQ-002/004 | P2 | TODO |
| TYP-071 | Flow DAG topology check: reject cycles at compile time | unidirectional_data_flow_spec.md §2.3.1 UDF-THM-001 | P2 | TODO |
| TYP-072 | Polarity type enforcement: `<T` read-only source, `>T` write-only sink | unidirectional_data_flow_spec.md §2.4 UDF-REQ-004/005 | P2 | TODO |
| TYP-073 | Type checking O(n) where n = AST size (< 100ms for 10K nodes) | type_system_spec.md §3.2 TYP-NFR-001 | P1 | TODO |
| TYP-074 | Weak reference type `Weak<T>` for cycle-breaking; upgrade returns `Option<Val<T>>` | memory_model_spec.md §2.5 MMS-INV-010/011 | P1 | TODO |
| TYP-075 | Type-level cycle detection in recursive struct definitions | memory_model_spec.md §2.6.2 MMS-INV-027 | P1 | TODO |
| TYP-076 | Monadic effect system: block syntax desugars to `>>=` bind; effect set accumulates | monadic_effect_spec.md §1-2 | P1 | TODO |
| TYP-077 | `Result` monad: `?` operator as bind restricted to failure path; satisfies monad laws | monadic_effect_spec.md §3 | P0 | TODO |
| TYP-078 | Impure statements must not be reordered (Kleisli non-commutativity) | monadic_effect_spec.md §2.1 | P1 | TODO |
| TYP-079 | Compile-time deadlock detection: build wait-for graph from `async let` dependencies, reject cycles | concurrency_process_algebra_spec.md §3.1 CON-REQ-004 | P1 | TODO |
| TYP-080 | Compile-time affine type checking: detect use-after-move, enforce context splitting | arc_affine_integration_spec.md §2.2 ARC-AAI-INV-004/005 | P0 | TODO |
| TYP-081 | Strong reference graph is a DAG (acyclicity theorem) | arc_affine_integration_spec.md §2.4.3 ARC-AAI-THM-002 | P0 | TODO |
| TYP-082 | Iso type cannot form reference cycles (compile-time enforcement) | arc_affine_integration_spec.md §2.4.1 ARC-AAI-THM-001 | P0 | TODO |
| TYP-083 | No use-after-free guarantee via affine type checker | arc_affine_integration_spec.md §2.5.1 ARC-AAI-THM-003 | P0 | TODO |
| TYP-084 | Layered concurrency: pure function enforcement for application layer reducers | layered_concurrency_spec.md §3.1 LCA-REQ-004/009 | P2 | TODO |
| TYP-085 | Dialect isomorphism: min and hum are isomorphic representations of same AST | dialect_projection_spec.md §3.1 DIA-REQ-007/008 | P1 | TODO |
| TYP-086 | Mailbox FIFO ordering within each actor | concurrency_process_algebra_spec.md §5.2 CON-INV-002 | P1 | TODO |
| TYP-087 | Messages are not duplicated or lost (communication invariants) | concurrency_process_algebra_spec.md §5.2 CON-INV-003/004 | P1 | TODO |

---

## Phase 4: Code Generation

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| CG-001 | MorphIR generation: platform-agnostic bytecode (`.mar` libraries) | morph_language_spec §7.3 LANG-REQ-049 | P1 | TODO |
| CG-002 | Consumer-side final machine code generation for ABI stability | morph_language_spec §7.3 LANG-REQ-050 | P1 | TODO |
| CG-003 | Monomorphization: generate specialized code per concrete generic type | morph_language_spec §5.1 LANG-REQ-029, type_system_spec.md TYP-REQ-014 | P1 | TODO |
| CG-004 | Static dispatch for all method calls (no vtables) | type_system_spec.md §2.5.3 TYP-INV-009 | P1 | TODO |
| CG-005 | Arena allocation for actor-local scope (freed O(1) at message completion) | morph_language_spec §4.2 LANG-REQ-025 | P0 | TODO |
| CG-006 | ARC for `#Val` shared types (atomic reference counting) | morph_language_spec §4.2 LANG-REQ-025 | P0 | TODO |
| CG-007 | Zero-copy transitions between capability types (metadata bit-flip) | memory_model_spec.md §2.1.3 MMS-INV-003 | P1 | TODO |
| CG-008 | Zero-copy move semantics for affine types (pointer transfer) | memory_model_spec.md §2.4.2 MMS-INV-009 | P1 | TODO |
| CG-009 | Unit type erasure: `f64<Meter>` compiles to raw `f64` | morph_language_spec §3.4 LANG-REQ-021 | P3 | TODO |
| CG-010 | Preemption checkpoints injected at loop headers and function entries | execution_model_spec.md §2.2.5 EMS-REQ-007 | P1 | TODO |
| CG-011 | Affine dead-variable optimization: promote dead `val` to mutable in backend | type_system_spec.md §2.7.2 TYP-REQ-009 | P3 | TODO |
| CG-012 | Contracts as optimization hints in release mode (`llvm.assume`) | morph_language_spec §6.1 LANG-REQ-039 | P3 | TODO |
| CG-013 | Stream fusion: linear flow chains compiled into single function/actor | unidirectional_data_flow_spec.md §2.5.2 UDF-REQ-007 | P2 | TODO |
| CG-014 | `comptime` block execution during semantic analysis phase | morph_language_spec §5.2 LANG-REQ-031 | P2 | TODO |
| CG-015 | `meta.fields(T)` reflection for code generation | morph_language_spec §5.2 LANG-REQ-032 | P3 | TODO |
| CG-016 | Optimization Search Engine: `??` resolved by hill climbing/grid search | morph_language_spec §5.3 LANG-REQ-033/034 | P3 | TODO |
| CG-017 | `morph.lock` caching for reproducible builds | morph_language_spec §5.3 LANG-REQ-035 | P2 | TODO |
| CG-018 | Implicit suspension: I/O functions auto-yield green thread (fiber) | morph_language_spec §4.1 LANG-REQ-023 | P1 | TODO |
| CG-019 | Struct layout: C-compatible (ordered, packed by alignment) | type_system_spec.md §2.2.1 | P1 | TODO |
| CG-020 | Sum type layout: discriminant (u8) + max(variant size) | type_system_spec.md §2.2.2 | P0 | TODO |
| CG-021 | Data layout definition for all types: (size, alignment, fields) | memory_model_spec.md §2.8.1 MMS-INV-016 | P1 | TODO |
| CG-022 | BigInt Small-Object Optimization: inline for register-fit, heap spill | morph_language_spec §3.1 LANG-REQ-014 | P2 | TODO |
| CG-023 | Bidirectional min↔hum translation with O(n) complexity, semantic equivalence | syntax_translation_spec.md §6 SYN-REQ-001/005/008/009 | P1 | TODO |
| CG-024 | Keyword translation: `fn`↔`function`, `ret`↔`return`, `use`↔`import`, `act`↔`actor`, `fix`↔`match` | syntax_translation_spec.md §4.1 SYN-REQ-002 | P1 | TODO |
| CG-025 | Type name translation: `i32`↔`Int32`, `str`↔`String`, etc. | syntax_translation_spec.md §4.2 SYN-REQ-003 | P1 | TODO |
| CG-026 | Operator translation: `:=` ↔ `let ... =`, `->` ↔ `:` in signatures | syntax_translation_spec.md §4.3 SYN-REQ-004 | P1 | TODO |
| CG-027 | Round-trip property: min→hum→min yields semantically equivalent code | syntax_translation_spec.md §7.2 SYN-REQ-006 | P1 | TODO |
| CG-028 | `@fuzz` auto-generates fuzz tests using type + contract definitions | morph_language_spec §6.4 LANG-REQ-044 | P4 | TODO |
| CG-029 | Content-addressable storage: code referenced by AST hash | morph_language_spec §9.4 LANG-REQ-073 | P2 | TODO |
| CG-030 | MorphUI IR: platform-independent vector command buffer for rendering | morph_language_spec §8.3 LANG-REQ-060 | P4 | TODO |
| CG-031 | Selective monomorphization: cost-benefit decision per generic function instantiation | selective_monomorphization_spec.md §2.3 SMS-INV-007 | P2 | TODO |
| CG-032 | Hot path detection: profiling-based + static analysis (loop, recursive, caller) | selective_monomorphization_spec.md §4.3 SMS-INV-012/013 | P2 | TODO |
| CG-033 | Code sharing for identical monomorphizations (deduplication) | selective_monomorphization_spec.md §4.4 SMS-INV-014/015 | P2 | TODO |
| CG-034 | Binary size budget validation with clear error messages | selective_monomorphization_spec.md §4.6 SMS-INV-019/020 | P2 | TODO |
| CG-035 | VTable generation for dynamically dispatched generic functions | selective_monomorphization_spec.md §2.2 SMS-INV-004 | P2 | TODO |
| CG-036 | Affine dead-variable optimization: promote dead val to mutable in backend | arc_affine_integration_spec.md §2.6.3 ARC-AAI-INV-012 | P2 | TODO |
| CG-037 | Projectional editing: LSP render/parse functions for min and hum dialects | dialect_projection_spec.md §4.2 DIA-REQ-013/014/015 | P3 | TODO |
| CG-038 | Incremental rendering: only re-render modified AST subtrees for projections | dialect_projection_spec.md §9.2 | P3 | TODO |

---

## Phase 5: Runtime Support

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| RT-001 | Bare-metal runtime library (MRE) statically linked into executable | execution_model_spec.md §2.1.1 EMS-REQ-001 | P0 | TODO |
| RT-002 | Stackful coroutines (fibers) as fundamental execution unit; 4KB starting stack | execution_model_spec.md §2.1.2 EMS-REQ-002 | P0 | TODO |
| RT-003 | M:N scheduling: M fibers on N OS threads (executors) | execution_model_spec.md §2.2.1 EMS-INV-004 | P0 | TODO |
| RT-004 | Work-stealing scheduler (production): Chase-Lev deque, random victim selection | execution_model_spec.md §2.2.1 EMS-REQ-005/018 | P0 | TODO |
| RT-005 | Deterministic scheduler (debug only): FIFO, via link-time replacement | execution_model_spec.md §2.2.2 EMS-REQ-006/007 | P2 | TODO |
| RT-006 | Link-time scheduler selection (`--debug-scheduler` flag); never both in binary | execution_model_spec.md §2.2.3 EMS-REQ-003/004/008/009/010 | P1 | TODO |
| RT-007 | IO-aware implicit suspension: intercept syscall → register with OS poller → switch fiber | execution_model_spec.md §2.2.4 EMS-REQ-015 | P0 | TODO |
| RT-008 | Preemption via compiler-injected checkpoints at loop headers/function entries | execution_model_spec.md §2.2.5 EMS-REQ-007 | P1 | TODO |
| RT-009 | Actors as stateful fibers with MPSC mailboxes | execution_model_spec.md §2.3.1 EMS-REQ-008, §2.1.3 EMS-REQ-018 | P0 | TODO |
| RT-010 | Sequential message processing within actor (data race freedom) | execution_model_spec.md §2.3.1 | P0 | TODO |
| RT-011 | Supervision trees: OneForOne, OneForAll strategies for actor failure recovery | execution_model_spec.md §2.3.2 EMS-REQ-009/028 | P1 | TODO |
| RT-012 | Dataflow parallelism: `async let x = foo()` spawns task; wait-by-necessity on access | morph_language_spec §4.1 LANG-REQ-024 | P1 | TODO |
| RT-013 | Unified global allocator: single allocator for all memory (stack, arena, heap) | memory_model_spec.md §2.1.1 MMS-INV-001 | P0 | TODO |
| RT-014 | No tracing GC: ARC only with deterministic deallocation | memory_model_spec.md §2.7 MMS-REQ-013, morph_language_spec §4.2 LANG-REQ-026 | P0 | TODO |
| RT-015 | Arc<T> control block: 32 bytes, cache-line aligned, atomic ref counting | memory_model_spec.md §4.4.1 MMS-INV-032/033/034 | P0 | TODO |
| RT-016 | Stack layout with guard pages for overflow detection | memory_model_spec.md §2.8.2 MMS-REQ-016 | P1 | TODO |
| RT-017 | Sequential consistency within single actor | memory_model_spec.md §2.6 MMS-INV-013 | P0 | TODO |
| RT-018 | Happens-before relations: message send ≺ receive, spawn ≺ first instruction, complete ≺ await | memory_model_spec.md §2.6.1 MMS-INV-012 | P0 | TODO |
| RT-019 | Weak reference upgrade: `Weak<T> → Option<Val<T>>` via atomic CAS | memory_model_spec.md §2.5 MMS-REQ-010 | P1 | TODO |
| RT-020 | Runtime cycle detection tools: `detect_cycles()`, `analyze_cycles()`, `break_cycle()` | memory_model_spec.md §2.6.5 MMS-REQ-017 | P2 | TODO |
| RT-021 | Pessimistic FFI: foreign calls dispatched to OS thread pool (assume blocking) | morph_language_spec §4.3 LANG-REQ-027 | P1 | TODO |
| RT-022 | `trait [NonBlocking]` for FFI on green thread scheduler | morph_language_spec §4.3 LANG-REQ-028 | P2 | TODO |
| RT-023 | Implicit `ctx` propagation for deadline management and cancellation | morph_language_spec §6.3 LANG-REQ-042 | P1 | TODO |
| RT-024 | Panic propagation: fiber termination → actor supervisor notification | morph_language_spec §15.3 LANG-REQ-076/079 | P1 | TODO |
| RT-025 | Credit-based backpressure for reactive streams | unidirectional_data_flow_spec.md §2.5.1 UDF-REQ-006 | P2 | TODO |
| RT-026 | SSUS command executor: runtime executes command descriptors asynchronously | strict_state_unidirectional_spec.md §2.3.2 SSUS-REQ-003 | P2 | TODO |
| RT-027 | `@critical` mode: zero-allocation, thread-pinned, kernel bypass | morph_language_spec §8.1 LANG-REQ-053 | P3 | TODO |
| RT-028 | `@auditable` immutable logging sidecar for state mutations | morph_language_spec §8.1 LANG-REQ-054 | P3 | TODO |
| RT-029 | Input ring buffer for deterministic replay debugging | morph_language_spec §9.4 LANG-REQ-072 | P2 | TODO |
| RT-030 | `morph audit` SPDX SBOM generation | morph_language_spec §9.3 LANG-REQ-070 | P3 | TODO |
| RT-031 | License policy gating: build fails on dependency violations | morph_language_spec §9.3 LANG-REQ-068 | P2 | TODO |
| RT-032 | Morph Canonical Input Events (MCIE): runtime exposes only normalized events | morph_language_spec §9.4 LANG-REQ-071 | P2 | TODO |
| RT-033 | Growable fiber stacks (starting 4KB, expandable) | execution_model_spec.md §2.1.2 EMS-REQ-002 | P0 | TODO |
| RT-034 | Lock-free MPSC queue for actor mailboxes | execution_model_spec.md §2.3.1.1.4 EMS-REQ-027 | P1 | TODO |
| RT-035 | Deterministic RNG with fixed seed for debug scheduler | execution_model_spec.md §2.2.2 EMS-REQ-023 | P2 | TODO |
| RT-036 | Execution trace for reproducibility verification | execution_model_spec.md §2.2.2 EMS-REQ-024 | P2 | TODO |
| RT-037 | Deterministic scheduling: round-robin victim selection, fixed random seed, logical clock | scheduling_modes_spec.md §2.1.1 SCHED-REQ-001/006/008 | P2 | TODO |
| RT-038 | Runtime mode switching API: setSchedulingModeDeterministic/Randomized with safety constraints | scheduling_modes_spec.md §2.2.2 SCHED-REQ-004/010 | P2 | TODO |
| RT-039 | Deterministic mode default for debug builds; randomized default for release | scheduling_modes_spec.md §2.3 SCHED-INV-006, SCHED-REQ-005 | P1 | TODO |
| RT-040 | Mailbox backpressure: block sender when receiver mailbox is full | concurrency_process_algebra_spec.md §3.1 CON-REQ-003 | P1 | TODO |
| RT-041 | Compile-time deadlock detection → runtime deadlock freedom guarantee | concurrency_process_algebra_spec.md §2.3 CON-THM-001 | P1 | TODO |
| RT-042 | Eventual message delivery in live (deadlock-free) systems | concurrency_process_algebra_spec.md §5.1 CON-THM-002 | P1 | TODO |
| RT-043 | ARC O(1) operations: retain, release, weak_retain, weak_release, weak upgrade | arc_affine_integration_spec.md §2.6.1 ARC-AAI-INV-011 | P0 | TODO |
| RT-044 | ARC bounded latency: no stop-the-world, no heap traversal | arc_affine_integration_spec.md §2.6.2 ARC-AAI-THM-006 | P1 | TODO |
| RT-045 | Zero-copy move semantics for Iso types (pointer transfer) | arc_affine_integration_spec.md §4.3 ARC-AAI-INV-012 | P0 | TODO |
| RT-046 | Layer boundary: zero-copy message passing between application and concurrency layers | layered_concurrency_spec.md §3.2 LCA-NFR-004 | P2 | TODO |

---

## Phase 6: AST Graph (Merkle DAG)

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| AST-001 | AST as Typed, Ordered, Rooted, Merkle DAG: G=(V,E,μ,τ,ω) | ast_graph_spec.md §2.1 | P0 | TODO |
| AST-002 | Acyclicity invariant: AST graph contains no cycles | ast_graph_spec.md §2.2.1 AST-INV-001 | P0 | TODO |
| AST-003 | Single root invariant: exactly one Module root node | ast_graph_spec.md §2.2.2 AST-INV-002 | P0 | TODO |
| AST-004 | Merkle hash: μ(v) = SHA256(Content(v) ∥ μ(c₁) ∥ ... ∥ μ(cₙ)) | ast_graph_spec.md §2.2.3 AST-INV-003 | P0 | TODO |
| AST-005 | Node taxonomy: Structural (Module, Block, impl, trait), Nominal (FnDecl, TypeDecl, ActDecl, ConstDecl), Expression (BinaryOp, Call, Literal, Match, Return) | ast_graph_spec.md §2.3 | P0 | TODO |
| AST-006 | Nominal node hash uniqueness within parent scope | ast_graph_spec.md §2.3.2 AST-INV-004 | P1 | TODO |
| AST-007 | Ancestor hash recomputation on node modification | ast_graph_spec.md §3.1 AST-REQ-002 | P0 | TODO |
| AST-008 | Edge deletion cleanup: remove all edges referencing deleted node | ast_graph_spec.md §3.1 AST-REQ-003 | P1 | TODO |
| AST-009 | Deterministic edge ordering for children | ast_graph_spec.md §3.1 AST-REQ-005 | P0 | TODO |
| AST-010 | Max 1000 children per node limit | ast_graph_spec.md §6.4.2 AST-INV-011 | P2 | TODO |
| AST-011 | Refactoring semantic equivalence verification | ast_graph_spec.md §4.4.1 AST-REQ-006 | P2 | TODO |
| AST-012 | Equal root hashes imply identical AST structures | ast_graph_spec.md §5.1.1 AST-THM-001 | P0 | TODO |
| AST-013 | Node hash cache: O(1) for cached nodes, < 1μs per node | ast_graph_spec.md §3.2 AST-NFR-001 | P1 | TODO |
| AST-014 | Cycle detection in O(V+E), < 100ms for 100K nodes | ast_graph_spec.md §3.2 AST-NFR-003 | P1 | TODO |
| AST-015 | Support AST graphs up to 1,000,000 nodes, < 1GB memory | ast_graph_spec.md §3.2 AST-NFR-002 | P2 | TODO |

---

## Phase 7: Security (Compile-Time)

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| SEC-001 | Security lattice: (Public, Confidential, Secret) × (Low, High integrity) | security_flow_spec.md §2.1 | P2 | TODO |
| SEC-002 | Non-interference enforcement: high-security data cannot affect low-security outputs | security_flow_spec.md §2.2.2 SFS-INV-004 | P1 | TODO |
| SEC-003 | Type-based taint tracking at compile time | security_flow_spec.md §2.2, §3.1 | P2 | TODO |
| SEC-004 | Capability-based access control: Capability = (resource, permissions) | security_flow_spec.md §2.3 SFS-INV-005 | P2 | TODO |
| SEC-005 | Message security: level(m) ≤ level(receiver) | security_flow_spec.md §2.4.1 SFS-INV-007 | P1 | TODO |
| SEC-006 | Declassification/endorsement annotations for controlled security level changes | security_flow_spec.md §3.1.2 | P3 | TODO |
| SEC-007 | Side channel analysis: timing, cache, covert channel threat detection | security_flow_spec.md §2.7 SFS-INV-016-020 | P3 | TODO |
| SEC-008 | Constant-time execution enforcement for security-sensitive operations | security_flow_spec.md §2.7.2 SFS-INV-017 | P3 | TODO |
| SEC-009 | Taint check before capability check (precedence order) | security_flow_spec.md §2.6.2 SFS-INV-012 | P2 | TODO |
| SEC-010 | Object capability (OCap) security model integration | security_ocap_spec.md | P2 | TODO |

---

## Phase 8: Build System

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| BLD-001 | Build lattice: partial order on build artifacts with dependency relations | build_lattice_spec.md §2.1 BLS-INV-001 | P1 | TODO |
| BLD-002 | Incremental compilation: detect changes via timestamp + hash comparison | build_lattice_spec.md §2.2.1 BLS-INV-003 | P1 | TODO |
| BLD-003 | Rebuild all dependent artifacts on change | build_lattice_spec.md §2.2.2 BLS-INV-004 | P1 | TODO |
| BLD-004 | Build artifact cache with hit/miss optimization | build_lattice_spec.md §2.3 BLS-INV-005/006 | P2 | TODO |
| BLD-005 | Topological sort for correct build order | build_lattice_spec.md §2.4.1 BLS-INV-007 | P1 | TODO |
| BLD-006 | Parallel execution of independent build artifacts | build_lattice_spec.md §2.4.2 BLS-INV-008 | P2 | TODO |
| BLD-007 | Circular dependency detection at build time | build_lattice_spec.md §6.4.1 | P1 | TODO |
| BLD-008 | Incremental build change detection: O(n), < 1ms per artifact | build_lattice_spec.md §3.2 BLS-NFR-001 | P2 | TODO |
| BLD-009 | Content-addressable linking by AST hash (not file name) | module_system_spec.md §2.1 | P2 | TODO |
| BLD-010 | Dependency satisfaction via SAT solver | dependency_sat_spec.md | P2 | TODO |

---

## Cross-Cutting: Error Handling

| ID | Requirement | Spec Source | Priority | Status |
|----|-------------|-------------|----------|--------|
| ERR-001 | Complete error type hierarchy: CompileError, SyntaxError, LexicalError, ParseError, TypeError, UnificationError, EffectError (compile-time); ContractViolation, Panic, RuntimeError, SystemError, IOError, NetworkError, TimeoutError, CancellationError, MemoryError, ConcurrencyError, ActorError, MessageError, FFIError, SecurityError, CapabilityError (runtime) | morph_language_spec §15 LANG-REQ-114 | P0 | TODO |
| ERR-002 | Unique error codes per category: `ERR_COMPILE_*`, `ERR_TYPE_*`, `ERR_RUNTIME_*`, etc. | morph_language_spec §15 LANG-REQ-115 | P1 | TODO |
| ERR-003 | Structured diagnostics as JSON: `node_id`, `context`, `suggested_fixes` | morph_language_spec §9.1 LANG-REQ-065 | P1 | TODO |

---

## Summary Statistics

| Phase | P0 | P1 | P2 | P3 | P4 | Total |
|-------|----|----|----|----|----|-------|
| Phase 1: Lexer | 22 | 7 | 4 | 3 | 0 | 39 |
| Phase 2: Parser | 17 | 15 | 15 | 7 | 2 | 53 |
| Phase 3: Type Checker | 34 | 32 | 13 | 7 | 0 | 87 |
| Phase 4: Code Gen | 5 | 13 | 12 | 8 | 1 | 38 |
| Phase 5: Runtime | 16 | 15 | 10 | 3 | 0 | 42 |
| Phase 6: AST Graph | 6 | 5 | 2 | 0 | 0 | 15 |
| Phase 7: Security | 0 | 2 | 4 | 3 | 0 | 10 |
| Phase 8: Build System | 0 | 4 | 4 | 0 | 0 | 10 |
| Cross-cutting | 1 | 2 | 0 | 0 | 0 | 3 |
| **Total** | **101** | **95** | **64** | **31** | **3** | **297** |
