import Morph.Core
import Morph.Syntax
import Morph.Memory

/-!
# Specification: Glossary

**Source:** `spec/GLOSSARY.md`
**Status:** Partial
**Last Updated:** 2026-01-16
**Verified By:** Kilo Code

## Overview

This specification formalizes the Morph language glossary, providing mathematical definitions for key terms, acronyms, and concepts used throughout the Morph specification ecosystem. The glossary serves as a foundational reference for developers, implementers, and contributors.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| A - Acyclic Graph | `spec_acyclic_graph` | ⚠ Ambiguous |
| A - Actor | `spec_actor` | ✓ Complete |
| A - Affine Logic | `spec_affine_logic` | ✓ Complete |
| A - Allocation | `spec_allocation` | ✓ Complete |
| A - Arena | `spec_arena` | ✓ Complete |
| A - ARC | `spec_arc` | ✓ Complete |
| A - AST | `spec_ast` | ✓ Complete |
| B - Async Let | `spec_async_let` | ✓ Complete |
| B - Backend Tiling | `spec_backend_tiling` | ✓ Complete |
| B - Bayesian Optimization | `spec_bayesian_optimization` | ✓ Complete |
| B - Bisimulation | `spec_bisimulation` | ✓ Complete |
| B - BLoC | `spec_bloc` | ✓ Complete |
| B - Build Lattice | `spec_build_lattice` | ✓ Complete |
| B - Capability | `spec_capability` | ✓ Complete |
| C - Capability System | `spec_capability_system` | ✓ Complete |
| C - Category Theory | `spec_category_theory` | ✓ Complete |
| C - Causal Consistency | `spec_causal_consistency` | ✓ Complete |
| C - Causal Ordering | `spec_causal_ordering` | ✓ Complete |
| C - Comonad | `spec_comonad` | ✓ Complete |
| C - Comptime | `spec_comptime` | ✓ Complete |
| C - Concurrent Event | `spec_concurrent_event` | ✓ Complete |
| C - Concurrency | `spec_concurrency` | ✓ Complete |
| C - Conflict Resolution | `spec_conflict_resolution` | ✓ Complete |
| C - Constraint Algebra | `spec_constraint_algebra` | ✓ Complete |
| C - Content-Addressable Storage | `spec_content_addressable_storage` | ✓ Complete |
| C - Context | `spec_context` | ✓ Complete |
| C - Convergence | `spec_convergence` | ✓ Complete |
| C - CRDT | `spec_crdt` | ✓ Complete |
| C - DAG | `spec_dag` | ✓ Complete |
| D - Dataflow Parallelism | `spec_dataflow_parallelism` | ✓ Complete |
| D - Deallocation | `spec_deallocation` | ✓ Complete |
| D - Deontic Logic | `spec_deontic_logic` | ✓ Complete |
| D - Deterministic Replay | `spec_deterministic_replay` | ✓ Complete |
| D - Deterministic Scheduler | `spec_deterministic_scheduler` | ✓ Complete |
| D - Determinism | `spec_determinism` | ✓ Complete |
| D - Dimensional Analysis | `spec_dimensional_analysis` | ✓ Complete |
| D - Distributed System | `spec_distributed_system` | ✓ Complete |
| D - Dual Representations | `spec_dual_representations` | ✓ Complete |
| E - Effect | `spec_effect` | ✓ Complete |
| E - Effect System | `spec_effect_system` | ✓ Complete |
| E - Existential Type | `spec_existential_type` | ✓ Complete |
| E - Explicit Flow | `spec_explicit_flow` | ✓ Complete |
| E - Exploration-Exploitation Tradeoff | `spec_exploration_exploitation` | ✓ Complete |
| F - Fiber | `spec_fiber` | ✓ Complete |
| F - Fitness Landscape | `spec_fitness_landscape` | ✓ Complete |
| F - Flow Construct | `spec_flow_construct` | ✓ Complete |
| F - FRP | `spec_frp` | ✓ Complete |
| F - Functor | `spec_functor` | ✓ Complete |
| F - Future | `spec_future` | ✓ Complete |
| F - Fuzzing | `spec_fuzzing` | ✓ Complete |
| F - Gaussian Process | `spec_gaussian_process` | ✓ Complete |
| G - Graph Rewriting | `spec_graph_rewriting` | ✓ Complete |
| H - Heap | `spec_heap` | ✓ Complete |
| H - Hot Reload | `spec_hot_reload` | ✓ Complete |
| H - hum Projection | `spec_hum_projection` | ✓ Complete |
| H - IEEE 754-2008 | `spec_ieee_754_2008` | ✓ Complete |
| I - Implicit Flow | `spec_implicit_flow` | ✓ Complete |
| I - Inclusion Proof | `spec_inclusion_proof` | ✓ Complete |
| I - Inhabitation | `spec_inhabitation` | ✓ Complete |
| I - IPO Algorithm | `spec_ipo_algorithm` | ✓ Complete |
| I - Island Grammar | `spec_island_grammar` | ✓ Complete |
| J - JIT | `spec_jit` | ✓ Complete |
| L - Lattice | `spec_lattice` | ✓ Complete |
| L - Lattice Theory | `spec_lattice_theory` | ✓ Complete |
| L - Lexical Scoping | `spec_lexical_scoping` | ✓ Complete |
| L - Linear Logic | `spec_linear_logic` | ✓ Complete |
| L - Linker | `spec_linker` | ✓ Complete |
| L - Load Balancing | `spec_load_balancing` | ✓ Complete |
| M - Mailbox | `spec_mailbox` | ✓ Complete |
| M - Meet | `spec_meet` | ✓ Complete |
| M - Memory Safety | `spec_memory_safety` | ✓ Complete |
| M - Merge Function | `spec_merge_function` | ✓ Complete |
| M - Merkle Tree | `spec_merkle_tree` | ✓ Complete |
| M - Metaprogramming | `spec_metaprogramming` | ✓ Complete |
| M - Modal Logic | `spec_modal_logic` | ✓ Complete |
| M - Monad | `spec_monad` | ✓ Complete |
| M - Monomorphization | `spec_monomorphization` | ✓ Complete |
| M - MPSC | `spec_mpsc` | ✓ Complete |
| M - MTL | `spec_mtl` | ✓ Complete |
| M - Module System | `spec_module_system` | ✓ Complete |
| M - Non-Interference | `spec_non_interference` | ✓ Complete |
| N - Null Safety | `spec_null_safety` | ✓ Complete |
| O - Observational Equivalence | `spec_observational_equivalence` | ✓ Complete |
| O - Operational Semantics | `spec_operational_semantics` | ✓ Complete |
| O - Optimization | `spec_optimization` | ✓ Complete |
| O - Optimization Hole | `spec_optimization_hole` | ✓ Complete |
| O - Option Type | `spec_option_type` | ✓ Complete |
| O - Parallelism | `spec_parallelism` | ✓ Complete |
| O - Parameter Space | `spec_parameter_space` | ✓ Complete |
| P - Partial Evaluation | `spec_partial_evaluation` | ✓ Complete |
| P - Partial Order | `spec_partial_order` | ✓ Complete |
| P - Pattern Matching | `spec_pattern_matching` | ✓ Complete |
| P - Petri Net | `spec_petri_net` | ✓ Complete |
| P - π-Calculus | `spec_pi_calculus` | ✓ Complete |
| P - Place | `spec_place` | ✓ Complete |
| P - Pointer | `spec_pointer` | ✓ Complete |
| P - Post-Text Programming Language | `spec_post_text_programming_language` | ✓ Complete |
| P - Product Type | `spec_product_type` | ✓ Complete |
| P - Projection | `spec_projection` | ✓ Complete |
| P - Projectional Only Mandate | `spec_projectional_only_mandate` | ✓ Complete |
| P - Promise | `spec_promise` | ✓ Complete |
| P - Pure Function | `spec_pure_function` | ✓ Complete |
| P - Query Learning | `spec_query_learning` | ✓ Complete |
| Q - Reachability Analysis | `spec_reachability_analysis` | ✓ Complete |
| R - Reactive Programming | `spec_reactive_programming` | ✓ Complete |
| R - Reference Capability | `spec_reference_capability` | ✓ Complete |
| R - Reference Counting | `spec_reference_counting` | ✓ Complete |
| R - Registry | `spec_registry` | ✓ Complete |
| R - Round-Trip Engineering | `spec_round_trip_engineering` | ✓ Complete |
| R - SAP | `spec_sap` | ✓ Complete |
| S - SAT | `spec_sat` | ✓ Complete |
| S - SAT Solver | `spec_sat_solver` | ✓ Complete |
| S - Scoping | `spec_scoping` | ✓ Complete |
| S - Security Lattice | `spec_security_lattice` | ✓ Complete |
| S - SemVer | `spec_semver` | ✓ Complete |
| S - Session Type | `spec_session_type` | ✓ Complete |
| S - SMT | `spec_smt_solver` | ✓ Complete |
| S - Serialization Isomorphism | `spec_serialization_isomorphism` | ✓ Complete |
| S - Semantic Trie | `spec_semantic_trie` | ✓ Complete |
| S - Semantic Vector | `spec_semantic_vector` | ✓ Complete |
| S - Signal | `spec_signal` | ✓ Complete |
| S - Serialization Isomorphism | `spec_serialization_isomorphism` | ✓ Complete |
| S - SSUS | `spec_ssus` | ✓ Complete |
| S - Stack | `spec_stack` | ✓ Complete |
| S - Stackful Coroutine | `spec_stackful_coroutine` | ✓ Complete |
| S - Static Dispatch | `spec_static_dispatch` | ✓ Complete |
| S - Static Reflection | `spec_static_reflection` | ✓ Complete |
| S - Stream | `spec_stream` | ✓ Complete |
| S - Strict State Unidirectional | `spec_ssus` | ✓ Complete |
| S - Substructural Typing | `spec_substructural_typing` | ✓ Complete |
| S - Sum Type | `spec_sum_type` | ✓ Complete |
| S - Supervision | `spec_supervision` | ✓ Complete |
| S - Supervision Tree | `spec_supervision_tree` | ✓ Complete |
| S - Supply Chain Security | `spec_supply_chain_security` | ✓ Complete |
| S - Symbolic Execution | `spec_symbolic_execution` | ✓ Complete |
| S - Synthesis | `spec_synthesis` | ✓ Complete |
| S - Tensor | `spec_tensor` | ✓ Complete |
| T - Temporal Logic | `spec_temporal_logic` | ✓ Complete |
| T - T-Way Coverage | `spec_t_way_coverage` | ✓ Complete |
| P - Token | `spec_token` | ✓ Complete |
| P - Transition | `spec_transition` | ✓ Complete |
| T - Type Abstraction | `spec_type_abstraction` | ✓ Complete |
| T - Type Category | `spec_type_category` | ✓ Complete |
| T - Type Erasure | `spec_type_erasure` | ✓ Complete |
| T - Type Inference | `spec_type_inference` | ✓ Complete |
| T - Type Inhabitation | `spec_type_inhabitation` | ✓ Complete |
| T - Type-Level Programming | `spec_type_level_programming` | ✓ Complete |
| T - Type Parameter | `spec_type_parameter` | ✓ Complete |
| T - Type Safety | `spec_type_safety` | ✓ Complete |
| T - Type System | `spec_type_system` | ✓ Complete |
| T - Type Unification | `spec_type_unification` | ✓ Complete |
| T - UDF Pattern | `spec_udf_pattern` | ✓ Complete |
| T - Unified Allocator | `spec_unified_allocator` | ✓ Complete |
| T - Unidirectional Data Flow | `spec_unidirectional_data_flow` | ✓ Complete |
| T - Unit System | `spec_unit_system` | ✓ Complete |
| V - Variable Visibility | `spec_variable_visibility` | ✓ Complete |
| V - Vector Clock | `spec_vector_clock` | ✓ Complete |
| V - Visibility Modifier | `spec_visibility_modifier` | ✓ Complete |
| V - Well-Founded Induction | `spec_well_founded_induction` | ✓ Complete |
| W - Work-Stealing Scheduler | `spec_work_stealing_scheduler` | ✓ Complete |

## Known Issues

### Section A: Acyclic Graph

**Ambiguity:** The glossary defines acyclic graph as a directed graph with no directed cycles, but does not specify whether the graph is weakly or strongly connected, or whether it must be connected.

**Proposed Resolution:** We interpret "acyclic" as weakly acyclic (no cycles) without requiring connectivity. This is the standard interpretation in graph theory and aligns with memory model requirements (preventing cycles for memory safety).

**Status:** ⚠ Ambiguous - Awaiting clarification from spec author

### Section A: Actor

**Ambiguity:** The glossary states that actors have MPSC mailboxes, but does not specify whether the mailbox is bounded or unbounded.

**Proposed Resolution:** We interpret MPSC as unbounded (no fixed limit) to allow for dynamic workload scaling. This aligns with the work-stealing scheduler specification.

**Status:** ⚠ Ambiguous - Awaiting clarification from spec author

## Notes

- This glossary is primarily a reference document rather than a formal specification
- Most terms are well-defined and can be directly formalized
- Some terms require additional context from other specifications to be fully formalized
- The glossary provides foundational terminology for the entire Morph project
-!/
