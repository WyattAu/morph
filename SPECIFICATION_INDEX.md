# Specification Index

Complete index of all Morph specification documents organized by category.

---

## Architecture

| Specification | Description |
|--------------|-------------|
| [`spec/architecture/layered_concurrency_spec.md`](spec/architecture/layered_concurrency_spec.md) | Layered concurrency architecture unifying SSUS and actor model |

## Build

| Specification | Description |
|--------------|-------------|
| [`spec/build/abi_alignment_algebra_spec.md`](spec/build/abi_alignment_algebra_spec.md) | ABI alignment algebra for struct layout |
| [`spec/build/abi_data_refinement_spec.md`](spec/build/abi_data_refinement_spec.md) | ABI data refinement between representation layers |
| [`spec/build/backend_tiling_spec.md`](spec/build/backend_tiling_spec.md) | Backend instruction tiling correctness |
| [`spec/build/build_lattice_spec.md`](spec/build/build_lattice_spec.md) | Build dependency lattice and incremental compilation |
| [`spec/build/dependency_sat_spec.md`](spec/build/dependency_sat_spec.md) | Dependency satisfaction and version resolution |
| [`spec/build/linker_logic_spec.md`](spec/build/linker_logic_spec.md) | Linker logic for module symbol resolution |

## Concurrency

| Specification | Description |
|--------------|-------------|
| [`spec/concurrency/concurrency_process_algebra_spec.md`](spec/concurrency/concurrency_process_algebra_spec.md) | Process algebra formalization of concurrent communication |
| [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md) | Execution model, actor model, and scheduler |
| [`spec/concurrency/monadic_effect_spec.md`](spec/concurrency/monadic_effect_spec.md) | Monadic effect handlers for side effects |
| [`spec/concurrency/scheduling_modes_spec.md`](spec/concurrency/scheduling_modes_spec.md) | Scheduling modes and policies |

## Conventions

| Specification | Description |
|--------------|-------------|
| [`spec/conventions/terminology_standardization_spec.md`](spec/conventions/terminology_standardization_spec.md) | Canonical terminology and naming conventions |
| [`spec/conventions/version_compatibility_spec.md`](spec/conventions/version_compatibility_spec.md) | Version compatibility rules for specifications |

## Language

| Specification | Description |
|--------------|-------------|
| [`spec/language/ast_graph_spec.md`](spec/language/ast_graph_spec.md) | AST graph structure and operations |
| [`spec/language/dialect_projection_spec.md`](spec/language/dialect_projection_spec.md) | Dialect system and projectional editing |
| [`spec/language/dual_optimization_spec.md`](spec/language/dual_optimization_spec.md) | Dual optimization for agent-first and human usability |
| [`spec/language/lexical_structure_syntax_spec.md`](spec/language/lexical_structure_syntax_spec.md) | Lexical structure and syntax tokens |
| [`spec/language/module_system_spec.md`](spec/language/module_system_spec.md) | Module system and namespace management |
| [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md) | Core Morph language specification |
| [`spec/language/operator_null_coalescing_spec.md`](spec/language/operator_null_coalescing_spec.md) | Null coalescing operator semantics |
| [`spec/language/scoping_lambda_calculus_spec.md`](spec/language/scoping_lambda_calculus_spec.md) | Scoping rules and lambda calculus foundation |
| [`spec/language/strict_state_unidirectional_spec.md`](spec/language/strict_state_unidirectional_spec.md) | SSUS pattern: state/effect separation |
| [`spec/language/syntax_translation_spec.md`](spec/language/syntax_translation_spec.md) | Syntax translation between dialects |
| [`spec/language/unidirectional_data_flow_spec.md`](spec/language/unidirectional_data_flow_spec.md) | Unidirectional data flow specification |

## Licensing

| Specification | Description |
|--------------|-------------|
| [`spec/licensing/license_deontic_logic_spec.md`](spec/licensing/license_deontic_logic_spec.md) | Deontic logic for license obligations |
| [`spec/licensing/licensing_spec.md`](spec/licensing/licensing_spec.md) | License specification and compliance |

## Math

| Specification | Description |
|--------------|-------------|
| [`spec/math/maths_spec.md`](spec/math/maths_spec.md) | Mathematical foundations |
| [`spec/math/unit_group_theory_spec.md`](spec/math/unit_group_theory_spec.md) | Unit group theory for algebraic structures |

## Memory

| Specification | Description |
|--------------|-------------|
| [`spec/memory/arc_affine_integration_spec.md`](spec/memory/arc_affine_integration_spec.md) | ARC and affine type integration |
| [`spec/memory/memory_acyclicity_spec.md`](spec/memory/memory_acyclicity_spec.md) | Memory acyclicity guarantees |
| [`spec/memory/memory_affine_logic_spec.md`](spec/memory/memory_affine_logic_spec.md) | Affine logic for resource management |
| [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md) | Core memory model specification |
| [`spec/memory/memory_petri_net_spec.md`](spec/memory/memory_petri_net_spec.md) | Petri net modeling of memory operations |

## Optimization

| Specification | Description |
|--------------|-------------|
| [`spec/optimization/optimization_bayesian_spec.md`](spec/optimization/optimization_bayesian_spec.md) | Bayesian optimization for compiler tuning |
| [`spec/optimization/optimization_manifold_spec.md`](spec/optimization/optimization_manifold_spec.md) | Optimization manifold exploration |
| [`spec/optimization/optimization_search_engine_specification.md`](spec/optimization/optimization_search_engine_specification.md) | Search engine optimization |
| [`spec/optimization/selective_monomorphization_spec.md`](spec/optimization/selective_monomorphization_spec.md) | Selective monomorphization optimization |

## Security

| Specification | Description |
|--------------|-------------|
| [`spec/security/infrastructure_safety_contracts_spec.md`](spec/security/infrastructure_safety_contracts_spec.md) | Infrastructure safety contracts |
| [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md) | Information flow security and taint tracking |
| [`spec/security_ocap_spec.md`](spec/security_ocap_spec.md) | Object capability security model |

## Stdlib

| Specification | Description |
|--------------|-------------|
| [`spec/stdlib/stdlib_algebraic_spec.md`](spec/stdlib/stdlib_algebraic_spec.md) | Standard library algebraic data types |
| [`spec/stdlib/stdlib_amortized_spec.md`](spec/stdlib/stdlib_amortized_spec.md) | Amortized analysis for stdlib data structures |

## Tooling

| Specification | Description |
|--------------|-------------|
| [`spec/tooling/agent_planning_mdp_spec.md`](spec/tooling/agent_planning_mdp_spec.md) | Agent planning via Markov decision processes |
| [`spec/tooling/analysis_abstract_interp_spec.md`](spec/tooling/analysis_abstract_interp_spec.md) | Abstract interpretation for static analysis |
| [`spec/tooling/compiler_bisimulation_spec.md`](spec/tooling/compiler_bisimulation_spec.md) | Compiler bisimulation correctness |
| [`spec/tooling/comptime_partial_eval_spec.md`](spec/tooling/comptime_partial_eval_spec.md) | Compile-time partial evaluation |
| [`spec/tooling/context_comonad_spec.md`](spec/tooling/context_comonad_spec.md) | Context management via comonadic structure |
| [`spec/tooling/context_temporal_logic_spec.md`](spec/tooling/context_temporal_logic_spec.md) | Temporal logic for context reasoning |
| [`spec/tooling/deterministic_time_spec.md`](spec/tooling/deterministic_time_spec.md) | Deterministic time semantics |
| [`spec/tooling/diagnose_protocol_spec.md`](spec/tooling/diagnose_protocol_spec.md) | Diagnostic protocol specification |
| [`spec/tooling/distributed_crdt_spec.md`](spec/tooling/distributed_crdt_spec.md) | Distributed CRDT data types |
| [`spec/tooling/fuzzing_combinatorial_spec.md`](spec/tooling/fuzzing_combinatorial_spec.md) | Combinatorial fuzzing strategies |
| [`spec/tooling/graph_rewriting_spec.md`](spec/tooling/graph_rewriting_spec.md) | Graph rewriting transformations |
| [`spec/tooling/history_persistent_tree_spec.md`](spec/tooling/history_persistent_tree_spec.md) | Persistent tree for history tracking |
| [`spec/tooling/hot_reload_projection_spec.md`](spec/tooling/hot_reload_projection_spec.md) | Hot reload and projectional editing |
| [`spec/tooling/learning_theory_spec.md`](spec/tooling/learning_theory_spec.md) | Learning theory for adaptive compilation |
| [`spec/tooling/meta_modal_logic_spec.md`](spec/tooling/meta_modal_logic_spec.md) | Meta-modal logic for specification |
| [`spec/tooling/metaprogramming_spec.md`](spec/tooling/metaprogramming_spec.md) | Metaprogramming capabilities |
| [`spec/tooling/operational_semantics_spec.md`](spec/tooling/operational_semantics_spec.md) | Operational semantics definition |
| [`spec/tooling/parsing_island_grammar_spec.md`](spec/tooling/parsing_island_grammar_spec.md) | Island grammar parsing |
| [`spec/tooling/pattern_coverage_matrix_spec.md`](spec/tooling/pattern_coverage_matrix_spec.md) | Pattern coverage matrix analysis |
| [`spec/tooling/protocol_session_types_spec.md`](spec/tooling/protocol_session_types_spec.md) | Session types for protocol verification |
| [`spec/tooling/reactive_frp_spec.md`](spec/tooling/reactive_frp_spec.md) | Functional reactive programming |
| [`spec/tooling/realtime_mtl_spec.md`](spec/tooling/realtime_mtl_spec.md) | Real-time monad transformer layer |
| [`spec/tooling/registry_merkle_spec.md`](spec/tooling/registry_merkle_spec.md) | Merkle tree registry |
| [`spec/tooling/semantic_trie_spec.md`](spec/tooling/semantic_trie_spec.md) | Semantic trie data structure |
| [`spec/tooling/semantic_vector_spec.md`](spec/tooling/semantic_vector_spec.md) | Semantic vector encoding |
| [`spec/tooling/serialization_isomorphism_spec.md`](spec/tooling/serialization_isomorphism_spec.md) | Serialization isomorphism guarantees |
| [`spec/tooling/symbolic_execution_fuzz_spec.md`](spec/tooling/symbolic_execution_fuzz_spec.md) | Symbolic execution fuzzing |
| [`spec/tooling/synthesis_inhabitation_spec.md`](spec/tooling/synthesis_inhabitation_spec.md) | Type inhabitation for program synthesis |

## Type System

| Specification | Description |
|--------------|-------------|
| [`spec/type/effect_system_spec.md`](spec/type/effect_system_spec.md) | Effect system specification |
| [`spec/type/pure_type_spec.md`](spec/type/pure_type_spec.md) | Pure type system foundation |
| [`spec/type/type_category_spec.md`](spec/type/type_category_spec.md) | Type category theory |
| [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md) | Core type system specification |
| [`spec/type/type_unification_spec.md`](spec/type/type_unification_spec.md) | Type unification algorithm |

## UI

| Specification | Description |
|--------------|-------------|
| [`spec/ui/semantic_accessibility_spec.md`](spec/ui/semantic_accessibility_spec.md) | Semantic accessibility specification |
| [`spec/ui/ui_constraint_algebra_spec.md`](spec/ui/ui_constraint_algebra_spec.md) | UI constraint algebra |
| [`spec/ui/ui_event_topology_spec.md`](spec/ui/ui_event_topology_spec.md) | UI event topology |

## Validation

| Specification | Description |
|--------------|-------------|
| [`spec/validation/unproven_assumptions_spec.md`](spec/validation/unproven_assumptions_spec.md) | Formal validation of unproven assumptions |

## Cross-Cutting

| Document | Description |
|----------|-------------|
| [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md) | Distributed vector clock specification |
| [`spec/scheduler_randomized_stealing_spec.md`](spec/scheduler_randomized_stealing_spec.md) | Randomized work-stealing scheduler |
| [`spec/storage_dawg_spec.md`](spec/storage_dawg_spec.md) | DAWG storage specification |
| [`spec/module_existential_spec.md`](spec/module_existential_spec.md) | Module existential specification |
| [`spec/registry_consensus_spec.md`](spec/registry_consensus_spec.md) | Registry consensus specification |
| [`spec/financial/financial_spec.md`](spec/financial/financial_spec.md) | Financial domain specification |
| [`spec/GLOSSARY.md`](spec/GLOSSARY.md) | Unified glossary of terms |
| [`spec/README.md`](spec/README.md) | Specification directory overview |
| [`SPEC_STATUS.md`](SPEC_STATUS.md) | Spec module implementation status |
| [`SPEC_CONTRADICTIONS.md`](SPEC_CONTRADICTIONS.md) | Contradiction analysis and resolutions |
| [`SPEC_FIX_PROPOSAL.md`](SPEC_FIX_PROPOSAL.md) | Proposed fixes for identified issues |
| [`SPEC_GAPS_AND_BASIS.md`](SPEC_GAPS_AND_BASIS.md) | Specification gaps and foundational basis |
| [`SPEC_INCONSISTENCIES.md`](SPEC_INCONSISTENCIES.md) | Terminology inconsistencies and conventions |
