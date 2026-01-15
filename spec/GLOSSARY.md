# Morph Specification Glossary

**Version:** 1.0.0  
**Date:** 2026-01-02  
**Author:** Kilo Code  
**Status:** Active

---

## 1. Introduction

This glossary provides comprehensive definitions of terms, acronyms, and concepts used throughout the Morph specification ecosystem. It serves as a reference for developers, implementers, and contributors working with the Morph language and its specifications.

**Purpose:**
- Provide clear, concise definitions of Morph-specific terminology
- Explain technical concepts and formalisms used in specifications
- Ensure consistent understanding across all specification documents
- Support onboarding and knowledge transfer

**Organization:**
- Terms are organized alphabetically
- Each term includes definition, context, and related specifications
- Cross-references to related terms are provided

---

## 2. Glossary

### A

#### ABI (Application Binary Interface)
**Definition:** The binary interface between two program components, defining how data structures are laid out in memory, how functions are called, and how values are returned. ABI compatibility ensures that compiled code can interoperate across different versions or implementations.

**Context:** Build System, Type System  
**Related Specifications:** [`spec/build/abi_alignment_algebra_spec.md`](spec/build/abi_alignment_algebra_spec.md), [`spec/build/abi_data_refinement_spec.md`](spec/build/abi_data_refinement_spec.md)

---

#### Actor
**Definition:** A concurrent entity that encapsulates state and communicates with other actors exclusively through asynchronous message passing. Actors have MPSC (Multi-Producer Single-Consumer) mailboxes and can be supervised by parent actors.

**Context:** Concurrency, Runtime  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md), [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** Fiber, Mailbox, Supervision Tree

---

#### Acyclic Graph
**Definition:** A directed graph with no directed cycles. In the context of Morph memory model, the reference graph must be acyclic to ensure memory safety and prevent memory leaks.

**Context:** Memory Model, Graph Theory  
**Related Specifications:** [`spec/memory/memory_acyclicity_spec.md`](spec/memory/memory_acyclicity_spec.md)

**See Also:** DAG (Directed Acyclic Graph), Well-Founded Induction

---

#### Affine Logic
**Definition:** A substructural logic where resources can be used at most once. In Morph, affine logic is used to enforce memory safety by tracking resource usage through the type system.

**Context:** Type System, Memory Model  
**Related Specifications:** [`spec/memory/memory_affine_logic_spec.md`](spec/memory/memory_affine_logic_spec.md), [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Linear Logic, Substructural Typing, Capability System

---

#### Agent-First
**Definition:** A design philosophy that prioritizes AI agent generation of code over human authoring. Morph is designed as a post-text programming language optimized for LLM generation, with the `min` dialect serving as the canonical representation.

**Context:** Language Design, Philosophy  
**Related Specifications:** [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** Projectional Only Mandate, Dual Dialects

---

#### Algebraic Data Type (ADT)
**Definition:** A composite type formed by combining other types. ADTs include product types (structs, tuples) and sum types (enums, tagged unions). Morph supports both product and sum types with pattern matching.

**Context:** Type System  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Product Type, Sum Type, Pattern Matching

---

#### Allocation
**Definition:** The process of reserving memory for data structures. Morph uses a unified allocator that manages Stack, Arena, and Heap allocations with different lifetime and performance characteristics.

**Context:** Memory Model, Runtime  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)

**See Also:** Deallocation, Unified Allocator, ARC

---

#### Arena
**Definition:** A memory region where allocations are made sequentially and freed all at once. Arenas provide fast allocation and deallocation for temporary data structures with known lifetimes.

**Context:** Memory Model, Runtime  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)

**See Also:** Stack, Heap, Unified Allocator

---

#### ARC (Atomic Reference Counting)
**Definition:** A memory management technique where each object maintains a count of references to it. When the count reaches zero, the object is deallocated. ARC provides deterministic memory reclamation without stop-the-world pauses.

**Context:** Memory Model, Runtime  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)

**See Also:** Reference Counting, Deallocation, Memory Safety

---

#### AST (Abstract Syntax Tree)
**Definition:** A tree representation of the syntactic structure of source code. ASTs abstract away concrete syntax details (whitespace, parentheses) while preserving the hierarchical structure of the code.

**Context:** Compiler, Language Design  
**Related Specifications:** [`spec/language/ast_graph_spec.md`](spec/language/ast_graph_spec.md)

**See Also:** Parse Tree, Concrete Syntax, Semantic Analysis

---

#### Async Let
**Definition:** A concurrency primitive that spawns a concurrent task and returns a future for the result. `async let` enables dataflow parallelism by allowing multiple independent computations to run concurrently.

**Context:** Concurrency, Language Design  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md), [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** Future, Dataflow Parallelism, Concurrency

---

---

### B

#### Backend Tiling
**Definition:** An optimization technique for code generation that partitions computation into tiles to improve cache locality and parallelism. Tiling is used in backend optimization passes for loops and array operations.

**Context:** Build System, Optimization  
**Related Specifications:** [`spec/build/backend_tiling_spec.md`](spec/build/backend_tiling_spec.md)

**See Also:** Optimization, Code Generation, Cache Locality

---

#### Bayesian Optimization
**Definition:** A probabilistic optimization strategy that uses Gaussian processes to model the objective function and balance exploration and exploitation. Bayesian optimization is used in the Morph optimization search engine.

**Context:** Optimization, Machine Learning  
**Related Specifications:** [`spec/optimization/optimization_bayesian_spec.md`](spec/optimization/optimization_bayesian_spec.md)

**See Also:** Optimization Search Engine, Gaussian Process, Exploration-Exploitation

---

#### Bisimulation
**Definition:** A relation between two systems that ensures they are observationally equivalent. In Morph, compiler bisimulation ensures that optimizations preserve program behavior.

**Context:** Compiler, Verification  
**Related Specifications:** [`spec/tooling/compiler_bisimulation_spec.md`](spec/tooling/compiler_bisimulation_spec.md)

**See Also:** Observational Equivalence, Optimization Correctness, Compiler Verification

---

#### BLoC (Business Logic Component)
**Definition:** A design pattern for managing state and business logic in reactive applications. BLoCs separate business logic from UI components and emit state changes as streams.

**Context:** UI Framework, State Management  
**Related Specifications:** [`spec/language/unidirectional_data_flow_spec.md`](spec/language/unidirectional_data_flow_spec.md)

**See Also:** State Management, Reactive Programming, Stream

---

#### Build Lattice
**Definition:** A partially ordered set of build configurations where each configuration can be compared and combined using lattice operations (join and meet). The build lattice is used for dependency resolution and version compatibility checking.

**Context:** Build System, Dependency Management  
**Related Specifications:** [`spec/build/build_lattice_spec.md`](spec/build/build_lattice_spec.md)

**See Also:** Lattice Theory, Dependency Resolution, SemVer

---

---

### C

#### Capability
**Definition:** An unforgeable token that grants permission to perform an operation on a resource. In Morph, capabilities are enforced through the type system using sigils (^Iso, #Val, &Ref).

**Context:** Type System, Security  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md), [`spec/security/security_ocap_spec.md`](spec/security/security_ocap_spec.md)

**See Also:** Capability System, Reference Capability, Object Capability Model

---

#### Capability System
**Definition:** A security model where access to resources is controlled through capabilities. Morph's capability system uses type-level sigils to enforce memory safety and access control.

**Context:** Type System, Security  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md), [`spec/security/security_ocap_spec.md`](spec/security/security_ocap_spec.md)

**See Also:** Capability, Reference Capability, Object Capability Model

---

#### Category Theory
**Definition:** A branch of mathematics that studies mathematical structures and their relationships. Category theory provides the formal foundation for Morph's type system, including functors, monads, and comonads.

**Context:** Type System, Mathematics  
**Related Specifications:** [`spec/type/type_category_spec.md`](spec/type/type_category_spec.md)

**See Also:** Functor, Monad, Comonad, Type Category

---

#### Causal Consistency
**Definition:** A consistency model for distributed systems where operations that are causally related are seen in the same order by all processes, but concurrent operations may be seen in different orders.

**Context:** Distributed Systems, Concurrency  
**Related Specifications:** [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md)

**See Also:** Vector Clock, Happens-Before Relation, CRDT

---

#### Causal Ordering
**Definition:** A partial order on events in a distributed system based on their causal relationships. Event A causally precedes event B if A must have happened before B.

**Context:** Distributed Systems, Concurrency  
**Related Specifications:** [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md)

**See Also:** Happens-Before Relation, Vector Clock, Causal Consistency

---

#### Comonad
**Definition:** A categorical structure dual to a monad, used for modeling contexts and environments. In Morph, the context comonad is used for managing context and deadlines in concurrent systems.

**Context:** Type System, Concurrency  
**Related Specifications:** [`spec/tooling/context_comonad_spec.md`](spec/tooling/context_comonad_spec.md)

**See Also:** Monad, Context, Category Theory

---

#### Comptime
**Definition:** Compile-time execution of code. Comptime blocks in Morph allow code to be executed during compilation for metaprogramming, constant folding, and type-level computation.

**Context:** Metaprogramming, Compiler  
**Related Specifications:** [`spec/tooling/metaprogramming_spec.md`](spec/tooling/metaprogramming_spec.md), [`spec/tooling/comptime_partial_eval_spec.md`](spec/tooling/comptime_partial_eval_spec.md)

**See Also:** Metaprogramming, Partial Evaluation, Type-Level Programming

---

#### Concurrent Event
**Definition:** Two or more events in a distributed system that are not causally related and can occur in any order. Concurrent events are detected using vector clocks.

**Context:** Distributed Systems, Concurrency  
**Related Specifications:** [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md)

**See Also:** Causal Ordering, Vector Clock, Happens-Before Relation

---

#### Concurrency
**Definition:** The execution of multiple tasks or computations simultaneously or in overlapping time periods. Morph provides concurrency through actors, fibers, and async/await.

**Context:** Concurrency, Runtime  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Actor, Fiber, Async Let, Parallelism

---

#### Conflict Resolution
**Definition:** The process of resolving conflicting updates in distributed systems. CRDTs provide automatic conflict resolution through merge functions that guarantee convergence.

**Context:** Distributed Systems, CRDT  
**Related Specifications:** [`spec/tooling/distributed_crdt_spec.md`](spec/tooling/distributed_crdt_spec.md)

**See Also:** CRDT, Merge Function, Convergence

---

#### Constraint Algebra
**Definition:** An algebraic system for expressing and solving constraints. In Morph, constraint algebra is used for UI layout computation and optimization.

**Context:** UI Framework, Optimization  
**Related Specifications:** [`spec/ui/ui_constraint_algebra_spec.md`](spec/ui/ui_constraint_algebra_spec.md)

**See Also:** Constraint Solving, Layout Engine, UI

---

#### Content-Addressable Storage
**Definition:** A storage system where data is addressed by a cryptographic hash of its content. Morph uses content-addressable storage for code artifacts and package registry.

**Context:** Infrastructure, Registry  
**Related Specifications:** [`spec/tooling/registry_merkle_spec.md`](spec/tooling/registry_merkle_spec.md)

**See Also:** Merkle Tree, Hash, Package Registry

---

#### Context
**Definition:** A data structure that carries request-scoped values across API boundaries and between processes. In Morph, the context comonad is used for managing deadlines, cancellation, and tracing.

**Context:** Concurrency, Distributed Systems  
**Related Specifications:** [`spec/tooling/context_comonad_spec.md`](spec/tooling/context_comonad_spec.md)

**See Also:** Comonad, Deadline, Cancellation

---

#### Convergence
**Definition:** The property of distributed systems where replicas eventually reach the same state despite network partitions and concurrent updates. CRDTs guarantee convergence.

**Context:** Distributed Systems, CRDT  
**Related Specifications:** [`spec/tooling/distributed_crdt_spec.md`](spec/tooling/distributed_crdt_spec.md)

**See Also:** CRDT, Conflict Resolution, Merge Function

---

#### CRDT (Conflict-Free Replicated Data Type)
**Definition:** A data structure designed for distributed systems that can be replicated across multiple nodes and updated concurrently without conflicts, guaranteeing eventual consistency.

**Context:** Distributed Systems, Data Structures  
**Related Specifications:** [`spec/tooling/distributed_crdt_spec.md`](spec/tooling/distributed_crdt_spec.md)

**See Also:** Convergence, Conflict Resolution, Merge Function

---

---

### D

#### DAG (Directed Acyclic Graph)
**Definition:** A directed graph with no directed cycles. DAGs are used in Morph to represent immutable data structures and dependency graphs.

**Context:** Graph Theory, Memory Model  
**Related Specifications:** [`spec/memory/memory_acyclicity_spec.md`](spec/memory/memory_acyclicity_spec.md)

**See Also:** Acyclic Graph, Immutable Data Structure, Dependency Graph

---

#### Dataflow Parallelism
**Definition:** A parallel programming model where computations are expressed as a dataflow graph, and parallelism is achieved by executing independent nodes concurrently. Morph's `async let` enables dataflow parallelism.

**Context:** Concurrency, Parallelism  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Async Let, Dataflow Graph, Parallelism

---

#### Deallocation
**Definition:** The process of freeing memory that is no longer needed. Morph uses ARC for automatic deallocation when reference counts reach zero.

**Context:** Memory Model, Runtime  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)

**See Also:** Allocation, ARC, Memory Management

---

#### Deadline
**Definition:** A time limit for completing a computation or request. In Morph, deadlines are managed through the context comonad and can trigger cancellation or timeout handling.

**Context:** Concurrency, Distributed Systems  
**Related Specifications:** [`spec/tooling/context_comonad_spec.md`](spec/tooling/context_comonad_spec.md)

**See Also:** Context, Cancellation, Timeout

---

#### Deontic Logic
**Definition:** A modal logic for reasoning about permissions, obligations, and prohibitions. Deontic logic is used in Morph's licensing model to formalize license policies.

**Context:** Licensing, Logic  
**Related Specifications:** [`spec/licensing/license_deontic_logic_spec.md`](spec/licensing/license_deontic_logic_spec.md)

**See Also:** Licensing, Permission, Obligation, Prohibition

---

#### Deterministic Replay
**Definition:** The ability to replay a sequence of events and obtain the same result. Morph's UI event topology supports deterministic replay for testing and debugging.

**Context:** UI, Testing, Debugging  
**Related Specifications:** [`spec/ui/ui_event_topology_spec.md`](spec/ui/ui_event_topology_spec.md)

**See Also:** Determinism, Testing, Debugging

---

#### Deterministic Scheduler
**Definition:** A scheduler that always makes the same scheduling decisions given the same input. Morph provides a deterministic scheduler as a debug-only shim for reproducible execution.

**Context:** Concurrency, Debugging  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Work-Stealing Scheduler, Determinism, Debugging

---

#### Determinism
**Definition:** The property of a system where the same input always produces the same output. Determinism is important for testing, debugging, and reproducibility.

**Context:** Concurrency, UI, Testing  
**Related Specifications:** [`spec/ui/ui_event_topology_spec.md`](spec/ui/ui_event_topology_spec.md), [`spec/tooling/deterministic_time_spec.md`](spec/tooling/deterministic_time_spec.md)

**See Also:** Deterministic Replay, Deterministic Scheduler, Testing

---

#### Dimensional Analysis
**Definition:** The analysis of physical quantities in terms of their dimensions (e.g., length, time, mass). Morph's unit system uses dimensional analysis to ensure type-safe unit operations.

**Context:** Math, Type System  
**Related Specifications:** [`spec/math/unit_group_theory_spec.md`](spec/math/unit_group_theory_spec.md)

**See Also:** Unit System, Type Safety, Physical Quantity

---

#### Distributed System
**Definition:** A system whose components are located on different networked computers. Morph provides distributed system support through vector clocks, CRDTs, and distributed consensus.

**Context:** Distributed Systems, Concurrency  
**Related Specifications:** [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md), [`spec/tooling/distributed_crdt_spec.md`](spec/tooling/distributed_crdt_spec.md)

**See Also:** Vector Clock, CRDT, Consensus

---

#### Dual Representations
**Definition:** Morph's two representations: `min` (canonical, compressed, optimized for storage and LLM generation) and `hum` (transient in-memory projection, human-readable, generated from `min` by the Language Server Protocol).

**Context:** Language Design, Agent-First
**Related Specifications:** [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** Projectional Only Mandate, Agent-First, min Dialect, hum Projection

---

---

### E

#### Effect
**Definition:** A side effect or observable behavior of a computation. Morph's effect system tracks effects (Pure, IO, Net, Time, System) to enable reasoning about program behavior.

**Context:** Type System, Concurrency  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md), [`spec/concurrency/monadic_effect_spec.md`](spec/concurrency/monadic_effect_spec.md)

**See Also:** Effect System, Side Effect, Pure Function

---

#### Effect System
**Definition:** A type system extension that tracks and controls side effects. Morph's effect system categorizes effects (Pure, IO, Net, Time, System) and enforces effect constraints.

**Context:** Type System, Concurrency  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md), [`spec/concurrency/monadic_effect_spec.md`](spec/concurrency/monadic_effect_spec.md)

**See Also:** Effect, Side Effect, Pure Function

---

#### Existential Type
**Definition:** A type that hides some type information, allowing values of different concrete types to be used uniformly. Existential types are used in Morph's module system for abstracting over implementations.

**Context:** Type System, Module System  
**Related Specifications:** [`spec/module_existential_spec.md`](spec/module_existential_spec.md)

**See Also:** Universal Type, Module System, Type Abstraction

---

#### Explicit Flow
**Definition:** Information flow that is explicitly visible in the program's control flow, such as through assignments and function calls. Morph's security flow engine tracks explicit flows to enforce security policies.

**Context:** Security, Type System  
**Related Specifications:** [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Implicit Flow, Information Flow, Security Lattice

---

#### Exploration-Exploitation Tradeoff
**Definition:** The balance between exploring new solutions and exploiting known good solutions in optimization. Bayesian optimization manages this tradeoff using probabilistic models.

**Context:** Optimization, Machine Learning  
**Related Specifications:** [`spec/optimization/optimization_bayesian_spec.md`](spec/optimization/optimization_bayesian_spec.md)

**See Also:** Bayesian Optimization, Gaussian Process, Optimization

---

---

### F

#### Fiber
**Definition:** A lightweight, stackful coroutine that can be suspended and resumed. Fibers are used in Morph as the execution units for actors and concurrent tasks.

**Context:** Concurrency, Runtime  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Actor, Coroutine, Stackful Coroutine

---

#### Fitness Landscape
**Definition:** A mapping from parameter space to objective function values, representing the quality of different solutions in an optimization problem. Morph's optimization search engine uses fitness landscapes to guide optimization.

**Context:** Optimization, Machine Learning  
**Related Specifications:** [`spec/optimization/optimization_manifold_spec.md`](spec/optimization/optimization_manifold_spec.md)

**See Also:** Optimization Search Engine, Objective Function, Parameter Space

---

#### Flow Construct
**Definition:** A language construct in Morph for defining reactive streams and unidirectional data flow. The `flow` keyword is used to create stream processing pipelines.

**Context:** Language Design, Reactive Programming  
**Related Specifications:** [`spec/language/unidirectional_data_flow_spec.md`](spec/language/unidirectional_data_flow_spec.md)

**See Also:** Stream, Signal, UDF Pattern

---

#### FRP (Functional Reactive Programming)
**Definition:** A declarative programming paradigm for reactive systems based on functional programming and time-varying values. Morph supports FRP through signals, streams, and reactive operators.

**Context:** UI, Reactive Programming  
**Related Specifications:** [`spec/tooling/reactive_frp_spec.md`](spec/tooling/reactive_frp_spec.md)

**See Also:** Signal, Stream, Reactive Programming

---

#### Functor
**Definition:** A mapping between categories that preserves structure. In programming, functors represent types that can be mapped over (e.g., lists, options).

**Context:** Type System, Category Theory  
**Related Specifications:** [`spec/type/type_category_spec.md`](spec/type/type_category_spec.md)

**See Also:** Monad, Category Theory, Type System

---

#### Future
**Definition:** A placeholder for a value that will become available asynchronously. Futures are used in Morph's `async let` construct to represent concurrent computations.

**Context:** Concurrency, Language Design  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Async Let, Concurrency, Promise

---

#### Fuzzing
**Definition:** Automated testing technique that generates random or semi-random inputs to find bugs and vulnerabilities. Morph supports combinatorial fuzzing using IPO algorithms.

**Context:** Testing, Security  
**Related Specifications:** [`spec/tooling/fuzzing_combinatorial_spec.md`](spec/tooling/fuzzing_combinatorial_spec.md), [`spec/tooling/symbolic_execution_fuzz_spec.md`](spec/tooling/symbolic_execution_fuzz_spec.md)

**See Also:** IPO Algorithm, Symbolic Execution, Testing

---

---

### G

#### Gaussian Process
**Definition:** A probabilistic model that defines a distribution over functions. Gaussian processes are used in Bayesian optimization to model the objective function and guide search.

**Context:** Optimization, Machine Learning  
**Related Specifications:** [`spec/optimization/optimization_bayesian_spec.md`](spec/optimization/optimization_bayesian_spec.md)

**See Also:** Bayesian Optimization, Probabilistic Model, Optimization

---

#### Generic
**Definition:** A type or function that can operate on different types without being rewritten for each type. Morph supports generics with monomorphization for zero-cost abstractions.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Monomorphization, Type Parameter, Zero-Cost Abstraction

---

#### Graph Rewriting
**Definition:** The process of transforming graphs by applying rewrite rules. Graph rewriting is used in Morph for program transformation and optimization.

**Context:** Compiler, Optimization  
**Related Specifications:** [`spec/tooling/graph_rewriting_spec.md`](spec/tooling/graph_rewriting_spec.md)

**See Also:** AST, Optimization, Program Transformation

---

---

### H

#### Happens-Before Relation
**Definition:** A partial order on events in a distributed system that captures causal relationships. Event A happens-before event B if A must have occurred before B.

**Context:** Distributed Systems, Concurrency  
**Related Specifications:** [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md)

**See Also:** Causal Ordering, Vector Clock, Causal Consistency

---

#### Heap
**Definition:** A memory region for dynamic allocation with flexible lifetimes. Heap allocations are managed by ARC in Morph and provide flexibility at the cost of allocation overhead.

**Context:** Memory Model, Runtime  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)

**See Also:** Stack, Arena, Unified Allocator, ARC

---

#### Hot Reload
**Definition:** The ability to update code while an application is running without restarting. Morph supports hot reload through projection and state migration.

**Context:** Tooling, Development Experience  
**Related Specifications:** [`spec/tooling/hot_reload_projection_spec.md`](spec/tooling/hot_reload_projection_spec.md)

**See Also:** Projection, State Migration, Development Experience

---

#### hum Projection
**Definition:** The human-readable projection of Morph, generated as a transient in-memory representation from the canonical `min` dialect. The `hum` projection is never persisted to disk and is used exclusively for human auditing and understanding through the Language Server Protocol (LSP).

**Warning:** If `hum` exists as a file format, you create sync issues. This must be a hard constraint in the specification.

**Context:** Language Design, Agent-First
**Related Specifications:** [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** min Dialect, Projectional Only Mandate, Projection

---

---

### I

#### IEEE 754-2008
**Definition:** The IEEE standard for floating-point arithmetic, including the Decimal128 format used by Morph's `dec128` type for financial calculations.

**Context:** Financial, Type System  
**Related Specifications:** [`spec/financial/financial_spec.md`](spec/financial/financial_spec.md)

**See Also:** dec128, Decimal Arithmetic, Financial

---

#### Implicit Flow
**Definition:** Information flow that is not directly visible in the program's control flow, such as through control structures (if statements, loops). Morph's security flow engine tracks implicit flows to enforce security policies.

**Context:** Security, Type System  
**Related Specifications:** [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Explicit Flow, Information Flow, Security Lattice

---

#### Inclusion Proof
**Definition:** A cryptographic proof that a specific piece of data is included in a Merkle tree. Inclusion proofs are used in Morph's package registry for supply chain security.

**Context:** Infrastructure, Security  
**Related Specifications:** [`spec/tooling/registry_merkle_spec.md`](spec/tooling/registry_merkle_spec.md)

**See Also:** Merkle Tree, Content-Addressable Storage, Supply Chain Security

---

#### Information Flow
**Definition:** The movement of data through a program, including both explicit flows (assignments, function calls) and implicit flows (control structures). Morph's security flow engine tracks information flow to enforce security policies.

**Context:** Security, Type System  
**Related Specifications:** [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Explicit Flow, Implicit Flow, Security Lattice

---

#### Inhabitation
**Definition:** The property of a type having at least one value (inhabitant). Inhabitation checking is used in Morph for program synthesis and type-level programming.

**Context:** Type System, Metaprogramming  
**Related Specifications:** [`spec/tooling/synthesis_inhabitation_spec.md`](spec/tooling/synthesis_inhabitation_spec.md)

**See Also:** Type Inhabitation, Program Synthesis, Type-Level Programming

---

#### IPO (In-Parameter Order) Algorithm
**Definition:** A combinatorial testing algorithm that generates test suites covering t-way combinations of input parameters. IPO is used in Morph's fuzzing framework.

**Context:** Testing, Fuzzing  
**Related Specifications:** [`spec/tooling/fuzzing_combinatorial_spec.md`](spec/tooling/fuzzing_combinatorial_spec.md)

**See Also:** Fuzzing, T-Way Coverage, Test Generation

---

#### Island Grammar
**Definition:** A parsing technique that defines a core grammar with "islands" of more complex syntax. Island grammars provide robust and error-tolerant parsing for Morph code.

**Context:** Compiler, Parsing  
**Related Specifications:** [`spec/tooling/parsing_island_grammar_spec.md`](spec/tooling/parsing_island_grammar_spec.md)

**See Also:** Parsing, Error Recovery, Syntax Error

---

---

### J

#### JIT (Just-In-Time) Compilation
**Definition:** Compilation that occurs at runtime, just before code is executed. Morph supports JIT compilation for math operations and hot code paths.

**Context:** Compiler, Performance  
**Related Specifications:** [`spec/math/maths_spec.md`](spec/math/maths_spec.md)

**See Also:** Compilation, Performance, Runtime

---

---

### L

#### Lattice
**Definition:** A partially ordered set where every pair of elements has a least upper bound (join) and greatest lower bound (meet). Lattices are used in Morph for dependency resolution, security labels, and type systems.

**Context:** Type System, Build System, Security  
**Related Specifications:** [`spec/build/build_lattice_spec.md`](spec/build/build_lattice_spec.md), [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Partial Order, Join, Meet, Lattice Theory

---

#### Lattice Theory
**Definition:** The branch of mathematics that studies lattices and their properties. Lattice theory provides the formal foundation for Morph's build lattice and security lattice.

**Context:** Mathematics, Type System, Security  
**Related Specifications:** [`spec/build/build_lattice_spec.md`](spec/build/build_lattice_spec.md), [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Lattice, Partial Order, Join, Meet

---

#### Lexical Scoping
**Definition:** A scoping rule where variable visibility is determined by the textual structure of the code. Variables are visible in the block where they are defined and nested blocks.

**Context:** Language Design, Type System  
**Related Specifications:** [`spec/language/scoping_lambda_calculus_spec.md`](spec/language/scoping_lambda_calculus_spec.md)

**See Also:** Scoping, Variable Visibility, Block

---

#### Linear Logic
**Definition:** A substructural logic where resources must be used exactly once. Linear logic is a stricter form of affine logic and is related to Morph's capability system.

**Context:** Type System, Logic  
**Related Specifications:** [`spec/memory/memory_affine_logic_spec.md`](spec/memory/memory_affine_logic_spec.md)

**See Also:** Affine Logic, Substructural Typing, Capability System

---

#### Linker
**Definition:** A tool that combines object files and libraries into an executable or library. Morph's linker logic specification defines symbol resolution and ABI compatibility checking.

**Context:** Build System, Compiler  
**Related Specifications:** [`spec/build/linker_logic_spec.md`](spec/build/linker_logic_spec.md)

**See Also:** ABI, Symbol Resolution, Build System

---

#### Load Balancing
**Definition:** The distribution of work across multiple processors or threads to optimize performance. Morph's work-stealing scheduler provides automatic load balancing.

**Context:** Concurrency, Performance  
**Related Specifications:** [`spec/scheduler_randomized_stealing_spec.md`](spec/scheduler_randomized_stealing_spec.md)

**See Also:** Work-Stealing Scheduler, Concurrency, Performance

---

---

### M

#### Mailbox
**Definition:** A message queue used for asynchronous communication between actors. Morph actors have MPSC (Multi-Producer Single-Consumer) mailboxes.

**Context:** Concurrency, Actor Model  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Actor, MPSC, Asynchronous Communication

---

#### Meet
**Definition:** The greatest lower bound of two elements in a lattice. In Morph, meet operations are used for security label intersection and type system operations.

**Context:** Type System, Security, Mathematics  
**Related Specifications:** [`spec/build/build_lattice_spec.md`](spec/build/build_lattice_spec.md), [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Join, Lattice, Partial Order

---

#### Memory Safety
**Definition:** The property of a program that prevents memory errors such as buffer overflows, use-after-free, and memory leaks. Morph ensures memory safety through ARC, affine logic, and capability-based ownership.

**Context:** Memory Model, Type System  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md), [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** ARC, Affine Logic, Capability System

---

#### Merge Function
**Definition:** A function that combines two states of a CRDT into a new state, ensuring convergence. Merge functions are commutative, associative, and idempotent.

**Context:** Distributed Systems, CRDT  
**Related Specifications:** [`spec/tooling/distributed_crdt_spec.md`](spec/tooling/distributed_crdt_spec.md)

**See Also:** CRDT, Convergence, Conflict Resolution

---

#### Merkle Tree
**Definition:** A binary tree where each node contains a hash of its children. Merkle trees are used in Morph for content-addressable storage and supply chain security.

**Context:** Infrastructure, Security  
**Related Specifications:** [`spec/tooling/registry_merkle_spec.md`](spec/tooling/registry_merkle_spec.md)

**See Also:** Content-Addressable Storage, Hash, Supply Chain Security

---

#### Metaprogramming
**Definition:** Writing programs that manipulate or generate other programs. Morph supports metaprogramming through comptime blocks, static reflection, and AST-based macros.

**Context:** Compiler, Language Design  
**Related Specifications:** [`spec/tooling/metaprogramming_spec.md`](spec/tooling/metaprogramming_spec.md)

**See Also:** Comptime, Static Reflection, AST

---

#### Modal Logic
**Definition:** A type of logic that deals with modalities such as necessity and possibility. Modal logic is used in Morph for reasoning about permissions, obligations, and type-level modalities.

**Context:** Logic, Type System, Licensing  
**Related Specifications:** [`spec/tooling/meta_modal_logic_spec.md`](spec/tooling/meta_modal_logic_spec.md), [`spec/licensing/license_deontic_logic_spec.md`](spec/licensing/license_deontic_logic_spec.md)

**See Also:** Deontic Logic, Necessity, Possibility

---

#### Monad
**Definition:** A design pattern and categorical structure for sequencing computations. Monads are used in Morph for effect handling, error management, and asynchronous operations.

**Context:** Type System, Category Theory  
**Related Specifications:** [`spec/type/type_category_spec.md`](spec/type/type_category_spec.md)

**See Also:** Functor, Comonad, Category Theory

---

#### Monomorphization
**Definition:** The process of generating specialized code for each concrete type used with a generic function or type. Morph uses monomorphization for zero-cost abstractions.

**Context:** Type System, Compiler  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md), [`spec/tooling/metaprogramming_spec.md`](spec/tooling/metaprogramming_spec.md)

**See Also:** Generic, Zero-Cost Abstraction, Code Generation

---

#### MPSC (Multi-Producer Single-Consumer)
**Definition:** A communication channel where multiple producers can send messages to a single consumer. Morph actors use MPSC mailboxes for message passing.

**Context:** Concurrency, Actor Model  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Actor, Mailbox, Asynchronous Communication

---

#### MTL (Metric Temporal Logic)
**Definition:** An extension of temporal logic with time constraints, used for specifying and verifying real-time properties. MTL is used in Morph for real-time constraint specification.

**Context:** Concurrency, Real-Time Systems  
**Related Specifications:** [`spec/tooling/realtime_mtl_spec.md`](spec/tooling/realtime_mtl_spec.md)

**See Also:** Temporal Logic, Real-Time, Deadline

---

---

### N

#### Non-Interference
**Definition:** A security property where high-security data cannot affect low-security outputs. Non-interference is enforced in Morph through the security flow engine and capability system.

**Context:** Security, Type System  
**Related Specifications:** [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Information Flow, Security Lattice, Capability System

---

#### Null Safety
**Definition:** The property of a type system that prevents null reference errors. Morph ensures null safety through the Option type and explicit null handling.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Option Type, Type Safety, Reference

---

---

### O

#### Object Capability Model
**Definition:** A security model where access to resources is controlled through capabilities that are unforgeable and must be explicitly passed. Morph's capability system is based on the object capability model.

**Context:** Security, Type System  
**Related Specifications:** [`spec/security/security_ocap_spec.md`](spec/security/security_ocap_spec.md)

**See Also:** Capability, Capability System, Security

---

#### Observational Equivalence
**Definition:** Two programs are observationally equivalent if they produce the same observable behavior for all possible inputs. Compiler bisimulation ensures optimizations preserve observational equivalence.

**Context:** Compiler, Verification  
**Related Specifications:** [`spec/tooling/compiler_bisimulation_spec.md`](spec/tooling/compiler_bisimulation_spec.md)

**See Also:** Bisimulation, Optimization Correctness, Compiler Verification

---

#### Operational Semantics
**Definition:** A formal specification of program behavior through reduction rules and evaluation contexts. Operational semantics define how programs execute step-by-step.

**Context:** Compiler, Language Design  
**Related Specifications:** [`spec/tooling/operational_semantics_spec.md`](spec/tooling/operational_semantics_spec.md)

**See Also:** Denotational Semantics, Reduction Rules, Evaluation Context

---

#### Optimization
**Definition:** The process of transforming code to improve performance, reduce size, or enhance other properties while preserving behavior. Morph provides automated optimization through the optimization search engine.

**Context:** Compiler, Performance  
**Related Specifications:** [`spec/optimization/optimization_manifold_spec.md`](spec/optimization/optimization_manifold_spec.md)

**See Also:** Optimization Search Engine, Fitness Landscape, Code Generation

---

#### Optimization Hole
**Definition:** A placeholder in code (using the `??` operator) that the optimization search engine can fill with optimized implementations. Optimization holes enable automated code optimization.

**Context:** Metaprogramming, Optimization  
**Related Specifications:** [`spec/tooling/metaprogramming_spec.md`](spec/tooling/metaprogramming_spec.md), [`spec/optimization/optimization_manifold_spec.md`](spec/optimization/optimization_manifold_spec.md)

**See Also:** Optimization Search Engine, Metaprogramming, Code Generation

---

#### Option Type
**Definition:** A type that represents an optional value, either `Some(value)` or `None`. Option types are used in Morph for null safety and explicit handling of absent values.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Null Safety, Type Safety, Sum Type

---

---

### P

#### Parallelism
**Definition:** The simultaneous execution of multiple computations. Morph provides parallelism through actors, fibers, and dataflow parallelism.

**Context:** Concurrency, Performance  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Concurrency, Dataflow Parallelism, Actor

---

#### Parameter Space
**Definition:** The set of all possible parameter values for an optimization problem. Morph's optimization search engine explores the parameter space to find optimal solutions.

**Context:** Optimization, Machine Learning  
**Related Specifications:** [`spec/optimization/optimization_manifold_spec.md`](spec/optimization/optimization_manifold_spec.md)

**See Also:** Fitness Landscape, Optimization Search Engine, Objective Function

---

#### Partial Evaluation
**Definition:** The process of evaluating parts of a program at compile time when some inputs are known. Partial evaluation is used in Morph's comptime blocks for constant folding and type-level computation.

**Context:** Compiler, Metaprogramming  
**Related Specifications:** [`spec/tooling/comptime_partial_eval_spec.md`](spec/tooling/comptime_partial_eval_spec.md)

**See Also:** Comptime, Constant Folding, Type-Level Programming

---

#### Partial Order
**Definition:** A binary relation that is reflexive, antisymmetric, and transitive. Partial orders are used in Morph for lattices, version ordering, and causal ordering.

**Context:** Mathematics, Type System, Distributed Systems  
**Related Specifications:** [`spec/build/build_lattice_spec.md`](spec/build/build_lattice_spec.md), [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md)

**See Also:** Lattice, Total Order, Causal Ordering

---

#### Pattern Matching
**Definition:** A mechanism for checking a value against a pattern and extracting data. Morph supports pattern matching on ADTs, tuples, and other data structures.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** ADT, Sum Type, Product Type

---

#### Petri Net
**Definition:** A mathematical modeling tool for describing distributed systems, consisting of places, transitions, and arcs. Petri nets are used in Morph to model memory operations and verify safety properties.

**Context:** Memory Model, Verification  
**Related Specifications:** [`spec/memory/memory_petri_net_spec.md`](spec/memory/memory_petri_net_spec.md)

**See Also:** Place, Transition, Reachability Analysis

---

#### π-Calculus
**Definition:** A process algebra for modeling concurrent systems with communication through named channels. π-calculus is used in Morph to formalize actor communication.

**Context:** Concurrency, Process Algebra  
**Related Specifications:** [`spec/concurrency/concurrency_process_algebra_spec.md`](spec/concurrency/concurrency_process_algebra_spec.md)

**See Also:** Process Algebra, Actor, Communication

---

#### Place
**Definition:** A node in a Petri net that represents a condition or state. Places hold tokens and are connected to transitions by arcs.

**Context:** Memory Model, Verification  
**Related Specifications:** [`spec/memory/memory_petri_net_spec.md`](spec/memory/memory_petri_net_spec.md)

**See Also:** Petri Net, Transition, Token

---

#### Post-Text Programming Language
**Definition:** A programming language designed for the post-text era, where code is primarily generated by AI agents rather than written by humans. Morph is a post-text programming language.

**Context:** Language Design, Philosophy  
**Related Specifications:** [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** Agent-First, Projectional Only Mandate, Dual Dialects

---

#### Product Type
**Definition:** A composite type that combines multiple values into a single value. Product types include structs and tuples in Morph.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Sum Type, ADT, Pattern Matching

---

#### Projection
**Definition:** The process of generating a human-readable representation from a canonical representation. In Morph, the `hum` projection is a transient in-memory projection of the canonical `min` dialect, generated by the Language Server Protocol (LSP) for human auditing and readability.

**Context:** Language Design, Agent-First
**Related Specifications:** [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** Projectional Only Mandate, Dual Representations, hum Projection

---

#### Projectional Only Mandate
**Definition:** The principle that the `min` dialect is the canonical, authoritative representation of Morph code stored on disk, while the `hum` projection is a transient in-memory representation for human auditing. The `hum` projection is never persisted to disk to avoid sync issues.

**Context:** Language Design, Philosophy
**Related Specifications:** [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** Agent-First, Dual Representations, Projection

---

#### Promise
**Definition:** A placeholder for a value that will become available asynchronously. Promises are similar to futures and are used in concurrent programming.

**Context:** Concurrency, Language Design  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Future, Async Let, Concurrency

---

#### Pure Function
**Definition:** A function that has no side effects and always returns the same output for the same input. Pure functions are marked with the `Pure` effect in Morph.

**Context:** Type System, Functional Programming  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Effect, Effect System, Side Effect

---

---

### Q

#### Query Learning
**Definition:** A machine learning technique where an algorithm learns a concept by making queries to an oracle. Query learning is used in Morph for program synthesis and type inhabitation.

**Context:** Machine Learning, Metaprogramming  
**Related Specifications:** [`spec/tooling/learning_theory_spec.md`](spec/tooling/learning_theory_spec.md)

**See Also:** Program Synthesis, Oracle, Inhabitation

---

---

### R

#### Reachability Analysis
**Definition:** The process of determining which states in a system can be reached from a given initial state. Reachability analysis is used in Morph for verifying memory safety and concurrency properties.

**Context:** Verification, Memory Model  
**Related Specifications:** [`spec/memory/memory_petri_net_spec.md`](spec/memory/memory_petri_net_spec.md)

**See Also:** Petri Net, Verification, Memory Safety

---

#### Reactive Programming
**Definition:** A declarative programming paradigm for reactive systems based on asynchronous data streams and automatic propagation of changes. Morph supports reactive programming through FRP and the UDF pattern.

**Context:** UI, Concurrency  
**Related Specifications:** [`spec/tooling/reactive_frp_spec.md`](spec/tooling/reactive_frp_spec.md), [`spec/language/unidirectional_data_flow_spec.md`](spec/language/unidirectional_data_flow_spec.md)

**See Also:** FRP, Stream, Signal, UDF Pattern

---

#### Reference Capability
**Definition:** A type-level annotation that specifies how a reference can be used. Morph uses sigils (^Iso, #Val, &Ref) to denote reference capabilities.

**Context:** Type System, Memory Model  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Capability, Capability System, Sigil

---

#### Reference Counting
**Definition:** A memory management technique where each object maintains a count of references to it. When the count reaches zero, the object is deallocated. Morph uses ARC for reference counting.

**Context:** Memory Model, Runtime  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)

**See Also:** ARC, Deallocation, Memory Management

---

#### Registry
**Definition:** A centralized repository for storing and distributing Morph packages and artifacts. The Morph registry uses content-addressable storage and Merkle trees for security.

**Context:** Infrastructure, Package Management  
**Related Specifications:** [`spec/tooling/registry_merkle_spec.md`](spec/tooling/registry_merkle_spec.md), [`spec/registry_consensus_spec.md`](spec/registry_consensus_spec.md)

**See Also:** Content-Addressable Storage, Merkle Tree, Package Management

---

#### Round-Trip Engineering
**Definition:** The process of converting between different representations of code (e.g., between `min` and `hum` dialects) while preserving semantics. Morph supports round-trip engineering through projection.

**Context:** Language Design, Tooling  
**Related Specifications:** [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)

**See Also:** Projection, Dual Dialects, Round-Trip

---

---

### S

#### SAP (Semantic Accessibility Protocol)
**Definition:** A protocol for ensuring UI accessibility and semantic understanding. SAP defines semantic trees, accessibility roles, and assistive technology integration.

**Context:** UI, Accessibility  
**Related Specifications:** [`spec/ui/semantic_accessibility_spec.md`](spec/ui/semantic_accessibility_spec.md)

**See Also:** Semantic Tree, Accessibility, Assistive Technology

---

#### SAT (Satisfiability)
**Definition:** The problem of determining whether a given Boolean formula has a satisfying assignment. SAT solvers are used in Morph for dependency resolution and constraint solving.

**Context:** Build System, Verification  
**Related Specifications:** [`spec/build/dependency_sat_spec.md`](spec/build/dependency_sat_spec.md)

**See Also:** SAT Solver, Dependency Resolution, Constraint Solving

---

#### SAT Solver
**Definition:** An algorithm that determines whether a Boolean formula is satisfiable. SAT solvers are used in Morph for dependency resolution and constraint solving.

**Context:** Build System, Verification  
**Related Specifications:** [`spec/build/dependency_sat_spec.md`](spec/build/dependency_sat_spec.md)

**See Also:** SAT, Dependency Resolution, Constraint Solving

---

#### Scoping
**Definition:** The rules that determine where variables and names are visible in a program. Morph uses lexical scoping with visibility modifiers (Pub, Package, Private).

**Context:** Language Design, Type System  
**Related Specifications:** [`spec/language/scoping_lambda_calculus_spec.md`](spec/language/scoping_lambda_calculus_spec.md)

**See Also:** Lexical Scoping, Variable Visibility, Visibility Modifier

---

#### Security Lattice
**Definition:** A partially ordered set of security labels with join and meet operations. The security lattice is used in Morph to enforce information flow policies.

**Context:** Security, Type System  
**Related Specifications:** [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Lattice, Information Flow, Non-Interference

---

#### SemVer (Semantic Versioning)
**Definition:** A versioning scheme that uses three-part version numbers (MAJOR.MINOR.PATCH) to communicate API compatibility. Morph uses SemVer for package versioning.

**Context:** Build System, Package Management  
**Related Specifications:** [`spec/build/build_lattice_spec.md`](spec/build/build_lattice_spec.md)

**See Also:** Version Compatibility, Dependency Resolution, Build Lattice

---

#### Session Type
**Definition:** A type that describes the communication protocol between two processes. Session types ensure type-safe communication and protocol adherence.

**Context:** Concurrency, Distributed Systems  
**Related Specifications:** [`spec/tooling/protocol_session_types_spec.md`](spec/tooling/protocol_session_types_spec.md)

**See Also:** Protocol, Type Safety, Communication

---

#### SMT (Satisfiability Modulo Theories)
**Definition:** An extension of SAT that includes theories such as arithmetic, arrays, and bit-vectors. SMT solvers are used in Morph for verification and constraint solving.

**Context:** Verification, Build System  
**Related Specifications:** [`spec/build/dependency_sat_spec.md`](spec/build/dependency_sat_spec.md)

**See Also:** SAT Solver, Verification, Constraint Solving

---

#### SMT Solver
**Definition:** An algorithm that determines whether a formula is satisfiable modulo theories. SMT solvers are used in Morph for verification and constraint solving.

**Context:** Verification, Build System  
**Related Specifications:** [`spec/build/dependency_sat_spec.md`](spec/build/dependency_sat_spec.md)

**See Also:** SMT, SAT Solver, Verification

---

#### Signal
**Definition:** A time-varying value that can be observed and transformed. Signals are used in Morph's FRP and UDF patterns for reactive programming.

**Context:** UI, Reactive Programming  
**Related Specifications:** [`spec/tooling/reactive_frp_spec.md`](spec/tooling/reactive_frp_spec.md), [`spec/language/unidirectional_data_flow_spec.md`](spec/language/unidirectional_data_flow_spec.md)

**See Also:** Stream, FRP, UDF Pattern

---

#### Sigil
**Definition:** A symbol used to denote reference capabilities in Morph. The three sigils are `^Iso` (isolated ownership), `#Val` (shared value), and `&Ref` (borrowed reference).

**Context:** Type System, Memory Model  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Reference Capability, Capability System, Type System

---

#### Stack
**Definition:** A memory region for function call frames with LIFO (Last-In-First-Out) allocation. Stack allocations are fast and have automatic deallocation when functions return.

**Context:** Memory Model, Runtime  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)

**See Also:** Heap, Arena, Unified Allocator

---

#### Stackful Coroutine
**Definition:** A coroutine that has its own stack and can be suspended and resumed. Fibers in Morph are stackful coroutines.

**Context:** Concurrency, Runtime  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Fiber, Coroutine, Stack

---

#### Static Dispatch
**Definition:** The process of selecting which function implementation to call at compile time based on static type information. Static dispatch enables zero-cost abstractions in Morph.

**Context:** Type System, Compiler  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Dynamic Dispatch, Monomorphization, Zero-Cost Abstraction

---

#### Static Reflection
**Definition:** The ability to inspect and manipulate type information at compile time. Morph supports static reflection through comptime blocks and type-level programming.

**Context:** Metaprogramming, Type System  
**Related Specifications:** [`spec/tooling/metaprogramming_spec.md`](spec/tooling/metaprogramming_spec.md)

**See Also:** Comptime, Type-Level Programming, Metaprogramming

---

#### Stream
**Definition:** A sequence of values over time. Streams are used in Morph's FRP and UDF patterns for reactive programming and event handling.

**Context:** UI, Reactive Programming  
**Related Specifications:** [`spec/tooling/reactive_frp_spec.md`](spec/tooling/reactive_frp_spec.md), [`spec/language/unidirectional_data_flow_spec.md`](spec/language/unidirectional_data_flow_spec.md)

**See Also:** Signal, FRP, UDF Pattern

---

#### Strict State Unidirectional (SSUS)
**Definition:** A pattern for unidirectional data flow with strict state management, using `update` and `command` functions. SSUS ensures deterministic state transitions.

**Context:** Language Design, State Management
**Related Specifications:** [`spec/language/strict_state_unidirectional_spec.md`](spec/language/strict_state_unidirectional_spec.md)

**See Also:** UDF Pattern, Unidirectional Data Flow, State Management

---

#### Substructural Typing
**Definition:** A type system that tracks resource usage through substructural logics such as linear and affine logic. Morph uses substructural typing for memory safety.

**Context:** Type System, Memory Model  
**Related Specifications:** [`spec/memory/memory_affine_logic_spec.md`](spec/memory/memory_affine_logic_spec.md)

**See Also:** Affine Logic, Linear Logic, Capability System

---

#### Sum Type
**Definition:** A composite type that represents a value that can be one of several variants. Sum types include enums and tagged unions in Morph.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Product Type, ADT, Pattern Matching

---

#### Supervision
**Definition:** A fault-tolerance mechanism where parent actors monitor and restart child actors on failure. Supervision trees provide hierarchical error handling in Morph.

**Context:** Concurrency, Fault Tolerance  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Actor, Supervision Tree, Fault Tolerance

---

#### Supervision Tree
**Definition:** A hierarchical structure of actors where parent actors supervise child actors. Supervision trees provide fault tolerance and error recovery in Morph.

**Context:** Concurrency, Fault Tolerance  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)

**See Also:** Actor, Supervision, Fault Tolerance

---

#### Supply Chain Security
**Definition:** The practice of securing the software supply chain from vulnerabilities and malicious code. Morph uses content-addressable storage and Merkle trees for supply chain security.

**Context:** Infrastructure, Security  
**Related Specifications:** [`spec/tooling/registry_merkle_spec.md`](spec/tooling/registry_merkle_spec.md)

**See Also:** Content-Addressable Storage, Merkle Tree, Inclusion Proof

---

#### Symbolic Execution
**Definition:** A program analysis technique that explores program paths using symbolic values instead of concrete inputs. Symbolic execution is used in Morph for automated testing and vulnerability discovery.

**Context:** Testing, Security  
**Related Specifications:** [`spec/tooling/symbolic_execution_fuzz_spec.md`](spec/tooling/symbolic_execution_fuzz_spec.md)

**See Also:** Fuzzing, SMT Solver, Testing

---

#### Synthesis
**Definition:** The automatic generation of code from specifications or examples. Morph supports program synthesis through inhabitation checking and query learning.

**Context:** Metaprogramming, Machine Learning  
**Related Specifications:** [`spec/tooling/synthesis_inhabitation_spec.md`](spec/tooling/synthesis_inhabitation_spec.md)

**See Also:** Program Synthesis, Inhabitation, Query Learning

---

---

### T

#### Taint Tracking
**Definition:** A static analysis technique that tracks the flow of sensitive data through a program to prevent information leakage. Taint tracking is used in Morph's security flow engine.

**Context:** Security, Static Analysis  
**Related Specifications:** [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)

**See Also:** Information Flow, Security Lattice, Static Analysis

---

#### Tensor
**Definition:** A multi-dimensional array used for mathematical and machine learning operations. Morph provides tensor primitives with slicing and automatic differentiation.

**Context:** Math, Machine Learning  
**Related Specifications:** [`spec/math/maths_spec.md`](spec/math/maths_spec.md)

**See Also:** Automatic Differentiation, Slicing, Machine Learning

---

#### Temporal Logic
**Definition:** A formal logic for reasoning about time and temporal properties. Temporal logic is used in Morph for specifying and verifying real-time constraints.

**Context:** Concurrency, Real-Time Systems  
**Related Specifications:** [`spec/tooling/context_temporal_logic_spec.md`](spec/tooling/context_temporal_logic_spec.md), [`spec/tooling/realtime_mtl_spec.md`](spec/tooling/realtime_mtl_spec.md)

**See Also:** MTL, Real-Time, Deadline

---

#### T-Way Coverage
**Definition:** A testing criterion that ensures all combinations of t parameters are covered. T-way coverage is used in Morph's fuzzing framework.

**Context:** Testing, Fuzzing  
**Related Specifications:** [`spec/tooling/fuzzing_combinatorial_spec.md`](spec/tooling/fuzzing_combinatorial_spec.md)

**See Also:** IPO Algorithm, Fuzzing, Test Generation

---

#### Token
**Definition:** A unit of data in a Petri net that represents the presence of a condition or state. Tokens move between places through transitions.

**Context:** Memory Model, Verification  
**Related Specifications:** [`spec/memory/memory_petri_net_spec.md`](spec/memory/memory_petri_net_spec.md)

**See Also:** Petri Net, Place, Transition

---

#### Transition
**Definition:** A node in a Petri net that represents an event or operation. Transitions consume tokens from input places and produce tokens in output places.

**Context:** Memory Model, Verification  
**Related Specifications:** [`spec/memory/memory_petri_net_spec.md`](spec/memory/memory_petri_net_spec.md)

**See Also:** Petri Net, Place, Token

---

#### Type Abstraction
**Definition:** The hiding of implementation details behind a type interface. Type abstraction is used in Morph's module system through existential types.

**Context:** Type System, Module System  
**Related Specifications:** [`spec/module_existential_spec.md`](spec/module_existential_spec.md)

**See Also:** Existential Type, Module System, Encapsulation

---

#### Type Category
**Definition:** A category whose objects are types and whose morphisms are functions between types. Type category theory provides the formal foundation for Morph's type system.

**Context:** Type System, Category Theory  
**Related Specifications:** [`spec/type/type_category_spec.md`](spec/type/type_category_spec.md)

**See Also:** Category Theory, Type System, Functor

---

#### Type Erasure
**Definition:** The removal of type information at runtime. Morph erases type information for units and other type-level constructs to improve performance.

**Context:** Type System, Runtime  
**Related Specifications:** [`spec/math/unit_group_theory_spec.md`](spec/math/unit_group_theory_spec.md)

**See Also:** Type System, Runtime, Performance

---

#### Type Inference
**Definition:** The automatic deduction of types from expressions without explicit type annotations. Morph supports type inference for improved developer experience.

**Context:** Type System, Compiler  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Type System, Compiler, Developer Experience

---

#### Type Inhabitation
**Definition:** The property of a type having at least one value (inhabitant). Type inhabitation checking is used in Morph for program synthesis and type-level programming.

**Context:** Type System, Metaprogramming  
**Related Specifications:** [`spec/tooling/synthesis_inhabitation_spec.md`](spec/tooling/synthesis_inhabitation_spec.md)

**See Also:** Inhabitation, Program Synthesis, Type-Level Programming

---

#### Type-Level Programming
**Definition:** Writing programs that operate on types rather than values. Morph supports type-level programming through comptime blocks and generic constraints.

**Context:** Metaprogramming, Type System  
**Related Specifications:** [`spec/tooling/metaprogramming_spec.md`](spec/tooling/metaprogramming_spec.md)

**See Also:** Comptime, Generic, Type System

---

#### Type Parameter
**Definition:** A placeholder for a type in a generic type or function. Type parameters are used in Morph generics to enable code reuse across different types.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Generic, Monomorphization, Type System

---

#### Type Safety
**Definition:** The property of a type system that prevents type errors at runtime. Morph ensures type safety through static typing, null safety, and capability-based ownership.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Static Typing, Null Safety, Capability System

---

#### Type System
**Definition:** A formal system for defining and checking types in a programming language. Morph's type system includes primitive types, ADTs, capabilities, effects, and generics.

**Context:** Type System, Language Design  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Type Safety, Type Inference, Generic

---

#### Type Unification
**Definition:** The process of finding a common type that makes two type expressions equivalent. Type unification is used in Morph for type inference and generic instantiation.

**Context:** Type System, Compiler  
**Related Specifications:** [`spec/type/type_unification_spec.md`](spec/type/type_unification_spec.md)

**See Also:** Type Inference, Generic, Type System

---

---

### U

#### UDF (Unidirectional Data Flow) Pattern
**Definition:** A pattern for reactive stream processing using `reduce` functions. The UDF pattern ensures unidirectional data flow and deterministic state transitions.

**Context:** Language Design, Reactive Programming  
**Related Specifications:** [`spec/language/unidirectional_data_flow_spec.md`](spec/language/unidirectional_data_flow_spec.md)

**See Also:** SSUS Pattern, Stream, Signal

---

#### Unified Allocator
**Definition:** A memory allocator that manages Stack, Arena, and Heap allocations in a unified way. Morph's unified allocator provides flexible memory management with different performance characteristics.

**Context:** Memory Model, Runtime  
**Related Specifications:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)

**See Also:** Stack, Arena, Heap, Allocation

---

#### Unidirectional Data Flow
**Definition:** A data flow pattern where data flows in a single direction through the system. Morph supports unidirectional data flow through the SSUS and UDF patterns.

**Context:** Language Design, State Management  
**Related Specifications:** [`spec/language/unidirectional_data_flow_spec.md`](spec/language/unidirectional_data_flow_spec.md)

**See Also:** SSUS Pattern, UDF Pattern, State Management

---

#### Unit System
**Definition:** A system for representing and manipulating physical units (e.g., meters, seconds, kilograms). Morph's unit system uses dimensional analysis to ensure type-safe unit operations.

**Context:** Math, Type System  
**Related Specifications:** [`spec/math/unit_group_theory_spec.md`](spec/math/unit_group_theory_spec.md)

**See Also:** Dimensional Analysis, Type Safety, Physical Quantity

---

---

### V

#### Variable Visibility
**Definition:** The rules that determine where variables can be accessed in a program. Morph uses visibility modifiers (Pub, Package, Private) to control variable visibility.

**Context:** Language Design, Type System  
**Related Specifications:** [`spec/language/scoping_lambda_calculus_spec.md`](spec/language/scoping_lambda_calculus_spec.md)

**See Also:** Scoping, Visibility Modifier, Encapsulation

---

#### Vector Clock
**Definition:** A data structure for tracking causal relationships in distributed systems. Each process maintains a vector of logical clocks, one for each process in the system.

**Context:** Distributed Systems, Concurrency  
**Related Specifications:** [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md)

**See Also:** Causal Ordering, Happens-Before Relation, Causal Consistency

---

#### Visibility Modifier
**Definition:** A keyword that controls the visibility of variables, functions, and types. Morph supports three visibility modifiers: Pub (public), Package (package-private), and Private (private).

**Context:** Language Design, Type System  
**Related Specifications:** [`spec/language/scoping_lambda_calculus_spec.md`](spec/language/scoping_lambda_calculus_spec.md)

**See Also:** Variable Visibility, Scoping, Encapsulation

---

---

### W

#### Well-Founded Induction
**Definition:** A proof technique for proving properties about well-founded relations. Well-founded induction is used in Morph to prove memory acyclicity and safety properties.

**Context:** Verification, Memory Model  
**Related Specifications:** [`spec/memory/memory_acyclicity_spec.md`](spec/memory/memory_acyclicity_spec.md)

**See Also:** Acyclic Graph, Memory Safety, Verification

---

#### Work-Stealing Scheduler
**Definition:** A concurrent scheduler where idle processors steal tasks from busy processors' queues. Morph uses an M:N work-stealing scheduler as the default scheduler.

**Context:** Concurrency, Runtime  
**Related Specifications:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md), [`spec/scheduler_randomized_stealing_spec.md`](spec/scheduler_randomized_stealing_spec.md)

**See Also:** Scheduler, Load Balancing, Concurrency

---

---

### Z

#### Zero-Cost Abstraction
**Definition:** A language feature that provides high-level abstractions without runtime overhead. Morph achieves zero-cost abstractions through monomorphization and static dispatch.

**Context:** Type System, Compiler  
**Related Specifications:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)

**See Also:** Monomorphization, Static Dispatch, Generic

---

---

## 3. Acronyms

| Acronym | Full Name | Definition |
|---------|-----------|------------|
| ABI | Application Binary Interface | Binary interface between program components |
| ADT | Algebraic Data Type | Composite type formed by combining other types |
| ARC | Atomic Reference Counting | Memory management with atomic reference counts |
| AST | Abstract Syntax Tree | Tree representation of code structure |
| BLoC | Business Logic Component | Design pattern for state management |
| CRDT | Conflict-Free Replicated Data Type | Data structure for distributed systems |
| DAG | Directed Acyclic Graph | Directed graph with no cycles |
| FRP | Functional Reactive Programming | Declarative reactive programming paradigm |
| IPO | In-Parameter Order | Combinatorial testing algorithm |
| JIT | Just-In-Time | Runtime compilation |
| LLM | Large Language Model | AI model for code generation |
| M:N | M-to-N | Many-to-many mapping (e.g., fibers to threads) |
| MCIE | Morph Controlled Input Environment | Deterministic input source for UI testing |
| MTL | Metric Temporal Logic | Temporal logic with time constraints |
| MPSC | Multi-Producer Single-Consumer | Communication channel pattern |
| OIR | Intermediate Representation | Compiler intermediate representation |
| SAP | Semantic Accessibility Protocol | UI accessibility protocol |
| SAT | Satisfiability | Boolean satisfiability problem |
| SBOM | Software Bill of Materials | List of software components |
| SemVer | Semantic Versioning | Versioning scheme for API compatibility |
| SMT | Satisfiability Modulo Theories | Extension of SAT with theories |
| SSUS | Strict State Unidirectional | Pattern for unidirectional data flow |
| UDF | Unidirectional Data Flow | Pattern for reactive stream processing |

---

## 4. Cross-Reference Index

### By Domain

- **Core Language:** Actor, Agent-First, Async Let, Comptime, Dual Representations, Flow Construct, hum Projection, min Dialect, Post-Text Programming Language, Projection, Projectional Only Mandate, Round-Trip Engineering, Scoping, SSUS Pattern, UDF Pattern, Unidirectional Data Flow, Variable Visibility, Visibility Modifier

- **Type System:** ADT, Affine Logic, Capability, Capability System, Category Theory, Effect, Effect System, Existential Type, Functor, Generic, Inhabitation, Monad, Monomorphization, Null Safety, Option Type, Pattern Matching, Product Type, Reference Capability, Static Dispatch, Static Reflection, Substructural Typing, Sum Type, Type Abstraction, Type Category, Type Erasure, Type Inference, Type Inhabitation, Type-Level Programming, Type Parameter, Type Safety, Type System, Type Unification

- **Memory Model:** Acyclic Graph, Affine Logic, Allocation, Arena, ARC, DAG, Deallocation, Heap, Memory Safety, Petri Net, Place, Reachability Analysis, Reference Counting, Stack, Stackful Coroutine, Substructural Typing, Token, Transition, Unified Allocator, Well-Founded Induction

- **Concurrency:** Actor, Async Let, Causal Consistency, Causal Ordering, Concurrent Event, Concurrency, Dataflow Parallelism, Deterministic Scheduler, Determinism, Fiber, Future, Load Balancing, Mailbox, MPSC, Parallelism, Promise, π-Calculus, Session Type, Supervision, Supervision Tree, Work-Stealing Scheduler

- **Build System:** ABI, Backend Tiling, Build Lattice, JIT, Lattice, Lattice Theory, Linker, SAT, SAT Solver, SemVer, SMT, SMT Solver

- **Security:** Capability, Capability System, Deontic Logic, Explicit Flow, Implicit Flow, Information Flow, Non-Interference, Object Capability Model, Security Lattice, Supply Chain Security, Taint Tracking

- **Tooling:** Bayesian Optimization, Bisimulation, Comptime, Comonad, Context, Deadline, Deterministic Replay, Determinism, Fuzzing, Graph Rewriting, Hot Reload, Inclusion Proof, Inhabitation, IPO Algorithm, Island Grammar, Metaprogramming, Modal Logic, Monomorphization, Operational Semantics, Optimization, Optimization Hole, Partial Evaluation, Pattern Coverage Matrix, Query Learning, Reachability Analysis, SAP, SAT, SAT Solver, Semantic Trie, Semantic Vector, Serialization Isomorphism, Static Reflection, Symbolic Execution, Synthesis, T-Way Coverage, Type Inhabitation, Type-Level Programming

- **Optimization:** Bayesian Optimization, Fitness Landscape, Gaussian Process, Optimization, Optimization Hole, Parameter Space

- **Distributed Systems:** Causal Consistency, Causal Ordering, Concurrent Event, Convergence, CRDT, Conflict Resolution, Distributed System, Happens-Before Relation, Merge Function, Vector Clock

- **Financial:** dec128, IEEE 754-2008

- **Math:** Automatic Differentiation, Dimensional Analysis, Tensor, Unit System

- **UI:** BLoC, Constraint Algebra, FRP, Hit Testing, Reactive Programming, SAP, Semantic Tree, Signal, Stream

- **Licensing:** Deontic Logic, Licensing, Permission, Obligation, Prohibition

- **Module System:** Existential Type, Module System, Type Abstraction

- **Registry:** Content-Addressable Storage, Inclusion Proof, Merkle Tree, Registry, Supply Chain Security

---

## 5. Related Specifications

For detailed information about specific concepts, please refer to the following specification documents:

- **Core Language:** [`spec/language/morph_language_spec.md`](spec/language/morph_language_spec.md)
- **Type System:** [`spec/type/type_system_spec.md`](spec/type/type_system_spec.md)
- **Memory Model:** [`spec/memory/memory_model_spec.md`](spec/memory/memory_model_spec.md)
- **Concurrency:** [`spec/concurrency/execution_model_spec.md`](spec/concurrency/execution_model_spec.md)
- **Build System:** [`spec/build/build_lattice_spec.md`](spec/build/build_lattice_spec.md)
- **Security:** [`spec/security/security_flow_spec.md`](spec/security/security_flow_spec.md)
- **Tooling:** [`spec/tooling/metaprogramming_spec.md`](spec/tooling/metaprogramming_spec.md)
- **Optimization:** [`spec/optimization/optimization_manifold_spec.md`](spec/optimization/optimization_manifold_spec.md)
- **Distributed Systems:** [`spec/distributed_vector_clock_spec.md`](spec/distributed_vector_clock_spec.md)
- **Financial:** [`spec/financial/financial_spec.md`](spec/financial/financial_spec.md)
- **Math:** [`spec/math/maths_spec.md`](spec/math/maths_spec.md)
- **UI:** [`spec/ui/ui_constraint_algebra_spec.md`](spec/ui/ui_constraint_algebra_spec.md)

---

## 6. Change Log

| Version | Date | Author | Changes |
|---------|------|---------|---------|
| 1.0.0 | 2026-01-02 | Kilo Code | Initial version |

---

**End of Glossary**
