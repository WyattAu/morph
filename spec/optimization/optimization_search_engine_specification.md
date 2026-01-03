# Optimization Search Engine Specification (OSE)

- `System:* Morph Ecosystem
- `Version:* 1.0.0
- `Context:* Layer 2 (Compiler Backend) $\rightarrow$ Layer 1 (Build Cache)
- `Formalism:* Search-Based Software Engineering (SBSE), Profile-Guided Optimization (PGO)

- -

## 1. Introduction

### 1.1 Purpose

The OSE resolves **Optimization Holes** (`??`). An Agent often knows _what_ to optimize (e.g., "Unroll this loop") but lacks the hardware intuition to know _how much_ (e.g., "Factor 4 or 8?"). The OSE shifts this tuning burden from the Agent to the Compiler.

### 1.2 Scope

The OSE operates during the **Release Build** phase. In Debug builds, `??` resolves to a safe default (typically `1` or `0`) to minimize compilation latency.

- -

## 2. The Hole Primitive (`??`)

### 2.1 Valid Contexts

The `??` operator is a valid expression only in contexts expecting a **Scalar Compile-Time Constant**.

- **Valid:*
  ```rust
  const BUFFER_SIZE = ??;           // Global Constant
  @unroll(??) loop ...              // Attribute Parameter
  let arr: [i32; ??];               // Array Size
  ```
- **Invalid:*
  ```rust
  let x = runtime_val + ??;         // Runtime expression
  fn foo() -> ?? { ... }            // Return Type
  ```

### 2.2 Semantic Constraints

Every `??` must be bounded.

- **Implicit Bounds:*
  - `@unroll(??)` $\rightarrow$ Bounds: $[1 \dots \text{LoopBodySize}]$.
  - `u8` constant $\rightarrow$ Bounds: $[0 \dots 255]$.
- **Explicit Constraints (via Contracts):*
  ```rust
  const CHUNK = ??;
  // The OSE reads this invariant to prune the search space
  invariant { CHUNK % 64 == 0 && CHUNK <= 4096 }
  ```

- -

## 3. Search Architecture

The OSE operates as a feedback loop within the compiler driver.

### 3.1 The Search Pipeline

1.  **Extraction:* The compiler identifies all `??` tokens in a module.
2.  **Variant Generation:* The OSE generates $N$ candidate versions of the OIR (Optimizable IR), each with a different concrete value for `??`.
3.  **Micro-Benchmarking (Evaluation):*
    - **Static Mode (Fast):* Uses **LLVM-MCA** (Machine Code Analyzer) to simulate cycle counts based on the target CPU's instruction scheduler model.
    - **Dynamic Mode (Accurate):* JIT-compiles the specific function and runs it against a generated Fuzz Input or Agent-provided `@test` case.
4.  **Selection:* The candidate with the best **Fitness Score** is selected.
5.  **Locking:* The winning value is written to `morph.lock` to ensure future builds are deterministic.

### 3.2 The Objective Function (Fitness)

The definition of "Best" is controlled by the `@optimize(metric)` attribute.

| Metric                | Description                             | Evaluation Method                    |
| :-------------------- | :-------------------------------------- | :----------------------------------- |
| **`speed`** (Default) | Minimize CPU Cycles / Execution Time.   | Dynamic Benchmark or MCA throughput. |
| **`size`**            | Minimize Machine Code size (Bytes).     | Static `.text` section measurement.  |
| **`latency`**         | Minimize Instruction Pipeline Stalls.   | MCA structural hazard analysis.      |
| **`energy`**          | Minimize estimated Joules (Mobile/IoT). | Instruction weight heuristic.        |

- -

## 4. Search Algorithms

The OSE selects a search strategy based on the domain of the hole.

### 4.1 The Power-of-Two Grid (Default)

Used for memory sizes, buffer alignments, and texture dimensions.

- **Strategy:* Test $\{1, 2, 4, 8, 16, 32, \dots, \text{Max}\}$.
- **Rationale:* Computer architecture performance cliffs usually happen at powers of two (Cache Lines, Pages).

### 4.2 Hill Climbing (Local Search)

Used for loop unrolling factors and thread pool counts.

- **Strategy:*
  1.  Start at Seed (e.g., 4). Measure Fitness $F_4$.
  2.  Test Neighbors (3 and 5).
  3.  Move in direction of improvement.
  4.  Stop when neighbors offer no improvement ($\Delta < \epsilon$).

### 4.3 Binary Search

Used when the Fitness Function is proven monotonic (rare, but applicable to simple thresholds).

- -

## 5. Persistence & Determinism

### 5.1 The `morph.lock` Solution

Searching is expensive. Morph ensures it happens only once.

- **First Run:* OSE runs the search. Takes 500ms - 5s.
- **Locking:* The result is saved:
  ```toml
  # morph.lock
  [optimizations]
  "module_hash:function_name:hole_index_0" = 8
  ```
- **Subsequent Runs:* Compiler reads `morph.lock`. `??` is replaced by `8` instantly.
- **CI/CD:* The `morph.lock` file is committed to version control. The CI server uses the lockfile, ensuring the production build is deterministic.

### 5.2 Cache Invalidation

The OSE recalculates _only_ if:

1.  The AST of the function containing `??` changes.
2.  The Target CPU Architecture changes (e.g., dev on x86, deploy to ARM).
3.  The `morph.lock` entry is manually deleted.

- -

## 6. Safety & Resource Governance

### 6.1 The "Time Budget"

To prevent "Compilation Hangs," the OSE enforces strict quotas.

- **Per-Hole Budget:* Max 2 seconds of search time.
- **Global Budget:* Max 10% of total build time.
- **Fallback:* If the budget is exhausted, the OSE falls back to the **Canonical Default** (defined per context, e.g., Unroll=1, Buffer=1024).

### 6.2 Side-Effect Isolation

- **Constraint:* Code executed during Dynamic Evaluation (Micro-benchmarking) MUST be **Side-Effect Free** (`[Pure]`).
- **Enforcement:* The Effect System rejects `??` optimization on functions marked `[IO]` or `[Net]` unless the benchmark is strictly isolated (mocked).

- -

## 7. Interfaces

### 7.1 Agent Interaction

The Agent interacts with OSE via the MCP `diagnostics` endpoint.

- **Request:* Agent writes `const X = ??;`.
- **Response (Post-Build):*
  ```json
  {
    "type": "optimization_result",
    "hole_id": "AST-502",
    "selected_value": 16,
    "improvement": "14% speedup vs default",
    "suggestion": "Consider hardcoding 16 if target hardware is fixed."
  }
  ```
- **Reasoning:* This allows the Agent to "learn" the hardware characteristics over time.

- -

## 8. Requirements Traceability

| Feature                  | Rationale                    | Requirement |
| :----------------------- | :--------------------------- | :---------- |
| **`??` Operator**        | Defines the search space.    | REQ-META-01 |
| **`morph.lock`**         | Ensures reproducible builds. | REQ-BLD-02  |
| **LLVM-MCA Integration** | Fast static profiling.       | REQ-COMP-04 |
| **Budget Quotas**        | Prevents build system DOS.   | REQ-SAFE-04 |

This specification turns the compiler into an empirical scientist, running experiments on behalf of the Agent to bridge the gap between abstract logic and concrete silicon.
