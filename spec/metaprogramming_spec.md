# Morph Metaprogramming & Generics Specification (MGS)

**System:** Morph Programming Language
**Version:** 1.0.0-FINAL
**Context:** Layer 2 (Compilation Phase)
**Formalism:** Monomorphization, Staged Compilation, Attribute-Driven

---

## 1. Parametric Polymorphism (Generics)

Morph utilizes a **Monomorphization** strategy (similar to C++ Templates or Rust Generics) rather than Type Erasure (Java). This ensures that abstractions have zero runtime cost.

### 1.1 Definition & Syntax

Generics allow functions and data structures to be parameterized by Types or Constants.

- **Syntax:**
  ```rust
  fn map<T, U>(list: List<T>, op: fn(T)->U) -> List<U> { ... }
  ```
- **Instantiation:**
  When the Agent writes `map(int_list, to_str)`, the compiler generates a specialized symbol `map_i32_str` in the OIR.
- **Rationale:** Eliminates dynamic dispatch (v-tables) and boxing, which is critical for the performance requirements of AI-generated code.

### 1.2 Constraint Enforcement (Traits)

Unconstrained generics are **Prohibited** in public APIs. All type parameters must strictly adhere to a Semantic Trait (Concept).

- **Syntax:** `<T: Serializable + Comparable>`
- **Validation:** The Semantic Tree validates that the concrete type implements the Trait _before_ generating the specialized code.
- **Rationale:** Prevents "Template Metaprogramming Hell" where errors occur deep inside library code. The Agent receives errors at the _call site_ (e.g., "Type `User` does not implement `Serializable`").

### 1.3 Constant Generics

Types can be parameterized by compile-time scalar constants.

- **Syntax:** `type Matrix<T, ROWS: const int, COLS: const int> = ...`
- **Usage:** `let m: Matrix<f32, 4, 4> = ...`
- **Rationale:** Critical for Linear Algebra and ML kernels. Allows the OIR to perform complete loop unrolling and register tiling.

---

## 2. Compile-Time Execution (`comptime`)

Morph adopts a **Staged Compilation** model. The compiler contains a sandboxed interpreter capable of executing a subset of Morph code to generate data or logic.

### 2.1 The `comptime` Block

- **Semantics:** Any code within `comptime { ... }` is executed during the Semantic Analysis phase.
- **Output:** The result of the block replaces the block itself in the AST.
- **Example (Pre-computed Lookup Table):**
  ```rust
  const SIN_TABLE = comptime {
      mut t = [0.0; 360];
      loop i in 0..360 { t[i] = sin(degrees(i)); }
      ret t;
  };
  ```
  - **Result:** In the final binary, `SIN_TABLE` is a static array of bytes in the `.rodata` section. No runtime calculation occurs.

### 2.2 Sandboxing & Limits

To prevent malicious Agents or infinite loops from hanging the build:

- **Resource Quota:** 500ms CPU time, 128MB RAM allocation.
- **I/O Restriction:** Read-Only access to the project directory (for embedding assets). No Network access.
- **Rationale:** Ensures reproducible, hermetic builds.

### 2.3 Asset Embedding

`comptime` is the standard mechanism for including static assets.

```rust
const LOGO_PNG = comptime { include_bytes("assets/logo.png") };
```

- **Result:** The file content is embedded directly into the binary as a `^Bytes` array.

---

## 3. The Optimization Hole (`??`)

This is a Morph-exclusive feature designed for **AI-Compiler Symbiosis**.

### 3.1 Definition

The `??` token represents a **Search Space**. It is valid anywhere a numeric constant or heuristic parameter is expected.

### 3.2 Compilation Process (The Search)

When the compiler encounters `??`:

1.  **Identification:** It identifies the context (e.g., Loop Unroll Factor, Buffer Size).
2.  **Generation:** It generates multiple OIR variants (e.g., `unroll=4`, `unroll=8`, `unroll=16`).
3.  **Evaluation:**
    - **Heuristic Mode:** Uses internal cost models (LLVM-MCA) to pick the best theoretical performance.
    - **Profile Mode:** Benchmarks the snippets if a test harness is available.
4.  **Collapse:** The `??` is replaced by the winning constant in the final machine code.

### 3.3 Example

```rust
fn copy_memory(src: &u8, dst: &u8, len: usize) {
    // Agent doesn't know the optimal chunk size for this CPU
    const CHUNK = ??;

    loop i in 0..len step CHUNK {
        // ... SIMD copy logic ...
    }
}
```

- **Rationale:** Agents often hallucinate "magic numbers" (e.g., 1024 vs 4096). This feature allows the Agent to admit ignorance and delegate tuning to the hardware-aware compiler.

---

## 4. Compiler Directives (Attributes)

Morph utilizes Semantic Attributes (prefixed with `@`) to allow the Agent to declare **Intent**, enforcing constraints on the OIR generation or static analysis.

### 4.1 Hardware Targeting

These attributes control backend dispatch.

| Attribute     | Context  | Semantics                                                                                                         |
| :------------ | :------- | :---------------------------------------------------------------------------------------------------------------- |
| **`@gpu`**    | Function | Compiles logic to SPIR-V/PTX. **Constraint:** Forbidden from using System I/O, Heap Allocation, or `ref` globals. |
| **`@kernel`** | Function | Marks a GPU entry point (Compute Shader). Implies `@gpu`.                                                         |
| **`@wasm`**   | Function | Exports the symbol to WebAssembly memory space, enforcing JS-compatible types.                                    |

**Rationale:** Prevents "Performance Hallucinations." If an Agent writes `@gpu` but uses `print()`, the compiler catches the violation immediately.

### 4.2 Optimization Strategies

These attributes guide the OIR optimizer passes.

| Attribute        | Context  | Semantics                                                                                                          |
| :--------------- | :------- | :----------------------------------------------------------------------------------------------------------------- |
| **`@inline`**    | Function | Forces inlining at call sites.                                                                                     |
| **`@no_inline`** | Function | Prevents inlining (for debug traces).                                                                              |
| **`@simd`**      | Loop     | Asserts that iterations are independent. **Constraint:** Compile error if loop dependencies prevent vectorization. |
| **`@unroll(N)`** | Loop     | Unrolls the loop N times. Supports `??` for search-based unrolling.                                                |
| **`@cold`**      | Block    | Marks a branch as unlikely, optimizing layout for the hot path.                                                    |

**Rationale:** Allows the Agent to act as a "Performance Engineer" by explicitly requesting vectorization or unrolling.

### 4.3 Diagnostics & Safety

These attributes manage compiler feedback.

| Attribute       | Context  | Semantics                                                                  |
| :-------------- | :------- | :------------------------------------------------------------------------- |
| **`@unused`**   | Variable | Suppresses "Unused Variable" warnings (e.g., `[[maybe_unused]]`).          |
| **`@must_use`** | Type/Fn  | Warning if the return value/type is discarded. Default for `Result` types. |
| **`@test`**     | Function | Marks a logic block as a Unit Test.                                        |
| **`@fuzz`**     | Function | Marks a logic block for Automatic Fuzzing generation.                      |

---

## 5. Static Reflection (Introspection)

Morph supports **Compile-Time Introspection** to drive code generation, eliminating the need for runtime reflection.

### 5.1 Type Inspection

`comptime` code can query the structure of types via the `meta` namespace.

- `meta.fields(T)`: Returns a list of field names and types.
- `meta.name(T)`: Returns the string name.
- `meta.has_trait(T, Trait)`: Returns boolean.

### 5.2 Use Case: Intrinsic Serialization

This mechanism powers the auto-generated JSON support (REQ-11.1).

```rust
// Internal logic for .toJson()
comptime {
    loop field in meta.fields(Self) {
        emit(field.name, self[field.name].toJson());
    }
}
```

- **Rationale:** Removes the need for external tools (Protoc) or runtime reflection overhead.

---

## 6. Macros (AST Generation)

Morph strictly **rejects** text-substitution macros. It supports **AST-Based Generation** via generative functions.

### 6.1 Generative Logic

A function marked `comptime` that returns `Code` (an AST fragment) can be injected.

- **Constraint:** The AST fragment must be hygienically typed.
- **Usage:** Used for Domain Specific Languages (DSLs) like the `routing` block or SQL mapping.

---

## 7. Requirements Traceability

| Feature              | Requirement Addressed         | Implementation                    |
| :------------------- | :---------------------------- | :-------------------------------- |
| **Monomorphization** | Performance (REQ-META-02)     | OIR specialization per type.      |
| **`@gpu` / `@simd`** | Hardware Control (REQ-3.2.3)  | Backend dispatch & loop analysis. |
| **`??` Operator**    | Agent Usability (REQ-META-01) | Compiler search pass.             |
| **`comptime`**       | Static Gen (REQ-META-03)      | Sandboxed interpreter.            |
| **`@unused`**        | Diagnostics                   | Static analysis suppression.      |
| **Reflection**       | Serialization (REQ-TYPE-03)   | Compile-time meta-programming.    |
