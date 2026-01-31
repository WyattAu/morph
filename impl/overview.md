# Implementation Strategy Document (ISD)

* System:** Morph Toolchain
* Version:** 1.0.0
* Target:** Bootstrapping Phase (v0.1 $\rightarrow$ v1.0)

- -

## 0. Formal Verification Layer (COMPLETED)

**Status: Lean 4 Migration COMPLETED** ✓

The Morph project includes a comprehensive formal verification layer that provides mathematical guarantees about the language's semantics, type system, and execution model. This layer has been successfully migrated to Lean 4 v4.10.0.

### 0.1 Technology Stack

- **Formal Verification Framework**: Lean 4 v4.10.0
- **Standard Library**: mathlib4 (comprehensive mathematical library)
- **Proof Automation**: aesop (automated proof search), batteries (collection of useful tactics)
- **Build System**: Lake (Lean's package manager and build tool)

### 0.2 Specification Modules

The formal verification layer includes 40+ specification modules, each following the three-file module pattern:

- **Spec.lean**: Formal specifications and type definitions
- **Lemmas.lean**: Lemmas and theorems with complete proofs
- **Examples.lean**: Examples demonstrating usage

Key specification areas include:

- **Algebraic Structures**: AbiAlignmentAlgebra, BuildLattice, DualOptimization
- **Process Calculi**: ConcurrencyProcessAlgebra, LayeredConcurrency, SchedulerRandomizedStealing
- **Memory Models**: MemoryModel, MemoryAcyclicity, MemoryAffineLogic
- **Type Systems**: ScopingLambdaCalculus, DialectProjection, MonadicEffect
- **Security**: SecurityFlow, SecurityOCap, InfrastructureSafetyContracts
- **Language Features**: LexicalStructureSyntax, MorphLanguage, OperatorNullCoalescing
- **Domain-Specific**: Financial, Licensing, LinkerLogic

### 0.3 Migration Details

The migration to Lean 4 was completed with the following outcomes:

- All specification modules have been migrated to Lean 4 v4.10.0
- All proofs are complete (no `sorry` placeholders)
- Build system configured for Lean 4 using Lake
- CI/CD pipelines updated for Lean 4 compilation
- Documentation updated to reflect Lean 4 usage

For more details on the Lean 4 migration, see:
- [ADR-003: Lean 4 with mathlib4](../.specs/02_adrs/ADR-003-lean4-mathlib4.md)
- [ADR-004: Lake Build System](../.specs/02_adrs/ADR-004-lake-build-system.md)
- [Coding Standards](../.specs/01_standards/coding_standards.md)

### 0.4 Relationship to Runtime Implementation

The formal verification layer (Lean 4) and the runtime implementation (Rust/C++) serve complementary purposes:

- **Formal Verification Layer**: Provides mathematical guarantees about the language specification, type system, and semantics. This is the "specification" layer that defines what the Morph language should do.
- **Runtime Implementation**: Provides the actual executable implementation of the Morph language, including the compiler, runtime environment, and tooling. This is the "implementation" layer that defines how the Morph language works in practice.

The formal verification layer serves as the "source of truth" for the runtime implementation. The Rust/C++ implementation should conform to the specifications defined in Lean 4, and where possible, the formal proofs can guide implementation decisions and verify correctness properties.

- -

## 1. The Toolchain Language Decision

You suggested **C++**. While C++ is the industry standard for high-performance runtimes (V8, JVM), it is risky for the **Compiler Frontend** due to memory safety issues and slow iteration speeds.

* Recommendation: The Hybrid "Rust + C++" Architecture.**

### 1.1 The Compiler & Build System (MBS) $\rightarrow$ **Rust**

We should write the **Morph Compiler (`morphc`)** and **Build System (`morph`)** in **Rust**.

- **Why:**
  - **Algebraic Data Types (Enums):** Morph's AST is heavily reliant on ADTs. Rust's `enum` matching is superior to `std::variant`.
  - **Memory Safety:** We are parsing untrusted Agent code. A buffer overflow in the compiler is a security vector. Rust prevents this.
  - **Parallelism:** Rust's `rayon` library makes writing the parallel graph-based build system (MBS) trivial.
  - **Serialization:** `serde` is the gold standard for high-performance JSON/Binary serialization (essential for MCP and MorphIR).

### 1.2 The Runtime & Execution Engine (MRE) $\rightarrow$ **C++23**

We should write the **Morph Runtime Environment (`libmorphrt`)** in **C++23**.

- **Why:**
  - **Raw Pointer Manipulation:** Implementing the Arena Allocator and Fiber Context Switching (`ucontext` / assembly) requires "unsafe" access that is cleaner in C++.
  - **LLVM Integration:** LLVM is written in C++. Integration is seamless.
  - **ABI Control:** We need precise layout control for the `dec128` and `BigInt` primitives.
  - **Vendor SDKs:** CUDA, Vulkan, and OS APIs (Win32/POSIX) have native C++ headers.

- -

## 2. The Intermediate Representation (MorphIR)

MorphIR is the stable interface between the frontend (Analysis) and backend (Codegen). It must be **Platform-Agnostic** and **Serializable**.

### 2.1 Format Specification

We will use **FlatBuffers** to define MorphIR. This allows Zero-Copy reading from disk (critical for fast builds).

* Schema Concept:**

```fbs
table Module {
  hash: [ubyte];
  functions: [Function];
  types: [TypeDefinition];
}

table Function {
  name_hash: u64;
  blocks: [BasicBlock];
  attributes: [Attribute]; // @gpu, @simd
}

union Instruction {
  Alloc,      // Stack allocation
  Call,       // Static dispatch
  CallVirt,   // Interface dispatch
  Spawn,      // Green thread creation
  Yield,      // IO Suspension
  VectorAdd,  // SIMD primitive
  // ...
}
```

### 2.2 The "OIR" Lowering Phase

MorphIR is too high-level for CPU execution. We utilize **LLVM IR** as the physical OIR.

- **MorphIR:** `Spawn(FunctionId)`
- **Lowering Logic (C++):**
  ```cpp
  // Translates MorphIR 'Spawn' to Runtime Call
  Value* spawn_task = builder.CreateCall(
      runtime_funcs.spawn_fiber,
      { function_ptr, context_ptr }
  );
  ```

- -

## 3. Backend Implementations

### 3.1 The CPU Backend (LLVM)

- **Tool:** LLVM Core Libraries (18.x or newer).
- **Strategy:**
  - **Fibers:** Implemented via **Shadow Stacks** or Split Stacks to support the small memory footprint.
  - **Async:** We use `llvm.coro` intrinsics or custom state-machine generation for the `async let` logic.
  - **Optimization:** We write custom LLVM Passes to handle the `??` (Optimization Hole) resolution.

### 3.2 The GPU Backend (CUDA / PTX)

We do not generate C++ CUDA code (too slow to compile). We generate **NVVM IR** (LLVM IR with NVPTX intrinsics) directly.

- **Mapping:**
  - `loop` inside `@gpu` $\rightarrow$ Mapped to Thread ID (`threadIdx.x`).
  - `^Tensor` $\rightarrow$ Mapped to Device Memory Pointers.
  - `shared` keyword $\rightarrow$ `__shared__` memory space.
- **Safety:** The compiler injects a check: If code inside `@gpu` calls `malloc` or `print`, the build fails _before_ reaching the NVPTX generator.

### 3.3 The Graphics Backend (Vulkan/SPIR-V)

For the UI (`morph::ui`) and cross-vendor compute.

- **Tool:** **Google's `shaderc`** or **`rspirv`**.
- **Pipeline:**
  1.  Morph UI Layout Engine runs on CPU.
  2.  Generates **MUI-IR** (Command Buffer).
  3.  Runtime uploads MUI-IR to a Uniform Buffer Object (UBO).
  4.  Vertex Shader reads commands and emits triangles.
  5.  Fragment Shader renders SDF text and Rounded Rects.

### 3.4 The Web Backend (Wasm)

- **Strategy:** **Linear Memory Model**.
- **Implementation:**
  - We treat Wasm memory as a raw byte array.
  - We compile `libmorphrt` (The Runtime) to Wasm.
  - We link the User Code (compiled via LLVM Wasm backend) against it.
- **The Bridge:**
  - We generate a small `morph_bridge.js` file.
  - It handles the DOM events (Mouse/Keyboard) and serializes them into the **Input Ring Buffer** in Wasm memory.

- -

## 4. Specific Component Implementations

### 4.1 The Morph Codebase Manager (MCM)

- **Database:** **SQLite**.
- **Why:** It is a single file, highly reliable, and supports concurrent reads.
- **Schema:**
  ```sql
  CREATE TABLE modules (
      ast_hash BLOB PRIMARY KEY,
      source_min BLOB,
      semantic_vector BLOB -- (384-dim float array for RAG)
  );
  ```
- **Vector Search:** Use `sqlite-vss` (Vector Similarity Search) extension to enable the Agent to query symbols by meaning.

### 4.2 The Optimization Search Engine (OSE)

- **Runner:** A dedicated LLVM JIT instance (`LLJIT`).
- **Process:**
  1.  Isolate the function with `??`.
  2.  Generate variants (Variant A: unroll=4, Variant B: unroll=8).
  3.  JIT compile both.
  4.  Run them against the `@test` harness 10,000 times.
  5.  Measure CPU cycles via `rdtsc` instruction.
  6.  Return the winner.

### 4.3 The Auto-Fuzzer

- **Library:** **libFuzzer** (LLVM integration).
- **Strategy:**
  - Morph Compiler generates a C++ wrapper that accepts `uint8_t* data`.
  - Wrapper acts as a "Deserializer" converting random bytes into valid Morph `data` structures (based on types).
  - If `data` conforms to `requires` contract, it calls the function.
  - If function panics, `libFuzzer` saves the input.

- -

## 5. Bootstrapping Roadmap

### Stage 1: The "C-Core" (Months 1-3)

- Write `libmorphrt` in C++.
- Implement the Arena Allocator, Green Thread Scheduler, and basic TCP/File I/O.
- _Output:_ A C++ library that can run manually constructed tasks.

### Stage 2: The "Rust-Shell" (Months 3-6)

- Write `morphc` in Rust.
- Implement the Parser (using `chumsky` or `nom`) for the `min` syntax.
- Implement the AST-to-LLVM Lowering.
- _Output:_ A compiler that can compile "Hello World" to an executable linking `libmorphrt`.

### Stage 3: The "Agent Layer" (Months 6-9)

- Implement the MCP Server.
- Integrate SQLite and Vector Embeddings.
- Build the "Tabula Rasa" prompt generators.
- _Output:_ An Agent can now write code, hit errors, and fix them.

### Stage 4: Domain Extensions (Months 9-12)

- Add the `dec128` logic to LLVM lowering.
- Add the UI Renderer (Vulkan backend).
- _Output:_ v1.0 Release Candidate.

- -

## 6. Summary

We are building a **Hybrid Toolchain**:

1.  **Rust Frontend:** Safe, parallel, JSON-native (for Agents/Builds).
2.  **C++ Backend:** Raw, fast, hardware-native (for Runtime/FFI).
3.  **LLVM Middle:** The heavy lifter for optimization.

This approach minimizes the risk of writing a compiler from scratch while maximizing the performance required for the "Post-Text" era.
