# Build System Architecture Document (BSAD)

**System:** Morph Build System (MBS)
**Version:** 1.0.0-FINAL
**Context:** Integral component of the Morph Ecosystem
**Status:** Architecture Locked

---

## 1. Architectural Overview

### 1.1 Design Philosophy

The Morph Build System (MBS) is a **Declarative, Graph-Centric, and Hermetic** orchestration engine. It fundamentally abstracts away imperative build scripts by treating the codebase as a structured, immutable database. The MBS functions as a **Topological Query Engine**, inferring the complete dependency graph and build instructions directly from the Abstract Syntax Tree (AST) and package metadata.

### 1.2 Core Objectives

1.  **Zero-Configuration Build Graph:** The dependency graph is automatically discovered and maintained, eliminating manual build script authoring.
2.  **Universal Reproducibility:** Every build, regardless of environment or initiator (Agent or Human), must yield bit-for-bit identical output binaries.
3.  **Correctness by Construction:** Build failures are identified as graph topology or semantic errors by the compiler, providing precise, actionable diagnostics before execution.
4.  **Optimal Efficiency:** Leveraging fine-grained caching and parallel execution to achieve build times comparable to highly optimized, hand-tuned systems.

---

## 2. System Components (Architecture)

### 2.1 The Graph Engine (Topology Resolver)

- **Role:** Constructs and maintains the definitive Build Execution Graph (BEG).
- **Input:** Workspace root path or a specific package identifier.
- **Process:**
  1.  **Package Discovery:** Recursively scans the workspace for `morph.pkg` manifests, identifying all local packages.
  2.  **AST Analysis:** Parses each package's source files into their Canonical ASTs.
  3.  **Dependency Inference:** Resolves `import` statements by matching declared package names (or specific symbol hashes for external dependencies) against the discovered package map. Creates edges in the BEG.
  4.  **Graph Validation:** Performs static analysis on the BEG for circular dependencies and ambiguous references, raising "Topology Errors" as structured diagnostics.
- **Output:** A fully-resolved, immutable, and canonical **Build Execution Graph (BEG)** representing all necessary compilation and linking steps.

### 2.2 The Artifact Cache (Deterministic Memoization)

- **Role:** Stores and retrieves intermediate and final build artifacts based on cryptographic hashes.
- **Storage Backend:** Tiered architecture comprising a local content-addressable store (e.g., SQLite-backed key-value) and configurable remote object storage (e.g., S3-compatible).
- **Key Generation:** Each cache entry key is `SHA256(InputHash + ToolchainHash + TargetArch + BuildFlags)`.
  - `InputHash`: Merkle root of the AST for a compilation unit.
  - `ToolchainHash`: Hash of the exact Morph Compiler version and its internal toolchain.
  - `TargetArch`: Specific CPU architecture (e.g., `x86_64-linux-avx512`).
  - `BuildFlags`: Canonicalized representation of compiler flags (e.g., `O3`, `debug`).
- **Granularity:** Supports caching at multiple levels:
  - **MorphIR Modules:** Compiled MorphIR bytecode for a given package.
  - **Function Objects:** Relocatable machine code fragments for individual functions.
  - **Final Binaries:** Statically linked executables (`.mpx`) or libraries (`.mar`).

### 2.3 The Sandbox Orchestrator (Hermetic Execution Environment)

- **Role:** Guarantees isolation and reproducibility for every build action.
- **Mechanism:** Utilizes operating system-level virtualization (e.g., Linux Namespaces, chroot, or custom Wasm-based sandboxes) to create ephemeral, isolated build environments.
- **Virtual File System (VFS):** Each sandbox is provisioned with a minimal, read-only VFS containing _only_ the explicitly declared build inputs (source files, vendored dependencies, Morph toolchain).
- **Strict Access Control:** Network access is restricted to artifact fetching. All host-system paths (`/usr`, `/lib`, user environment variables) are strictly inaccessible to the build process.

### 2.4 The Polyglot Compiler Driver

- **Role:** Manages the invocation and output processing of various language toolchains.
- **Morph Toolchain Integration:** Communicates with the Morph Compiler Daemon (via MCP/IPC) to trigger AST parsing, MorphIR generation, and OIR lowering.
- **C/C++ Foreign Compilation:** Embeds a **Clang-derived compiler** for compiling vendored C/C++ dependencies. This ensures ABI/API consistency with the Morph-generated code and maintains hermeticity.

### 2.5 The Incremental Linker

- **Role:** Assembles compiled units into final executable or library artifacts.
- **Algorithm:** Operates on pre-computed machine code segments retrieved from the Artifact Cache. It performs efficient, partial linking by stitching function-level object fragments (`.o`) directly into the final binary's memory layout, avoiding full recompilation of unaffected translation units.

---

## 3. Data Flow & Build Pipelines

### 3.1 Workspace Resolution Pipeline (Topological Discovery)

1.  **Scan Phase:** MBS is invoked from a directory containing `morph.workspace` (the monorepo root). It recursively discovers all `morph.pkg` manifests, identifying all local packages.
2.  **Indexing Phase:** The MBS maps each discovered local package name to its absolute path. This forms the **Virtual Workspace Namespace**.
3.  **Dependency Graph Construction:** For each package's source, the MBS:
    - Parses `import` statements to extract logical dependency names.
    - Resolves these names against the Virtual Workspace Namespace (prioritized) and the external Registry.
    - Adds directed edges to the BEG.
4.  **Validation Phase:** The BEG is validated for:
    - Circular dependencies (topology error).
    - Ambiguous imports (multiple packages with the same name, resolved by priority rules).
    - Diamond Dependency Conflicts (resolved by implicit multi-version linking where unique hashes allow).

### 3.2 Compilation & Linking Pipeline (Execution)

1.  **Topological Sort:** The BEG is topologically sorted to determine the correct build order (dependencies before dependents).
2.  **Artifact Retrieval/Generation:** For each node (function, module, package) in the BEG:
    - **Cache Lookup:** Query the Artifact Cache using the cryptographic key.
    - **Cache Hit:** Retrieve the pre-computed artifact (e.g., MorphIR, machine code).
    - **Cache Miss:**
      - **Morph Code:** Invoke the Polyglot Compiler Driver to generate MorphIR, then OIR, then machine code.
      - **C/C++ Code:** Invoke the embedded Clang compiler for specified source.
      - The newly generated artifact is then committed to the Artifact Cache.
3.  **Final Linking:** The Incremental Linker assembles the final `.mpx` or `.mar` artifact by stitching together cached or newly generated machine code.

---

## 4. Workspaces & Dependency Management

### 4.1 Local Workspace Resolution (Monorepo Cohesion)

- **Mechanism:** Within a workspace (defined by `morph.workspace`), package dependencies are resolved by their **Logical Package Name** (e.g., `import physics_engine`), not by filesystem path.
- **Priority:** Local workspace definitions take precedence over external registry dependencies for name resolution.
- **Automatic Target Inference:**
  - A package containing a `main(ctx: Context)` entry point is inferred as an **Executable** (produces `.mpx`).
  - A package without a `main` entry point is inferred as a **Library** (produces `.mar`).
  - These inferences can be overridden via package-level traits (e.g., `[DynamicLib]`).

### 4.2 External Dependency Management (Registry Integration)

- **Format:** External libraries are retrieved from the **Morph Vector Registry** as **MorphIR bytecode** (`.mar`).
- **Declaration:** `morph.pkg` manifests declare external dependencies by unique registry identifier and a pinned cryptographic hash (e.g., `github.com/org/pkg@sha256:abcd...`).
- **Versioning:** The system implicitly supports **multi-version linking** of the same library (Diamond Dependencies) by treating each version's MorphIR (and thus its compiled symbols) as unique entities due to content addressing.

### 4.3 C/C++ Foreign Function Interface (FFI) Integration

- **Vendoring:** C/C++ dependencies must be explicitly declared in `morph.pkg` with a source URL and hash. The MBS downloads and vendors these sources.
- **Hermetic Compilation:** The MBS compiles these vendored C/C++ sources internally using its embedded Clang driver, guaranteeing ABI compatibility with Morph-generated code by using the exact same compiler flags and target environment.

---

## 5. Deployment & Artifacts

### 5.1 Artifact Types

- **`.mar` (Morph Archive):** The standard format for publishing and distributing Morph libraries. Contains MorphIR, semantic metadata, and type contracts.
- **`.mpx` (Morph Portable Executable):** A self-contained, statically linked binary. It bundles all dependencies (including the Morph Runtime and vendored C/C++ libraries) and assets into a single file.
- **`.o` (Object Fragment):** Internal object file used by the incremental linker.

### 5.2 OIR Distribution Model (ABI Stability)

- **Publisher Workflow:** Source code is compiled once to MorphIR (`.mar`) and uploaded to the registry.
- **Consumer Workflow:** Upon consuming a `.mar` library, the MBS compiles its MorphIR to machine code _locally_, using the consumer's specific compiler version, target architecture, and build flags.
- **Benefit:** This approach entirely eliminates ABI compatibility issues across different compiler versions or target platforms, as the final machine code is always generated in a unified context.

---

## 6. Interfaces

### 6.1 Agent Interface (Model Context Protocol - MCP)

The MBS exposes a structured, queryable API to AI Agents.

- `GET /build_graph?target={package_name}`: Returns a JSON representation of the BEG.
- `POST /build?target={package_name}`: Triggers a build, returning structured diagnostics.
- `GET /check_integrity?target={package_name}`: Runs static analysis and contract checks.
- `POST /diagnose_dependency_error`: Allows an Agent to provide context about a build failure and receive an explicit proposed fix (e.g., "Add `morph.pkg` entry for `std.net`").

### 6.2 Human Interface (CLI)

- `morph build [target]`: Compiles the specified package or the default workspace entry point.
- `morph test [target]`: Executes test logic blocks.
- `morph release [target]`: Performs an optimized, stripped build for production.
- `morph graph [target]`: Generates a visualization of the BEG (e.g., Graphviz DOT format).
- `morph inspect [hash]`: Dumps the AST, MorphIR, or metadata for a given content hash.

---

## 7. Safety & Limits

### 7.1 Resource Governance

- **Comptime Execution:** Sandboxed `comptime` blocks are subject to strict CPU time (e.g., 500ms) and memory (e.g., 128MB) limits to prevent infinite loops during compilation.
- **Fuzzing Limits:** Automated fuzzing runs for a configurable duration (default 60s per target) during development builds to balance thoroughness with build time.

### 7.2 Security by Default

- **Network Access:** The core compilation process operates in an **offline-by-default** sandbox. Network access is restricted to a dedicated "Fetcher" component for explicit dependency download.
- **Supply Chain Integrity:** All registry dependencies are fetched via cryptographic hash validation against a lockfile.

---

## 8. Requirements Traceability Matrix (Cross-Reference to SRS)

| Component / Feature            | Morph SRS Requirement(s)             |
| :----------------------------- | :----------------------------------- |
| **Graph Engine**               | REQ-COMP-01, REQ-COMP-02, REQ-BLD-02 |
| **Artifact Cache**             | REQ-BLD-03                           |
| **Sandbox Orchestrator**       | REQ-BLD-01                           |
| **Polyglot Compiler Driver**   | REQ-CONC-04 (for FFI), REQ-BLD-01    |
| **Incremental Linker**         | REQ-BLD-03                           |
| **Workspace Discovery**        | REQ-PKG-01                           |
| **Automatic Target Inference** | REQ-PKG-02                           |
| **OIR Distribution Model**     | REQ-COMP-03, REQ-PKG-02              |
| **Registry Integration**       | REQ-PKG-02                           |
| **C/C++ FFI Compilation**      | REQ-BLD-01                           |
| **MCP Integration**            | REQ-MCP-01, REQ-MCP-02               |
| **Resource Governance**        | REQ-META-01, REQ-SAFE-04             |
| **Security by Default**        | REQ-BLD-01, REQ-SAFE-04              |
