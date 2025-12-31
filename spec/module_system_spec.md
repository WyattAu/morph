# Morph Module System Specification (MSS)

**System:** Morph Programming Language
**Version:** 1.0.0
**Context:** Layer 2 (Compilation) & Layer 1 (Infrastructure)
**Formalism:** Content-Addressable, Graph-Based, Hermetic

---

## 1. Definitions

### 1.1 The Module (`mod`)

- **Definition:** The atomic unit of code organization. Usually corresponds to a single `.morph` source file or a directory of files.
- **Identity:** A module is identified internally by the **Merkle Hash** of its Abstract Syntax Tree (AST).
- **Namespace:** A module creates a local namespace for symbols defined within it.

### 1.2 The Package (`pkg`)

- **Definition:** The atomic unit of distribution and versioning. Defined by a `morph.pkg` manifest.
- **Composition:** A Package contains a tree of Modules.
- **Output:** A Package compiles to a single Artifact (`.mar` Library or `.mpx` Executable).

### 1.3 The Workspace (`ws`)

- **Definition:** A collection of Packages sharing a common root and dependency graph.
- **Resolution:** Enables "Live Linking" between packages without publishing to a registry.

---

## 2. Addressing & Resolution

Morph decouples **Naming** (for Humans/Agents) from **Linking** (for Compilers).

### 2.1 Content-Addressable Linking

- **The Truth:** The compiler links against `Hash(AST)`.
- **The View:** The Agent uses logical names (`use std.net`).
- **Mechanism:**
  1.  Agent writes `use physics;`.
  2.  Compiler queries Workspace Map: `physics` $\rightarrow$ Package UUID.
  3.  Compiler queries Artifact Cache: Package UUID $\rightarrow$ Latest AST Hash.
  4.  Linker binds to the Hash.
- **Benefit:** If the Agent renames the _file_ `physics.morph` to `engine.morph` but leaves the package name as `physics`, the code **does not break**. The logical link persists.

### 2.2 Atomic Refactoring

- **Scenario:** Agent renames function `calculate` to `calc`.
- **Traditional Failure:** All files importing `calculate` break.
- **Morph Behavior:**
  - The IDE/MCP sends a `patch_ast` command.
  - The Compiler updates the definition.
  - The Compiler walks the **Reverse Dependency Graph** (known via Hashes).
  - It automatically updates all call sites in the Workspace to point to the new symbol name.
  - **Result:** Zero-error refactoring.

---

## 3. Import Syntax (`use`)

Morph uses the `use` keyword to bring symbols into scope.

### 3.1 Basic Imports

```rust
// Import a package from the workspace/registry
use std;
use physics_engine;

// Import a local module relative to current
use .utils;
```

### 3.2 Selective & Alias Imports

```rust
// Import specific symbols
use std.math::{sin, cos, PI};

// Rename on import (Conflict Resolution)
use std.json as j;
use other.json as o;
```

### 3.3 Re-Exporting (`pub use`)

Modules can act as facades for internal implementation details.

```rust
// In lib.morph
pub use .internal.deep_logic.User;
```

- **Effect:** `User` appears to exist at the library root, hiding the folder structure.

---

## 4. Visibility & Encapsulation

Morph enforces a **"Private by Default"** security model to prevent API surface pollution.

### 4.1 Access Modifiers

| Keyword       | Scope       | Description                                                     |
| :------------ | :---------- | :-------------------------------------------------------------- |
| _(none)_      | **Private** | Visible only within the current Module (File).                  |
| `pub`         | **Package** | Visible to other modules within the same Package.               |
| `pub(global)` | **Public**  | Exported in the `.mar` artifact; visible to external consumers. |

### 4.2 Granular Control

- **Fields:** Struct fields are private by default.
  ```rust
  type User = {
      pub name: str, // Accessible everywhere
      id: u64        // Accessible only in this module
  };
  ```
- **Rationale:** Forces Agents to write accessor methods or constructors, ensuring Invariants (`invariant`) are checked during construction.

---

## 5. Dependency Management

### 5.1 The `morph.pkg` Manifest

This file defines the Package Identity and dependencies.

```toml
[package]
name = "my_game"
version = "1.0.0"
edition = "2025"

[dependencies]
# Registry Dependency (Pinned by Hash implies immutability)
std = { registry = "morph/std", version = "1.2" }

# Workspace Dependency (Live Head)
physics = { path = "../physics" }

# Git Dependency (Vendored)
legacy_algo = { git = "https://...", rev = "a1b2c3" }
```

### 5.2 Diamond Dependencies (Multi-Version Linking)

Morph solves "DLL Hell" via symbol mangling based on hash.

- **Scenario:**
  - App depends on `LibA` and `LibB`.
  - `LibA` depends on `Log v1.0`.
  - `LibB` depends on `Log v2.0`.
- **Resolution:**
  - The linker includes **BOTH** `Log v1.0` and `Log v2.0` in the final binary.
  - Symbols are name-mangled: `Log_v1_0_Logger` and `Log_v2_0_Logger`.
  - **Constraint:** You cannot pass an object created in `LibA` (Log v1) to `LibB` (Log v2) unless they are structurally identical and explicitly cast.

---

## 6. The Registry Protocol

### 6.1 Publishing

- **Input:** Source Code + `morph.pkg`.
- **Process:**
  1.  Compiler generates **MorphIR** (Platform Agnostic Bytecode).
  2.  Compiler strips all `pub` symbols not marked `pub(global)`.
  3.  Compiler embeds Documentation Vectors (for RAG).
  4.  Artifact (`.mar`) is signed and uploaded.
- **Immutability:** Once published, a version `1.0.0` is content-addressed. It can never change.

### 6.2 Discovery

- **Agent Query:** "I need a library for Fast Fourier Transform."
- **MCP Action:** Queries the Registry Vector DB.
- **Result:** Returns `morph/science-fft`. The Agent adds it to `morph.pkg`.

---

## 7. Requirements Traceability

| Feature                   | Rationale                                | Requirement |
| :------------------------ | :--------------------------------------- | :---------- |
| **Content Addressing**    | Unbreakable imports; Atomic Refactoring. | REQ-16.1    |
| **Virtual Workspace**     | Monorepo support without config hell.    | REQ-18.1    |
| **`pub(global)`**         | Explicit API surface control.            | REQ-PKG-01  |
| **Multi-Version Linking** | Solves Dependency Hell.                  | REQ-18.3    |
| **MorphIR Dist**          | Solves ABI Incompatibility.              | REQ-17.3    |

This Module System is designed to be **invisible** to the Agent during the happy path (Workspace Resolution) but **rigidly precise** during the deployment path (Registry Resolution), ensuring that if code works once, it works forever.
