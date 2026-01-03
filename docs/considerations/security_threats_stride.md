# Morph Security Threat Model (MSTM)
* System:** Morph Ecosystem
* Version:** 1.0.0
* Methodology:** STRIDE / Microsoft SDL
* Scope:** Compiler, Runtime, Build System, Agent Interface

- -

## 1. Executive Summary

Morph introduces unique security challenges due to its **Agentic Nature** (LLMs writing code) and **Stateful Build System** (Content-Addressable Database). The primary threat vectors shift from "Human Logic Errors" (Buffer Overflows) to "Semantic Hallucinations" (Hallucinated Dependencies, Infinite Loops) and "Infrastructure Attacks" (Cache Poisoning).

The security architecture relies on **Zero-Trust Compilation**, **Capability-Based Memory**, and **Hermetic Infrastructure** to mitigate these risks.

- -

## 2. Threat Analysis Matrix (STRIDE)

### 2.1 Spoofing (Identity & Authenticity)

| Component | Threat Description | Severity | Mitigation Strategy |
| :--- | :--- | :--- | :--- |
| **Registry** | **Malicious Package Injection:** An attacker publishes a modified library (e.g., `std.net`) with a matching name but malicious bytecode. | **Critical** | **Content Addressing:** Packages are identified by Hash, not Name. **Signature Verification:** `.mar` artifacts must be signed by the publisher's key. |
| **MCP** | **Rogue Agent:** An unauthorized LLM or script connects to the MCP port and injects code patches. | **High** | **Localhost Binding:** MCP binds to `127.0.0.1` by default. **Token Auth:** Requires a session token generated at compiler startup. |
| **MCM** | **Hash Collision Attack:** Attacker generates a malicious AST that produces the same Merkle Hash as a legitimate module. | **Critical** | **SHA-256 / BLAKE3:** Usage of collision-resistant cryptographic hashes. |

### 2.2 Tampering (Data Integrity)

| Component | Threat Description | Severity | Mitigation Strategy |
| :--- | :--- | :--- | :--- |
| **Artifact Cache** | **Cache Poisoning:** Attacker modifies the `.o` or `.mar` files in the local cache (`~/.morph/cache`), causing the linker to include malware in valid builds. | **High** | **Integrity Check:** The Build System verifies the checksum of cached artifacts against the request key before linking. |
| **Codebase DB** | **AST Corruption:** Direct SQL injection or disk corruption alters the stored AST nodes in the SQLite/Vector DB. | **Medium** | **Schema Enforcement:** Strict schema validation on load. **Re-Hashing:** Compiler re-calculates AST hashes on load; mismatches trigger a database repair/wipe. |
| **Runtime** | **Memory Corruption:** Buffer overflows in `unsafe` C++ FFI code overwrite Actor memory. | **High** | **Pessimistic FFI:** External code runs in separate OS threads (System Pool). **Sandboxing:** (Future) Wasm-based isolation for FFI. |

### 2.3 Repudiation (Non-deniability)

| Component | Threat Description | Severity | Mitigation Strategy |
| :--- | :--- | :--- | :--- |
| **Agent** | **"It wasn't me":** An Agent generates malicious logic (e.g., exfiltration) and then deletes the trace. | **Medium** | **Immutable History:** The MCM stores version history (Git-like). **Audit Logs:** MCP logs all `patch_ast` commands with the Agent ID and Timestamp. |
| **Runtime** | **Crash Silence:** A production binary crashes without leaving a trace of the cause. | **High** | **Flight Recorder:** The Ring Buffer telemetry (REQ-RUN-02) dumps the last $N$ states to disk upon panic/signal. |

### 2.4 Information Disclosure (Privacy)

| Component | Threat Description | Severity | Mitigation Strategy |
| :--- | :--- | :--- | :--- |
| **Memory** | **Cross-Actor Leaks:** Actor A reads sensitive data (keys) belonging to Actor B via a dangling pointer. | **Critical** | **Capability System:** The Type System proves `iso` ownership. It is physically impossible to construct a pointer to another Actor's private `ref` memory. |
| **Build** | **Environment Leakage:** Build scripts read `AWS_ACCESS_KEY` from the host environment and embed it in the binary. | **High** | **Hermetic Builds:** The Sandbox environment (REQ-BLD-01) strips all environment variables except an explicit allow-list. |
| **Telemetry** | **Secrets in Logs:** The Flight Recorder captures variables containing passwords/keys. | **Medium** | **Type Redaction:** Types marked `^Secret` or `@sensitive` are redacted (`***`) in the State Graph and Ring Buffer. |

### 2.5 Denial of Service (Availability)

| Component | Threat Description | Severity | Mitigation Strategy |
| :--- | :--- | :--- | :--- |
| **Runtime** | **Scheduler Starvation:** An Agent writes an infinite loop or calls a blocking C function, freezing the UI. | **High** | **Preemption:** Compiler injects yield points in loops. **Pessimistic FFI:** Blocking calls are forced off the Green Thread pool. |
| **Compiler** | **Compilation Bomb:** `comptime` code executes an infinite loop or allocates gigabytes of RAM during build. | **Medium** | **Resource Quotas:** `comptime` sandbox has strict CPU time (500ms) and RAM (128MB) limits. |
| **Network** | **Actor Mailbox Flood:** An actor sends millions of messages to another, exhausting heap memory. | **High** | **Backpressure:** Bounded Mailboxes. `send()` suspends the sender if the receiver's mailbox is full. |

### 2.6 Elevation of Privilege (Authorization)

| Component | Threat Description | Severity | Mitigation Strategy |
| :--- | :--- | :--- | :--- |
| **Effects** | **Effect Bypass:** A function marked `[Pure]` performs Network I/O. | **Critical** | **Static Verification:** The Semantic Tree enforces Effect Bounds. The Runtime (Debug build) double-checks syscalls against the allowed effect mask. |
| **Sandboxing** | **Container Escape:** Build process breaks out of the chroot/namespace to modify host files. | **Critical** | **OS Virtualization:** Usage of Linux Namespaces (Bubblewrap) or Wasm sandboxing. **Read-Only VFS:** Host mounts are Read-Only. |

- -

## 3. Specific Attack Surface Analysis

### 3.1 The "Prompt Injection" Vector
-   **Scenario:** An Agent is fed a malicious prompt from the web (e.g., via a scraped README) that instructs it to write a Morph backdoor.
-   **Morph Defense:** **Design by Contract**.
    -   Even if the Agent tries to write the backdoor, it must satisfy the `requires`/`ensures` contracts and the Effect System.
    -   If the Agent tries to add `import net` to a calculator library, the Effect System flags the library as `[Net]`. The Human Architect/Reviewer sees the Effect signature change and rejects it.

### 3.2 The "Supply Chain" Vector
-   **Scenario:** A legitimate library dependency is compromised.
-   **Morph Defense:** **Hash Pinned Dependencies**.
    -   The `morph.pkg` locks dependencies to the **AST Hash**.
    -   If the upstream library changes (malicious update), the Hash changes.
    -   The build fails immediately because the lockfile hash does not match the downloaded artifact hash.

### 3.3 The "FFI" Vector (The Weakest Link)
-   **Scenario:** Vulnerable C code causes a Buffer Overflow.
-   **Morph Defense:** **Memory Isolation**.
    -   Morph's memory (Arenas) is segregated from the C-Heap.
    -   While a C overflow can corrupt the process, it cannot easily manipulate Morph's internal object graph due to Address Space Layout Randomization (ASLR) and the non-standard memory layout of Actors.

- -

## 4. Security Architecture Diagram

```mermaid
graph TD
    subgraph "Host OS (Untrusted)"
        User[User/Agent]
        Net[Internet]
    end

    subgraph "Morph Build Boundary (Hermetic)"
        MBS[Build System]
        Sandbox[Container]
    end

    subgraph "Runtime Boundary (Memory Safe)"
        ActA[Actor A (Arena)]
        ActB[Actor B (Arena)]
        Heap[Global Heap (ARC)]
    end

    %% Attack Vectors Blocked
    Net -- "Malicious Package" --> MBS
    MBS -- "Sig Check" --> Sandbox
    Sandbox -- "Sandboxed" --> ActA

    ActA -- "Iso Ptr" --> ActB
    ActA -. "Direct Ref (Blocked)" .-> ActB

    User -- "MCP Command" --> MBS
    MBS -- "Effect Check" --> ActA
```

## 5. Summary of Mitigations

1.  **Code is Data:** Content-addressing makes "stealth edits" mathematically impossible.
2.  **Explicit Effects:** The Effect System forces "Privilege Declaration" (If you want Network, you must declare `[Net]`).
3.  **Hermetic Infrastructure:** The build system trusts nothing from the host environment.
4.  **Memory Proofs:** The Type System proves ownership at compile time, removing entire classes of runtime exploits (Use-After-Free, Double-Free, Data Races).

This Threat Model confirms that Morph is designed to be **Secure by Architecture**, shifting the burden of security from the Developer (who might make mistakes) to the Compiler (which strictly enforces rules).