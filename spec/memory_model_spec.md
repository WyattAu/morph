# Morph Memory Model Specification (MMS)

**System:** Morph Programming Language
**Version:** 1.0.0
**Context:** Layer 3 (Runtime) & Layer 2 (Semantic Analysis)
**Formalism:** Region-Based, Affine, Capability-Secure

---

## 1. Abstract Memory Architecture

Morph presents a **Segmented Memory Architecture**. Unlike C++ (flat heap) or Java (managed heap), Morph divides memory into strictly isolated domains based on the **Actor Model**.

### 1.1 The Domain Topology

1.  **The Stack Segment (Fiber Local):**
    - Each Green Thread (Fiber) has a growable stack (default 4KB).
    - Stores: Primitive values (`i32`, `f64`), Function Call Frames, and Capabilities (Pointers).
2.  **The Arena Segment (Actor Local):**
    - Each `logic` block (Actor) owns a linear memory region (Arena).
    - Stores: `ref` (Mutable Local) objects and temporary `data` structures.
    - **Lifecycle:** Reset (bulk deallocation) when the Actor finishes processing a message or yields.
3.  **The Global Heap (Shared):**
    - A concurrent allocator (e.g., hardened mimalloc variant).
    - Stores: `val` (Shared Immutable) and `iso` (Exchangeable) objects.
    - **Lifecycle:** Managed via Atomic Reference Counting (ARC).

---

## 2. Capability-Based Access Control

The Memory Model relies on the Type System to enforce access rights at compile-time. The runtime relies on these guarantees to elide locks.

### 2.1 The Capability Matrix

| Capability            | Aliasable? | Mutable? | Sendable?          | Memory Location     |
| :-------------------- | :--------- | :------- | :----------------- | :------------------ |
| **`iso` (Isolated)**  | **No**     | **Yes**  | **Yes** (Move)     | Global Heap         |
| **`val` (Value)**     | **Yes**    | **No**   | **Yes** (Copy Ref) | Global Heap         |
| **`ref` (Reference)** | **Yes**    | **Yes**  | **No**             | Actor Arena / Stack |

### 2.2 Deny Properties (Safety Guarantees)

1.  **Deny Global Mutation:** It is impossible to hold a mutable reference (`ref`) to an object that is aliased by another Actor.
2.  **Deny Write-After-Share:** Once an `iso` is converted to `val` (Frozen), it can never be mutated again.
3.  **Deny Read-After-Move:** Once an `iso` is sent to another Actor, the sender's reference is invalidated.

---

## 3. Allocation Strategy

### 3.1 The Arena Allocator (Bump Pointer)

- **Target:** Objects typed as `ref` or created temporarily within a function.
- **Mechanism:**
  - The Runtime maintains a `current_ptr` and `end_ptr` for the active Actor.
  - `alloc(size)` $\rightarrow$ `result = current_ptr; current_ptr += size;`
  - **Cost:** ~3 CPU Cycles (Add + Compare).
- **Deallocation:**
  - **No Destructors:** Morph `data` types are POD (Plain Old Data) or pointers. They do not have custom destructors (RAII is handled via `defer` for external resources only).
  - **Reset:** At the end of the Message Loop, `current_ptr` is reset to `start_ptr`.
- **Benefits:** Zero fragmentation, infinite cache locality, zero deallocation cost.

### 3.2 The ARC Allocator (Global Heap)

- **Target:** Objects typed as `iso` or `val`.
- **Mechanism:**
  - Allocates a `ControlBlock` + `Data`.
  - `ControlBlock` contains an `Atomic<usize>` reference count.
- **Optimization (Biased ARC):**
  - Since `val` objects are immutable, we do not need complex memory barriers for _reading_ data, only for the _reference counter_.
  - We utilize `std::memory_order_relaxed` for increments and `std::memory_order_acq_rel` for decrements to maximize performance on ARM/x86.

---

## 4. Affine Types & Move Semantics

To reduce pressure on the Heap Allocator, the Morph Compiler utilizes **Affine Type Analysis**.

### 4.1 The "Use-Once" Rule

An Affine Type is a value that can be used at most once.

- **`iso` Types are Affine.**
  ```rust
  let a: ^Data = create();
  let b = a; // 'a' is consumed here.
  // 'a' is now technically uninitialized memory.
  ```

### 4.2 In-Place Mutation (The Functional Optimization)

Morph allows functional syntax to be compiled into imperative mutation.

- **Source:** `let s2 = s1.update(x);` (where `s1` is `val`)
- **Analysis:** If `s1` is never used again (last use), and the ref-count is exactly 1 (checked at runtime via `is_unique()`).
- **Optimization:** The compiler rewrites this to mutate `s1` in place instead of allocating `s2`.
- **Result:** Functional purity with C-style performance.

---

## 5. Memory Consistency Model

Morph guarantees **Sequential Consistency (SC)** for data race freedom, but relies on relaxed models for internal synchronization.

### 5.1 Happens-Before Relations

1.  **Message Passing:** Sending a message $M$ from Actor $A$ **happens-before** Actor $B$ receives $M$.
    - _Implication:_ All writes to the data inside $M$ by $A$ are visible to $B$.
2.  **Spawn:** Spawning Task $T$ **happens-before** the first instruction of $T$.
3.  **Future:** The completion of Task $T$ **happens-before** the return of `await` (implicit or explicit) on $T$'s result.

### 5.2 Deep Immutability (`val`)

- Morph defines "Deep Immutability." If a root object is `val`, **all** objects reachable from it are transitively `val`.
- This property allows the CPU to cache `val` data aggressively without fear of cache invalidation snooping (False Sharing), as no core will ever write to that cache line.

---

## 6. Garbage Collection (The "No-GC" Strategy)

Morph strictly **prohibits** Tracing Garbage Collection (Mark-and-Sweep / Generational).

### 6.1 Cycle Handling

- **Problem:** ARC is vulnerable to reference cycles ($A \to B \to A$), which cause leaks.
- **Morph's Solution:** **Structural Acyclicity**.
  - Since `val` data is immutable, you cannot create a cycle _after_ construction.
  - You can only create a cycle during recursive construction (`let rec`).
  - **Constraint:** The Type System allows recursive types, but the standard library constructors for graph structures utilize **Indices/IDs** rather than direct pointers for back-references.
  - _Fallback:_ If users manually construct cyclic pointer graphs using `unsafe`, they leak. This is accepted behavior for the sake of determinism.

---

## 7. Low-Level Layout (ABI)

### 7.1 Data Layout

- **Alignment:** Natural alignment (e.g., `u64` is 8-byte aligned).
- **Padding:** Structure fields are reordered by the compiler (unless `#[packed]`) to minimize padding holes.
- **Discriminants:** Sum Type tags are optimized.
  - `Option<^T>`: Uses the "Null Pointer Optimization". `None` is `0x0`. `Some` is the pointer. Size overhead = 0.
  - `Result<T, E>`: Uses bits from the pointer alignment if available, or a trailing byte.

### 7.2 Stack Layout (Fibers)

- **Size:** 4KB initial, geometrically resizing.
- **Guard Page:** A protected memory page at the stack limit triggers a generic Segment Fault, which the Runtime catches to grow the stack (split-stack or copying stack strategy).

---

## 8. Requirements Traceability

| Requirement               | MMS Implementation                                   |
| :------------------------ | :--------------------------------------------------- |
| **Deterministic Latency** | Arena (O(1)) + ARC (Incremental). No Stop-the-World. |
| **Data Race Freedom**     | Capability System (`ref` vs `val`).                  |
| **High Concurrency**      | Stackful Fibers (Small footprint).                   |
| **Zero-Copy Messaging**   | `iso` pointers transferred via queue pointers.       |

This specification ensures that Morph's memory behavior is predictable enough for Real-Time Systems (Game Engines, High-Freq Trading) while remaining safe enough for AI generation.
