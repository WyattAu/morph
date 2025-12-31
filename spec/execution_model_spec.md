# Morph Execution Model Specification (EMS)

**System:** Morph Programming Language
**Version:** 1.0.0
**Context:** Layer 3 (Runtime)
**Formalism:** M:N Scheduling, Actor-Based, Non-Blocking

---

## 1. The Runtime Architecture

### 1.1 The Runtime Library (MRE)

Morph does not run on a Virtual Machine (like the JVM). It runs on a **Bare-Metal Runtime Library** that is statically linked into the final executable (`.mpx`).

- **Role:** Abstraction of OS primitives (Threads, I/O, Memory).
- **Composition:** A lightweight kernel written in C++/Assembly (optimized for each architecture) controlled by MorphIR instructions.

### 1.2 The Execution Unit: The Fiber

- **Definition:** The fundamental unit of execution is a **Fiber** (Stackful Coroutine).
- **Characteristics:**
  - **Stack:** Growable, starting at 4KB (vs. 1MB for OS threads).
  - **Cost:** Creating a Fiber takes nanoseconds.
  - **State:** Holds CPU registers and stack pointer.
- **Rationale:** "Colorless" async (implicit suspension) requires _Stackful_ coroutines. The runtime must be able to pause a function deep in the call stack without unwinding it (unlike Stackless `async/await` in Rust/JS).

---

## 2. Concurrency Scheduling

### 2.1 The M:N Scheduler

The MRE implements an M:N scheduling model, mapping **M Fibers** onto **N OS Threads** (Executors).

- **N (Executors):** Typically equal to `Hardware_Cores`. Each Executor runs a local Work Queue.
- **Work Stealing:** If an Executor runs out of Fibers, it steals jobs from the tail of another Executor's queue.
- **Rationale:** Maximizes CPU utilization. Prevents a single heavy task from blocking the entire application (as happens in Node.js single-threaded event loops).

### 2.2 Implicit Suspension Protocol

Morph eliminates `async`/`await` keywords via **IO-Aware Yielding**.

1.  **The Call:** Agent writes `file.read()`.
2.  **The Trap:** The Runtime intercepts the syscall.
3.  **The Registration:** The Runtime registers the File Descriptor with the OS Poller (`io_uring`/`kqueue`/`IOCP`).
4.  **The Switch:** The Runtime saves the current Fiber state and immediately switches the Executor to the next Fiber in the Ready Queue.
5.  **The Resume:** When the OS signals data availability, the Poller moves the original Fiber back to the Ready Queue.

- **Rationale:** Zero blocking. The CPU never idles waiting for I/O.

### 2.3 Preemption (The "Anti-Hang" Mechanism)

- **Problem:** A Fiber entering `while(true) {}` could starve other Fibers on that core.
- **Solution:** The Compiler injects **Checkpoints** at loop headers and function entries.
- **Runtime Logic:**
  ```cpp
  // Pseudo-code injected by compiler
  if (runtime_ticks() > time_slice_limit) {
      yield();
  }
  ```
- **Rationale:** Guarantees system responsiveness (especially UI) even if the Agent writes inefficient algorithms.

---

## 3. The Actor Model (`logic`)

### 3.1 Actor Structure

A `logic` block compiles into a **Stateful Fiber**.

- **Mailbox:** A lock-free MPSC (Multi-Producer, Single-Consumer) queue.
- **Behavior:** The Fiber loops efficiently:
  - If Mailbox is empty $\rightarrow$ Fiber Suspend (0% CPU).
  - If Message arrives $\rightarrow$ Fiber Wakeup.
- **Processing:** Messages are processed sequentially. This guarantees **Data Race Freedom** within the Actor.

### 3.2 Supervision Trees

- **Concept:** Actors form a parent-child hierarchy.
- **Failure Mode:** If an Actor panics (e.g., asserts fail), the Fiber terminates.
- **Recovery:** The Runtime intercepts the panic signal and notifies the Supervisor.
- **Strategy Execution:**
  - `OneForOne`: The Supervisor spawns a fresh instance of the failed Actor (fresh memory arena).
  - `OneForAll`: The Supervisor terminates and restarts all sibling Actors.
- **Rationale:** "Let It Crash." Agents cannot predict every error. The system must self-heal.

---

## 4. Dataflow Parallelism (`async let`)

### 4.1 Implementation

`async let x = foo()` is sugar for spawning a **Ephemeral Fiber**.

- **Storage:** The return value is stored in a `Future<T>` slot in the Parent Fiber's stack frame.
- **State:** The Future has three states: `Pending`, `Ready`, `Poisoned` (Panic).

### 4.2 Wait-by-Necessity

- **Mechanism:** When the code accesses `x`:
  - **Case 1 (Ready):** Read value immediately (0 cost).
  - **Case 2 (Pending):** The Parent Fiber yields (suspends). It is added to the "Dependency List" of the Child Fiber.
  - **Case 3 (Poisoned):** The Parent Fiber panics (propagating the error).
- **Wakeup:** When the Child Fiber finishes, it writes the result to the `Future` slot and wakes up the Parent Fiber.

---

## 5. Memory Management

### 5.1 The Hybrid Allocator

Morph uses distinct strategies based on data lifetime.

#### 5.1.1 The Arena (Region)

- **Scope:** Per-Actor (or Per-Request).
- **Allocation:** Bump Pointer (Increment `ptr` by size). Extremely fast (~3 CPU cycles).
- **Deallocation:** No `free()` per object. The entire region is reset when the Actor finishes processing a message or the Request ends.
- **Usage:** Temporary variables (`ref`), scratch buffers.

#### 5.1.2 The Global Heap (ARC)

- **Scope:** Shared Data (`val`).
- **Allocation:** `malloc` (or slab allocator).
- **Management:** **Atomic Reference Counting**.
  - Clone `val` $\rightarrow$ Atomic Increment.
  - Drop `val` $\rightarrow$ Atomic Decrement.
  - Count == 0 $\rightarrow$ Free.
- **Rationale:** Deterministic latency. No Stop-the-World pauses associated with Tracing GC.

### 5.2 Capability Enforcement

- **Runtime Check:** Debug builds verify that `iso` pointers passed between threads are indeed unique (detecting unsafe C++ FFI leaks). Release builds assume compile-time proofs are correct.

---

## 6. Foreign Function Interface (FFI)

### 6.1 The Dual-Pool Strategy

To prevent C/C++ code from blocking the M:N scheduler, Morph maintains two thread pools.

1.  **The Green Pool:** Runs Morph Fibers.
2.  **The System Pool:** Runs blocking OS threads.

### 6.2 The Switch Protocol

When a Morph Fiber calls a C function:

- **Default Behavior:**
  1.  Task is moved from Green Pool to System Pool.
  2.  C function executes (blocking the System Thread).
  3.  Task is moved back to Green Pool.
- **Optimization (`[NonBlocking]` trait):**
  1.  Task remains on Green Pool.
  2.  C function executes immediately.
  3.  **Risk:** If C function sleeps, the Morph Executor hangs.
- **Rationale:** Safety by default. An Agent importing a buggy C library shouldn't freeze the GUI.

---

## 7. Observability & Debugging

### 7.1 Time-Travel State Graph (Debug Mode)

- **Mechanism:** The Runtime maintains a **Shadow Stack**.
- **Operation:** On every state mutation (assignment to `state` variable):
  1.  The old value is serialized (copy-on-write).
  2.  A node is added to the DAG: `(Timestamp, AST_ID, Previous_Hash, New_Value)`.
- **Crash Dump:** On panic, the Runtime exports this DAG to the MCP server.

### 7.2 The Flight Recorder (Release Mode)

- **Mechanism:** A 1MB Circular Buffer per Executor.
- **Logging:** Records compact "Event Codes" (e.g., `ActorSpawn`, `MsgStart`, `MsgEnd`, `Error`).
- **Overhead:** < 1% CPU.
- **Rationale:** Allows diagnosing production crashes ("What was the last message processed?") without full overhead.

---

## 8. Requirements Traceability

| Feature             | Implementation                     | Requirement |
| :------------------ | :--------------------------------- | :---------- |
| **Colorless Async** | Stackful Fibers + I/O Polling      | REQ-CONC-01 |
| **Dataflow**        | Ephemeral Fibers + Future Slots    | REQ-CONC-02 |
| **Actor Isolation** | MPSC Mailboxes + Serial Processing | REQ-CONC-03 |
| **No GC**           | Arena + ARC                        | REQ-MEM-01  |
| **Responsiveness**  | Compiler-injected Preemption       | REQ-RUN-01  |
| **Safety**          | System Pool FFI dispatch           | REQ-SAFE-02 |
