# Morph Infrastructure & Safety Contracts Specification (ISCS)

**System:** Morph Programming Language
**Version:** 1.0.0
**Context:** Layer 2 (Semantics) & Layer 4 (Framework)
**Formalism:** Hoare Logic, Effect-Oriented, Pessimistic FFI

---

## 1. Design by Contract (DbC)

Morph implements a first-class **Contract System** based on Hoare Logic. Contracts serve two purposes: Runtime Verification (Debug) and Static Optimization (Release).

### 1.1 Contract Clauses

Contracts are defined in the function signature block.

- **`requires { expr }` (Precondition):**
  - Defines constraints on arguments _before_ execution.
  - **Responsibility:** Caller.
  - **Failure:** `ContractViolation::Precondition` (Blames Caller).
- **`ensures { expr }` (Postcondition):**
  - Defines guarantees on the return value (`ret`) or state _after_ execution.
  - **Responsibility:** Callee (Function Author).
  - **Failure:** `ContractViolation::Postcondition` (Blames Callee).
- **`invariant { expr }` (State Consistency):**
  - Defines truth that must hold before and after every public method of a `logic` block or `type`.

### 1.2 Syntax Example

```rust
fn divide(a: i32, b: i32) -> i32
    requires { b != 0 }
    ensures  { ret * b == a }
{
    ret a / b;
}
```

### 1.3 Compilation Behavior

- **Debug Mode:** Contracts are compiled into **Runtime Assertions**.
- **Release Mode:** Contracts are compiled into **OIR Constraints** (`llvm.assume`).
  - _Optimization:_ If `requires { b != 0 }` is present, the compiler removes the CPU-level division-by-zero check for performance.
- **Agent Interaction:** When an Agent writes code calling `divide(x, 0)`, the Semantic Tree detects the violation at compile-time via constant folding or abstract interpretation, returning a specific error: _"Precondition violation: b != 0"_.

---

## 2. The Effect System

Morph utilizes a **Typed Effect System** to track and restrict side effects, preventing "Spooky Action at a Distance."

### 2.1 Effect Taxonomy

| Effect     | Description                                           |
| :--------- | :---------------------------------------------------- |
| **`Pure`** | Deterministic computation. No side effects. (Default) |
| **`IO`**   | Filesystem access, Console I/O.                       |
| **`Net`**  | Network socket creation/usage.                        |
| **`Time`** | Access to non-monotonic clocks (System Time).         |
| **`Sys`**  | Process spawning, FFI, System Calls.                  |

### 2.2 Propagation Rules

- **Inference:** If a function calls an `IO` function, it becomes `IO`.
- **Explicit Declaration:** `fn log() performs [IO] { ... }`
- **Containment:** Pure functions strictly _cannot_ call Impure functions.
- **Encapsulation:** `logic` blocks (Actors) act as Effect Boundaries. Side effects are permitted inside Event Handlers, but the Event Interface itself is pure data.

### 2.3 Agent Safety

This prevents Hallucinations where an Agent attempts to perform I/O in a context meant for calculation (e.g., inside a `comptime` block or a pure math kernel).

---

## 3. Foreign Function Interface (FFI) Safety

Interoperating with C/C++ is the biggest source of runtime instability. Morph adopts a **Pessimistic Safety Model**.

### 3.1 The "Blocking by Default" Rule

- **Assumption:** The Runtime assumes ALL FFI calls are **Blocking** and **Unsafe**.
- **Mechanism:**
  1.  The Green Thread (Fiber) yields.
  2.  The task is dispatched to a dedicated **OS Thread Pool** (System Pool).
  3.  Upon return, the result is moved back to the Green Thread.
- **Impact:** A C function `sleep(10)` pauses a background OS thread, but the Morph Event Loop (UI/Logic) remains responsive.

### 3.2 The Non-Blocking Override

- **Trait:** `trait [NonBlocking]`
- **Usage:**
  ```rust
  // Agent asserts this C function is instant (< 100ns)
  @ffi(lib="math")
  fn fast_sin(x: f64) -> f64 performs [Pure, NonBlocking];
  ```
- **Behavior:** Executed directly on the Green Thread stack for zero overhead.

---

## 4. Intrinsic Infrastructure Primitives

Morph "bakes in" architectural patterns that usually require external libraries in other languages.

### 4.1 The Universal Context (`ctx`)

- **Definition:** An implicit, immutable object propagated down the call stack.
- **Components:**
  - **Cancellation:** `ctx.done()` channel.
  - **Deadline:** `ctx.deadline()` timestamp.
  - **Values:** Request-scoped Key/Value store (e.g., TraceID, UserID).
- **Injection:** The Compiler automatically injects `ctx` as the first argument to any `async` or `IO` function in the OIR. The Agent does not type it manually.

### 4.2 Declarative Routing

A built-in DSL for mapping external signals to internal Actor Events.

- **Syntax:**
  ```rust
  routing WebRoutes {
      // Syntax: VERB PATH -> Target.Event(args)
      GET "/users/:id" -> UserActor.Fetch(id);

      // Auto-Deserialization of Body -> Struct
      POST "/login" -> AuthActor.Login(body);
  }
  ```
- **Generation:** The compiler generates the HTTP Server, Route Trie, and JSON Deserializers automatically.
- **Safety:** The route is only valid if `UserActor.Fetch` accepts an argument matching the type of `:id`.

---

## 5. Automated Quality Assurance

Morph shifts testing from "Manual Construction" to "Compiler Generation."

### 5.1 Auto-Fuzzing (`@fuzz`)

- **Concept:** Since Morph types are strict (`data`) and constraints are explicit (`requires`), the compiler can synthesize valid and invalid inputs.
- **Mechanism:**
  1.  Agent marks a function `@fuzz`.
  2.  Build System generates a Fuzz Target.
  3.  Fuzzer generates inputs based on the Type Schema.
  4.  Inputs are filtered against `requires` (Preconditions).
  5.  Function is executed.
  6.  Crashes or `ensures` violations are reported.

### 5.2 Unit Testing

- **Syntax:** `test "name" { ... }` blocks.
- **Isolation:** Tests run in ephemeral Sandboxes.
- **Mocking:** The Type System supports **Interface Injection** (Traits) to easily mock `Net` or `IO` effects during testing.

---

## 6. Requirements Traceability

| Feature              | Rationale                          | Requirement |
| :------------------- | :--------------------------------- | :---------- |
| **DbC (`requires`)** | Constraints prevent logic errors.  | REQ-SAFE-01 |
| **Effect System**    | Prevents architectural violations. | REQ-7.1.3   |
| **Pessimistic FFI**  | Prevents UI freezes from C libs.   | REQ-SAFE-02 |
| **Implicit `ctx`**   | Prevents "Zombie Tasks" (leaks).   | REQ-11.2    |
| **`routing` Block**  | Reduces boilerplate/hallucination. | REQ-11.3    |
| **Auto-Fuzzing**     | Finds edge cases Agents miss.      | REQ-SAFE-04 |

This specification ensures that Morph code is not just "runnable," but **architecturally sound** and **resilient** by default.
