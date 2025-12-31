# Morph Type System Specification (TSS)

**System:** Morph Programming Language
**Version:** 1.0.0
**Context:** Layer 2 (Semantic Analysis)
**Formalism:** Affine, Capability-Based, Statically Typed

---

## 1. Type Hierarchy & Primitives

Morph relies on a set of fixed-width primitives to ensure direct mapping to OIR and machine hardware.

### 1.1 Scalar Primitives

| Type             | Bit Width | Description                       | OIR Mapping       |
| :--------------- | :-------- | :-------------------------------- | :---------------- |
| `bool`           | 1         | Boolean (`true`, `false`)         | `i1`              |
| `u8` - `u64`     | 8-64      | Unsigned Integer                  | `i8` - `i64`      |
| `i8` - `i64`     | 8-64      | Signed Integer (Two's Complement) | `i8` - `i64`      |
| `f32`, `f64`     | 32, 64    | IEEE-754 Floating Point           | `float`, `double` |
| `usize`, `isize` | Arch      | Pointer-sized Integer             | `ptr_int`         |
| `void`           | 0         | Unit Type (Empty Tuple)           | `void`            |

### 1.2 The `str` and `Bytes` Dualism

Morph distinguishes between Unicode Text and Binary Data to prevent encoding bugs.

- **`str`:** UTF-8 encoded, immutable string slice. Non-null.
- **`Bytes`:** Raw `u8` array. Used for network packets/binary parsing.

### 1.3 The "Hole" Type (`??`)

- **Definition:** A placeholder type used during compilation search.
- **Resolution:** The compiler replaces `??` with a concrete Scalar Primitive (`i32`, `u64`, etc.) that optimizes a specific fitness function (e.g., execution speed).

---

## 2. Algebraic Data Types (ADTs)

Morph unifies Structs, Enums, and Unions into a single `type` construct.

### 2.1 Product Types (Records)

Named fields stored contiguously in memory.

```rust
type Vec3 = { x: f32, y: f32, z: f32 };
```

- **Layout:** C-compatible (ordered, packed based on alignment).
- **Semantics:** **Value Semantics** by default. Copying a `Vec3` copies the bits.

### 2.2 Sum Types (Tagged Unions)

Disjoint unions where a value holds exactly one variant.

```rust
type Shape =
  | Circle { radius: f32 }
  | Rect { w: f32, h: f32 };
```

- **Layout:** `Discriminant (u8) + Max(SizeOf(Variants))`.
- **Safety:** Access to fields requires exhaustive Pattern Matching (`fix`). Direct field access is a compile error if the field is not present in _all_ variants.

### 2.3 Intrinsic Behaviors

All `type` definitions automatically derive:

1.  **Equality:** Structural `==` checking.
2.  **Serialization:** `.toJson()`, `.fromBytes()`.
3.  **Hashing:** Deterministic hashing for map keys.

---

## 3. Reference Capabilities (The Ownership Model)

Morph uses **Capabilities** to enforce memory safety without a Garbage Collector and to enable Zero-Copy concurrency. This is a simplified adaptation of the Pony language model.

### 3.1 The Three Sigils

| Sigil   | Name    | Capability    | Semantics                                                            | Memory Location            |
| :------ | :------ | :------------ | :------------------------------------------------------------------- | :------------------------- |
| **`^`** | **Iso** | **Isolated**  | Mutable. Unique. **Move-Only**. No other aliases exist.              | Arena (if scoped) or Heap. |
| **`#`** | **Val** | **Value**     | Immutable. Shared. **Copy-by-Reference**. Safe to send to Actors.    | ARC (Atomic Ref Count).    |
| **`&`** | **Ref** | **Reference** | Mutable. Local Alias. **Non-Sendable**. Strictly bound to one Actor. | Stack / Arena.             |

### 3.2 Capability Transition Rules

The type system enforces strict transitions to prevent data races.

1.  **Consume (`consume ^x`):** Destroys the variable `x` and returns its value. Used to move `iso` types.
2.  **Freeze (`^x` $\rightarrow$ `#x`):** An `iso` (Unique) can be converted to `val` (Shared Immutable). This is a one-way trip.
3.  **Borrow (`^x` $\rightarrow$ `&x`):** You can create a temporary mutable reference from an `iso`, provided the `iso` is not moved while the borrow is active.

### 3.3 Zero-Copy Message Passing

- **Constraint:** Messages sent between Actors (`logic` blocks) must be **Sendable**.
- **Sendable Types:**
  - Primitives (`i32`, `f64`).
  - `val` types (`#User`).
  - `iso` types (`^Image`) — _Note: Sending an `iso` consumes it from the sender._
- **Rejected Types:** `ref` types (`&Buffer`) cannot be sent. This prevents two Actors from mutating the same memory simultaneously (Data Race Freedom).

---

## 4. Null Safety & Optionals

### 4.1 Non-Nullable Default

- `let x: String = null;` $\rightarrow$ **Compile Error**.

### 4.2 The Optional Type (`T?`)

- `T?` is syntactic sugar for `Option<T>`.
- Internally represented as a Tagged Union: `Some(T) | None`.

### 4.3 Flow-Sensitive Smart Casts

The compiler tracks control flow to "unwrap" types automatically.

```rust
fn print_len(s: str?) {
    // s is str?
    if (s != null) {
        // s is explicitly promoted to 'str' here
        print(s.length);
    }
}
```

---

## 5. Generics & Polymorphism

### 5.1 Parametric Polymorphism

Morph supports Generics with **Monomorphization**.

```rust
type List<T> = { head: T, tail: ^List<T>? };
```

- **Implementation:** The compiler generates a distinct copy of the code for every concrete type used (`List_i32`, `List_str`). This enables inlining and eliminates vtable overhead.

### 5.2 Constraint System (Traits)

Generics must be constrained by Traits (Concepts). Unconstrained generics are prohibited in public APIs to prevent "Template Errors" inside library code.

```rust
trait Drawable {
    fn draw(ctx: &Context);
}

fn render<T: Drawable>(item: T) { ... }
```

### 5.3 Static Dispatch

All method calls are resolved at compile time. Morph does **not** support dynamic dispatch (Virtual Methods) by default. Dynamic behavior must be implemented explicitly via Enums (Sum Types).

---

## 6. The Effect System

Morph tracks side effects to ensure architectural purity and security.

### 6.1 Effect Categories

| Effect Tag | Description                                      |
| :--------- | :----------------------------------------------- |
| `Pure`     | No side effects. Deterministic output. (Default) |
| `IO`       | File system, Console access.                     |
| `Net`      | Network sockets.                                 |
| `Time`     | Clock access (Non-deterministic).                |
| `System`   | FFI, Process spawning.                           |

### 6.2 Effect Propagation

- A function marked `Pure` cannot call a function marked `IO`.
- A function marked `IO` _can_ call a `Pure` function.
- **Inference:** If a function has no explicit effect signature, the compiler infers the effect set based on the functions it calls.

### 6.3 Effect Bounds

```rust
// Contract: This function MUST NOT access the network
fn parser(data: str) -> Json performs [Pure] {
    net.get("..."); // Compile Error: Effect Violation
}
```

---

## 7. Type Inference Rules

### 7.1 Bidirectional Inference

The compiler infers types from context (Top-Down) and usage (Bottom-Up).

- **Variable Definition:** `x := 10` $\rightarrow$ `x` is `i32`.
- **Return Type:**
  ```rust
  fn get_id() { ret 5; } // Return type inferred as i32
  ```
- **Literal Coercion:**
  ```rust
  let x: u8 = 10; // '10' is inferred as u8, not default i32
  ```

### 7.2 Affine Type Inference (Optimization)

If a `val` (immutable) variable is used in a way where it is never referenced again, the compiler secretly promotes usage to a mutable operation in the backend OIR to avoid copying.

- **Input:** `s2 := s1.append("x");` (Functionally pure)
- **Analysis:** `s1` is dead after this line.
- **Optimization:** Mutate `s1` in place.

---

## 8. Requirements Traceability Matrix

| Feature              | Requirement Addressed | Implementation                                                   |
| :------------------- | :-------------------- | :--------------------------------------------------------------- |
| **`iso` / `val`**    | Safety / No GC        | Enforced by Type Checker; maps to Arena/ARC.                     |
| **`data`**           | Hallucination         | Intrinsic serialization ensures data schema matches wire format. |
| **`T?` Smart Casts** | Agent Usability       | Allows Agents to write "defensive" code patterns naturally.      |
| **Effects**          | Security              | Prevents logic blocks from performing unauthorized I/O.          |
| **Monomorphization** | Performance           | Guarantees C++ level runtime performance for generics.           |
