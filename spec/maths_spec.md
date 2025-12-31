# Domain Extension Specification: Math & Physics (DES-MP)

**System:** Morph Ecosystem
**Version:** 1.0.0
**Context:** Layer 2 (Compiler) & Layer 4 (Standard Library)

---

## 1. Unit Algebra Specification

How do we declare units? We do not want them to be runtime objects (too slow). They must be **Compile-Time Metadata Tags** attached to numeric types.

### 1.1 Declaration Syntax (`unit`)

Morph introduces the `unit` keyword to define **Base Dimensions**.

```rust
// 1. Base Dimensions (The Atoms)
unit Meter;
unit Second;
unit Gram;

// 2. Derived Dimensions (The Molecules)
// The compiler treats this algebraically: Velocity = Meter * Second^-1
unit Velocity = Meter / Second;
unit Acceleration = Velocity / Second;
unit Newton = Gram * Acceleration;
```

### 1.2 Type Annotation (`<Unit>`)

Units are attached to scalar primitives using angle brackets. They are **Type Erasable**—in the final binary, `f64<Meter>` is just a raw `f64`.

```rust
// Variable Declaration
let dist: f64<Meter> = 100.0;
let time: f64<Second> = 9.8;

// Algebraic Inference
// Compiler knows: <Meter> / <Second> -> <Velocity>
let speed = dist / time;
// Type of 'speed' is inferred as f64<Velocity>
```

### 1.3 Dimensional Safety

The compiler enforces dimensional consistency.

```rust
let x: f64<Meter> = 10.0;
let y: f64<Second> = 5.0;

let z = x + y;
// COMPILE ERROR: Dimension Mismatch.
// Cannot add <Meter> and <Second>.
```

### 1.4 The `scalar` Unit

To strip a unit (e.g., needed for a generic math function), you cast to `scalar` (dimensionless).

```rust
let ratio = (10.0<Meter> / 2.0<Meter>); // Result is f64<scalar> (5.0)
```

---

## 2. Arbitrary Precision Specification

You asked for a type to store "infinitely large numbers." The standard implementation (linked lists of digits) is too slow for a high-performance language.

The Best Practice solution is **Small-Object Optimized (SOO) BigInts**.

### 2.1 The `BigInt` Primitive

- **Definition:** A signed integer that grows dynamically to fit any value.
- **Memory Layout (The "Hybrid" Strategy):**
  The compiler uses pointer tagging (or a struct layout) to distinguish between "Small" and "Large" states.

  - **Case A: Fits in 64 bits (Small)**
    - If the value fits in `i63`, it is stored **inline**. No heap allocation. No pointer chasing.
    - Performance: Near-native `i64` speed.
  - **Case B: Overflow (Large)**
    - If the value exceeds $2^{63}$, the runtime allocates a `BigDigit` array in the **Arena** (for local calc) or **Heap** (for storage).
    - Performance: Slower, but mathematically correct.

### 2.2 Syntax & Usage

```rust
// 'B' suffix forces BigInt literal
let x = 100B;

// Automatic promotion prevents overflow panic
let huge = x.pow(1000); // Allocates automatically
```

### 2.3 Integration with `@gpu`

- **Constraint:** `BigInt` relies on dynamic branching/allocation (if large).
- **Conflict:** GPUs hate branching and allocation.
- **Resolution:** Usage of `BigInt` inside a `@gpu` kernel triggers a **Compile Error**. The Agent must use `i64` or `u64` for GPU code.

---

## 3. Requirements Traceability

| Feature              | Solution                             | Benefit                                                  |
| :------------------- | :----------------------------------- | :------------------------------------------------------- |
| **Unit Declaration** | `unit Name;` keyword.                | Readable, mathematically sound (Abelian Group).          |
| **Unit Cost**        | **Erasure.**                         | Zero runtime overhead. `f64<Meter>` is as fast as `f64`. |
| **Infinite Numbers** | `BigInt` primitive.                  | Safe math for crypto/science.                            |
| **BigInt Speed**     | **SOO (Small Object Optimization).** | 99% of calculations are fast (stack-only).               |

### Summary of the "Scientific Stack"

1.  **Define:** `unit Meter;`
2.  **Measure:** `let x: f64<Meter> = ...`
3.  **Compute:** `let result = x * y;` (Compiler checks dimensions).
4.  **Scale:** If numbers get astronomical, use `BigInt` (`100B`).

This ensures the Agent behaves like a Physicist (checking units) and a Mathematician (infinite precision) simultaneously.
