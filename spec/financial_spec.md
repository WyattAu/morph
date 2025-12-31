# Domain Extension Specification: Financial (DES-FIN)

**System:** Morph Ecosystem
**Version:** 1.0.0-FINAL
**Context:** Layer 2 (Compiler) & Layer 4 (Standard Library)
**Formalism:** Dimensional Analysis, Fixed-Point Logic, Kernel Bypass

---

## 1. Unified Monetary Semantics

Morph treats Currency as a **Physical Dimension**, utilizing the compiler's Unit Algebra engine to enforce logical correctness in exchange and valuation.

### 1.1 Currency Units

- **REQ-FIN-01 (Unit Declaration):** Currencies SHALL be defined using the `unit` keyword.
- **REQ-FIN-02 (Base Primitive):** The backing type for monetary values MUST be `dec128` (IEEE 754-2008) to ensure 34 digits of decimal precision and exact representation of powers of 10.
- **Syntax:**

  ```rust
  // Base Units
  unit USD;
  unit EUR;
  unit BTC;

  // Usage (Type Erasure applies at runtime)
  let balance: dec128<USD> = 100.50d;
  ```

### 1.2 Dimensional Exchange Rates

Exchange rates are not raw numbers; they are **Ratios**. This prevents the "Inverted Rate" bug (multiplying when one should divide).

- **REQ-FIN-03 (Ratio Types):** Exchange rates MUST be typed as `dec128<Target / Source>`.
- **REQ-FIN-04 (Algebraic Cancellation):** The Compiler SHALL enforce cancellation rules.

  ```rust
  fn convert(amount: dec128<USD>, rate: dec128<EUR / USD>) -> dec128<EUR> {
      // [USD] * [EUR / USD] == [EUR]
      ret amount * rate;
  }

  // HALLUCINATION CHECK:
  // If Agent writes: 'ret amount / rate;'
  // Result Unit: [USD] / [EUR / USD] == [USD^2 / EUR]
  // Compiler Error: Type Mismatch. Expected <EUR>, found <USD^2 / EUR>.
  ```

### 1.3 Variance and Risk Models

- **REQ-FIN-05 (Higher Order Units):** The compiler supports squared units for statistical risk models.
  - Variance: `dec128<USD * USD>`
  - Covariance: `dec128<USD * EUR>`

---

## 2. Arithmetic Safety & Precision

### 2.1 Explicit Rounding Contexts

Financial operations involving division or multiplication by non-integer rates often result in infinite repeating decimals.

- **REQ-FIN-06 (Rounding Scope):** Operations that can increase scale (precision) beyond the storage type are PROHIBITED outside of a `rounding` block.
- **Syntax:**

  ```rust
  let price: dec128<USD> = 10.00d;
  let tax_rate: dec128 = 0.08125d;

  // Compile Error: Implicit truncation prohibited.
  // let tax: dec128<USD> = price * tax_rate;

  // Valid:
  with rounding(Mode::Bankers, Scale::2) {
      let tax: dec128<USD> = price * tax_rate; // result 0.81
  }
  ```

### 2.2 Temporal Day Counting

- **REQ-FIN-07 (Standardized Time):** The standard library provides `morph::fin::DayCount`.
- **Behavior:** Enforces specific logic for `Date` subtraction (e.g., `Act/360`, `30/360`) to align with ISDA standards.

---

## 3. High-Frequency Trading (HFT) Extensions

For Order Matching Engines and Market Makers, the Morph Runtime (`Green Threads` + `Arenas`) is too slow. We introduce **Bare Metal Mode**.

### 3.1 The `@critical` Attribute

- **REQ-FIN-08 (The HFT Constraint):** Functions marked `@critical` trigger the **Zero-Latency Compiler Pass**.
- **Constraints:**
  1.  **No Allocation:** Heap allocation (`iso`, `val`) is a Compile Error. Only Stack variables allow.
  2.  **No Scheduler:** Code does not yield. It runs on a dedicated, pinned OS Thread (`pthread_setaffinity`).
  3.  **No Bounds Checks:** Array indexing is unchecked (Agent must prove safety via `requires` or use fixed-size arrays).
  4.  **No `dec128`:** Logic must use `i64` (Fixed Point Micros/Nanos) for integer-only arithmetic.

### 3.2 Memory Layout (Cache Line Alignment)

- **REQ-FIN-09 (Packed Structures):** The `#[packed(64)]` attribute forces data structures to align to CPU Cache Lines (typically 64 bytes) to prevent False Sharing in multi-core order books.
  ```rust
  @critical
  type Order = {
      price: i64, // 8 bytes
      qty: u32,   // 4 bytes
      id: u32     // 4 bytes
  } #[packed(cache_line)];
  ```

---

## 4. Auditability & Compliance

Regulatory bodies (SEC, ESMA) require immutable logs of why a decision was made.

### 4.1 Intrinsic Audit Logging

- **REQ-FIN-10 (Sidecar Injection):** Modules marked `@auditable` undergo AST injection.
- **Behavior:** Every public state mutation automatically:
  1.  Captures the Timestamp (High Precision).
  2.  Captures the Input Arguments.
  3.  Captures the Pre-image and Post-image Hash of the State.
  4.  Writes to an append-only `Ledger` struct.
- **Agent Safety:** The Agent cannot "forget" to log a trade execution. The compiler inserts the logger.

### 4.2 Immutable Ledgers

- **REQ-FIN-11 (Append-Only):** The `Ledger<T>` type supports `append()` and `read()`, but strictly NO `delete()` or `update()`. This enforces WORM (Write Once, Read Many) compliance at the type level.

---

## 5. Summary

| Feature               | Problem Solved        | Mechanism                                      |
| :-------------------- | :-------------------- | :--------------------------------------------- |
| **`dec128<USD>`**     | Floating Point Errors | IEEE 754-2008 Decimals + Unit Algebra.         |
| **`dec128<EUR/USD>`** | Inverted Rate Bugs    | Algebraic Cancellation of Units.               |
| **`@critical`**       | GC/Scheduler Latency  | Kernel Bypass, Thread Pinning, No-Alloc check. |
| **`@auditable`**      | Regulatory Compliance | Compiler-injected State Logging.               |

This specification allows Morph to serve two masters: the **Quant** who needs sub-microsecond execution (`@critical`), and the **Banker** who needs perfect decimal accounting (`dec128<USD>`).
