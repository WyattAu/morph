/- Copyright 2024-2025 The Morph Project Authors
-- SPDX-License-Identifier: Apache-2.0
-/
import Std

namespace Morph.Core

/-!
## Phase Enumeration

The three phases of the AST pipeline:
- `Surface`: Raw source code with syntactic sugar and type inference placeholders
- `Resolved`: Names resolved to unique IDs, syntactic sugar desugared
- `Core`: Minimal CFG/ANF form used as specification target

This parameterization enables type-safe transformations between phases and
compile-time guarantees that phase transitions are explicit.

See ADR-001 for details on the Phase-Separated AST Pattern.
-!/
inductive Phase where
  | Surface
  | Resolved
  | Core
deriving Repr, BEq, Hashable

/-!
## BlockId

Unique identifier for a memory block in the block-offset pointer model.

The block-offset model (CompCert style) represents a pointer not as an integer,
but as a composite key consisting of a block identifier and an offset within
that block. This approach is sound for C++/++/Rust memory models because:

1. **Provenance Tracking:** Enables tracking which allocation a pointer originated from
2. **Alignment Safety:** Block boundaries can be checked for alignment violations
3. **Pointer Arithmetic Safety:** Offsets are bounds-checked within their block

See ADR-002 and Coding Standards Section 1.2 for details.
-!/
structure BlockId where
  id : Nat
deriving Repr, BEq, Hashable

/-!
## ProvenanceId

Unique identifier for pointer provenance tracking.

Provenance tracking is crucial for sound verification of C++/++/Rust optimizations
that rely on pointer provenance (e.g., escape analysis, noalias optimizations).
Each pointer carries an optional provenance ID to track its origin.

See Coding Standards Section 1.2 and RISK-SEC-007 (Memory Model Soundness).
-!/
structure ProvenanceId where
  id : Nat
deriving Repr, BEq, Hashable

/-!
## Pointer

Block-offset pointer with optional provenance tracking.

A pointer consists of:
- `block`: The memory block identifier
- `offset`: Byte offset within the block (can be negative for pre-decrement)
- `provenance`: Optional provenance ID for tracking pointer origin

The offset can be negative to support pre-increment/decrement operations
(e.g., `--ptr` in C). Negative offsets are valid as long as they
stay within block bounds.

See Coding Standards Section 1.2 for block-offset memory model.
-!/
structure Pointer where
  block : BlockId
  offset : Int
  provenance : Option ProvenanceId
deriving Repr, BEq

/-!
## Value

Runtime value representation for the Morph language.

Values can be:
- `int`: Integer values (arbitrary precision)
- `bool`: Boolean values (true/false)
- `string`: String values
- `pointer`: Pointer values (block-offset with provenance)
- `unit`: Unit value (for void functions)
- `undef`: Undefined value (for uninitialized memory)

The `undef` constructor is crucial for modeling uninitialized memory
explicitly, as required by the memory model (see Coding Standards Section 1.2).

See Coding Standards Section 1.2 for memory model details.
-!/
inductive Value where
  | int : Int -> Value
  | bool : Bool -> Value
  | string : String -> Value
  | pointer : Pointer -> Value
  | unit : Value
  | undef : Value
deriving Repr, BEq

/-!
## Type

Type system enumeration for the Morph language.

Types can be:
- `intType`: Integer type
- `boolType`: Boolean type
- `stringType`: String type
- `pointerType`: Pointer type (to any block)
- `unitType`: Unit type (void)
- `arrayType`: Array type with element type and size
- `functionType`: Function type with parameter types and return type

The type system supports both primitive types and composite types (arrays,
functions). This provides a foundation for bidirectional typing (see ADR-004).

See Coding Standards Section 1.4 for bidirectional typing details.
-!/
inductive Typ where
  | intType : Typ
  | boolType : Typ
  | stringType : Typ
  | pointerType : Typ
  | unitType : Typ
  | arrayType : Typ -> Nat -> Typ
  | functionType : List Typ -> Typ -> Typ
deriving Repr, BEq, Hashable

/-!
## Operator

Arithmetic and logical operators for the Morph language.

Operators are categorized by their purpose:
- **Arithmetic:** `add`, `sub`, `mul`, `div`, `mod`
- **Comparison:** `eq`, `neq`, `lt`, `leq`, `gt`, `geq`
- **Logical:** `and`, `or`, `not`
- **Bitwise:** `andb`, `orb`, `xorb`, `notb`, `shl`, `shr`
- **Pointer:** `ptrAdd`, `ptrSub`, `ptrLoad`, `ptrStore`

Pointer operators are crucial for sound verification of pointer arithmetic
and memory operations. They explicitly model pointer operations rather than
relying on integer arithmetic, which could lead to unsoundness.

See Coding Standards Section 1.2 for memory model details.
-!/
inductive Operator where
  -- Arithmetic operators
  | add : Operator
  | sub : Operator
  | mul : Operator
  | div : Operator
  | mod : Operator
  -- Comparison operators
  | eq : Operator
  | neq : Operator
  | lt : Operator
  | leq : Operator
  | gt : Operator
  | geq : Operator
  -- Logical operators
  | and : Operator
  | or : Operator
  | not : Operator
  -- Bitwise operators
  | andb : Operator
  | orb : Operator
  | xorb : Operator
  | notb : Operator
  | shl : Operator
  | shr : Operator
  -- Pointer operators
  | ptrAdd : Operator
  | ptrSub : Operator
  | ptrLoad : Operator
  | ptrStore : Operator
deriving Repr, BEq, Hashable

/-!
## Env

Environment for variable bindings using List for variable bindings.

The environment maps variable names (strings) to their runtime values.
Using `List` for simplicity; can be optimized to HashMap later
if needed for performance (see Coding Standards Section 10.1).

Empty environment can be constructed using `[]`.
Variables can be looked up using list operations.

See Coding Standards Section 10.1 for performance considerations.
-!/
abbrev Env := List (String × Value)

end Morph.Core
