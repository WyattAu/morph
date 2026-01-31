# DESIGN-002: Type System Design

**Design ID:** DESIGN-002  
**Title:** Type System Design  
**Status:** Draft  
**Created:** 2026-01-30  
**Related ADRs:** ADR-003, ADR-001  
**Related Requirements:** REQ-001, REQ-002, REQ-003, REQ-004

---

## Purpose and Scope

This design document defines the technical specifications for type system patterns used across the Morph language Lean 4 formal verification project. It specifies common type patterns, type alias conventions, inductive type structures, and type class usage patterns.

The scope includes:
- Type definitions in Spec.lean files
- Type alias conventions
- Inductive type structures
- Type class definitions and instances
- Dependent type patterns
- Monadic type patterns

---

## Technical Specifications

### Type Naming Conventions

#### Types (PascalCase)

All type names must use PascalCase:

```lean
-- Good
structure MemoryBlock where ...
inductive Expr where ...
abbrev BlockId := ObjectId
class MonadState where ...

-- Bad
structure block where ...
inductive expr where ...
abbrev blockId := ObjectId
```

#### Type Parameters

Type parameters should use descriptive names in PascalCase:

```lean
-- Good
structure Result (ErrorType : Type) (ValueType : Type) where ...
inductive Tree (Element : Type) where ...
abbrev Map (Key : Type) (Value : Type) := RBMap Key Value

-- Bad
structure Result (E : Type) (V : Type) where ...
inductive Tree (T : Type) where ...
abbrev Map (K : Type) (V : Type) := RBMap K V
```

#### Type Aliases (abbrev)

Type aliases must use `abbrev` keyword and PascalCase names:

```lean
-- Good
abbrev MemoryState := Array MemoryBlock
abbrev ProgramId := ObjectId
abbrev TypeEnv := HashMap String Type

-- Bad
def MemoryState := Array MemoryBlock
abbrev memoryState := Array MemoryBlock
```

---

## Common Type Patterns

### Option Type Pattern

Use Lean's built-in `Option` type for optional values:

```lean
/-- Find a block by address, returning none if not found. -/
def findBlock (address : Nat) (state : MemoryState) : Option MemoryBlock :=
  state.find? (fun b => b.address = address)

-- Usage example
def getBlockOrError (address : Nat) (state : MemoryState) : MemoryBlock :=
  match findBlock address state with
  | some block => block
  | none => panic! "Block not found"
```

### Result Type Pattern

Define a custom Result type for operations that can fail:

```lean
/-- A result type that can either succeed with a value or fail with an error. -/
inductive Result (ErrorType : Type) (ValueType : Type) where
  | ok : ValueType → Result ErrorType ValueType
  | error : ErrorType → Result ErrorType ValueType
  deriving Repr, BEq

/-- Shorthand for Result with String error type. -/
abbrev ResultE (ValueType : Type) := Result String ValueType

-- Usage example
def safeDivide (numerator denominator : Nat) : ResultE Nat :=
  if denominator = 0 then
    Result.error "Division by zero"
  else
    Result.ok (numerator / denominator)
```

### Either Type Pattern

Define an Either type for values that can be one of two types:

```lean
/-- An either type that can be left or right. -/
inductive Either (LeftType : Type) (RightType : Type) where
  | left : LeftType → Either LeftType RightType
  | right : RightType → Either LeftType RightType
  deriving Repr, BEq

-- Usage example
def parseOrCompute (input : String) : Either String Nat :=
  match input.toNat? with
  | some n => Either.right n
  | none => Either.left "Invalid number"
```

### Pair/Tuple Type Pattern

Use Lean's built-in `Prod` type for pairs:

```lean
/-- Return both the new state and the allocated address. -/
def allocate (size : Nat) (state : MemoryState) : MemoryState × Nat :=
  let address := findFreeAddress state
  let block := { address := address, size := size, allocated := true }
  (state.push block, address)

-- Usage example
def allocateAndPrint (size : Nat) (state : MemoryState) : IO Unit := do
  let (newState, address) := allocate size state
  IO.println s!"Allocated block at address {address}"
```

---

## Inductive Type Structures

### Basic Inductive Type Pattern

Inductive types should have clear constructors and be well-documented:

```lean
/-- A memory block with its properties. -/
inductive MemoryBlock where
  | mk : (address : Nat) → (size : Nat) → (allocated : Bool) → MemoryBlock
  deriving Repr, BEq

-- Alternative structure syntax (preferred for records)
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
  deriving Repr, BEq
```

### Recursive Inductive Type Pattern

Recursive types should use explicit recursion and be well-founded:

```lean
/-- An abstract syntax tree for expressions. -/
inductive Expr where
  | const : Nat → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr, BEq

-- Compute the size of an expression
def Expr.size : Expr → Nat
  | .const _ => 1
  | .var _ => 1
  | .add e1 e2 => 1 + e1.size + e2.size
  | .mul e1 e2 => 1 + e1.size + e2.size
```

### Parameterized Inductive Type Pattern

Parameterized types should use descriptive type parameters:

```lean
/-- A binary tree with elements of the given type. -/
inductive Tree (Element : Type) where
  | leaf : Tree Element
  | node : Element → Tree Element → Tree Element → Tree Element
  deriving Repr, BEq

-- Compute the height of a tree
def Tree.height {Element : Type} : Tree Element → Nat
  | .leaf => 0
  | .node _ left right => 1 + Nat.max left.height right.height
```

### Dependent Inductive Type Pattern

Dependent types should be used when type-level information is needed:

```lean
/-- A vector with a statically known length. -/
inductive Vec (Element : Type) : Nat → Type where
  | nil : Vec Element 0
  | cons : Element → Vec Element n → Vec Element (n + 1)

-- Safe indexing with dependent types
def Vec.get {Element : Type} {n : Nat} (v : Vec Element n) (i : Fin n) : Element :=
  match v with
  | .nil => nomatch i
  | .cons head tail =>
    match i with
    | 0 => head
    | i+1 => tail.get i
```

---

## Structure Type Patterns

### Basic Structure Pattern

Structures should use the `structure` keyword for record-like types:

```lean
/-- A memory block with its properties. -/
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
  deriving Repr, BEq
```

### Structure with Methods Pattern

Structures can have methods defined in the same namespace:

```lean
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
  deriving Repr, BEq

namespace MemoryBlock

/-- Check if the block is free (not allocated). -/
def isFree (block : MemoryBlock) : Bool :=
  !block.allocated

/-- Get the end address of the block. -/
def endAddress (block : MemoryBlock) : Nat :=
  block.address + block.size

end MemoryBlock
```

### Structure with Inheritance Pattern

Structures can extend other structures:

```lean
/-- A base block type. -/
structure Block where
  address : Nat
  size : Nat
  deriving Repr, BEq

/-- A memory block that extends Block with allocation status. -/
structure MemoryBlock extends Block where
  allocated : Bool
  deriving Repr, BEq

/-- A code block that extends Block with executable flag. -/
structure CodeBlock extends Block where
  executable : Bool
  deriving Repr, BEq
```

---

## Type Class Patterns

### Basic Type Class Pattern

Type classes should define interfaces for common operations:

```lean
/-- A type class for hashable types. -/
class Hashable (α : Type) where
  hash : α → Nat

instance : Hashable Nat where
  hash n := n

instance : Hashable String where
  hash s := s.foldl (fun h c => h + c.toNat) 0
```

### Type Class with Laws Pattern

Type classes should document their laws:

```lean
/-- A type class for monoids.
    
    A monoid is a set with an associative binary operation and an identity element.
    
    **Laws:**
    1. Associativity: `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`
    2. Identity: `a ⊕ e = a` and `e ⊕ a = a`
-/
class Monoid (α : Type) where
  op : α → α → α
  identity : α

instance : Monoid Nat where
  op := Nat.add
  identity := 0

-- Example usage
def monoidExample (a b c : Nat) : Bool :=
  (Monoid.op (Monoid.op a b) c) = (Monoid.op a (Monoid.op b c))
```

### Type Class with Default Instances Pattern

Type classes should provide default instances for common types:

```lean
/-- A type class for comparable types. -/
class Comparable (α : Type) where
  compare : α → α → Ordering

instance : Comparable Nat where
  compare a b :=
  if a < b then Ordering.lt
  else if a > b then Ordering.gt
  else Ordering.eq

instance : Comparable String where
  compare a b := compare a b
```

---

## Monadic Type Patterns

### Option Monad Pattern

Use the Option monad for computations that may fail:

```lean
/-- Safe division that returns none on division by zero. -/
def safeDivide (numerator denominator : Nat) : Option Nat :=
  if denominator = 0 then none else some (numerator / denominator)

/-- Chain multiple safe operations using Option monad. -/
def computeAverage (numbers : List Nat) : Option Nat :=
  if numbers.isEmpty then none
  else
    let sum := numbers.foldl (fun acc n => acc + n) 0
    some (sum / numbers.length)
```

### State Monad Pattern

Use the State monad for stateful computations:

```lean
/-- Allocate a block and update the memory state. -/
def allocateBlock (size : Nat) : State MemoryState Nat := do
  let state ← get
  let address := findFreeAddress state
  let block := { address := address, size := size, allocated := true }
  modify (fun s => s.push block)
  pure address

/-- Allocate multiple blocks sequentially. -/
def allocateBlocks (sizes : List Nat) : State MemoryState (List Nat) := do
  sizes.mapM allocateBlock
```

### Except Monad Pattern

Use the Except monad for computations with explicit errors:

```lean
/-- Division with explicit error handling. -/
def divide (numerator denominator : Nat) : Except String Nat :=
  if denominator = 0 then
    throw "Division by zero"
  else
    pure (numerator / denominator)

/-- Chain multiple operations with error handling. -/
def computeExpression (a b c : Nat) : Except String Nat := do
  let x ← divide a b
  let y ← divide x c
  pure y
```

---

## Dependent Type Patterns

### Fin Type Pattern

Use `Fin n` for bounded natural numbers:

```lean
/-- Safe array indexing using Fin. -/
def getSafe {n : Nat} (arr : Array Nat) (i : Fin n) : Nat :=
  arr.get i

-- Example: This type-checks because 3 < 5
def exampleSafeAccess : Nat :=
  let arr := #[1, 2, 3, 4, 5]
  getSafe arr (Fin.mk 3 (by decide (3 < 5)))
```

### Sigma Type Pattern

Use sigma types for pairs where the second type depends on the first:

```lean
/-- A block with its size as a dependent pair. -/
abbrev SizedBlock := Σ (size : Nat), MemoryBlock

-- Create a sized block
def makeSizedBlock (size : Nat) : SizedBlock :=
  ⟨size, { address := 0, size := size, allocated := true }⟩
```

### Subtype Pattern

Use subtypes to represent constrained values:

```lean
/-- A natural number that is non-zero. -/
abbrev NonZeroNat := { n : Nat // n ≠ 0 }

-- Safe division using subtype
def divideNonZero (numerator : Nat) (denominator : NonZeroNat) : Nat :=
  numerator / denominator.val
```

---

## Type Alias Conventions

### Simple Type Aliases

Simple aliases should use `abbrev`:

```lean
abbrev MemoryState := Array MemoryBlock
abbrev ProgramId := ObjectId
abbrev TypeEnv := HashMap String Type
```

### Parameterized Type Aliases

Parameterized aliases should use descriptive names:

```lean
abbrev ResultE (ValueType : Type) := Result String ValueType
abbrev OptionE (ValueType : Type) := Option ValueType
abbrev ListE (ElementType : Type) := List ElementType
```

### Composite Type Aliases

Composite aliases should be well-documented:

```lean
/-- A memory state with a free list and allocated blocks. -/
abbrev MemorySystem := (freeList : List Nat) × (allocated : Array MemoryBlock)

/-- A program with its type environment and memory state. -/
abbrev ProgramState := (typeEnv : TypeEnv) × (memory : MemoryState)
```

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Using `def` Instead of `abbrev`

**Incorrect:**
```lean
def MemoryState := Array MemoryBlock
```

**Correct:**
```lean
abbrev MemoryState := Array MemoryBlock
```

### Anti-Pattern 2: Underspecified Type Parameters

**Incorrect:**
```lean
inductive Tree (T : Type) where ...
```

**Correct:**
```lean
inductive Tree (Element : Type) where ...
```

### Anti-Pattern 3: Missing Deriving Clauses

**Incorrect:**
```lean
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
```

**Correct:**
```lean
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
  deriving Repr, BEq
```

### Anti-Pattern 4: Using Option When Result is More Appropriate

**Incorrect:**
```lean
def divide (numerator denominator : Nat) : Option Nat :=
  if denominator = 0 then none else some (numerator / denominator)
```

**Correct:**
```lean
def divide (numerator denominator : Nat) : ResultE Nat :=
  if denominator = 0 then Result.error "Division by zero"
  else Result.ok (numerator / denominator)
```

### Anti-Pattern 5: Overusing Dependent Types

**Incorrect:**
```lean
-- Overly complex dependent type for simple case
inductive Vec (Element : Type) : Nat → Type where
  | nil : Vec Element 0
  | cons : Element → Vec Element n → Vec Element (n + 1)
```

**Correct:**
```lean
-- Use List for most cases
abbrev Vec (Element : Type) := List Element
```

---

## Verification Checklist

For each type definition, verify:

- [ ] Type name uses PascalCase
- [ ] Type parameters use descriptive PascalCase names
- [ ] Type aliases use `abbrev` keyword
- [ ] Structures include `deriving` clauses where appropriate
- [ ] Inductive types have clear constructors
- [ ] Recursive types are well-founded
- [ ] Dependent types are necessary and well-justified
- [ ] Type classes document their laws
- [ ] Monadic patterns use appropriate monad (Option, State, Except)
- [ ] Types have complete docstrings

---

## References

- [ADR-003: Lean 4 with mathlib4](../02_adrs/ADR-003-lean4-mathlib4.md)
- [ADR-001: Three-File Module Pattern](../02_adrs/ADR-001-three-file-module-pattern.md)
- [Coding Standards](../01_standards/coding_standards.md)
- [REQ-001: Core Foundation Requirements](../04_future_state/reqs/REQ-001-core-foundation.md)
- [Lean 4 Documentation on Types](https://leanprover.github.io/lean4/doc/types.html)
