# DESIGN-005: Documentation Design

**Design ID:** DESIGN-005  
**Title:** Documentation Design  
**Status:** Draft  
**Created:** 2026-01-30  
**Related ADRs:** ADR-001, ADR-002, ADR-006  
**Related Requirements:** REQ-001 through REQ-007

---

## Purpose and Scope

This design document defines technical specifications for documentation in the Morph language Lean 4 formal verification project. It specifies docstring structure and format, documentation patterns for types, theorems, lemmas, and examples, and cross-reference conventions.

The scope includes:
- Docstring structure and format
- Module-level documentation
- Type documentation
- Function and theorem documentation
- Lemma and proof documentation
- Example documentation
- Cross-reference conventions
- Inline comment guidelines

---

## Technical Specifications

### Documentation Principles

#### Comment the "Why," Not the "What"

Documentation should explain the reasoning behind code, not just what the code does:

```lean
-- Good: Explains why we do this
-- Reverse iteration to handle index shifting during deletion
for i in List.reverse indices do
  ...

-- Bad: Describes what the code does
-- Loop through the array in reverse
for i in List.reverse indices do
  ...
```

#### Be Complete and Precise

Documentation must be complete and precise:

```lean
-- Good: Complete documentation
/-- Compute the SHA256 hash of module content.
    
    This hash is used for content-addressable module identification.
    
    **Parameters:**
    - `content`: The module source code as a string
    
    **Returns:** The SHA256 hash as a hexadecimal string
    
    **Invariant:** The hash is deterministic for identical inputs
-/
def computeModuleHash (content : String) : String := ...

-- Bad: Incomplete documentation
/-- Compute hash of content. -/
def computeModuleHash (content : String) : String := ...
```

---

## Docstring Structure and Format

### Module-Level Documentation

Every module must have module-level documentation using `/-! ... -/`:

```lean
/-!
# Specification: Memory Model

**Source:** `spec/memory/memory_model.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** John Doe

## Overview

This module formalizes the memory model for the Morph language, including
memory allocation, deallocation, and safety properties.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| MEM-001 | `memory_allocation_creates_block` | ✓ |
| MEM-002 | `memory_deallocation_frees_block` | ✓ |

## Known Issues

None

## TODO

None
-!/
```

### Type Documentation

All type definitions must have documentation:

```lean
/-- A memory block with its properties.
    
    A memory block represents a contiguous region of memory with a specific
    address, size, and allocation status. Blocks are used to track memory
    allocations and deallocations in the Morph language.
    
    **Fields:**
    - `address`: The starting address of the block
    - `size`: The size of the block in bytes
    - `allocated`: Whether the block is currently allocated
    
    **Invariants:**
    - `size > 0`: Blocks must have positive size
    - `address % alignment = 0`: Address must be aligned
-/
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
  deriving Repr, BEq
```

### Function Documentation

All public functions must have documentation:

```lean
/-- Allocate a new memory block of the given size.
    
    This function allocates a new memory block with the specified size
    and returns the updated memory state along with the address of the
    allocated block.
    
    **Parameters:**
    - `size`: The size of the block to allocate in bytes
    
    **Returns:** A pair consisting of the new memory state and the address
    of the allocated block
    
    **Preconditions:**
    - `size > 0`: Size must be positive
    - `size % alignment = 0`: Size must be aligned
    
    **Postconditions:**
    - The returned address is unique in the new state
    - The block at the returned address is marked as allocated
    - All existing blocks are preserved with their properties
    
    **Complexity:** O(n) where n is the number of blocks in the state
-/
def allocate (size : Nat) (state : MemoryState) : MemoryState × Nat :=
  sorry
```

### Theorem Documentation

All theorems must have documentation:

```lean
/-- Theorem: Allocation creates a unique block.
    
    This theorem states that allocating a new block always produces
    a block with a unique address that does not conflict with
    existing blocks.
    
    **Formal Statement:**
    ```
    ∀ size state, let (newState, address) := allocate size state
      ∀ b ∈ newState, b.address = address → b.allocated
    ```
    
    **Proof Strategy:**
    1. Use the definition of allocate to show the new block is allocated
    2. Show that no other block has the same address by uniqueness of allocation
    3. Conclude the result
    
    **Dependencies:**
    - `allocationDoesNotOverlap`
    - `findBlockByAddress`
    
    **Related Theorems:**
    - `deallocationFreesBlock`
    - `memorySafety`
-/
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) :
  let (newState, address) := allocate size state
  ∀ b ∈ newState, b.address = address → b.allocated := by
  sorry
```

### Lemma Documentation

All lemmas must have documentation:

```lean
/-- Lemma: Allocation preserves the size of existing blocks.
    
    This lemma proves that when allocating a new block, all existing
    blocks retain their original sizes.
    
    **Proof Strategy:** Direct proof using the definition of allocate.
    
    **Dependencies:** None
-/
lemma allocationPreservesSize (size : Nat) (state : MemoryState) :
  let (newState, _) := allocate size state
  ∀ b ∈ state, ∃ b' ∈ newState, b.address = b.address ∧ b'.size = b.size := by
  sorry
```

### Example Documentation

All examples must have documentation:

```lean
/-- Example: An empty memory state.
    
    This example demonstrates the empty memory state, which contains
    no allocated blocks.
-/
def emptyMemoryState : MemoryState := #[]

/-- Example: Allocate a 16-byte block in empty memory state.
    
    This example demonstrates allocating a 16-byte block in an empty
    memory state and shows the resulting state and address.
-/
#eval allocate 16 emptyMemoryState

/-- Verification: Verify that allocation preserves block sizes.
    
    This example demonstrates the use of `allocationPreservesSize` lemma
    to verify that allocation preserves the size of existing blocks.
-/
#example allocationPreservesSizeExample :
  let (newState, _) := allocate 16 oneBlockState
  allocationPreservesSize 16 oneBlockState := by
  sorry
```

---

## Documentation Patterns

### Type Documentation Pattern

Type documentation should include:
- Purpose of the type
- Description of fields/constructors
- Invariants (if any)
- Usage notes (if applicable)

```lean
/-- A memory block with its properties.
    
    A memory block represents a contiguous region of memory with a specific
    address, size, and allocation status. Blocks are used to track memory
    allocations and deallocations in the Morph language.
    
    **Fields:**
    - `address`: The starting address of the block
    - `size`: The size of the block in bytes
    - `allocated`: Whether the block is currently allocated
    
    **Invariants:**
    - `size > 0`: Blocks must have positive size
    - `address % alignment = 0`: Address must be aligned
    
    **Usage Notes:**
    - Blocks are created by the `allocate` function
    - Blocks are deallocated by the `deallocate` function
    - Use `findBlock` to locate a block by address
-/
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
  deriving Repr, BEq
```

### Function Documentation Pattern

Function documentation should include:
- Purpose of the function
- Description of parameters
- Description of return value
- Preconditions (if any)
- Postconditions (if any)
- Complexity (if applicable)
- Usage notes (if applicable)

```lean
/-- Allocate a new memory block of the given size.
    
    This function allocates a new memory block with the specified size
    and returns the updated memory state along with the address of the
    allocated block.
    
    **Parameters:**
    - `size`: The size of the block to allocate in bytes
    
    **Returns:** A pair consisting of the new memory state and the address
    of the allocated block
    
    **Preconditions:**
    - `size > 0`: Size must be positive
    - `size % alignment = 0`: Size must be aligned
    
    **Postconditions:**
    - The returned address is unique in the new state
    - The block at the returned address is marked as allocated
    - All existing blocks are preserved with their properties
    
    **Complexity:** O(n) where n is the number of blocks in the state
    
    **Usage Notes:**
    - Use `deallocate` to free the allocated block
    - Use `findBlock` to locate the allocated block
-/
def allocate (size : Nat) (state : MemoryState) : MemoryState × Nat :=
  sorry
```

### Theorem Documentation Pattern

Theorem documentation should include:
- Statement of what the theorem proves
- Formal statement (in mathematical notation)
- Proof strategy
- Dependencies (lemmas/theorems used)
- Related theorems

```lean
/-- Theorem: Allocation creates a unique block.
    
    This theorem states that allocating a new block always produces
    a block with a unique address that does not conflict with
    existing blocks.
    
    **Formal Statement:**
    ```
    ∀ size state, let (newState, address) := allocate size state
      ∀ b ∈ newState, b.address = address → b.allocated
    ```
    
    **Proof Strategy:**
    1. Use the definition of allocate to show the new block is allocated
    2. Show that no other block has the same address by uniqueness of allocation
    3. Conclude the result
    
    **Dependencies:**
    - `allocationDoesNotOverlap`
    - `findBlockByAddress`
    
    **Related Theorems:**
    - `deallocationFreesBlock`
    - `memorySafety`
-/
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) :
  let (newState, address) := allocate size state
  ∀ b ∈ newState, b.address = address → b.allocated := by
  sorry
```

---

## Cross-Reference Conventions

### Referencing Other Modules

When referencing definitions from other modules, use full paths:

```lean
/-- This function uses `Morph.Specs.Memory.MemoryModel.allocate` to
    allocate memory blocks.
-/
def allocateInMemory (size : Nat) : MemoryState × Nat :=
  Morph.Specs.Memory.MemoryModel.allocate size emptyMemoryState
```

### Referencing Lemmas and Theorems

When referencing lemmas and theorems, use their full names:

```lean
/-- This theorem uses `allocationPreservesSize` to prove that
    allocation does not change the size of existing blocks.
-/
theorem allocationDoesNotChangeSizes (size : Nat) (state : MemoryState) :
  let (newState, _) := allocate size state
  ∀ b ∈ state, ∃ b' ∈ newState, b'.size = b.size := by
  intro b b_in_state
  have h := allocationPreservesSize size state
  sorry
```

### Referencing Specification Documents

When referencing specification documents, use markdown links:

```lean
/-!
# Specification: Memory Model

**Source:** [`spec/memory/memory_model.md`](../../spec/memory/memory_model.md)
**Status:** Complete
-!/
```

### Referencing ADRs

When referencing ADRs, use markdown links:

```lean
/-!
# Specification: Memory Model

This module follows the three-file pattern as specified in
[`ADR-001: Three-File Module Pattern`](../02_adrs/ADR-001-three-file-module-pattern.md).
-!/
```

---

## Inline Comment Guidelines

### When to Use Inline Comments

Use inline comments when code is non-obvious:

```lean
-- Good: Explains non-obvious logic
-- Use bitwise XOR to combine hashes for better distribution
def combineHashes (h1 h2 : Nat) : Nat := h1 ^^^ h2
```

### When Not to Use Inline Comments

Don't use inline comments for obvious code:

```lean
-- Bad: States the obvious
-- Add two numbers
def add (x y : Nat) : Nat := x + y
```

### Section Comments

Use section comments to organize code:

```lean
/-! ## Type Definitions
-/

structure MemoryBlock where ...

/-! ## Core Operations
-/

def allocate (size : Nat) (state : MemoryState) : MemoryState × Nat := ...

/-! ## Specification Theorems
-/

theorem allocationCreatesUniqueBlock : Prop := ...
```

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Missing Documentation

**Incorrect:**
```lean
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
```

**Correct:**
```lean
/-- A memory block with its properties. -/
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
```

### Anti-Pattern 2: Incomplete Documentation

**Incorrect:**
```lean
/-- Allocate a block. -/
def allocate (size : Nat) (state : MemoryState) : MemoryState × Nat := ...
```

**Correct:**
```lean
/-- Allocate a new memory block of the given size.
    
    **Parameters:**
    - `size`: The size of the block to allocate in bytes
    
    **Returns:** The new memory state and the address of the allocated block
-/
def allocate (size : Nat) (state : MemoryState) : MemoryState × Nat := ...
```

### Anti-Pattern 3: Commenting the Obvious

**Incorrect:**
```lean
-- Add two numbers
def add (x y : Nat) : Nat := x + y
```

**Correct:**
```lean
def add (x y : Nat) : Nat := x + y
```

### Anti-Pattern 4: Commented-Out Code

**Incorrect (STRICTLY FORBIDDEN):**
```lean
-- Old implementation
-- def allocate_old (size : Nat) : MemoryState := ...

-- New implementation
def allocate (size : Nat) : MemoryState := ...
```

**Correct:**
```lean
def allocate (size : Nat) : MemoryState := ...
```

### Anti-Pattern 5: TODO Comments Without Tracking

**Incorrect:**
```lean
-- TODO: Implement this
def incompleteFunction : Nat := 0
```

**Correct:**
```lean
-- TODO: Implement this (tracked in issue #123)
def incompleteFunction : Nat := 0
```

---

## Verification Checklist

For each documentation element, verify:

- [ ] Module has module-level documentation
- [ ] All types have documentation
- [ ] All public functions have documentation
- [ ] All theorems have documentation
- [ ] All lemmas have documentation
- [ ] All examples have documentation
- [ ] Documentation is complete and precise
- [ ] Documentation explains "why" not just "what"
- [ ] Cross-references use proper formats
- [ ] No commented-out code blocks
- [ ] No TODO comments without tracking

---

## References

- [ADR-001: Three-File Module Pattern](../02_adrs/ADR-001-three-file-module-pattern.md)
- [ADR-002: Zero-Tolerance for Commented-Out Code](../02_adrs/ADR-002-zero-tolerance-commented-code.md)
- [ADR-006: Complete Proof Requirement](../02_adrs/ADR-006-complete-proof-requirement.md)
- [Coding Standards](../01_standards/coding_standards.md)
- [REQ-001: Core Foundation Requirements](../04_future_state/reqs/REQ-001-core-foundation.md)
- [Lean 4 Documentation on Documentation](https://leanprover.github.io/lean4/doc/documentation.html)
