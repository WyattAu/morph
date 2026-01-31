# DESIGN-004: Example Structure Design

**Design ID:** DESIGN-004  
**Title:** Example Structure Design  
**Status:** Draft  
**Created:** 2026-01-30  
**Related ADRs:** ADR-001, ADR-006  
**Related Requirements:** REQ-001 through REQ-007

---

## Purpose and Scope

This design document defines technical specifications for example structure in the Morph language Lean 4 formal verification project. It specifies example naming conventions, example organization patterns, verification patterns for examples, and executable example standards.

The scope includes:
- Example naming conventions
- Example organization within Examples.lean files
- Type instantiation examples
- Operation examples and usage demonstrations
- Verification examples using lemmas
- Executable examples using `#eval` and `#reduce`

---

## Technical Specifications

### Example Naming Conventions

#### Example Names (camelCase)

All example names must use camelCase and be descriptive:

```lean
-- Good
def emptyMemoryState : MemoryState := ...
def exampleBlock : MemoryBlock := ...
def allocate16Bytes : MemoryState × Nat := ...
def deallocateBlock : MemoryState := ...

-- Bad
def empty_state : MemoryState := ...
def example_block : MemoryBlock := ...
def alloc_16 : MemoryState × Nat := ...
def dealloc_block : MemoryState := ...
```

#### Test Case Names (camelCase)

Test case names should indicate what is being tested:

```lean
-- Good
#example allocationPreservesSizeExample : Prop := ...
#example deallocationPreservesOtherBlocksExample : Prop := ...
#example typePreservationExample : Prop := ...

-- Bad
#example alloc_size_test : Prop := ...
#example dealloc_other_test : Prop := ...
#example type_pres_test : Prop := ...
```

---

## Example Organization Patterns

### Section Organization

Examples.lean files should be organized into sections:

```lean
namespace Morph.Specs.Memory.MemoryModel

/-! ## Type Instantiations
-/

def emptyMemoryState : MemoryState := ...
def exampleBlock : MemoryBlock := ...

/-! ## Operation Examples
-/

#eval allocate 16 emptyMemoryState
#eval deallocate 0x1000 oneBlockState

/-! ## Verification Examples
-/

#example allocationPreservesSizeExample : Prop := ...
#example deallocationPreservesOtherBlocksExample : Prop := ...

/-! ## Complex Scenarios
-/

def allocateMultipleBlocks : MemoryState := ...
def deallocateAllBlocks : MemoryState := ...

end Morph.Specs.Memory.MemoryModel
```

### Example Structure Template

Each example should follow this structure:

```lean
/-- Example: Brief description of what the example demonstrates.
    
    **Purpose:** What this example shows
    
    **Related Lemma/ Theorem:** Which lemma or theorem this example verifies
-/
def exampleName : Type := 
  -- Example implementation
  ...

/-- Verification: Verify the example against a lemma. -/
#example verificationName : Prop := by
  -- Verification proof
  ...
```

---

## Type Instantiation Examples

### Simple Type Instantiation

```lean
/-- Example: An empty memory state. -/
def emptyMemoryState : MemoryState := #[]

/-- Example: A memory block at address 0x1000 with size 16 bytes. -/
def exampleBlock : MemoryBlock :=
  { address := 0x1000, size := 16, allocated := true }

/-- Example: A memory state with one allocated block. -/
def oneBlockState : MemoryState := #[exampleBlock]

/-- Example: A memory state with multiple allocated blocks. -/
def multipleBlocksState : MemoryState :=
  #[{ address := 0x1000, size := 16, allocated := true },
    { address := 0x2000, size := 32, allocated := true },
    { address := 0x3000, size := 64, allocated := true }]
```

### Parameterized Type Instantiation

```lean
/-- Example: A generic result type with String error. -/
abbrev StringResult (ValueType : Type) := Result String ValueType

/-- Example: A successful result. -/
def successResult : StringResult Nat :=
  Result.ok 42

/-- Example: An error result. -/
def errorResult : StringResult Nat :=
  Result.error "Division by zero"

/-- Example: An option type with Nat. -/
abbrev NatOption := Option Nat

/-- Example: Some value. -/
def someValue : NatOption := some 42

/-- Example: None value. -/
def noneValue : NatOption := none
```

### Complex Type Instantiation

```lean
/-- Example: A type environment mapping variable names to types. -/
def exampleTypeEnv : TypeEnv :=
  HashMap.ofList [("x", Nat), ("y", Nat), ("z", Bool)]

/-- Example: An expression AST. -/
def exampleExpr : Expr :=
  Expr.add (Expr.const 5) (Expr.mul (Expr.const 3) (Expr.const 7))

/-- Example: A program with multiple statements. -/
def exampleProgram : Program :=
  [{ stmt := Stmt.assign "x" (Expr.const 5) },
    { stmt := Stmt.assign "y" (Expr.add (Expr.var "x") (Expr.const 3)) }]
```

---

## Operation Examples

### Basic Operation Examples

```lean
/-! ## Allocation Examples
-/

/-- Example: Allocate a 16-byte block in empty memory state. -/
#eval allocate 16 emptyMemoryState

/-- Example: Allocate a 32-byte block in existing memory state. -/
#eval allocate 32 oneBlockState

/-- Example: Allocate a 64-byte block in memory state with multiple blocks. -/
#eval allocate 64 multipleBlocksState

/-! ## Deallocation Examples
-/

/-- Example: Deallocate the block at address 0x1000. -/
#eval deallocate 0x1000 oneBlockState

/-- Example: Deallocate the block at address 0x2000. -/
#eval deallocate 0x2000 multipleBlocksState

/-- Example: Deallocate all blocks sequentially. -/
#eval deallocate 0x3000 (deallocate 0x2000 (deallocate 0x1000 multipleBlocksState))
```

### Chained Operation Examples

```lean
/-- Example: Allocate multiple blocks sequentially. -/
def allocateMultipleBlocks (sizes : List Nat) : MemoryState × List Nat :=
  sizes.foldl (fun (state, addresses) size =>
    let (newState, address) := allocate size state
    (newState, addresses ++ [address])) (emptyMemoryState, [])

#eval allocateMultipleBlocks [16, 32, 64]

/-- Example: Allocate and then deallocate a block. -/
def allocateAndDeallocate (size : Nat) : MemoryState := do
  let (state, address) := allocate size emptyMemoryState
  deallocate address state

#eval allocateAndDeallocate 16
```

### Complex Operation Examples

```lean
/-- Example: Allocate blocks, deallocate some, and allocate more. -/
def complexAllocationSequence : MemoryState := do
  let (state1, addr1) := allocate 16 emptyMemoryState
  let (state2, addr2) := allocate 32 state1
  let state3 := deallocate addr1 state2
  let (state4, addr3) := allocate 64 state3
  state4

#eval complexAllocationSequence

/-- Example: Simulate a program's memory allocation pattern. -/
def simulateProgramMemory : MemoryState := do
  let (state1, heap) := allocate 1024 emptyMemoryState
  let (state2, stack) := allocate 512 state1
  let state3 := deallocate heap state2
  let (state4, newHeap) := allocate 2048 state3
  state4

#eval simulateProgramMemory
```

---

## Verification Examples

### Simple Verification Examples

```lean
/-! ## Basic Verification Examples
-/

/-- Example: Verify that allocation preserves block sizes.
    
    This example demonstrates the use of `allocationPreservesSize` lemma.
-/
#example allocationPreservesSizeExample :
  let (newState, _) := allocate 16 oneBlockState
  allocationPreservesSize 16 oneBlockState := by
  sorry

/-- Example: Verify that deallocation preserves other blocks.
    
    This example demonstrates the use of `deallocationPreservesOtherBlocks` lemma.
-/
#example deallocationPreservesOtherBlocksExample :
  let newState := deallocate 0x1000 oneBlockState
  deallocationPreservesOtherBlocks 0x1000 oneBlockState := by
  sorry
```

### Property Verification Examples

```lean
/-! ## Property Verification Examples
-/

/-- Example: Verify that allocation creates unique blocks.
    
    This example demonstrates the use of `allocationCreatesUniqueBlock` theorem.
-/
#example allocationCreatesUniqueBlockExample :
  let (newState, address) := allocate 16 emptyMemoryState
  allocationCreatesUniqueBlock 16 emptyMemoryState := by
  sorry

/-- Example: Verify that deallocation frees the block.
    
    This example demonstrates the use of `deallocationFreesBlock` theorem.
-/
#example deallocationFreesBlockExample :
  let newState := deallocate 0x1000 oneBlockState
  deallocationFreesBlock 0x1000 oneBlockState := by
  sorry
```

### Complex Verification Examples

```lean
/-! ## Complex Verification Examples
-/

/-- Example: Verify that multiple allocations preserve all block sizes.
    
    This example demonstrates chaining multiple lemmas to verify
    a complex property.
-/
#example multipleAllocationsPreserveSizes :
  let (state1, _) := allocate 16 emptyMemoryState
  let (state2, _) := allocate 32 state1
  let (state3, _) := allocate 64 state2
  allocationPreservesSize 16 emptyMemoryState ∧
  allocationPreservesSize 32 state1 ∧
  allocationPreservesSize 64 state2 := by
  sorry

/-- Example: Verify that deallocation maintains well-formedness.
    
    This example demonstrates using multiple lemmas to verify
    that a complex operation maintains an invariant.
-/
#example deallocationMaintainsWellFormedness :
  let newState := deallocate 0x1000 multipleBlocksState
  deallocationPreservesOtherBlocks 0x1000 multipleBlocksState ∧
  allocationDoesNotOverlap 16 emptyMemoryState ∧
  allocationDoesNotOverlap 32 (allocate 16 emptyMemoryState).fst := by
  sorry
```

---

## Executable Examples

### Using `#eval` for Computation

```lean
/-! ## Computation Examples
-/

/-- Example: Compute the size of an expression. -/
#eval exampleExpr.size

/-- Example: Compute the hash of a module. -/
#eval computeModuleHash "example module content"

/-- Example: Find a block by address. -/
#eval findBlock 0x1000 oneBlockState

/-- Example: Check if a block is allocated. -/
#eval exampleBlock.allocated
```

### Using `#reduce` for Reduction

```lean
/-! ## Reduction Examples
-/

/-- Example: Reduce an expression to normal form. -/
#reduce exampleExpr

/-- Example: Reduce a type expression. -/
#reduce (Nat → Nat)

/-- Example: Reduce a computation. -/
#reduce (allocate 16 emptyMemoryState).fst
```

### Using `#check` for Type Checking

```lean
/-! ## Type Checking Examples
-/

/-- Example: Check the type of an expression. -/
#check exampleExpr

/-- Example: Check the type of a memory state. -/
#check emptyMemoryState

/-- Example: Check the type of an allocation result. -/
#check (allocate 16 emptyMemoryState)
```

---

## Complex Scenario Examples

### Multi-Step Scenarios

```lean
/-! ## Multi-Step Scenarios
-/

/-- Example: Allocate blocks, perform operations, deallocate, verify.
    
    This example demonstrates a complete scenario that includes:
    1. Allocating multiple blocks
    2. Performing operations on the blocks
    3. Deallocating some blocks
    4. Verifying properties at each step
-/
def complexScenario : MemoryState := do
  let (state1, addr1) := allocate 16 emptyMemoryState
  let (state2, addr2) := allocate 32 state1
  let state3 := deallocate addr1 state2
  let (state4, addr3) := allocate 64 state3
  state4

#eval complexScenario

#example complexScenarioVerification :
  let (state1, addr1) := allocate 16 emptyMemoryState
  let (state2, addr2) := allocate 32 state1
  let state3 := deallocate addr1 state2
  let (state4, addr3) := allocate 64 state3
  allocationCreatesUniqueBlock 16 emptyMemoryState ∧
  allocationCreatesUniqueBlock 32 state1 ∧
  deallocationFreesBlock addr1 state2 ∧
  allocationCreatesUniqueBlock 64 state3 := by
  sorry
```

### Error Handling Scenarios

```lean
/-! ## Error Handling Scenarios
-/

/-- Example: Attempt to deallocate a non-existent block. -/
def deallocateNonExistentBlock : MemoryState :=
  deallocate 0x9999 emptyMemoryState

#eval deallocateNonExistentBlock

/-- Example: Attempt to allocate a zero-size block. -/
def allocateZeroSizeBlock : MemoryState × Nat :=
  allocate 0 emptyMemoryState

#eval allocateZeroSizeBlock

/-- Example: Attempt to deallocate an already deallocated block. -/
def deallocateTwice : MemoryState := do
  let state1 := deallocate 0x1000 oneBlockState
  deallocate 0x1000 state1

#eval deallocateTwice
```

### Performance Scenarios

```lean
/-! ## Performance Scenarios
-/

/-- Example: Allocate many small blocks. -/
def allocateManySmallBlocks (count : Nat) : MemoryState :=
  List.range count |> List.foldl (fun state _ =>
    (allocate 16 state).fst) emptyMemoryState

#eval allocateManySmallBlocks 100

/-- Example: Allocate and deallocate in a loop. -/
def allocateDeallocateLoop (iterations : Nat) : MemoryState :=
  List.range iterations |> List.foldl (fun state i =>
    let (s, addr) := allocate 16 state
    deallocate addr s) emptyMemoryState

#eval allocateDeallocateLoop 50

/-- Example: Simulate a realistic allocation pattern. -/
def realisticAllocationPattern : MemoryState := do
  let (s1, heap) := allocate 4096 emptyMemoryState
  let (s2, stack) := allocate 1024 s1
  let (s3, code) := allocate 2048 s2
  let s4 := deallocate stack s3
  let (s5, newStack) := allocate 2048 s4
  s5

#eval realisticAllocationPattern
```

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Examples Without Documentation

**Incorrect:**
```lean
def emptyMemoryState : MemoryState := #[]
```

**Correct:**
```lean
/-- Example: An empty memory state. -/
def emptyMemoryState : MemoryState := #[]
```

### Anti-Pattern 2: Non-Executable Examples

**Incorrect:**
```lean
def allocateExample : MemoryState :=
  allocate 16 emptyMemoryState
```

**Correct:**
```lean
/-- Example: Allocate a 16-byte block in empty memory state. -/
#eval allocate 16 emptyMemoryState
```

### Anti-Pattern 3: Examples Without Verification

**Incorrect:**
```lean
def allocateExample : MemoryState := do
  let (state, _) := allocate 16 emptyMemoryState
  state
```

**Correct:**
```lean
/-- Example: Allocate a 16-byte block. -/
def allocateExample : MemoryState := do
  let (state, _) := allocate 16 emptyMemoryState
  state

#eval allocateExample

/-- Verification: Verify allocation preserves sizes. -/
#example allocationPreservesSizeExample :
  let (newState, _) := allocate 16 emptyMemoryState
  allocationPreservesSize 16 emptyMemoryState := by
  sorry
```

### Anti-Pattern 4: Using `sorry` in Examples

**Incorrect:**
```lean
#example verificationExample : Prop := by
  sorry
```

**Correct:**
```lean
#example verificationExample : Prop := by
  -- Complete verification proof
  sorry
```

### Anti-Pattern 5: Commented-Out Example Code

**Incorrect:**
```lean
-- Old example that didn't work
-- def oldExample : MemoryState := ...

-- New example
def newExample : MemoryState := ...
```

**Correct:**
```lean
/-- Example: Current working example. -/
def newExample : MemoryState := ...
```

---

## Verification Checklist

For each example, verify:

- [ ] Example name uses camelCase
- [ ] Example has documentation
- [ ] Example is executable (uses `#eval` or `#reduce` where appropriate)
- [ ] Example has verification where applicable
- [ ] Example demonstrates a clear property or usage pattern
- [ ] Example is in the correct file (Examples.lean)
- [ ] Example imports only from Spec.lean and Lemmas.lean
- [ ] No commented-out example code
- [ ] No `sorry` placeholders in verification (unless demonstrating a lemma)
- [ ] Example is well-organized into sections

---

## References

- [ADR-001: Three-File Module Pattern](../02_adrs/ADR-001-three-file-module-pattern.md)
- [ADR-006: Complete Proof Requirement](../02_adrs/ADR-006-complete-proof-requirement.md)
- [Coding Standards](../01_standards/coding_standards.md)
- [REQ-001: Core Foundation Requirements](../04_future_state/reqs/REQ-001-core-foundation.md)
- [Lean 4 Documentation on Examples](https://leanprover.github.io/lean4/doc/examples.html)
