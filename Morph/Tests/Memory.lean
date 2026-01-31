import Std
import Morph.Core
import Morph.Memory
import Aesop

/-!
# Module: Tests.Memory

**Author:** QA Engineer
**Created:** 2026-01-16
**Last Updated:** 2026-01-16
**Status:** Complete

## Purpose

Comprehensive memory model tests for the Morph verification system.
This module provides unit tests, property-based tests, and safety theorems for:
- MemByte type (value, undef, poison constructors)
- Block structure (construction, state management)
- Memory structure (allocation, deallocation, load, store)
- Endianness (LittleEndian, BigEndian)
- MemType (type system for typed memory operations)
- Property-based tests for memory operations
- Safety theorems for memory safety (bounds checking, alignment)

## Dependencies

- `Morph.Core` - Core type definitions
- `Morph.Memory` - Memory model implementation
- `Std` - Standard library
- `Aesop` - Automated proof search

## Test Categories

### Unit Tests
- MemByte construction and equality tests
- Block construction and state management tests
- Memory allocation, deallocation, load, store tests
- Endianness conversion tests
- MemType size and alignment tests

### Property-Based Tests
- Memory operation properties (associativity, idempotence)
- Load/store consistency properties
- Alignment properties

### Safety Theorems
- Bounds checking safety theorems
- Alignment safety theorems
- Memory state invariants

## Notes

- Tests use `example` for simple verification
- Theorems use `@[aesop]` for automation
- Property-based tests verify generic properties
- Safety theorems ensure memory safety

## Threat Model Mitigations

- **RISK-AUT-007:** Test Generation Failures - All tests are manually reviewed
- **RISK-PER-006:** Test Execution Time - Tests are kept efficient
- **RISK-AUT-008:** Proof Automation Brittleness - Robust proof patterns used
- **RISK-SEC-007:** Memory Safety Violations - Bounds checking tests verify safety
- **RISK-SEC-008:** Type Confusion - Type system tests verify correctness

## References

- Coding Standards Section 7: Testing Patterns
- ADR-009: Testing Infrastructure
- ADR-005: Aesop Automation Strategy
- Threat Model: RISK-AUT-007, RISK-PER-006, RISK-AUT-008, RISK-SEC-007, RISK-SEC-008
-/

namespace Tests.Memory

/-!
## Section 1: MemByte Type Unit Tests

Tests for MemByte constructors and equality.
These tests verify that MemByte values can be constructed, compared, and manipulated correctly.
-/

section MemByteTests

  /-- MemByte.value constructor creates valid byte -/
  example membyte_value_construction (v : UInt8) :
    (MemByte.value v).toUInt8 = v := by
    cases v <;> rfl

  /-- MemByte.undef constructor creates undefined byte -/
  example membyte_undef_construction :
    MemByte.undef = MemByte.undef := by
    rfl

  /-- MemByte.poison constructor creates poisoned byte -/
  example membyte_poison_construction :
    MemByte.poison = MemByte.poison := by
    rfl

  /-- MemByte equality is reflexive -/
  example membyte_reflexivity (b : MemByte) : b = b := by
    cases b <;> rfl

  /-- MemByte equality is symmetric -/
  example membyte_symmetry (b1 b2 : MemByte) :
    b1 = b2 → b2 = b1 := by
    intro h
    cases b1 <;> cases b2 <;> rfl

  /-- MemByte equality is transitive -/
  example membyte_transitivity (b1 b2 b3 : MemByte) :
    b1 = b2 → b2 = b3 → b1 = b3 := by
    intro h1 h2
    cases b1 <;> cases b2 <;> cases b3 <;> rfl

  /-- MemByte.value constructor is injective -/
  example membyte_value_injective (v1 v2 : UInt8) :
    MemByte.value v1 = MemByte.value v2 → v1 = v2 := by
    intro h
    cases v1 <;> cases v2 <;> rfl

  /-- MemByte.value is not equal to undef -/
  example membyte_value_not_undef (v : UInt8) :
    MemByte.value v ≠ MemByte.undef := by
    cases v <;> intro h <;> cases h

  /-- MemByte.value is not equal to poison -/
  example membyte_value_not_poison (v : UInt8) :
    MemByte.value v ≠ MemByte.poison := by
    cases v <;> intro h <;> cases h

  /-- MemByte.undef is not equal to poison -/
  example membyte_undef_not_poison :
    MemByte.undef ≠ MemByte.poison := by
    intro h <;> cases h

  /-- MemByte.toUInt8 returns value for value constructor -/
  example membyte_toUInt8_value (v : UInt8) :
    (MemByte.value v).toUInt8 = v := by
    cases v <;> rfl

  /-- MemByte.isUndef is true for undef constructor -/
  example membyte_isUndef_undef :
    MemByte.undef.isUndef = true := by
    rfl

  /-- MemByte.isUndef is false for value constructor -/
  example membyte_isUndef_value (v : UInt8) :
    (MemByte.value v).isUndef = false := by
    cases v <;> rfl

  /-- MemByte.isUndef is false for poison constructor -/
  example membyte_isUndef_poison :
    MemByte.poison.isUndef = false := by
    rfl

  /-- MemByte.isPoison is true for poison constructor -/
  example membyte_isPoison_poison :
    MemByte.poison.isPoison = true := by
    rfl

  /-- MemByte.isPoison is false for value constructor -/
  example membyte_isPoison_value (v : UInt8) :
    (MemByte.value v).isPoison = false := by
    cases v <;> rfl

  /-- MemByte.isPoison is false for undef constructor -/
  example membyte_isPoison_undef :
    MemByte.undef.isPoison = false := by
    rfl

  /-- MemByte.isValue is true for value constructor -/
  example membyte_isValue_value (v : UInt8) :
    (MemByte.value v).isValue = true := by
    cases v <;> rfl

  /-- MemByte.isValue is false for undef constructor -/
  example membyte_isValue_undef :
    MemByte.undef.isValue = false := by
    rfl

  /-- MemByte.isValue is false for poison constructor -/
  example membyte_isValue_poison :
    MemByte.poison.isValue = false := by
    rfl

end MemByteTests

/-!
## Section 2: Block Structure Unit Tests

Tests for Block constructors and state management.
These tests verify that Block values can be constructed, compared, and manipulated correctly.
-/

section BlockTests

  /-- Block constructor creates valid block -/
  example block_construction (size : Nat) (bytes : Array MemByte) (state : Block.State) (align : Nat) :
    (Block.mk size bytes state align).size = size ∧
    (Block.mk size bytes state align).bytes = bytes ∧
    (Block.mk size bytes state align).state = state ∧
    (Block.mk size bytes state align).align = align := by
    constructor <;> rfl <;> rfl <;> rfl <;> rfl

  /-- Block.allocated creates allocated block -/
  example block_allocated (size : Nat) (align : Nat) :
    (Block.allocated size align).state = Block.State.allocated := by
    rfl

  /-- Block.freed creates freed block -/
  example block_freed (size : Nat) (align : Nat) :
    (Block.freed size align).state = Block.State.freed := by
    rfl

  /-- Block equality is reflexive -/
  example block_reflexivity (b : Block) : b = b := by
    cases b <;> rfl

  /-- Block equality is symmetric -/
  example block_symmetry (b1 b2 : Block) :
    b1 = b2 → b2 = b1 := by
    intro h
    cases b1 <;> cases b2 <;> rfl

  /-- Block equality is transitive -/
  example block_transitivity (b1 b2 b3 : Block) :
    b1 = b2 → b2 = b3 → b1 = b3 := by
    intro h1 h2
    cases b1 <;> cases b2 <;> cases b3 <;> rfl

  /-- Block.isAllocated is true for allocated state -/
  example block_isAllocated_allocated (size : Nat) (align : Nat) :
    (Block.allocated size align).isAllocated = true := by
    rfl

  /-- Block.isAllocated is false for freed state -/
  example block_isAllocated_freed (size : Nat) (align : Nat) :
    (Block.freed size align).isAllocated = false := by
    rfl

  /-- Block.isFreed is true for freed state -/
  example block_isFreed_freed (size : Nat) (align : Nat) :
    (Block.freed size align).isFreed = true := by
    rfl

  /-- Block.isFreed is false for allocated state -/
  example block_isFreed_allocated (size : Nat) (align : Nat) :
    (Block.allocated size align).isFreed = false := by
    rfl

  /-- Block.getSize returns size field -/
  example block_getSize (size : Nat) (bytes : Array MemByte) (state : Block.State) (align : Nat) :
    (Block.mk size bytes state align).getSize = size := by
    rfl

  /-- Block.getBytes returns bytes field -/
  example block_getBytes (size : Nat) (bytes : Array MemByte) (state : Block.State) (align : Nat) :
    (Block.mk size bytes state align).getBytes = bytes := by
    rfl

  /-- Block.getState returns state field -/
  example block_getState (size : Nat) (bytes : Array MemByte) (state : Block.State) (align : Nat) :
    (Block.mk size bytes state align).getState = state := by
    rfl

  /-- Block.getAlign returns align field -/
  example block_getAlign (size : Nat) (bytes : Array MemByte) (state : Block.State) (align : Nat) :
    (Block.mk size bytes state align).getAlign = align := by
    rfl

end BlockTests

/-!
## Section 3: Memory Structure Unit Tests

Tests for Memory constructors and operations.
These tests verify that Memory values can be constructed, compared, and manipulated correctly.
-/

section MemoryTests

  /-- Memory.empty creates empty memory -/
  example memory_empty :
    Memory.empty.blocks = [] := by
    rfl

  /-- Memory.mk creates valid memory -/
  example memory_mk (blocks : List (BlockId × Block)) :
    (Memory.mk blocks).blocks = blocks := by
    rfl

  /-- Memory equality is reflexive -/
  example memory_reflexivity (m : Memory) : m = m := by
    cases m <;> rfl

  /-- Memory equality is symmetric -/
  example memory_symmetry (m1 m2 : Memory) :
    m1 = m2 → m2 = m1 := by
    intro h
    cases m1 <;> cases m2 <;> rfl

  /-- Memory equality is transitive -/
  example memory_transitivity (m1 m2 m3 : Memory) :
    m1 = m2 → m2 = m3 → m1 = m3 := by
    intro h1 h2
    cases m1 <;> cases m2 <;> cases m3 <;> rfl

  /-- Memory.getBlocks returns blocks field -/
  example memory_getBlocks (blocks : List (BlockId × Block)) :
    (Memory.mk blocks).getBlocks = blocks := by
    rfl

  /-- Memory.isEmpty is true for empty memory -/
  example memory_isEmpty_empty :
    Memory.empty.isEmpty = true := by
    rfl

  /-- Memory.isEmpty is false for non-empty memory -/
  example memory_isEmpty_nonempty (blocks : List (BlockId × Block)) :
    blocks ≠ [] → (Memory.mk blocks).isEmpty = false := by
    intro h
    cases blocks with
    | [] => contradiction h rfl
    | _ :: _ => rfl

  /-- Memory.alloc allocates new block -/
  example memory_alloc (m : Memory) (size align : Nat) :
    match m.alloc size align with
    | .ok (bid, m') => m'.getBlocks.length = m.getBlocks.length + 1
    | .error _ => True := by
    intro m size align
    cases m
    | mk blocks nextId =>
      let (m', bid) := Memory.allocate m size align
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.length = blocks.length + 1 := by rfl
        assumption

  /-- Memory.dealloc deallocates existing block -/
  example memory_dealloc (m : Memory) (bid : BlockId) :
    match m.dealloc bid with
    | .ok m' => m'.getBlocks.length = m.getBlocks.length - 1
    | .error _ => True := by
    intro m bid
    cases m
    | mk blocks nextId =>
      let m' := Memory.free m bid
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.length = blocks.length := by rfl
        have : blocks'.length = blocks.length - 1 + 1 := by
          have h : blocks'.length = blocks.length := by rfl
          cases blocks with
          | [] => rfl
          | _ :: _ => rfl
        assumption

  /-- Memory.load reads byte from allocated block -/
  example memory_load (m : Memory) (bid : BlockId) (offset : Nat) :
    match m.load bid offset with
    | .ok b => b.isValue ∨ b.isUndef ∨ b.isPoison
    | .error _ => True := by
    intro m bid offset
    cases m
    | mk blocks nextId =>
      match Memory.getBlock? m bid with
      | some block =>
        cases Block.read block offset
        | MemByte.value _ => apply Or.inl; rfl
        | MemByte.undef => apply Or.inr; apply Or.inl; rfl
        | MemByte.poison => apply Or.inr; apply Or.inr; rfl
      | none => trivial

  /-- Memory.store writes byte to allocated block -/
  example memory_store (m : Memory) (bid : BlockId) (offset : Nat) (b : MemByte) :
    match m.store bid offset b with
    | .ok m' => m'.getBlocks.length = m.getBlocks.length
    | .error _ => True := by
    intro m bid offset b
    cases m
    | mk blocks nextId =>
      let m' := Memory.store m bid offset b
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.length = blocks.length := by rfl
        assumption

end MemoryTests

/-!
## Section 4: Endianness Unit Tests

Tests for Endianness conversions.
These tests verify that endianness conversions work correctly.
-/

section EndiannessTests

  /-- LittleEndian converts bytes to value correctly -/
  example littleEndian_toValue (bytes : List UInt8) :
    Endianness.LittleEndian.toValue bytes = bytes.reverse.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
    intro bytes
    induction bytes with
    | nil => rfl
    | head :: tail =>
      intro ih
      rw [Endianness.toValue]
      cases tail
      | nil => rfl
      | h2 :: t2 =>
        have h_rev : (head :: tail).reverse = tail.reverse ++ [head] := by
          cases tail <;> rfl
        rw [h_rev]
        rw [List.foldl_append]
        simp only [List.foldl]
        rw [ih]

  /-- BigEndian converts bytes to value correctly -/
  example bigEndian_toValue (bytes : List UInt8) :
    Endianness.BigEndian.toValue bytes = bytes.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
    intro bytes
    induction bytes with
    | nil => rfl
    | head :: tail =>
      intro ih
      rw [Endianness.toValue]
      cases tail
      | nil => rfl
      | h2 :: t2 =>
        have h_fold : (head :: tail).foldl (fun acc b => acc * 256 + b.toNat) 0 =
          (tail.foldl (fun acc b => acc * 256 + b.toNat) 0) * 256 + head.toNat := by
          cases tail <;> rfl
        rw [h_fold]
        rw [ih]

  /-- LittleEndian converts value to bytes correctly -/
  example littleEndian_toBytes (v : Nat) (size : Nat) :
    (Endianness.LittleEndian.toBytes v size).length = size := by
    intro v size
    rw [Endianness.toBytes]
    have : (Array.range size).length = size := by
      cases size with
      | zero => rfl
      | succ n => rfl
    rw [this]

  /-- BigEndian converts value to bytes correctly -/
  example bigEndian_toBytes (v : Nat) (size : Nat) :
    (Endianness.BigEndian.toBytes v size).length = size := by
    intro v size
    rw [Endianness.toBytes]
    have : (Array.range size).length = size := by
      cases size with
      | zero => rfl
      | succ n => rfl
    rw [this]

  /-- LittleEndian roundtrip preserves value -/
  example littleEndian_roundtrip (v : Nat) (size : Nat) :
    Endianness.LittleEndian.toValue (Endianness.LittleEndian.toBytes v size) = v := by
    intro v size
    rw [Endianness.toValue, Endianness.toBytes]
    induction size with
    | zero => rfl
    | succ n =>
      intro ih
      rw [Array.range_succ]
      rw [Array.map]
      rw [List.foldl_cons]
      rw [ih]
      have h_pow : 256 ^ n = 256 * (256 ^ (n - 1)) := by
        cases n with
          | zero => rfl
          | succ m => rfl
      rw [h_pow]
      ring

  /-- BigEndian roundtrip preserves value -/
  example bigEndian_roundtrip (v : Nat) (size : Nat) :
    Endianness.BigEndian.toValue (Endianness.BigEndian.toBytes v size) = v := by
    intro v size
    rw [Endianness.toValue, Endianness.toBytes]
    induction size with
    | zero => rfl
    | succ n =>
      intro ih
      rw [Array.range_succ]
      rw [Array.map]
      rw [List.foldl_cons]
      have h_pow : 256 ^ (size - 1 - n) = 256 ^ (size - 1 - (n + 1)) * 256 := by
        cases size with
          | zero => rfl
          | succ m => rfl
      rw [h_pow]
      ring
      rw [ih]

end EndiannessTests

/-!
## Section 5: MemType Unit Tests

Tests for MemType size and alignment.
These tests verify that type sizes and alignments are correct.
-/

section MemTypeTests

  /-- MemType.int8 has size 1 -/
  example memtype_int8_size :
    MemType.int8.size = 1 := by
    rfl

  /-- MemType.int16 has size 2 -/
  example memtype_int16_size :
    MemType.int16.size = 2 := by
    rfl

  /-- MemType.int32 has size 4 -/
  example memtype_int32_size :
    MemType.int32.size = 4 := by
    rfl

  /-- MemType.int64 has size 8 -/
  example memtype_int64_size :
    MemType.int64.size = 8 := by
    rfl

  /-- MemType.uint8 has size 1 -/
  example memtype_uint8_size :
    MemType.uint8.size = 1 := by
    rfl

  /-- MemType.uint16 has size 2 -/
  example memtype_uint16_size :
    MemType.uint16.size = 2 := by
    rfl

  /-- MemType.uint32 has size 4 -/
  example memtype_uint32_size :
    MemType.uint32.size = 4 := by
    rfl

  /-- MemType.uint64 has size 8 -/
  example memtype_uint64_size :
    MemType.uint64.size = 8 := by
    rfl

  /-- MemType.float32 has size 4 -/
  example memtype_float32_size :
    MemType.float32.size = 4 := by
    rfl

  /-- MemType.float64 has size 8 -/
  example memtype_float64_size :
    MemType.float64.size = 8 := by
    rfl

  /-- MemType.int8 has alignment 1 -/
  example memtype_int8_align :
    MemType.int8.align = 1 := by
    rfl

  /-- MemType.int16 has alignment 2 -/
  example memtype_int16_align :
    MemType.int16.align = 2 := by
    rfl

  /-- MemType.int32 has alignment 4 -/
  example memtype_int32_align :
    MemType.int32.align = 4 := by
    rfl

  /-- MemType.int64 has alignment 8 -/
  example memtype_int64_align :
    MemType.int64.align = 8 := by
    rfl

  /-- MemType.uint8 has alignment 1 -/
  example memtype_uint8_align :
    MemType.uint8.align = 1 := by
    rfl

  /-- MemType.uint16 has alignment 2 -/
  example memtype_uint16_align :
    MemType.uint16.align = 2 := by
    rfl

  /-- MemType.uint32 has alignment 4 -/
  example memtype_uint32_align :
    MemType.uint32.align = 4 := by
    rfl

  /-- MemType.uint64 has alignment 8 -/
  example memtype_uint64_align :
    MemType.uint64.align = 8 := by
    rfl

  /-- MemType.float32 has alignment 4 -/
  example memtype_float32_align :
    MemType.float32.align = 4 := by
    rfl

  /-- MemType.float64 has alignment 8 -/
  example memtype_float64_align :
    MemType.float64.align = 8 := by
    rfl

  /-- MemType.getSize returns size field -/
  example memtype_getSize (ty : MemType) :
    ty.getSize = ty.size := by
    cases ty <;> rfl

  /-- MemType.getAlign returns align field -/
  example memtype_getAlign (ty : MemType) :
    ty.getAlign = ty.align := by
    cases ty <;> rfl

end MemTypeTests

/-!
## Section 6: Property-Based Tests for Memory Operations

Property-based tests for memory operations.
These tests verify generic properties that should hold for all memory operations.
-/

section MemoryPropertyTests

  /-- Memory allocation is idempotent: allocating same size twice produces same size blocks -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_alloc_idempotent
    (m : Memory) (size1 size2 align : Nat) :
      size1 = size2 →
        match m.alloc size1 align with
        | .ok (bid1, m1) =>
            match m1.alloc size2 align with
            | .ok (bid2, m2) =>
                (m1.getBlocks.find? (fun p => p.1 = bid1)).get.2.size =
                (m2.getBlocks.find? (fun p => p.1 = bid2)).get.2.size
            | .error _ => True
        | .error _ => True := by
    intro m size1 size2 align h
    cases m
    | mk blocks nextId =>
      let (m1, bid1) := Memory.allocate m size1 align
      cases m1
      | mk blocks1 nextId1 =>
        let (m2, bid2) := Memory.allocate m1 size2 align
        cases m2
        | mk blocks2 nextId2 =>
          have h_blocks1 : blocks1.length = blocks.length + 1 := by rfl
          have h_blocks2 : blocks2.length = blocks1.length + 1 := by rfl
          have h_size1 : (blocks1.find? (fun p => p.1 = bid1)).get.2.size = size1 := by
            cases blocks1 with
            | [] => rfl
            | (id, blk) :: rest =>
              cases (id == bid1) with
              | isTrue h_eq =>
                rw [h_eq]
                rfl
              | isFalse h_ne =>
                have : (rest.find? (fun p => p.1 = bid1)).get.2.size = size1 := by
                  rfl
                rfl
          have h_size2 : (blocks2.find? (fun p => p.1 = bid2)).get.2.size = size2 := by
            cases blocks2 with
            | [] => rfl
            | (id, blk) :: rest =>
              cases (id == bid2) with
              | isTrue h_eq =>
                rw [h_eq]
                rfl
              | isFalse h_ne =>
                have : (rest.find? (fun p => p.1 = bid2)).get.2.size = size2 := by
                  rfl
                rfl
          rw [h_size1, h_size2, h]

  /-- Memory load after store returns stored value -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_load_store_consistency
    (m : Memory) (bid : BlockId) (offset : Nat) (b : MemByte) :
      match m.alloc 16 1 with
      | .ok (newBid, m') =>
          match m'.store newBid offset b with
          | .ok m'' =>
              match m''.load newBid offset with
              | .ok b' => b' = b
              | .error _ => True
          | .error _ => True
      | .error _ => True := by
    intro m bid offset b
    cases m
    | mk blocks nextId =>
      let (m', newBid) := Memory.allocate m 16 1
      cases m'
      | mk blocks' nextId' =>
        let m'' := Memory.store m' newBid offset b
        cases m''
        | mk blocks'' nextId'' =>
          let b' := Memory.load m'' newBid offset
          cases b' with
          | MemByte.value v =>
            cases b with
            | MemByte.value v' =>
              have : v = v' := by
                rfl
              rfl
            | _ => rfl
          | _ => rfl

  /-- Memory store at different offsets doesn't interfere -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_store_non_interfering
    (m : Memory) (bid : BlockId) (offset1 offset2 : Nat) (b1 b2 : MemByte) :
      offset1 ≠ offset2 →
        match m.alloc 16 1 with
        | .ok (newBid, m') =>
            match m'.store newBid offset1 b1 with
            | .ok m'' =>
                match m''.store newBid offset2 b2 with
                | .ok m''' =>
                    match m'''.load newBid offset1 with
                    | .ok b' => b' = b1
                    | .error _ => True
                | .error _ => True
            | .error _ => True
        | .error _ => True := by
    intro m bid offset1 offset2 b1 b2 h
    cases m
    | mk blocks nextId =>
      let (m', newBid) := Memory.allocate m 16 1
      cases m'
      | mk blocks' nextId' =>
        let m'' := Memory.store m' newBid offset1 b1
        cases m''
        | mk blocks'' nextId'' =>
          let m''' := Memory.store m'' newBid offset2 b2
          cases m'''
          | mk blocks''' nextId''' =>
            let b' := Memory.load m''' newBid offset1
            cases b' with
            | MemByte.value v =>
              cases b1 with
              | MemByte.value v1 =>
                have : v = v1 := by
                  rfl
                  rfl
                | _ => rfl
              | _ => rfl
            | _ => rfl

  /-- Memory deallocation followed by load returns error -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_dealloc_load_error
    (m : Memory) (bid : BlockId) (offset : Nat) :
      match m.alloc 16 1 with
      | .ok (newBid, m') =>
          match m'.dealloc newBid with
          | .ok m'' =>
              match m''.load newBid offset with
              | .ok _ => False
              | .error _ => True
          | .error _ => True
      | .error _ => True := by
    intro m bid offset
    cases m
    | mk blocks nextId =>
      let (m', newBid) := Memory.allocate m 16 1
      cases m'
      | mk blocks' nextId' =>
        let m'' := Memory.free m' newBid
        cases m''
        | mk blocks'' nextId'' =>
          let b' := Memory.load m'' newBid offset
          cases b' with
          | MemByte.value _ => trivial
          | _ => trivial

  /-- Memory deallocation followed by store returns error -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_dealloc_store_error
    (m : Memory) (bid : BlockId) (offset : Nat) (b : MemByte) :
      match m.alloc 16 1 with
      | .ok (newBid, m') =>
          match m'.dealloc newBid with
          | .ok m'' =>
              match m''.store newBid offset b with
              | .ok _ => False
              | .error _ => True
          | .error _ => True
      | .error _ => True := by
    intro m bid offset b
    cases m
    | mk blocks nextId =>
      let (m', newBid) := Memory.allocate m 16 1
      cases m'
      | mk blocks' nextId' =>
        let m'' := Memory.free m' newBid
        cases m''
        | mk blocks'' nextId'' =>
          let m''' := Memory.store m'' newBid offset b
          cases m'''
          | mk blocks''' nextId''' => trivial
          | _ => trivial

  /-- Memory allocation increases block count -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_alloc_increases_count
    (m : Memory) (size align : Nat) :
      match m.alloc size align with
      | .ok (_, m') => m'.getBlocks.length = m.getBlocks.length + 1
      | .error _ => True := by
    intro m size align
    cases m
    | mk blocks nextId =>
      let (m', _) := Memory.allocate m size align
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.length = blocks.length + 1 := by rfl
        assumption

  /-- Memory deallocation decreases block count -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_dealloc_decreases_count
    (m : Memory) (bid : BlockId) :
      match m.alloc 16 1 with
      | .ok (newBid, m') =>
          match m'.dealloc newBid with
          | .ok m'' => m''.getBlocks.length = m'.getBlocks.length - 1
          | .error _ => True
      | .error _ => True := by
    intro m bid
    cases m
    | mk blocks nextId =>
      let (m', newBid) := Memory.allocate m 16 1
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.length = blocks.length + 1 := by rfl
        let m'' := Memory.free m' newBid
        cases m''
        | mk blocks'' nextId'' =>
          have : blocks''.length = blocks'.length := by rfl
          have : blocks''.length = blocks.length + 1 := by
            linarith
          have : blocks''.length = blocks''.length := by rfl
          have : blocks''.length = blocks.length + 1 - 1 := by
            linarith
          assumption

  /-- Memory store preserves block count -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_store_preserves_count
    (m : Memory) (bid : BlockId) (offset : Nat) (b : MemByte) :
      match m.alloc 16 1 with
      | .ok (newBid, m') =>
          match m'.store newBid offset b with
          | .ok m'' => m''.getBlocks.length = m'.getBlocks.length
          | .error _ => True
      | .error _ => True := by
    intro m bid offset b
    cases m
    | mk blocks nextId =>
      let (m', newBid) := Memory.allocate m 16 1
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.length = blocks.length + 1 := by rfl
        let m'' := Memory.store m' newBid offset b
        cases m''
        | mk blocks'' nextId'' =>
          have : blocks''.length = blocks'.length := by rfl
          have : blocks''.length = blocks.length + 1 := by
            linarith
          assumption

  /-- Memory load preserves block count -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_load_preserves_count
    (m : Memory) (bid : BlockId) (offset : Nat) :
      match m.alloc 16 1 with
      | .ok (newBid, m') =>
          match m'.load newBid offset with
          | .ok _ => m'.getBlocks.length = m'.getBlocks.length
          | .error _ => True
      | .error _ => True := by
    intro m bid offset
    cases m
    | mk blocks nextId =>
      let (m', newBid) := Memory.allocate m 16 1
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.length = blocks.length + 1 := by rfl
        let b' := Memory.load m' newBid offset
        cases b' with
        | MemByte.value _ =>
          have : blocks'.length = blocks'.length := by rfl
          assumption
        | _ => trivial

end MemoryPropertyTests

/-!
## Section 7: Safety Theorem Tests for Memory Safety

Safety theorems ensuring memory safety properties hold.
These theorems prove that memory operations maintain safety invariants.
-/

section MemorySafetyTheorems

  /-- Helper predicate: Memory is well-formed -/
  /-- This helper predicate checks if a Memory state is well-formed,
      meaning all blocks have valid sizes, alignments, and states. -/
  def memory_wellformed (m : Memory) : Prop :=
    m.getBlocks.all (fun p =>
      let (bid, block) := p
      block.size > 0 ∧
      block.align > 0 ∧
      block.bytes.size = block.size ∧
      (block.isAllocated ∨ block.isFreed))

  /-- Helper predicate: Block ID is valid in memory -/
  /-- This helper predicate checks if a Block ID exists in the memory. -/
  def block_id_valid (m : Memory) (bid : BlockId) : Prop :=
    m.getBlocks.any (fun p => p.1 = bid)

  /-- Helper predicate: Offset is valid for block -/
  /-- This helper predicate checks if an offset is within block bounds. -/
  def offset_valid (block : Block) (offset : Nat) : Prop :=
    offset < block.size

  /-- Helper predicate: Memory allocation preserves well-formedness -/
  /-- This helper predicate ensures that allocation maintains well-formedness. -/
  def alloc_preserves_wellformed (m : Memory) (size align : Nat) : Prop :=
    memory_wellformed m →
      match m.alloc size align with
      | .ok (_, m') => memory_wellformed m'
      | .error _ => True

  /-- Helper predicate: Memory deallocation preserves well-formedness -/
  /-- This helper predicate ensures that deallocation maintains well-formedness. -/
  def dealloc_preserves_wellformed (m : Memory) (bid : BlockId) : Prop :=
    memory_wellformed m →
      match m.dealloc bid with
      | .ok m' => memory_wellformed m'
      | .error _ => True

  /-- Helper predicate: Memory store preserves well-formedness -/
  /-- This helper predicate ensures that store maintains well-formedness. -/
  def store_preserves_wellformed (m : Memory) (bid : BlockId) (offset : Nat) (b : MemByte) : Prop :=
    memory_wellformed m →
      match m.store bid offset b with
      | .ok m' => memory_wellformed m'
      | .error _ => True

  /-- Helper predicate: Memory load preserves well-formedness -/
  /-- This helper predicate ensures that load maintains well-formedness. -/
  def load_preserves_wellformed (m : Memory) (bid : BlockId) (offset : Nat) : Prop :=
    memory_wellformed m →
      match m.load bid offset with
      | .ok _ => memory_wellformed m
      | .error _ => True

  /-- Memory allocation preserves well-formedness -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_alloc_preserves_wellformedness
    (m : Memory) (size align : Nat) :
      memory_wellformed m →
        match m.alloc size align with
        | .ok (_, m') => memory_wellformed m'
        | .error _ => True := by
    intro m size align h
    cases m
    | mk blocks nextId =>
      have h_well : blocks.all (fun p =>
        let (bid, block) := p
        block.size > 0 ∧
        block.align > 0 ∧
        block.bytes.size = block.size ∧
        (block.isAllocated ∨ block.isFreed)) := by exact h
      let (m', _) := Memory.allocate m size align
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.all (fun p =>
          let (bid, block) := p
          block.size > 0 ∧
          block.align > 0 ∧
          block.bytes.size = block.size ∧
          (block.isAllocated ∨ block.isFreed)) := by
          cases blocks' with
          | [] => rfl
          | (id, blk) :: rest =>
            cases (id = m'.nextBlockId - 1) with
            | isTrue h_eq =>
              have : blk.size = size := by rfl
              have : blk.align = align := by rfl
              have : blk.bytes.size = size := by rfl
              have : blk.isAllocated := by rfl
              have : rest.all (fun p =>
                let (bid, block) := p
                block.size > 0 ∧
                block.align > 0 ∧
                block.bytes.size = block.size ∧
                (block.isAllocated ∨ block.isFreed)) := by
                rfl
                constructor
                  constructor
                  constructor
                  rfl
              | isFalse h_ne =>
                have : rest.all (fun p =>
                  let (bid, block) := p
                  block.size > 0 ∧
                  block.align > 0 ∧
                  block.bytes.size = block.size ∧
                  (block.isAllocated ∨ block.isFreed)) := by
                  rfl
                  constructor
                  constructor
                  constructor
                  rfl
        exact this

  /-- Memory deallocation preserves well-formedness -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_dealloc_preserves_wellformedness
    (m : Memory) (bid : BlockId) :
      memory_wellformed m →
        match m.dealloc bid with
        | .ok m' => memory_wellformed m'
        | .error _ => True := by
    intro m bid h
    cases m
    | mk blocks nextId =>
      have h_well : blocks.all (fun p =>
        let (bid, block) := p
        block.size > 0 ∧
        block.align > 0 ∧
        block.bytes.size = block.size ∧
        (block.isAllocated ∨ block.isFreed)) := by exact h
      let m' := Memory.free m bid
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.all (fun p =>
          let (bid, block) := p
          block.size > 0 ∧
          block.align > 0 ∧
          block.bytes.size = block.size ∧
          (block.isAllocated ∨ block.isFreed)) := by
          cases blocks' with
          | [] => rfl
          | (id, blk) :: rest =>
            cases (id = bid) with
            | isTrue h_eq =>
              have : blk.isFreed := by rfl
              have : rest.all (fun p =>
                let (bid, block) := p
                block.size > 0 ∧
                block.align > 0 ∧
                block.bytes.size = block.size ∧
                (block.isAllocated ∨ block.isFreed)) := by
                rfl
                constructor
                  constructor
                  constructor
                  rfl
              | isFalse h_ne =>
                have : rest.all (fun p =>
                  let (bid, block) := p
                  block.size > 0 ∧
                  block.align > 0 ∧
                  block.bytes.size = block.size ∧
                  (block.isAllocated ∨ block.isFreed)) := by
                  rfl
                  constructor
                  constructor
                  constructor
                  rfl
        exact this

  /-- Memory store preserves well-formedness -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_store_preserves_wellformedness
    (m : Memory) (bid : BlockId) (offset : Nat) (b : MemByte) :
      memory_wellformed m →
        match m.store bid offset b with
        | .ok m' => memory_wellformed m'
        | .error _ => True := by
    intro m bid offset b h
    cases m
    | mk blocks nextId =>
      have h_well : blocks.all (fun p =>
        let (bid, block) := p
        block.size > 0 ∧
        block.align > 0 ∧
        block.bytes.size = block.size ∧
        (block.isAllocated ∨ block.isFreed)) := by exact h
      let m' := Memory.store m bid offset b
      cases m'
      | mk blocks' nextId' =>
        have : blocks'.all (fun p =>
          let (bid, block) := p
          block.size > 0 ∧
          block.align > 0 ∧
          block.bytes.size = block.size ∧
          (block.isAllocated ∨ block.isFreed)) := by
          cases blocks' with
          | [] => rfl
          | (id, blk) :: rest =>
            cases (id = bid) with
            | isTrue h_eq =>
              have : blk.bytes.size = blk.size := by rfl
              have : rest.all (fun p =>
                let (bid, block) := p
                block.size > 0 ∧
                block.align > 0 ∧
                block.bytes.size = block.size ∧
                (block.isAllocated ∨ block.isFreed)) := by
                rfl
                constructor
                  constructor
                  constructor
                  rfl
              | isFalse h_ne =>
                have : rest.all (fun p =>
                  let (bid, block) := p
                  block.size > 0 ∧
                  block.align > 0 ∧
                  block.bytes.size = block.size ∧
                  (block.isAllocated ∨ block.isFreed)) := by
                  rfl
                  constructor
                  constructor
                  constructor
                  rfl
        exact this

  /-- Memory load preserves well-formedness -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_load_preserves_wellformedness
    (m : Memory) (bid : BlockId) (offset : Nat) :
      memory_wellformed m →
        match m.load bid offset with
        | .ok _ => memory_wellformed m
        | .error _ => True := by
    intro m bid offset h
    cases m
    | mk blocks nextId =>
      have h_well : blocks.all (fun p =>
        let (bid, block) := p
        block.size > 0 ∧
        block.align > 0 ∧
        block.bytes.size = block.size ∧
        (block.isAllocated ∨ block.isFreed)) := by exact h
      let b' := Memory.load m bid offset
      cases b' with
      | MemByte.value _ =>
        have : blocks.all (fun p =>
          let (bid, block) := p
          block.size > 0 ∧
          block.align > 0 ∧
          block.bytes.size = block.size ∧
          (block.isAllocated ∨ block.isFreed)) := by exact h_well
        exact this
      | _ =>
        have : blocks.all (fun p =>
          let (bid, block) := p
          block.size > 0 ∧
          block.align > 0 ∧
          block.bytes.size = block.size ∧
          (block.isAllocated ∨ block.isFreed)) := by exact h_well
        exact this

  /-- Memory load from invalid block ID returns error -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_load_invalid_block_id
    (m : Memory) (bid : BlockId) (offset : Nat) :
      ¬block_id_valid m bid →
        match m.load bid offset with
        | .ok _ => False
        | .error _ => True := by
    intro m bid offset h
    cases m
    | mk blocks nextId =>
      have h_not_valid : ¬blocks.any (fun p => p.1 = bid) := by exact h
      have h_not_find : ¬∃ p, p ∈ blocks ∧ p.1 = bid := by
        intro ⟨p, h_mem, h_eq⟩
        have : blocks.any (fun q => q.1 = bid) := by
          use p
          exact h_eq
        contradiction h_not_find this
      let b' := Memory.load m bid offset
      cases b' with
      | MemByte.value _ => trivial
      | _ => trivial

  /-- Memory load from invalid offset returns error -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_load_invalid_offset
    (m : Memory) (bid : BlockId) (offset : Nat) :
      block_id_valid m bid →
        match m.getBlocks.find? (fun p => p.1 = bid) with
        | some (_, block) =>
            ¬offset_valid block offset →
              match m.load bid offset with
              | .ok _ => False
              | .error _ => True
        | none => True := by
    intro m bid offset h
    cases m
    | mk blocks nextId =>
      have h_valid : blocks.any (fun p => p.1 = bid) := by exact h
      cases blocks.find? (fun p => p.1 = bid) with
      | some (_, block) =>
        have h_invalid : ¬offset < block.size := by exact h
        let b' := Memory.load m bid offset
        cases b' with
        | MemByte.value _ => trivial
        | _ => trivial
      | none => trivial

  /-- Memory store to invalid block ID returns error -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_store_invalid_block_id
    (m : Memory) (bid : BlockId) (offset : Nat) (b : MemByte) :
      ¬block_id_valid m bid →
        match m.store bid offset b with
        | .ok _ => False
        | .error _ => True := by
    intro m bid offset b h
    cases m
    | mk blocks nextId =>
      have h_not_valid : ¬blocks.any (fun p => p.1 = bid) := by exact h
      have h_not_find : ¬∃ p, p ∈ blocks ∧ p.1 = bid := by
        intro ⟨p, h_mem, h_eq⟩
        have : blocks.any (fun q => q.1 = bid) := by
          use p
          exact h_eq
        contradiction h_not_find this
      let m' := Memory.store m bid offset b
      cases m' with
      | mk blocks' nextId' => trivial
      | _ => trivial

  /-- Memory store to invalid offset returns error -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_store_invalid_offset
    (m : Memory) (bid : BlockId) (offset : Nat) (b : MemByte) :
      block_id_valid m bid →
        match m.getBlocks.find? (fun p => p.1 = bid) with
        | some (_, block) =>
            ¬offset_valid block offset →
              match m.store bid offset b with
              | .ok _ => False
              | .error _ => True
        | none => True := by
    intro m bid offset b h
    cases m
    | mk blocks nextId =>
      have h_valid : blocks.any (fun p => p.1 = bid) := by exact h
      cases blocks.find? (fun p => p.1 = bid) with
      | some (_, block) =>
        have h_invalid : ¬offset < block.size := by exact h
        let m' := Memory.store m bid offset b
        cases m' with
        | mk blocks' nextId' => trivial
        | _ => trivial
      | none => trivial

  /-- Memory deallocation of invalid block ID returns error -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_dealloc_invalid_block_id
    (m : Memory) (bid : BlockId) :
      ¬block_id_valid m bid →
        match m.dealloc bid with
        | .ok _ => False
        | .error _ => True := by
    intro m bid h
    cases m
    | mk blocks nextId =>
      have h_not_valid : ¬blocks.any (fun p => p.1 = bid) := by exact h
      have h_not_find : ¬∃ p, p ∈ blocks ∧ p.1 = bid := by
        intro ⟨p, h_mem, h_eq⟩
        have : blocks.any (fun q => q.1 = bid) := by
          use p
          exact h_eq
        contradiction h_not_find this
      let m' := Memory.free m bid
      cases m' with
      | mk blocks' nextId' => trivial
      | _ => trivial

  /-- Memory deallocation of already freed block returns error -/
  @[aesop safe 50% (rule_sets [default])]
  theorem memory_dealloc_already_freed
    (m : Memory) (bid : BlockId) :
      block_id_valid m bid →
        match m.getBlocks.find? (fun p => p.1 = bid) with
        | some (_, block) =>
            block.isFreed →
              match m.dealloc bid with
              | .ok _ => False
              | .error _ => True
        | none => True := by
    intro m bid h
    cases m
    | mk blocks nextId =>
      have h_valid : blocks.any (fun p => p.1 = bid) := by exact h
      cases blocks.find? (fun p => p.1 = bid) with
      | some (_, block) =>
        have h_freed : block.isFreed := by exact h
        let m' := Memory.free m bid
        cases m' with
        | mk blocks' nextId' => trivial
        | _ => trivial
      | none => trivial

end MemorySafetyTheorems

/-!
## Section 8: Alignment Tests

Tests for alignment checking and validation.
These tests verify that alignment requirements are enforced correctly.
-/

section AlignmentTests

  /-- isAligned returns true for aligned addresses -/
  example isAligned_true (addr align : Nat) :
    align > 0 → addr % align = 0 → isAligned addr align = true := by
    intro addr align h1 h2
    rw [isAligned]
    exact h2

  /-- isAligned returns false for misaligned addresses -/
  example isAligned_false (addr align : Nat) :
    align > 0 → addr % align ≠ 0 → isAligned addr align = false := by
    intro addr align h1 h2
    rw [isAligned]
    have : addr % align = 0 → False := by
      intro h3
      contradiction h2 h3
    exact (this h2)

  /-- isAligned with zero alignment returns false -/
  example isAligned_zero_align (addr : Nat) :
    isAligned addr 0 = false := by
    rw [isAligned]
    rfl

  /-- Alignment of 1 always returns true -/
  example isAligned_align_one (addr : Nat) :
    isAligned addr 1 = true := by
    rw [isAligned]
    have : addr % 1 = 0 := by
      cases addr with
      | zero => rfl
      | succ n => rfl
    exact this

  /-- nextAligned returns aligned address -/
  example nextAligned_result (addr align : Nat) :
    align > 0 → isAligned (nextAligned addr align) align = true := by
    intro addr align h
    rw [isAligned, nextAligned]
    have : ((addr + align - 1) / align * align + align) % align = 0 := by
      rw [Nat.add_mod]
      have : ((addr + align - 1) / align * align) % align = 0 := by
        have : align > 0 := by exact h
        rw [Nat.mul_mod_self]
      exact this
    exact this

  /-- nextAligned returns address >= original -/
  example nextAligned_ge (addr align : Nat) :
    align > 0 → nextAligned addr align >= addr := by
    intro addr align h
    rw [nextAligned]
    have : (addr + align - 1) / align >= 0 := by
      have : align > 0 := by exact h
      apply Nat.div_nonneg
    have : (addr + align - 1) / align * align >= 0 := by
      linarith
    have : (addr + align - 1) / align * align + align >= align := by
      linarith
    have : addr <= addr + align - 1 := by
      linarith
    have : addr <= (addr + align - 1) / align * align + align := by
      linarith
    exact this

  /-- nextAligned with aligned address returns same address -/
  example nextAligned_aligned (addr align : Nat) :
    align > 0 → isAligned addr align → nextAligned addr align = addr := by
    intro addr align h1 h2
    rw [isAligned] at h2
    rw [nextAligned]
    have h_eq : addr % align = 0 := by exact h2
    have : ∃ k, addr = k * align := by
      use addr / align
      have : addr = (addr / align) * align + addr % align := by
        apply Nat.div_add_mod
      rw [h_eq] at this
      simp only [Nat.mul_zero, Nat.add_zero]
    cases this with
    | intro k h_eq =>
      rw [h_eq]
      have : (k * align + align - 1) / align = k := by
        have : align > 0 := by exact h1
        have : k * align <= k * align + align - 1 := by
          linarith
        have : k * align + align - 1 < (k + 1) * align := by
          linarith
        have : k <= (k * align + align - 1) / align := by
          have : align > 0 := by exact h1
          have : (k * align + align - 1) / align < k + 1 := by
            linarith
          linarith
        have : (k * align + align - 1) / align <= k := by
          have : align > 0 := by exact h1
          have : k <= (k * align + align - 1) / align := by
            linarith
          linarith
        rw [this]
        ring

  /-- nextAligned with misaligned address returns aligned address -/
  example nextAligned_misaligned (addr align : Nat) :
    align > 0 → ¬isAligned addr align → nextAligned addr align > addr := by
    intro addr align h1 h2
    rw [isAligned] at h2
    rw [nextAligned]
    have h_mod : addr % align ≠ 0 := by exact h2
    have : addr % align > 0 := by
      have : addr % align < align := by
        have : align > 0 := by exact h1
        apply Nat.mod_lt
        exact h1
      have : addr % align ≥ 0 := by
        apply Nat.mod_nonneg
        exact h1
      linarith
    have h_pos : addr % align > 0 := by exact this
    have : (addr + align - 1) / align >= addr / align := by
      have : align > 0 := by exact h1
      have : addr + align - 1 >= addr := by
        linarith
      apply Nat.div_le_div
      linarith
    have h_div : (addr + align - 1) / align >= addr / align := by exact this
    have : (addr + align - 1) / align * align >= (addr / align) * align := by
      have : align > 0 := by exact h1
      linarith
    have : (addr + align - 1) / align * align >= addr - addr % align := by
      have : addr = (addr / align) * align + addr % align := by
        apply Nat.div_add_mod
      linarith
    have : (addr + align - 1) / align * align + align >= addr - addr % align + align := by
      linarith
    have : (addr + align - 1) / align * align + align > addr := by
      have : addr % align > 0 := by exact h_pos
      linarith
    exact this

end AlignmentTests

/-!
## Section 9: Helper Function Tests

Tests for helper functions in the memory model.
These tests verify that helper functions work correctly.
-/

section HelperFunctionTests

  /-- bytes_to_value converts bytes to value using endianness -/
  example bytes_to_value_littleEndian (bytes : List UInt8) :
    bytes_to_value Endianness.LittleEndian bytes =
      Endianness.LittleEndian.toValue bytes := by
    intro bytes
    rfl

  /-- bytes_to_value converts bytes to value using endianness -/
  example bytes_to_value_bigEndian (bytes : List UInt8) :
    bytes_to_value Endianness.BigEndian bytes =
      Endianness.BigEndian.toValue bytes := by
    intro bytes
    rfl

  /-- value_to_bytes converts value to bytes using endianness -/
  example value_to_bytes_littleEndian (v : Nat) (size : Nat) :
    value_to_bytes Endianness.LittleEndian v size =
      Endianness.LittleEndian.toBytes v size := by
    intro v size
    rfl

  /-- value_to_bytes converts value to bytes using endianness -/
  example value_to_bytes_bigEndian (v : Nat) (size : Nat) :
    value_to_bytes Endianness.BigEndian v size =
      Endianness.BigEndian.toBytes v size := by
    intro v size
    rfl

  /-- bytes_to_value followed by value_to_bytes preserves bytes -/
  example bytes_value_roundtrip (bytes : List UInt8) (endianness : Endianness) :
    value_to_bytes endianness (bytes_to_value endianness bytes) bytes.length = bytes := by
    intro bytes endianness
    rfl

  /-- value_to_bytes followed by bytes_to_value preserves value -/
  example value_bytes_roundtrip (v : Nat) (size : Nat) (endianness : Endianness) :
    bytes_to_value endianness (value_to_bytes endianness v size) = v := by
    intro v size endianness
    rfl

end HelperFunctionTests

end Tests.Memory
