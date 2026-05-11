import Morph.Core
import Morph.Memory

/-!
# Module: Tests.Memory

## Purpose

Tests for the Morph memory model covering MemByte, Block, Memory,
Endianness, MemType, and alignment checking.
-/

open Morph

namespace Tests.Memory

section MemByteTests

  /-- MemByte.value.toUInt8 returns the stored value -/
  example (v : UInt8) :
    (MemByte.value v).toUInt8 = v := by
    cases v <;> rfl

  /-- MemByte constructors are distinct -/
  example : MemByte.undef ≠ MemByte.poison := by
    intro h <;> cases h

  example (v : UInt8) : MemByte.value v ≠ MemByte.undef := by
    cases v <;> intro h <;> cases h

  example (v : UInt8) : MemByte.value v ≠ MemByte.poison := by
    cases v <;> intro h <;> cases h

  /-- MemByte.value is injective -/
  example (v1 v2 : UInt8) :
    MemByte.value v1 = MemByte.value v2 → v1 = v2 := by
    intro h; injection h; try assumption; try rfl

  /-- MemByte.isDefined -/
  example (v : UInt8) : (MemByte.value v).isDefined = true := by
    cases v <;> rfl

  example : MemByte.undef.isDefined = false := by rfl

  example : MemByte.poison.isDefined = false := by rfl

  /-- MemByte.isPoison -/
  example : MemByte.poison.isPoison = true := by rfl

  example (v : UInt8) : (MemByte.value v).isPoison = false := by
    cases v <;> rfl

  example : MemByte.undef.isPoison = false := by rfl

  /-- MemByte.toUInt8 defaults to 0 for undef/poison -/
  example : MemByte.undef.toUInt8 = 0 := by rfl

  example : MemByte.poison.toUInt8 = 0 := by rfl

  /-- MemByte equality is reflexive -/
  example (b : MemByte) : b = b := by
    cases b <;> rfl

end MemByteTests

section BlockTests

  def sampleBlockId : Core.BlockId := { id := 0 }

  /-- Block.make creates block with correct fields -/
  example :
    let b := Block.make sampleBlockId 8 4
    b.size = 8 ∧ b.bytes.size = 8 ∧ b.state = BlockState.allocated ∧ b.alignment = 4 := by
    constructor <;> constructor <;> constructor <;> rfl

  /-- Block.make initializes bytes to undef -/
  example :
    let b := Block.make sampleBlockId 4 1
    b.bytes[0]! = MemByte.undef ∧ b.bytes[1]! = MemByte.undef := by
    constructor <;> rfl

  /-- Block.isAllocated and Block.isFreed -/
  example : (Block.make sampleBlockId 8 4).isAllocated = true := by rfl

  example : (Block.make sampleBlockId 8 4).freeBlock.isFreed = true := by rfl

  example : (Block.make sampleBlockId 8 4).freeBlock.isAllocated = false := by rfl

  /-- Block.inBounds -/
  example : Block.inBounds (Block.make sampleBlockId 8 4) 3 = true := by rfl

  example : Block.inBounds (Block.make sampleBlockId 8 4) 8 = false := by rfl

  /-- Block.read -/
  example :
    let b := Block.make sampleBlockId 8 4
    Block.read b 0 = MemByte.undef := by rfl

  example :
    let b := Block.make sampleBlockId 8 4
    Block.read b 100 = MemByte.poison := by rfl

  /-- Block.write preserves size -/
  example :
    let b := Block.make sampleBlockId 8 4
    let b' := Block.write b 0 (MemByte.value 42)
    b'.size = b.size := by rfl

  /-- Block.write out of bounds is a no-op -/
  example :
    let b := Block.make sampleBlockId 8 4
    let b' := Block.write b 100 (MemByte.value 42)
    b'.bytes[0]! = MemByte.undef := by rfl

end BlockTests

section MemoryTests

  /-- Memory.empty -/
  example : Memory.empty.blocks = [] := by rfl

  example : Memory.empty.nextBlockId = 0 := by rfl

  /-- Memory.allocate adds a block -/
  example :
    let (m', _) := Memory.allocate Memory.empty 16 4
    m'.blocks.length = 1 := by rfl

  /-- Memory.allocate increments block IDs -/
  example :
    let (m1, id1) := Memory.allocate Memory.empty 16 4
    let (_m2, id2) := Memory.allocate m1 16 4
    id2.id = id1.id + 1 := by rfl

  /-- Memory.contains -/
  example :
    let (m', bid) := Memory.allocate Memory.empty 16 4
    Memory.contains m' bid = true := by rfl

  example : Memory.contains Memory.empty { id := 0 } = false := by rfl

  /-- Memory.getBlock? -/
  example :
    let (m', bid) := Memory.allocate Memory.empty 16 4
    match Memory.getBlock? m' bid with
    | some b => b.size = 16 ∧ b.isAllocated = true
    | none => False := by
    constructor <;> rfl

  example : Memory.getBlock? Memory.empty { id := 0 } = none := by rfl

  /-- Memory.free changes block state -/
  example :
    let (m', bid) := Memory.allocate Memory.empty 16 4
    let m'' := Memory.free m' bid
    match Memory.getBlock? m'' bid with
    | some b => b.isFreed = true
    | none => False := by rfl

  /-- Memory.free on missing ID is a no-op -/
  example :
    let m := Memory.free Memory.empty { id := 0 }
    m.blocks = [] := by rfl

end MemoryTests

section EndiannessTests

  /-- Endianness constructors are distinct -/
  example : Endianness.LittleEndian ≠ Endianness.BigEndian := by
    intro h <;> cases h

  /-- value_to_bytes produces the correct number of bytes -/
  example :
    (value_to_bytes 42 4 Endianness.LittleEndian).size = 4 := by
    simp [value_to_bytes]

  example :
    (value_to_bytes 0 0 Endianness.LittleEndian).size = 0 := by
    simp [value_to_bytes]

  example :
    (value_to_bytes 42 2 Endianness.LittleEndian).size = 2 := by
    simp [value_to_bytes]

  example :
    (value_to_bytes 42 2 Endianness.BigEndian).size = 2 := by
    simp [value_to_bytes]

  /-- bytes_to_value of empty array is 0 -/
  example :
    bytes_to_value #[] Endianness.LittleEndian = 0 := by
    unfold bytes_to_value; simp [Array.map, Array.foldl]

  example :
    bytes_to_value #[] Endianness.BigEndian = 0 := by
    unfold bytes_to_value; simp [Array.map, Array.foldl]

  example :
    (value_to_bytes 0 0 Endianness.LittleEndian).size = 0 := by
    simp [value_to_bytes]

  /-- value_to_bytes produces the correct number of bytes -/
  example :
    (value_to_bytes 42 2 Endianness.LittleEndian).size = 2 := by
    simp [value_to_bytes]

  example :
    (value_to_bytes 42 2 Endianness.BigEndian).size = 2 := by
    simp [value_to_bytes]

end EndiannessTests

section MemTypeTests

  /-- MemType.size -/
  example : MemType.size .Int8 = 1 := by rfl
  example : MemType.size .Int16 = 2 := by rfl
  example : MemType.size .Int32 = 4 := by rfl
  example : MemType.size .Int64 = 8 := by rfl
  example : MemType.size .UInt8 = 1 := by rfl
  example : MemType.size .UInt16 = 2 := by rfl
  example : MemType.size .UInt32 = 4 := by rfl
  example : MemType.size .UInt64 = 8 := by rfl
  example : MemType.size .Float32 = 4 := by rfl
  example : MemType.size .Float64 = 8 := by rfl
  example : MemType.size .PointerType = 8 := by rfl

  /-- MemType.alignment -/
  example : MemType.alignment .Int8 = 1 := by rfl
  example : MemType.alignment .Int16 = 2 := by rfl
  example : MemType.alignment .Int32 = 4 := by rfl
  example : MemType.alignment .Int64 = 8 := by rfl
  example : MemType.alignment .UInt8 = 1 := by rfl
  example : MemType.alignment .UInt16 = 2 := by rfl
  example : MemType.alignment .UInt32 = 4 := by rfl
  example : MemType.alignment .UInt64 = 8 := by rfl
  example : MemType.alignment .Float32 = 4 := by rfl
  example : MemType.alignment .Float64 = 8 := by rfl
  example : MemType.alignment .PointerType = 8 := by rfl

  /-- MemType.ArrayType -/
  example : MemType.size (.ArrayType .UInt8 4) = 4 := by rfl

  example : MemType.alignment (.ArrayType .UInt32 10) = 4 := by rfl

  /-- alignment_of -/
  example : alignment_of .Int32 = 4 := by rfl

end MemTypeTests

section AlignmentTests

  /-- check_alignment -/
  example : check_alignment 16 4 = true := by rfl

  example : check_alignment 17 4 = false := by rfl

  example : check_alignment 0 8 = true := by rfl

  example : check_alignment 7 1 = true := by rfl

  /-- check_bounds -/
  example : check_bounds (Block.make { id := 0 } 16 4) 4 8 = true := by rfl

  example : check_bounds (Block.make { id := 0 } 16 4) 12 8 = false := by rfl

  example : check_bounds (Block.make { id := 0 } 16 4) 8 0 = true := by rfl

end AlignmentTests

end Tests.Memory
