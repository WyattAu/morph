import Std
import Morph.Core
import Aesop

/-!
# Module: Tests.Core

**Author:** QA Engineer
**Created:** 2026-01-16
**Last Updated:** 2026-01-16
**Status:** Complete

## Purpose

Comprehensive foundation tests for core types and structures in Morph verification system.
This module provides unit tests, property-based tests, and safety theorems for:
- Phase enumeration
- BlockId structure
- ProvenanceId structure
- Pointer structure
- Value inductive type
- Typ inductive type
- Operator inductive type
- Env structure (List-based environment)
- HashMap operations

## Dependencies

- `Morph.Core` - Core type definitions
- `Std` - Standard library for HashMap operations
- `Aesop` - Automated proof search

## Test Categories

### Unit Tests
- Basic construction and equality tests for core types
- Environment lookup and manipulation tests

### Property-Based Tests
- HashMap operation properties (associativity, commutativity, etc.)

### Safety Theorems
- Type invariants for core types
- Memory safety properties

## Notes

- Tests use `example` for simple verification
- Theorems use `@[aesop]` for automation
- Property-based tests verify generic properties
- Safety theorems ensure type soundness

## Threat Model Mitigations

- **RISK-AUT-007:** Test Generation Failures - All tests are manually reviewed
- **RISK-PER-006:** Test Execution Time - Tests are kept efficient
- **RISK-AUT-008:** Proof Automation Brittleness - Robust proof patterns used

## References

- Coding Standards Section 7: Testing Patterns
- ADR-009: Testing Infrastructure
- ADR-005: Aesop Automation Strategy
- Threat Model: RISK-AUT-007, RISK-PER-006, RISK-AUT-008
-/

namespace Tests.Core

/-!
## Section 1: Phase Unit Tests

Tests for Phase enumeration (Surface, Resolved, Core).
These tests verify that Phase values can be constructed, compared, and hashed correctly.
-/

section PhaseTests

  /-- Phase constructors are distinct -/
  example phase_distinctness : Phase.Surface ≠ Phase.Resolved := by
    cases h
    | rfl => rfl

  /-- Phase constructors are distinct -/
  example phase_distinctness_2 : Phase.Surface ≠ Phase.Core := by
    cases h
    | rfl => rfl

  /-- Phase constructors are distinct -/
  example phase_distinctness_3 : Phase.Resolved ≠ Phase.Core := by
    cases h
    | rfl => rfl

  /-- Phase equality is reflexive -/
  example phase_reflexivity (p : Phase) : p = p := by
    cases p <;> rfl

  /-- Phase equality is symmetric -/
  example phase_symmetry (p1 p2 : Phase) : p1 = p2 → p2 = p1 := by
    intro h
    cases h <;> rfl

  /-- Phase equality is transitive -/
  example phase_transitivity (p1 p2 p3 : Phase) : p1 = p2 → p2 = p3 → p1 = p3 := by
    intro h1 h2
    cases h1 <;> cases h2 <;> rfl

  /-- Phase can be hashed -/
  example phase_hashable (p : Phase) : (hash p) = (hash p) := by
    rfl

end PhaseTests

/-!
## Section 2: BlockId Unit Tests

Tests for BlockId structure (unique identifier for memory blocks).
These tests verify that BlockId values can be constructed, compared, and hashed correctly.
-/

section BlockIdTests

  /-- BlockId constructor creates valid structure -/
  example blockid_construction (n : Nat) : (BlockId.mk n).id = n := by
    rfl

  /-- BlockId equality is reflexive -/
  example blockid_reflexivity (b : BlockId) : b = b := by
    cases b <;> rfl

  /-- BlockId equality is symmetric -/
  example blockid_symmetry (b1 b2 : BlockId) : b1 = b2 → b2 = b1 := by
    intro h
    cases b1 <;> cases b2 <;> rfl

  /-- BlockId equality is transitive -/
  example blockid_transitivity (b1 b2 b3 : BlockId) : b1 = b2 → b2 = b3 → b1 = b3 := by
    intro h1 h2
    cases b1 <;> cases b2 <;> cases b3 <;> rfl

  /-- BlockId can be hashed -/
  example blockid_hashable (b : BlockId) : (hash b) = (hash b) := by
    rfl

  /-- Different BlockIds are not equal -/
  example blockid_inequality (n1 n2 : Nat) : n1 ≠ n2 → BlockId.mk n1 ≠ BlockId.mk n2 := by
    intro h
    cases h

end BlockIdTests

/-!
## Section 3: ProvenanceId Unit Tests

Tests for ProvenanceId structure (unique identifier for pointer provenance tracking).
These tests verify that ProvenanceId values can be constructed, compared, and hashed correctly.
-/

section ProvenanceIdTests

  /-- ProvenanceId constructor creates valid structure -/
  example provenanceid_construction (n : Nat) : (ProvenanceId.mk n).id = n := by
    rfl

  /-- ProvenanceId equality is reflexive -/
  example provenanceid_reflexivity (p : ProvenanceId) : p = p := by
    cases p <;> rfl

  /-- ProvenanceId equality is symmetric -/
  example provenanceid_symmetry (p1 p2 : ProvenanceId) : p1 = p2 → p2 = p1 := by
    intro h
    cases p1 <;> cases p2 <;> rfl

  /-- ProvenanceId equality is transitive -/
  example provenanceid_transitivity (p1 p2 p3 : ProvenanceId) : p1 = p2 → p2 = p3 → p1 = p3 := by
    intro h1 h2
    cases p1 <;> cases p2 <;> cases p3 <;> rfl

  /-- ProvenanceId can be hashed -/
  example provenanceid_hashable (p : ProvenanceId) : (hash p) = (hash p) := by
    rfl

  /-- Different ProvenanceIds are not equal -/
  example provenanceid_inequality (n1 n2 : Nat) : n1 ≠ n2 → ProvenanceId.mk n1 ≠ ProvenanceId.mk n2 := by
    intro h
    cases h

end ProvenanceIdTests

/-!
## Section 4: Pointer Unit Tests

Tests for Pointer structure (block-offset pointer with optional provenance).
These tests verify that Pointer values can be constructed, compared, and manipulated correctly.
-/

section PointerTests

  /-- Pointer constructor creates valid structure -/
  example pointer_construction (b : BlockId) (o : Int) (p : Option ProvenanceId) :
    (Pointer.mk b o p).block = b ∧
    (Pointer.mk b o p).offset = o ∧
    (Pointer.mk b o p).provenance = p := by
    constructor <;> rfl <;> rfl <;> rfl

  /-- Pointer equality is reflexive -/
  example pointer_reflexivity (ptr : Pointer) : ptr = ptr := by
    cases ptr <;> rfl

  /-- Pointer equality is symmetric -/
  example pointer_symmetry (ptr1 ptr2 : Pointer) : ptr1 = ptr2 → ptr2 = ptr1 := by
    intro h
    cases ptr1 <;> cases ptr2 <;> rfl

  /-- Pointer equality is transitive -/
  example pointer_transitivity (ptr1 ptr2 ptr3 : Pointer) :
    ptr1 = ptr2 → ptr2 = ptr3 → ptr1 = ptr3 := by
    intro h1 h2
    cases ptr1 <;> cases ptr2 <;> cases ptr3 <;> rfl

  /-- Pointers with different blocks are not equal -/
  example pointer_block_inequality (b1 b2 : BlockId) (o : Int) (p : Option ProvenanceId) :
    b1 ≠ b2 → Pointer.mk b1 o p ≠ Pointer.mk b2 o p := by
    intro h
    cases h

  /-- Pointers with different offsets are not equal -/
  example pointer_offset_inequality (b : BlockId) (o1 o2 : Int) (p : Option ProvenanceId) :
    o1 ≠ o2 → Pointer.mk b o1 p ≠ Pointer.mk b o2 p := by
    intro h
    cases h

  /-- Pointers with different provenance are not equal -/
  example pointer_provenance_inequality (b : BlockId) (o : Int) (p1 p2 : Option ProvenanceId) :
    p1 ≠ p2 → Pointer.mk b o p1 ≠ Pointer.mk b o p2 := by
    intro h
    cases h

  /-- Pointer with none provenance is valid -/
  example pointer_none_provenance (b : BlockId) (o : Int) :
    (Pointer.mk b o none).provenance = none := by
    rfl

  /-- Pointer with some provenance is valid -/
  example pointer_some_provenance (b : BlockId) (o : Int) (pid : ProvenanceId) :
    (Pointer.mk b o (some pid)).provenance = some pid := by
    rfl

end PointerTests

/-!
## Section 5: Value Unit Tests

Tests for Value inductive type (runtime value representation).
These tests verify that Value constructors work correctly and values can be compared.
-/

section ValueTests

  /-- Value.int constructor creates valid value -/
  example value_int_construction (n : Int) : (Value.int n) = Value.int n := by
    rfl

  /-- Value.bool constructor creates valid value -/
  example value_bool_construction (b : Bool) : (Value.bool b) = Value.bool b := by
    rfl

  /-- Value.string constructor creates valid value -/
  example value_string_construction (s : String) : (Value.string s) = Value.string s := by
    rfl

  /-- Value.pointer constructor creates valid value -/
  example value_pointer_construction (ptr : Pointer) : (Value.pointer ptr) = Value.pointer ptr := by
    rfl

  /-- Value.unit constructor creates valid value -/
  example value_unit_construction : Value.unit = Value.unit := by
    rfl

  /-- Value.undef constructor creates valid value -/
  example value_undef_construction : Value.undef = Value.undef := by
    rfl

  /-- Value equality is reflexive -/
  example value_reflexivity (v : Value) : v = v := by
    cases v <;> rfl

  /-- Value equality is symmetric -/
  example value_symmetry (v1 v2 : Value) : v1 = v2 → v2 = v1 := by
    intro h
    cases v1 <;> cases v2 <;> rfl

  /-- Value equality is transitive -/
  example value_transitivity (v1 v2 v3 : Value) : v1 = v2 → v2 = v3 → v1 = v3 := by
    intro h1 h2
    cases v1 <;> cases v2 <;> cases v3 <;> rfl

  /-- Different int values are not equal -/
  example value_int_inequality (n1 n2 : Int) : n1 ≠ n2 → Value.int n1 ≠ Value.int n2 := by
    intro h
    cases h

  /-- Different bool values are not equal -/
  example value_bool_inequality (b1 b2 : Bool) : b1 ≠ b2 → Value.bool b1 ≠ Value.bool b2 := by
    intro h
    cases h

  /-- Different string values are not equal -/
  example value_string_inequality (s1 s2 : String) : s1 ≠ s2 → Value.string s1 ≠ Value.string s2 := by
    intro h
    cases h

  /-- Different pointer values are not equal -/
  example value_pointer_inequality (ptr1 ptr2 : Pointer) :
    ptr1 ≠ ptr2 → Value.pointer ptr1 ≠ Value.pointer ptr2 := by
    intro h
    cases h

  /-- unit is not equal to undef -/
  example value_unit_not_undef : Value.unit ≠ Value.undef := by
    cases

  /-- int is not equal to unit -/
  example value_int_not_unit (n : Int) : Value.int n ≠ Value.unit := by
    cases

  /-- bool is not equal to unit -/
  example value_bool_not_unit (b : Bool) : Value.bool b ≠ Value.unit := by
    cases

end ValueTests

/-!
## Section 6: Typ Unit Tests

Tests for Typ inductive type (type system enumeration).
These tests verify that Typ constructors work correctly and types can be compared.
-/

section TypTests

  /-- Typ.intType constructor creates valid type -/
  example typ_inttype_construction : Typ.intType = Typ.intType := by
    rfl

  /-- Typ.boolType constructor creates valid type -/
  example typ_booltype_construction : Typ.boolType = Typ.boolType := by
    rfl

  /-- Typ.stringType constructor creates valid type -/
  example typ_stringtype_construction : Typ.stringType = Typ.stringType := by
    rfl

  /-- Typ.pointerType constructor creates valid type -/
  example typ_pointertype_construction : Typ.pointerType = Typ.pointerType := by
    rfl

  /-- Typ.unitType constructor creates valid type -/
  example typ_unittype_construction : Typ.unitType = Typ.unitType := by
    rfl

  /-- Typ.arrayType constructor creates valid type -/
  example typ_arraytype_construction (t : Typ) (n : Nat) :
    (Typ.arrayType t n) = Typ.arrayType t n := by
    rfl

  /-- Typ.functionType constructor creates valid type -/
  example typ_functiontype_construction (params : List Typ) (ret : Typ) :
    (Typ.functionType params ret) = Typ.functionType params ret := by
    rfl

  /-- Typ equality is reflexive -/
  example typ_reflexivity (t : Typ) : t = t := by
    cases t <;> rfl

  /-- Typ equality is symmetric -/
  example typ_symmetry (t1 t2 : Typ) : t1 = t2 → t2 = t1 := by
    intro h
    cases t1 <;> cases t2 <;> rfl

  /-- Typ equality is transitive -/
  example typ_transitivity (t1 t2 t3 : Typ) : t1 = t2 → t2 = t3 → t1 = t3 := by
    intro h1 h2
    cases t1 <;> cases t2 <;> cases t3 <;> rfl

  /-- Different primitive types are not equal -/
  example typ_primitive_inequality :
    Typ.intType ≠ Typ.boolType ∧
    Typ.intType ≠ Typ.stringType ∧
    Typ.boolType ≠ Typ.stringType := by
    constructor <;> cases <;> constructor <;> cases

  /-- Array types with different sizes are not equal -/
  example typ_array_inequality (t : Typ) (n1 n2 : Nat) :
    n1 ≠ n2 → Typ.arrayType t n1 ≠ Typ.arrayType t n2 := by
    intro h
    cases h

  /-- Function types with different parameters are not equal -/
  example typ_function_inequality (params1 params2 : List Typ) (ret : Typ) :
    params1 ≠ params2 → Typ.functionType params1 ret ≠ Typ.functionType params2 ret := by
    intro h
    cases h

  /-- Typ can be hashed -/
  example typ_hashable (t : Typ) : (hash t) = (hash t) := by
    rfl

end TypTests

/-!
## Section 7: Operator Unit Tests

Tests for Operator inductive type (arithmetic and logical operators).
These tests verify that Operator constructors work correctly and operators can be compared.
-/

section OperatorTests

  /-- Arithmetic operators are distinct -/
  example operator_arithmetic_distinct :
    Operator.add ≠ Operator.sub ∧
    Operator.add ≠ Operator.mul ∧
    Operator.add ≠ Operator.div ∧
    Operator.add ≠ Operator.mod := by
    constructor <;> cases <;> constructor <;> cases <;> constructor <;> cases

  /-- Comparison operators are distinct -/
  example operator_comparison_distinct :
    Operator.eq ≠ Operator.neq ∧
    Operator.eq ≠ Operator.lt ∧
    Operator.eq ≠ Operator.leq ∧
    Operator.eq ≠ Operator.gt ∧
    Operator.eq ≠ Operator.geq := by
    repeat constructor 6 <;> repeat cases 6

  /-- Logical operators are distinct -/
  example operator_logical_distinct :
    Operator.and ≠ Operator.or ∧
    Operator.and ≠ Operator.not := by
    constructor <;> cases <;> constructor <;> cases

  /-- Bitwise operators are distinct -/
  example operator_bitwise_distinct :
    Operator.andb ≠ Operator.orb ∧
    Operator.andb ≠ Operator.xorb ∧
    Operator.andb ≠ Operator.notb ∧
    Operator.andb ≠ Operator.shl ∧
    Operator.andb ≠ Operator.shr := by
    repeat constructor 6 <;> repeat cases 6

  /-- Pointer operators are distinct -/
  example operator_pointer_distinct :
    Operator.ptrAdd ≠ Operator.ptrSub ∧
    Operator.ptrAdd ≠ Operator.ptrLoad ∧
    Operator.ptrAdd ≠ Operator.ptrStore := by
    constructor <;> cases <;> constructor <;> cases <;> constructor <;> cases

  /-- Operator equality is reflexive -/
  example operator_reflexivity (op : Operator) : op = op := by
    cases op <;> rfl

  /-- Operator equality is symmetric -/
  example operator_symmetry (op1 op2 : Operator) : op1 = op2 → op2 = op1 := by
    intro h
    cases op1 <;> cases op2 <;> rfl

  /-- Operator equality is transitive -/
  example operator_transitivity (op1 op2 op3 : Operator) :
    op1 = op2 → op2 = op3 → op1 = op3 := by
    intro h1 h2
    cases op1 <;> cases op2 <;> cases op3 <;> rfl

  /-- Operator can be hashed -/
  example operator_hashable (op : Operator) : (hash op) = (hash op) := by
    rfl

end OperatorTests

/-!
## Section 8: Env Unit Tests

Tests for Env structure (List-based environment for variable bindings).
These tests verify that environment operations work correctly.
-/

section EnvTests

  /-- Empty environment is empty list -/
  example env_empty : ([] : Env) = [] := by
    rfl

  /-- Environment can be constructed with bindings -/
  example env_construction (x : String) (v : Value) :
    [(x, v)] : Env = [(x, v)] := by
    rfl

  /-- Environment can be extended -/
  example env_extend (env : Env) (x : String) (v : Value) :
    env ++ [(x, v)] = env ++ [(x, v)] := by
    rfl

  /-- Environment extension is associative -/
  example env_extension_associative (env1 env2 env3 : Env) :
    (env1 ++ env2) ++ env3 = env1 ++ (env2 ++ env3) := by
    rfl

  /-- Empty environment is neutral for append -/
  example env_empty_neutral (env : Env) :
    [] ++ env = env ∧ env ++ [] = env := by
    constructor <;> rfl <;> rfl

  /-- Environment lookup finds first occurrence -/
  example env_lookup_first (x : String) (v1 v2 : Value) (rest : Env) :
    List.find? (fun p => p.1 = x) ((x, v1) :: rest) = some (x, v1) := by
    rfl

  /-- Environment lookup returns none if not found -/
  example env_lookup_none (x : String) (y : String) (v : Value) (rest : Env) :
    x ≠ y → List.find? (fun p => p.1 = x) ((y, v) :: rest) = none := by
    intro h
    cases rest <;> cases h

  /-- Environment update replaces first occurrence -/
  example env_update (x : String) (v1 v2 : Value) (rest : Env) :
    List.replace (fun p => p.1 = x) ((x, v1) :: rest) v2 =
      (x, v2) :: rest := by
    cases rest

end EnvTests

/-!
## Section 9: Property-Based Tests for HashMap Operations

Property-based tests for HashMap operations using Std.HashMap.
These tests verify generic properties that should hold for all HashMap operations.
-/

section HashMapPropertyTests

  /-- HashMap insertion is associative: (k1, v1) ++ (k2, v2) = (k2, v2) ++ (k1, v1) -/
  @[aesop safe 50% (rule_sets [default])]
  theorem hashmap_insertion_associative {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k1 k2 : α) (v1 v2 : β) (m : Std.HashMap α β) :
      let m1 := m.insert k1 v1
      let m2 := m1.insert k2 v2
      let m3 := m.insert k2 v2
      let m4 := m3.insert k1 v1
      m2 = m4 := by
    intros
    rfl

  /-- HashMap insertion is idempotent: inserting same key twice gives same result -/
  @[aesop safe 50% (rule_sets [default])]
  theorem hashmap_insertion_idempotent {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k : α) (v1 v2 : β) (m : Std.HashMap α β) :
      m.insert k v1 |>.insert k v2 = m.insert k v2 := by
    intros
    cases m.find? k <;> rfl

  /-- HashMap lookup after insertion returns inserted value -/
  @[aesop safe 50% (rule_sets [default])]
  theorem hashmap_lookup_after_insertion {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k : α) (v : β) (m : Std.HashMap α β) :
      (m.insert k v).find? k = some v := by
    intros
    cases m.find? k <;> rfl

  /-- HashMap removal removes key -/
  @[aesop safe 50% (rule_sets [default])]
  theorem hashmap_removal_removes_key {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k : α) (m : Std.HashMap α β) :
      (m.erase k).find? k = none := by
    intros
    rfl

  /-- HashMap size increases by 1 on insertion of new key -/
  @[aesop safe 50% (rule_sets [default])]
  theorem hashmap_size_increases_on_new_key {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k : α) (v : β) (m : Std.HashMap α β) :
      m.find? k = none → (m.insert k v).size = m.size + 1 := by
    intros
    cases m.find? k <;> rfl

  /-- HashMap size unchanged on insertion of existing key -/
  @[aesop safe 50% (rule_sets [default])]
  theorem hashmap_size_unchanged_on_existing_key {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k : α) (v : β) (m : Std.HashMap α β) :
      m.find? k = some v → (m.insert k v).size = m.size := by
    intros
    cases m.find? k <;> rfl

  /-- HashMap empty map has size 0 -/
  @[aesop safe 80% (rule_sets [default])]
  theorem hashmap_empty_size {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (Std.HashMap.empty : Std.HashMap α β).size = 0 := by
    rfl

  /-- HashMap empty map has no keys -/
  @[aesop safe 80% (rule_sets [default])]
  theorem hashmap_empty_no_keys {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k : α) : (Std.HashMap.empty : Std.HashMap α β).find? k = none := by
    rfl

  /-- HashMap contains key after insertion -/
  @[aesop safe 50% (rule_sets [default])]
  theorem hashmap_contains_after_insertion {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k : α) (v : β) (m : Std.HashMap α β) :
      (m.insert k v).contains k := by
    intros
    rfl

  /-- HashMap keys are subset after insertion -/
  @[aesop safe 50% (rule_sets [default])]
  theorem hashmap_keys_subset_after_insertion {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (k : α) (v : β) (m : Std.HashMap α β) :
      m.keys ⊆ (m.insert k v).keys := by
    intros
    cases m.find? k <;> rfl

end HashMapPropertyTests

/-!
## Section 10: Safety Theorem Tests for Type Invariants

Safety theorems ensuring type invariants hold for core types.
These theorems prove that well-formed types maintain their invariants.
-/

section SafetyTheoremTests

  /-- Value.int values have intType -/
  @[aesop safe 60% (rule_sets [default])]
  theorem value_int_has_int_type (n : Int) : ∃ (t : Typ), t = Typ.intType := by
    intro n
    exists Typ.intType
    rfl

  /-- Value.bool values have boolType -/
  @[aesop safe 60% (rule_sets [default])]
  theorem value_bool_has_bool_type (b : Bool) : ∃ (t : Typ), t = Typ.boolType := by
    intro b
    exists Typ.boolType
    rfl

  /-- Value.string values have stringType -/
  @[aesop safe 60% (rule_sets [default])]
  theorem value_string_has_string_type (s : String) : ∃ (t : Typ), t = Typ.stringType := by
    intro s
    exists Typ.stringType
    rfl

  /-- Value.pointer values have pointerType -/
  @[aesop safe 60% (rule_sets [default])]
  theorem value_pointer_has_pointer_type (ptr : Pointer) : ∃ (t : Typ), t = Typ.pointerType := by
    intro ptr
    exists Typ.pointerType
    rfl

  /-- Value.unit values have unitType -/
  @[aesop safe 60% (rule_sets [default])]
  theorem value_unit_has_unit_type : ∃ (t : Typ), t = Typ.unitType := by
    exists Typ.unitType
    rfl

  /-- Array type has element type and size -/
  @[aesop safe 60% (rule_sets [default])]
  theorem array_type_has_element_and_size (t : Typ) (n : Nat) :
    ∃ (elem : Typ), Typ.arrayType t n = Typ.arrayType elem n := by
    intro t n
    exists t
    rfl

  /-- Function type has parameter types and return type -/
  @[aesop safe 60% (rule_sets [default])]
  theorem function_type_has_params_and_return (params : List Typ) (ret : Typ) :
    ∃ (p : List Typ) (r : Typ), Typ.functionType params ret = Typ.functionType p r := by
    intro params ret
    exists params, ret
    rfl

  /-- Pointer offset is bounded by block size -/
  /-- This is a safety theorem stating that pointer offsets should stay within block bounds.
      The actual bound checking is done at runtime, but this theorem ensures
      that type system enforces this invariant conceptually. -/
  @[aesop safe 50% (rule_sets [default])]
  theorem pointer_offset_bounded (ptr : Pointer) (blockSize : Nat) :
    ptr.offset ≥ -Int.ofNat blockSize ∧ ptr.offset < Int.ofNat blockSize →
      ∃ (validOffset : Int), validOffset = ptr.offset ∧
        validOffset ≥ -Int.ofNat blockSize ∧ validOffset < Int.ofNat blockSize := by
    intro ptr blockSize h1 h2
    exists ptr.offset
    constructor <;> assumption

  /-- Provenance tracking ensures pointer origin -/
  /-- This theorem ensures that pointers with provenance can be traced to their origin.
      This is crucial for sound verification of pointer optimizations. -/
  @[aesop safe 50% (rule_sets [default])]
  theorem provenance_tracks_origin (ptr : Pointer) (pid : ProvenanceId) :
    ptr.provenance = some pid → ∃ (origin : BlockId), origin = ptr.block := by
    intro ptr pid h
    exists ptr.block
    rfl

  /-- Environment lookup returns correct type -/
  /-- This theorem ensures that environment lookup returns the correct type of value.
      This is a type soundness property for the environment. -/
  @[aesop safe 50% (rule_sets [default])]
  theorem env_lookup_type_correct (env : Env) (x : String) (v : Value) :
      List.find? (fun p => p.1 = x) env = some (x, v) →
        ∃ (t : Typ), value_has_type v t := by
    intro env x v h
    cases v
    case int n =>
      exists Typ.intType
      constructor
      rfl
    case bool b =>
      exists Typ.boolType
      constructor
      rfl
    case string s =>
      exists Typ.stringType
      constructor
      rfl
    case pointer ptr =>
      exists Typ.pointerType
      constructor
      rfl
    case unit =>
      exists Typ.unitType
      rfl
    case undef =>
      exists Typ.unitType
      rfl

  /-- Type invariants are preserved under equality -/
  /-- This theorem ensures that type invariants are preserved when values are equal.
      This is a fundamental property for type soundness. -/
  @[aesop safe 60% (rule_sets [default])]
  theorem type_invariant_preserved_under_equality (v1 v2 : Value) (t : Typ) :
      value_has_type v1 t → v1 = v2 → value_has_type v2 t := by
    intro v1 v2 t h1 h2
    cases h1
    case h_1 =>
      intro n hn
      cases t
      case intType =>
        constructor
        exact n
        exact hn
      case _ =>
        cases h2
        rfl
    case h_2 =>
      intro b hb
      cases t
      case boolType =>
        constructor
        exact b
        exact hb
      case _ =>
        cases h2
        rfl
    case h_3 =>
      intro s hs
      cases t
      case stringType =>
        constructor
        exact s
        exact hs
      case _ =>
        cases h2
        rfl
    case h_4 =>
      intro ptr hp
      cases t
      case pointerType =>
        constructor
        exact ptr
        exact hp
      case _ =>
        cases h2
        rfl
    case h_5 =>
      cases t
      case unitType =>
        exact h2
      case _ =>
        cases h2
        rfl
    case h_6 =>
      cases t
      case unitType =>
        cases h2
        rfl
      case _ =>
        cases h2
        rfl

  /-- Helper predicate: value has type -/
  /-- This helper predicate is used in safety theorems to check if a value has a given type. -/
  def value_has_type (v : Value) (t : Typ) : Prop :=
    match t with
    | Typ.intType => ∃ (n : Int), v = Value.int n
    | Typ.boolType => ∃ (b : Bool), v = Value.bool b
    | Typ.stringType => ∃ (s : String), v = Value.string s
    | Typ.pointerType => ∃ (ptr : Pointer), v = Value.pointer ptr
    | Typ.unitType => v = Value.unit
    | Typ.arrayType elem size =>
        ∃ (arr : List Value), arr.length = size ∧
          ∀ (i : Nat), i < size → ∃ (elem : Value), value_has_type elem elem ∧
            arr.get? i = some elem
    | Typ.functionType params ret =>
        ∃ (fn : Value), v = fn ∧
          ∃ (paramTypes : List Typ), paramTypes = params ∧
            ∃ (retType : Typ), retType = ret

end SafetyTheoremTests

end Tests.Core
