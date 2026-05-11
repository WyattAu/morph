# DESIGN-003: Proof Structure Design

**Design ID:** DESIGN-003  
**Title:** Proof Structure Design  
**Status:** Draft  
**Created:** 2026-01-30  
**Related ADRs:** ADR-006, ADR-003, ADR-001  
**Related Requirements:** REQ-001 through REQ-007

---

## Purpose and Scope

This design document defines technical specifications for proof structure in the Morph language Lean 4 formal verification project. It specifies theorem naming conventions, proof organization patterns, lemma hierarchy and dependency patterns, and proof automation strategies.

The scope includes:
- Theorem and lemma naming conventions
- Proof organization within Lemmas.lean files
- Lemma hierarchy and dependency patterns
- Proof automation using aesop and batteries
- Common proof patterns and tactics
- Proof documentation standards

---

## Technical Specifications

### Theorem Naming Conventions

#### Theorem Names (camelCase)

All theorem names must use camelCase and be descriptive:

```lean
-- Good
theorem allocationCreatesUniqueBlock (size : Nat) : Prop := ...
theorem memoryDeallocationFreesBlock (address : Nat) : Prop := ...
theorem typePreservation (e : Expr) (Γ : TypeEnv) (τ : Type) : Prop := ...
theorem progress (e : Expr) (Γ : TypeEnv) : Prop := ...

-- Bad
theorem alloc_block (size : Nat) : Prop := ...
theorem dealloc_block (address : Nat) : Prop := ...
theorem type_pres (e : Expr) (Γ : TypeEnv) (τ : Type) : Prop := ...
theorem prog (e : Expr) (Γ : TypeEnv) : Prop := ...
```

#### Lemma Names (camelCase)

Lemma names must use camelCase and indicate the property being proved:

```lean
-- Good
lemma allocationPreservesSize (size : Nat) (state : MemoryState) : Prop := ...
lemma deallocationPreservesOtherBlocks (address : Nat) (state : MemoryState) : Prop := ...
lemma substitutionLemma (e : Expr) (x : String) (v : Expr) : Prop := ...
lemma weakeningLemma (Γ : TypeEnv) (x : String) (τ : Type) : Prop := ...

-- Bad
lemma alloc_size (size : Nat) (state : MemoryState) : Prop := ...
lemma dealloc_other (address : Nat) (state : MemoryState) : Prop := ...
lemma sub_lemma (e : Expr) (x : String) (v : Expr) : Prop := ...
lemma weak_lemma (Γ : TypeEnv) (x : String) (τ : Type) : Prop := ...
```

#### Naming Patterns

Use consistent naming patterns for related theorems:

```lean
-- Allocation theorems
theorem allocationCreatesUniqueBlock : Prop := ...
theorem allocationPreservesWellFormedness : Prop := ...
theorem allocationDoesNotOverlap : Prop := ...

-- Deallocation theorems
theorem deallocationFreesBlock : Prop := ...
theorem deallocationPreservesOtherBlocks : Prop := ...
theorem deallocationMaintainsWellFormedness : Prop := ...

-- Type system theorems
theorem typePreservation : Prop := ...
theorem typeUniqueness : Prop := ...
theorem typeProgress : Prop := ...
```

---

## Proof Organization Patterns

### Section Organization

Lemmas.lean files should be organized into sections:

```lean
namespace Morph.Specs.Memory.MemoryModel

/-! ## Basic Properties
-/

lemma allocationPreservesSize : Prop := ...

/-! ## Allocation Properties
-/

theorem allocationCreatesUniqueBlock : Prop := ...
theorem allocationDoesNotOverlap : Prop := ...

/-! ## Deallocation Properties
-/

theorem deallocationFreesBlock : Prop := ...
theorem deallocationPreservesOtherBlocks : Prop := ...

/-! ## Helper Theorems
-/

theorem findBlockByAddress : Prop := ...

end Morph.Specs.Memory.MemoryModel
```

### Proof Structure Template

Each proof should follow this structure:

```lean
/-- Theorem statement with documentation.
    
    **Purpose:** Brief description of what the theorem proves
    
    **Proof Strategy:** High-level description of proof approach
    
    **Dependencies:** List of lemmas/theorems used
-/
theorem theoremName (parameters) : Prop := by
  -- Introduce variables
  intro ...
  
  -- Apply key lemmas
  apply ...
  
  -- Discharge remaining goals
  ...
```

### Simple Proof Pattern

For straightforward proofs, use direct tactics:

```lean
/-- Lemma: Allocation preserves the size of existing blocks. -/
lemma allocationPreservesSize (size : Nat) (state : MemoryState) :
  let (newState, _) := allocate size state
  ∀ b ∈ state, ∃ b' ∈ newState, b.address = b.address ∧ b'.size = b.size := by
  intro b b_in_state
  use b
  constructor
  rfl
  rfl
```

### Structured Proof Pattern

For complex proofs, use structured proof with `have` statements:

```lean
/-- Theorem: Allocation creates a unique block.
    
    **Proof Strategy:** 
    1. Assume allocation produces a block at address a
    2. Show that no other block in new state has address a
    3. Use the definition of allocate to show uniqueness
-/
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) :
  let (newState, address) := allocate size state
  ∀ b ∈ newState, b.address = address → b.allocated := by
  intro b b_in_new_state b_address_eq
  have h1 : b.address = address := b_address_eq
  have h2 : ∃ b0 ∈ state, b0.address = address := by
    sorry
  sorry
```

### Induction Proof Pattern

For proofs by induction, use explicit induction:

```lean
/-- Lemma: Expression size is non-negative. -/
lemma exprSizeNonNegative (e : Expr) : e.size ≥ 0 := by
  induction e with
  | const n =>
    rw [Expr.size]
    exact Nat.zero_le n
  | var x =>
    rw [Expr.size]
    exact Nat.zero_le 1
  | add e1 e2 ih1 ih2 =>
    rw [Expr.size]
    apply Nat.add_le_add_right
    exact Nat.le_trans ih1 (Nat.zero_le (e2.size + 1))
  | mul e1 e2 ih1 ih2 =>
    rw [Expr.size]
    apply Nat.add_le_add_right
    exact Nat.le_trans ih1 (Nat.zero_le (e2.size + 1))
```

---

## Lemma Hierarchy and Dependency Patterns

### Lemma Dependency Graph

Lemmas should be organized in a dependency hierarchy:

```
Level 1: Basic Helper Lemmas
├── findBlockByAddress
├── blockExistsAtAddress
└── isAllocatedBlock

Level 2: Property Lemmas
├── allocationPreservesSize
├── deallocationPreservesOtherBlocks
└── allocationDoesNotOverlap

Level 3: Main Theorems
├── allocationCreatesUniqueBlock
├── deallocationFreesBlock
└── memorySafety
```

### Helper Lemmas Pattern

Helper lemmas should be defined before they are used:

```lean
/-! ## Helper Theorems
-/

/-- Helper: Find a block by address in memory state. -/
theorem findBlockByAddress (address : Nat) (state : MemoryState) :
  (∃ b ∈ state, b.address = address) ↔
    (state.find? (fun b => b.address = address)).isSome := by
  sorry

/-- Helper: Check if a block is allocated. -/
theorem isAllocatedBlock (block : MemoryBlock) :
  block.allocated ↔ ∃ b ∈ [block], b.allocated := by
  sorry

/-! ## Property Lemmas
-/

/-- Lemma: Allocation preserves block sizes (uses helper lemmas). -/
lemma allocationPreservesSize (size : Nat) (state : MemoryState) :
  let (newState, _) := allocate size state
  ∀ b ∈ state, ∃ b' ∈ newState, b.address = b.address ∧ b'.size = b.size := by
  intro b b_in_state
  have h := findBlockByAddress b.address state
  sorry
```

### Main Theorems Pattern

Main theorems should use helper lemmas and property lemmas:

```lean
/-! ## Main Theorems
-/

/-- Theorem: Allocation creates a unique block.
    
    This theorem states that allocating a new block always produces
    a block with a unique address that does not conflict with
    existing blocks.
    
    **Proof Strategy:**
    1. Use `allocationDoesNotOverlap` to show no overlap
    2. Use `findBlockByAddress` to locate the new block
    3. Conclude uniqueness
-/
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) :
  let (newState, address) := allocate size state
  ∀ b ∈ newState, b.address = address → b.allocated := by
  intro b b_in_new_state b_address_eq
  have h1 := allocationDoesNotOverlap size state
  have h2 := findBlockByAddress address newState
  sorry
```

---

## Proof Automation Strategies

### Aesop Usage

Use aesop for automated proof search where appropriate:

```lean
import Aesop

/-- Lemma: Simple property provable by automation. -/
lemma simpleProperty (n : Nat) : n + 0 = n := by
  aesop

/-- Lemma: Property requiring specific configuration. -/
lemma configuredProperty (n m : Nat) : n + m = m + n := by
  aesop (config := { transparency := .default })
```

### Batteries Usage

Use batteries for additional tactics and lemmas:

```lean
import Batteries

/-- Lemma: Using batteries lemmas. -/
lemma listProperty (l : List Nat) : l.reverse.reverse = l := by
  rw [List.reverse_reverse]
```

### Custom Automation

Define custom tactics for domain-specific patterns:

```lean
/-- Custom tactic for memory allocation proofs. -/
syntax "solve_allocation" : tactic

macro_rules
  | `(tactic| solve_allocation) => `(tactic|
    (repeat (first | apply allocationCreatesUniqueBlock
                  | apply allocationDoesNotOverlap
                  | aesop))

/-- Lemma: Using custom tactic. -/
lemma allocationProperty (size : Nat) (state : MemoryState) : Prop := by
  solve_allocation
```

---

## Common Proof Patterns

### Trivial Proof Pattern

For trivially true statements:

```lean
/-- Lemma: Reflexivity of equality. -/
lemma equalityReflexive (a : Nat) : a = a := by
  rfl

/-- Lemma: True proposition. -/
lemma trueProposition : True := by
  trivial
```

### Contradiction Proof Pattern

For proofs by contradiction:

```lean
/-- Lemma: No block can be both allocated and deallocated. -/
lemma notAllocatedAndDeallocated (block : MemoryBlock) :
  ¬(block.allocated ∧ ¬block.allocated) := by
  intro h
  cases h with
  | intro h1 h2 =>
    apply h1
    exact h2
```

### Case Analysis Proof Pattern

For proofs by case analysis:

```lean
/-- Lemma: Block allocation status is boolean. -/
lemma allocationIsBoolean (block : MemoryBlock) :
  block.allocated = true ∨ block.allocated = false := by
  cases block.allocated with
  | true =>
    left
    rfl
  | false =>
    right
    rfl
```

### Induction Proof Pattern

For proofs by induction on data structures:

```lean
/-- Lemma: All expressions have non-negative size. -/
lemma exprSizeNonNegative (e : Expr) : e.size ≥ 0 := by
  induction e with
  | const n =>
    rw [Expr.size]
    exact Nat.zero_le n
  | var x =>
    rw [Expr.size]
    exact Nat.zero_le 1
  | add e1 e2 ih1 ih2 =>
    rw [Expr.size]
    apply Nat.add_le_add_right
    exact Nat.le_trans ih1 (Nat.zero_le (e2.size + 1))
  | mul e1 e2 ih1 ih2 =>
    rw [Expr.size]
    apply Nat.add_le_add_right
    exact Nat.le_trans ih1 (Nat.zero_le (e2.size + 1))
```

---

## Proof Documentation Standards

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

### Inline Proof Comments

Non-trivial proof steps should be commented:

```lean
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) :
  let (newState, address) := allocate size state
  ∀ b ∈ newState, b.address = address → b.allocated := by
  intro b b_in_new_state b_address_eq
  -- Use the definition of allocate to show the new block is allocated
  have h := allocationDoesNotOverlap size state
  -- Show that b must be the newly allocated block
  sorry
```

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Using `sorry` in Proofs

**Incorrect (STRICTLY FORBIDDEN):**
```lean
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) : Prop := by
  sorry
```

**Correct:**
```lean
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) : Prop := by
  -- Complete proof implementation
  ...
```

### Anti-Pattern 2: Missing Documentation

**Incorrect:**
```lean
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) : Prop := by
  ...
```

**Correct:**
```lean
/-- Theorem: Allocation creates a unique block.
    
    This theorem states that allocating a new block always produces
    a block with a unique address that does not conflict with
    existing blocks.
-/
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) : Prop := by
  ...
```

### Anti-Pattern 3: Overly Complex Proofs Without Structure

**Incorrect:**
```lean
theorem complexProperty (n m : Nat) : Prop := by
  -- Long, unstructured proof
  ...
  ...
  ...
```

**Correct:**
```lean
theorem complexProperty (n m : Nat) : Prop := by
  have h1 := lemma1 n m
  have h2 := lemma2 n m
  have h3 := lemma3 n m
  -- Use helper lemmas to structure the proof
  sorry
```

### Anti-Pattern 4: Using Automation Inappropriately

**Incorrect:**
```lean
theorem complexProperty (n m : Nat) : Prop := by
  aesop  -- May not work for complex proofs
```

**Correct:**
```lean
theorem complexProperty (n m : Nat) : Prop := by
  -- Structured proof with targeted automation
  have h1 := lemma1 n m
  aesop  -- Use automation for remaining simple goals
```

### Anti-Pattern 5: Commented-Out Proof Attempts

**Incorrect:**
```lean
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) : Prop := by
  -- Old approach that didn't work
  -- intro b b_in_new_state b_address_eq
  -- have h := allocationDoesNotOverlap size state
  -- sorry
  
  -- New approach
  sorry
```

**Correct:**
```lean
theorem allocationCreatesUniqueBlock (size : Nat) (state : MemoryState) : Prop := by
  -- Only the current approach
  sorry
```

---

## Verification Checklist

For each proof, verify:

- [ ] Theorem/lemma name uses camelCase
- [ ] Theorem/lemma has complete documentation
- [ ] Proof is complete (no `sorry` placeholders; 1 known exception in Preservation.lean)
- [ ] Proof follows a clear structure
- [ ] Non-trivial steps are commented
- [ ] Dependencies are documented
- [ ] Automation is used appropriately
- [ ] No commented-out proof attempts
- [ ] Proof is in the correct file (Lemmas.lean)
- [ ] Proof imports only from Spec.lean files

---

## References

- [ADR-006: Complete Proof Requirement](../02_adrs/ADR-006-complete-proof-requirement.md)
- [ADR-003: Lean 4 with mathlib4](../02_adrs/ADR-003-lean4-mathlib4.md)
- [ADR-001: Three-File Module Pattern](../02_adrs/ADR-001-three-file-module-pattern.md)
- [Coding Standards](../01_standards/coding_standards.md)
- [REQ-001: Core Foundation Requirements](../04_future_state/reqs/REQ-001-core-foundation.md)
- [Lean 4 Documentation on Proofs](https://leanprover.github.io/lean4/doc/proofs.html)
- [aesop Documentation](https://github.com/JLimperg/aesop)
