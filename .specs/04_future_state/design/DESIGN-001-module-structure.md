# DESIGN-001: Module Structure Design

**Design ID:** DESIGN-001  
**Title:** Module Structure Design  
**Status:** Draft  
**Created:** 2026-01-30  
**Related ADRs:** ADR-001, ADR-005  
**Related Requirements:** REQ-001 through REQ-007

---

## Purpose and Scope

This design document defines the technical specifications for module structure in the Morph language Lean 4 formal verification project. It specifies the three-file module pattern, file-level contracts, import patterns, and organization conventions that must be followed across all specification modules.

The scope includes:
- All specification modules in `Morph/Specs/`
- Domain-based organization structure
- File-level interfaces and contracts
- Import dependency patterns
- Module naming conventions

---

## Technical Specifications

### Module Directory Structure

Each specification module must follow this directory structure:

```
Morph/Specs/
└── [DomainName]/
    └── [ModuleName]/
        ├── Spec.lean
        ├── Lemmas.lean
        └── Examples.lean
```

**Example:**
```
Morph/Specs/Memory/
└── MemoryModel/
    ├── Spec.lean
    ├── Lemmas.lean
    └── Examples.lean
```

### Domain Classification

Modules are organized into semantic domains as defined in ADR-005:

| Domain | Purpose | Example Modules |
|--------|---------|----------------|
| Core | Language foundations | MorphLanguage, LexicalStructureSyntax, ScopingLambdaCalculus |
| Memory | Memory models and semantics | MemoryModel, MemoryAffineLogic, MemoryAcyclicity |
| Concurrency | Process calculi and scheduling | ConcurrencyProcessAlgebra, LayeredConcurrency, SchedulerRandomizedStealing |
| Security | Security properties and access control | SecurityFlow, SecurityOCap, InfrastructureSafetyContracts |
| Compilation | Compiler transformations | BackendTiling, DualOptimization, DialectProjection |
| Algebra | Algebraic structures | AbiAlignmentAlgebra, AbiDataRefinement, BuildLattice, Maths |
| Logic | Logical foundations | LicenseDeonticLogic, MonadicEffect |
| Infrastructure | Module systems and linking | ModuleSystem, ModuleExistential, LinkerLogic |
| Execution | Operational semantics | ExecutionModel, DependencySat |
| Storage | Data structures | StorageDAWG |
| Licensing | Licensing and compliance | Licensing, Financial |
| Meta | Meta-specifications | GLOSSARY, README, ASTGraph, CommonTypes |

---

## File-Level Contracts

### Spec.lean Contract

**Purpose:** Contains core type definitions, axioms, and theorem statements (declarations only).

**Required Content:**
1. File header with copyright and license
2. Module-level documentation block
3. Namespace declaration
4. Import statements (dependencies only)
5. Type definitions (structures, inductive types, classes)
6. Function signatures and axioms
7. Theorem statements (declarations, no proofs)
8. Section organization comments

**Prohibited Content:**
- Proof implementations
- Example code
- Test cases
- Commented-out code blocks
- `sorry` placeholders

**Import Rules:**
- Import from standard library (Std, Lean)
- Import from project core modules (Morph.Core, Morph.Syntax, etc.)
- Import from third-party libraries (Mathlib, Aesop, Batteries)
- Import from CommonTypes if needed
- **Never** import from Lemmas.lean or Examples.lean

**Example Structure:**
```lean
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

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

import Std
import Lean

import Morph.Core
import Morph.Syntax

import Mathlib.Data.Nat.Basic
import Batteries.Data.List.Basic

import Morph.Specs.CommonTypes

namespace Morph.Specs.Memory.MemoryModel

/-! ## Type Definitions
-/

/-- A memory block with its address, size, and allocation status. -/
structure MemoryBlock where
  address : Nat
  size : Nat
  allocated : Bool
  deriving Repr, BEq

/-- The memory state as a map from addresses to blocks. -/
abbrev MemoryState := Array MemoryBlock

/-! ## Core Operations
-/

/-- Allocate a new memory block of the given size.
    
    **Parameters:**
    - `size`: The size of the block to allocate in bytes
    
    **Returns:** The new memory state and the address of the allocated block
    
    **Invariant:** The allocated block has a unique address and is marked as allocated
-/
def allocate (size : Nat) (state : MemoryState) : MemoryState × Nat :=
  sorry

/-- Deallocate the memory block at the given address.
    
    **Parameters:**
    - `address`: The address of the block to deallocate
    
    **Returns:** The new memory state
    
    **Invariant:** The block at the address is marked as deallocated
-/
def deallocate (address : Nat) (state : MemoryState) : MemoryState :=
  sorry

/-! ## Specification Theorems
-/

/-- SPEC-MEM-001: Memory allocation creates a unique block.
    
    This theorem states that allocating a new block always produces
    a block with a unique address that does not conflict with
    existing blocks.
-/
theorem allocation_creates_unique_block (size : Nat) (state : MemoryState) :
  let (newState, address) := allocate size state
  ∀ b ∈ newState, b.address = address → b.allocated := by
  sorry

/-- SPEC-MEM-002: Memory deallocation frees the block.
    
    This theorem states that deallocating a block marks it as
    deallocated while preserving other blocks.
-/
theorem deallocation_frees_block (address : Nat) (state : MemoryState) :
  let newState := deallocate address state
  ∃ b ∈ state, b.address = address ∧ b.allocated = true →
    ∃ b' ∈ newState, b'.address = address ∧ b'.allocated = false := by
  sorry

end Morph.Specs.Memory.MemoryModel
```

### Lemmas.lean Contract

**Purpose:** Contains mathematical lemmas and their complete proofs.

**Required Content:**
1. File header with copyright and license
2. Module-level documentation block
3. Namespace declaration
4. Import from Spec.lean (same module)
5. Import from other modules' Spec.lean files as needed
6. Lemma statements and complete proofs
7. Helper theorems and their proofs
8. Section organization comments

**Prohibited Content:**
- Example code
- Test cases
- Commented-out code blocks
- `sorry` placeholders (strictly forbidden per ADR-006)

**Import Rules:**
- Import from Spec.lean in the same module: `import Morph.Specs.[Domain].[ModuleName].Spec`
- Import from other modules' Spec.lean files when needed
- Import from CommonTypes for shared types
- **Never** import from Examples.lean

**Example Structure:**
```lean
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Lemmas: Memory Model

**Source:** `spec/memory/memory_model.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** John Doe

## Overview

This module contains mathematical lemmas and proofs for the memory model.

## Proof Summary

| Lemma | Proof Method | Status |
|-------|--------------|--------|
| `allocation_preserves_size` | Induction | ✓ |
| `deallocation_preserves_other_blocks` | Case analysis | ✓ |

## Known Issues

None

## TODO

None
-!/

import Morph.Specs.Memory.MemoryModel.Spec
import Mathlib.Data.Array.Basic

namespace Morph.Specs.Memory.MemoryModel

/-! ## Basic Properties
-/

/-- Lemma: Allocation preserves the size of existing blocks.
    
    This lemma proves that when allocating a new block, all existing
    blocks retain their original sizes.
-/
lemma allocation_preserves_size (size : Nat) (state : MemoryState) :
  let (newState, _) := allocate size state
  ∀ b ∈ state, ∃ b' ∈ newState, b.address = b.address ∧ b'.size = b.size := by
  intro b b_in_state
  sorry

/-- Lemma: Deallocation preserves blocks at other addresses.
    
    This lemma proves that deallocating a block at one address
    does not affect blocks at different addresses.
-/
lemma deallocation_preserves_other_blocks (address : Nat) (state : MemoryState) :
  let newState := deallocate address state
  ∀ b ∈ state, b.address ≠ address → ∃ b' ∈ newState, b'.address = b.address := by
  intro b b_in_state b_address_neq
  sorry

/-! ## Helper Theorems
-/

/-- Helper: Find a block by address in memory state.
    
    This helper theorem is used in multiple proofs to locate blocks.
-/
theorem find_block_by_address (address : Nat) (state : MemoryState) :
  (∃ b ∈ state, b.address = address) ↔
    (state.find? (fun b => b.address = address)).isSome := by
  sorry

end Morph.Specs.Memory.MemoryModel
```

### Examples.lean Contract

**Purpose:** Contains concrete examples, usage demonstrations, and test cases.

**Required Content:**
1. File header with copyright and license
2. Module-level documentation block
3. Namespace declaration
4. Import from Spec.lean (same module)
5. Import from Lemmas.lean (same module) as needed
6. Concrete instantiations of types
7. Example computations and expected results
8. Usage demonstrations
9. Test cases using `#eval` or `#reduce`

**Prohibited Content:**
- New type definitions
- New theorem statements
- Commented-out code blocks
- `sorry` placeholders

**Import Rules:**
- Import from Spec.lean in the same module: `import Morph.Specs.[Domain].[ModuleName].Spec`
- Import from Lemmas.lean in the same module when needed
- Import from CommonTypes for shared types
- Import from other modules' Examples.lean files only for cross-module demonstrations

**Example Structure:**
```lean
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Examples: Memory Model

**Source:** `spec/memory/memory_model.md`
**Status:** Complete
**Last Updated:** 2026-01-30
**Verified By:** John Doe

## Overview

This module contains concrete examples and usage demonstrations for the memory model.

## Example Summary

| Example | Description | Status |
|---------|-------------|--------|
| `empty_memory_state` | Empty memory state | ✓ |
| `allocate_16_bytes` | Allocate 16-byte block | ✓ |
| `deallocate_block` | Deallocate a block | ✓ |

## Known Issues

None

## TODO

None
-!/

import Morph.Specs.Memory.MemoryModel.Spec
import Morph.Specs.Memory.MemoryModel.Lemmas

namespace Morph.Specs.Memory.MemoryModel

/-! ## Type Instantiations
-/

/-- Example: An empty memory state. -/
def emptyMemoryState : MemoryState := #[]

/-- Example: A memory block at address 0x1000 with size 16 bytes. -/
def exampleBlock : MemoryBlock :=
  { address := 0x1000, size := 16, allocated := true }

/-- Example: A memory state with one allocated block. -/
def oneBlockState : MemoryState := #[exampleBlock]

/-! ## Operation Examples
-/

/-- Example: Allocate a 16-byte block in empty memory state. -/
#eval allocate 16 emptyMemoryState

/-- Example: Allocate a 32-byte block in existing memory state. -/
#eval allocate 32 oneBlockState

/-- Example: Deallocate the block at address 0x1000. -/
#eval deallocate 0x1000 oneBlockState

/-! ## Verification Examples
-/

/-- Example: Verify that allocation preserves block sizes.
    
    This example demonstrates the use of `allocation_preserves_size` lemma.
-/
#example allocation_preserves_size_example :
  let (newState, _) := allocate 16 oneBlockState
  allocation_preserves_size 16 oneBlockState := by
  sorry

/-- Example: Verify that deallocation preserves other blocks.
    
    This example demonstrates the use of `deallocation_preserves_other_blocks` lemma.
-/
#example deallocation_preserves_other_blocks_example :
  let newState := deallocate 0x1000 oneBlockState
  deallocation_preserves_other_blocks 0x1000 oneBlockState := by
  sorry

end Morph.Specs.Memory.MemoryModel
```

---

## Module Import Patterns

### Import Dependency Hierarchy

```
Level 1: Standard Library
└── Std, Lean

Level 2: Project Core
└── Morph.Core, Morph.Syntax, Morph.Semantics, Morph.Memory

Level 3: Third-Party Libraries
└── Mathlib, Aesop, Batteries

Level 4: Shared Types
└── Morph.Specs.CommonTypes

Level 5: Module Specifications
└── Morph.Specs.[Domain].[ModuleName].Spec

Level 6: Module Lemmas
└── Morph.Specs.[Domain].[ModuleName].Lemmas

Level 7: Module Examples
└── Morph.Specs.[Domain].[ModuleName].Examples
```

### Import Order Convention

Within each file, imports must be organized in this order:

1. Standard library imports (Std, Lean)
2. Project core imports (Morph.Core, Morph.Syntax, etc.)
3. Third-party library imports (Mathlib, Aesop, Batteries)
4. Shared types (Morph.Specs.CommonTypes)
5. Cross-domain imports (other modules' Spec.lean)
6. Local module imports (same module's Spec.lean, Lemmas.lean)

**Example:**
```lean
-- Standard library
import Std
import Lean

-- Project core
import Morph.Core
import Morph.Syntax

-- Third-party
import Mathlib.Data.Nat.Basic
import Aesop
import Batteries.Data.List.Basic

-- Shared types
import Morph.Specs.CommonTypes

-- Cross-domain
import Morph.Specs.Memory.MemoryModel.Spec

-- Local
import Morph.Specs.Execution.ExecutionModel.Spec
```

### Cross-Domain Import Rules

When importing from another domain:
1. Use full import paths (e.g., `import Morph.Specs.Memory.MemoryModel.Spec`)
2. Document the reason for the cross-domain import in a comment
3. Minimize cross-domain dependencies where possible
4. Prefer importing from Spec.lean files, not Lemmas.lean or Examples.lean
5. Consider if a module should be moved if it has many cross-domain dependencies

**Example:**
```lean
-- Import MemoryModel for block allocation in execution semantics
import Morph.Specs.Memory.MemoryModel.Spec
```

---

## Module Naming Conventions

### Domain Names

- Use PascalCase
- Be descriptive and self-explanatory
- Avoid abbreviations unless widely understood

**Examples:**
- `Memory` (not `Mem`)
- `Concurrency` (not `Conc`)
- `Security` (not `Sec`)

### Module Names

- Use PascalCase
- Be descriptive and self-explanatory
- Avoid abbreviations unless widely understood
- Reflect the module's primary purpose

**Examples:**
- `MemoryModel` (not `MemModel`)
- `ConcurrencyProcessAlgebra` (not `CPA`)
- `SecurityFlow` (not `SecFlow`)

### Namespace Declaration

All definitions must be within a namespace following this pattern:

```lean
namespace Morph.Specs.[DomainName].[ModuleName]

-- Content here

end Morph.Specs.[DomainName].[ModuleName]
```

**Example:**
```lean
namespace Morph.Specs.Memory.MemoryModel

-- Content here

end Morph.Specs.Memory.MemoryModel
```

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Mixing Concerns in Single File

**Incorrect:**
```lean
-- Spec.lean with proofs mixed in
theorem allocation_creates_block (size : Nat) : Prop := by
  -- Proof should be in Lemmas.lean
  sorry
```

**Correct:**
```lean
-- Spec.lean: Declaration only
theorem allocation_creates_block (size : Nat) : Prop := by
  sorry

-- Lemmas.lean: Complete proof
theorem allocation_creates_block (size : Nat) : Prop := by
  -- Complete proof implementation
  ...
```

### Anti-Pattern 2: Circular Imports

**Incorrect:**
```lean
-- Spec.lean
import Morph.Specs.Execution.ExecutionModel.Lemmas

-- ExecutionModel/Lemmas.lean
import Morph.Specs.Memory.MemoryModel.Spec
```

**Correct:**
```lean
-- Spec.lean: Only import specifications
import Morph.Specs.Execution.ExecutionModel.Spec

-- Lemmas.lean: Import specifications, not lemmas
import Morph.Specs.Execution.ExecutionModel.Spec
```

### Anti-Pattern 3: Importing Examples in Spec or Lemmas

**Incorrect:**
```lean
-- Spec.lean
import Morph.Specs.Memory.MemoryModel.Examples
```

**Correct:**
```lean
-- Examples.lean: Only Examples.lean imports other Examples
import Morph.Specs.Memory.MemoryModel.Spec
import Morph.Specs.Memory.MemoryModel.Lemmas
```

### Anti-Pattern 4: Missing Namespace Declaration

**Incorrect:**
```lean
-- No namespace declaration
structure MemoryBlock where ...
```

**Correct:**
```lean
namespace Morph.Specs.Memory.MemoryModel

structure MemoryBlock where ...

end Morph.Specs.Memory.MemoryModel
```

### Anti-Pattern 5: Commented-Out Code

**Incorrect:**
```lean
-- Old implementation
-- def allocate_old (size : Nat) : MemoryState := ...

-- New implementation
def allocate (size : Nat) : MemoryState := ...
```

**Correct:**
```lean
-- Only the current implementation
def allocate (size : Nat) : MemoryState := ...
```

---

## Verification Checklist

For each module, verify:

- [ ] All three files exist (Spec.lean, Lemmas.lean, Examples.lean)
- [ ] All files have copyright header
- [ ] All files have module-level documentation
- [ ] All files have namespace declaration
- [ ] Imports follow the import order convention
- [ ] Spec.lean contains only declarations, no proofs
- [ ] Lemmas.lean contains complete proofs, no `sorry`
- [ ] Examples.lean contains executable examples
- [ ] No commented-out code blocks in any file
- [ ] No circular import dependencies
- [ ] Cross-domain imports are documented

---

## References

- [ADR-001: Three-File Module Pattern](../02_adrs/ADR-001-three-file-module-pattern.md)
- [ADR-005: Domain-Based Module Organization](../02_adrs/ADR-005-domain-based-module-organization.md)
- [ADR-006: Complete Proof Requirement](../02_adrs/ADR-006-complete-proof-requirement.md)
- [Coding Standards](../01_standards/coding_standards.md)
- [REQ-001: Core Foundation Requirements](../04_future_state/reqs/REQ-001-core-foundation.md)
