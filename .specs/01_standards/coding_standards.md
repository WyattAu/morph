# Morph Language Lean 4 Coding Standards

**Version:** 1.0.0  
**Status:** Active  
**Last Updated:** 2026-01-30  
**Purpose:** Establish strict coding standards for Lean 4 formal verification files in the Morph project

---

## Table of Contents

1. [Overview](#overview)
2. [File Organization](#file-organization)
3. [Formatting and Style](#formatting-and-style)
4. [Naming Conventions](#naming-conventions)
5. [Comment Policies](#comment-policies)
6. [Import Organization](#import-organization)
7. [Type and Definition Standards](#type-and-definition-standards)
8. [Theorem and Proof Structure](#theorem-and-proof-structure)
9. [Error Handling Patterns](#error-handling-patterns)
10. [Formal Verification Best Practices](#formal-verification-best-practices)
11. [Code Quality Rules](#code-quality-rules)
12. [Testing and Examples](#testing-and-examples)



---

## Overview

This document defines the coding standards for Lean 4 files in the Morph project. These standards ensure consistency, maintainability, and correctness across all formal verification code. All contributors must follow these standards.

### Project Context

- **Lean Version:** 4.10.0 (as specified in [`lean-toolchain`](../../lean-toolchain:1))
- **Build System:** Lake (as configured in [`lakefile.lean`](../../lakefile.lean:1) and [`lakefile.toml`](../../lakefile.toml:1))
- **Dependencies:** mathlib4, aesop, batteries (as specified in [`lakefile.lean`](../../lakefile.lean:55-57))

### Scope

These standards apply to all Lean 4 files in the `Morph/` directory, including:
- Core language definitions
- Specification files (`Spec.lean`)
- Lemma files (`Lemmas.lean`)
- Example files (`Examples.lean`)

---

## File Organization

### Module Structure

Each specification domain in `Morph/Specs/` must follow the three-file pattern:

```
Morph/Specs/[DomainName]/
├── Spec.lean      -- Core types, definitions, and specification theorems
├── Lemmas.lean    -- Mathematical lemmas and proofs
└── Examples.lean  -- Concrete examples and test cases
```

### File Header

Every Lean file must begin with the following header:

```lean
/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
```

### Module Documentation

Each file must include a module-level documentation block using the `/-! ... -/` syntax:

```lean
/-!
# Specification: [Domain Name]

**Source:** `spec/path/to/spec.md`
**Status:** [Complete | In Progress | Pending]
**Last Updated:** YYYY-MM-DD
**Verified By:** [Name or "Pending"]

## Overview

[Brief description of what this module formalizes]

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| SPEC-001 | `spec_proposition_name` | ✓ |
| SPEC-002 | `spec_proposition_name` | ✓ |

## Known Issues

[List any known issues or limitations]

## TODO

[List pending work items]
-!/
```

### Namespace Declaration

All definitions must be within a namespace:

```lean
namespace Morph.Specs.DomainName

-- Content here

end Morph.Specs.DomainName
```

---

## Formatting and Style

### Indentation

- **Indentation Style:** Spaces (as specified in [`.editorconfig`](../../.editorconfig:15))
- **Indentation Size:** 2 spaces (as specified in [`.editorconfig`](../../.editorconfig:16))
- **Tab Characters:** Strictly forbidden

### Line Length

- **Maximum Line Length:** 100 characters
- **Preferred Line Length:** 80-90 characters for readability
- **Exception:** Long type signatures and theorem statements may exceed this limit

### Blank Lines

- **Between Top-Level Definitions:** 1 blank line
- **Between Sections:** 2 blank lines
- **Within Definitions:** No blank lines unless separating logical blocks

### Whitespace

- **Trailing Whitespace:** Must be removed (as enforced by [`.editorconfig`](../../.editorconfig:10))
- **Final Newline:** Required at end of file (as enforced by [`.editorconfig`](../../.editorconfig:9))
- **Line Endings:** LF only (as enforced by [`.editorconfig`](../../.editorconfig:8))

### Alignment

Align similar constructs for readability:

```lean
-- Good: Aligned structure fields
structure Point where
  x : Float
  y : Float
  deriving Repr, BEq

-- Good: Aligned function parameters
def addPoints (p1 p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

-- Bad: Inconsistent indentation
structure Point where
    x : Float
  y : Float
```

---

## Naming Conventions

### Types (PascalCase)

- **Structures:** PascalCase
- **Inductive Types:** PascalCase
- **Type Aliases:** PascalCase
- **Classes:** PascalCase

```lean
-- Good
structure Block where ...
inductive Expr where ...
abbrev BlockId := ObjectId
class MonadState where ...

-- Bad
structure block where ...
inductive expr where ...
abbrev blockId := ObjectId
```

### Functions and Theorems (camelCase)

- **Definitions:** camelCase
- **Theorems:** camelCase with descriptive names
- **Lemmas:** camelCase with descriptive names
- **Instance Names:** camelCase

```lean
-- Good
def computeModuleHash (content : String) : String := ...
theorem module_hash_deterministic (content : String) : Prop := ...
lemma allocation_creates_unique_block : Prop := ...
instance : BEq Block where ...

-- Bad
def ComputeModuleHash (content : String) : String := ...
theorem Module_Hash_Deterministic (content : String) : Prop := ...
```

### Variables and Parameters (lowercaseCamelCase)

- **Function Parameters:** lowercaseCamelCase
- **Local Variables:** lowercaseCamelCase
- **Pattern Variables:** lowercaseCamelCase

```lean
-- Good
def add (x y : Nat) : Nat := x + y
theorem add_comm (a b : Nat) : a + b = b + a := by
  intro a b
  -- proof

-- Bad
def add (X Y : Nat) : Nat := X + Y
theorem add_comm (A B : Nat) : A + B = B + A := by
  intro A B
```

### Constants (UPPER_SNAKE_CASE)

- **Global Constants:** UPPER_SNAKE_CASE
- **Type Class Instances:** camelCase (exception)

```lean
-- Good
def MAX_BLOCK_SIZE : Nat := 4096
def DEFAULT_ALIGNMENT : Nat := 8

-- Bad
def MaxBlockSize : Nat := 4096
def default_alignment : Nat := 8
```

### Module Names (PascalCase)

- **Namespaces:** PascalCase
- **File Names:** PascalCase

```lean
-- Good
namespace Morph.Specs.MemoryModel
-- File: MemoryModel.lean

-- Bad
namespace Morph.Specs.memory_model
-- File: memory_model.lean
```

### Descriptive Names

All names must be descriptive and self-documenting:

```lean
-- Good
def computeModuleHash (content : String) : String := ...
theorem allocation_preserves_well_formedness : Prop := ...

-- Bad
def hash (s : String) : String := ...
theorem alloc_wf : Prop := ...
```

---

## Comment Policies

### When to Comment

**Comment the "Why," not the "What":**

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

### Module Documentation

- **Required:** Every module must have documentation
- **Format:** Use `/-! ... -/` for module-level docs
- **Content:** Include purpose, usage examples, and important invariants

### Function Documentation

- **Required:** Public functions must have documentation
- **Format:** Use `--` for single-line, `/- -/` for multi-line
- **Content:** Describe purpose, parameters, return value, and invariants

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

-- Bad: No documentation
def computeModuleHash (content : String) : String := ...
```

### Theorem Documentation

- **Required:** All theorems must have documentation
- **Format:** Use `--` for single-line
- **Content:** Describe the formal property being proven

```lean
-- Good: Describes the formal property
-- INV-001: Module hash is deterministic
theorem module_hash_deterministic (content : String) :
  computeModuleHash content = computeModuleHash content := by
  trivial

-- Bad: No documentation
theorem module_hash_deterministic (content : String) :
  computeModuleHash content = computeModuleHash content := by
  trivial
```

### Section Comments

- **Required:** Use section comments to organize code
- **Format:** Use `/-! ## Section Name -/`

```lean
/-! ## Module Hash Theorems

These theorems establish properties of module hashing.
-/

theorem module_hash_deterministic ...
```

### Inline Comments

- **Use Case:** When code is non-obvious
- **Format:** Use `--` for inline comments
- **Placement:** Above the code being explained

```lean
-- Good: Explains non-obvious logic
-- Use bitwise XOR to combine hashes for better distribution
def combineHashes (h1 h2 : Nat) : Nat := h1 ^^^ h2

-- Bad: States the obvious
-- Add two numbers
def add (x y : Nat) : Nat := x + y
```

### Commented-Out Code: STRICTLY FORBIDDEN

**Zero Tolerance Policy:**

Commented-out code is strictly forbidden in the Morph project. Code must either work or be removed.

```lean
-- STRICTLY FORBIDDEN
-- def oldFunction (x : Nat) : Nat := ...
-- theorem oldTheorem : Prop := ...

-- INSTEAD: Either implement it properly or remove it
def oldFunction (x : Nat) : Nat := x + 1  -- Implemented
```

**Rationale:**

1. **Version Control:** Git provides history; commented code is redundant
2. **Code Clarity:** Dead code confuses readers and reviewers
3. **Maintenance:** Commented code rots and becomes misleading
4. **Formal Verification:** Incomplete formalizations are worse than none

**Exception:**

The only exception is temporary code during active development that will be removed before commit. Such code must be marked with a `TODO` comment and removed before the PR is submitted:

```lean
-- TODO: Remove this temporary test case before merging
#eval temporaryTestFunction
```

### TODO Comments

- **Format:** Use `-- TODO: [description]` for pending work
- **Placement:** Above the code that needs work
- **Action Required:** All TODOs must be tracked in project issues

```lean
-- TODO: Implement actual SHA256 hashing instead of placeholder
def computeModuleHash (content : String) : String :=
  ""
```

---

## Import Organization

### Import Order

Imports must be organized in the following order:

1. **Standard Library Imports:** Lean 4 standard library
2. **Project Core Imports:** `Morph.Core`, `Morph.Syntax`, etc.
3. **Project Module Imports:** Other Morph modules
4. **Third-Party Imports:** mathlib, aesop, batteries
5. **Local Module Imports:** Files within the same domain

```lean
-- Good: Properly organized imports
import Std
import Lean

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics

import Mathlib.Data.Nat.Basic
import Batteries.Data.List.Basic

import Morph.Specs.CommonTypes

-- Bad: Unorganized imports
import Morph.Specs.CommonTypes
import Morph.Core
import Std
import Mathlib.Data.Nat.Basic
```

### Import Grouping

Separate import groups with blank lines:

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

-- Local
import Morph.Specs.CommonTypes
```

### Qualified vs Unqualified

- **Prefer:** Unqualified imports for frequently used symbols
- **Use:** Qualified imports for symbols with name conflicts
- **Avoid:** `open` statements that pollute the namespace

```lean
-- Good: Unqualified for common symbols
import Mathlib.Data.Nat.Basic

-- Good: Qualified for conflict avoidance
import Mathlib.Data.List (List as StdList)

-- Bad: Excessive open
open List Nat
```

### Unused Imports

- **Forbidden:** All imports must be used
- **Enforcement:** Linting tools will flag unused imports
- **Action:** Remove unused imports before committing

---

## Type and Definition Standards

### Structure Definitions

All structures must include:

1. **Documentation:** Describes the purpose
2. **Deriving:** Appropriate type class instances
3. **Fields:** Descriptive names with types

```lean
-- Good: Complete structure definition
/-- Memory block with size, data, and reference count.
    Represents a single allocated memory block in the Morph runtime.
-/
structure Block where
  /-- Unique identifier for this block -/
  id : BlockId
  /-- Size of the block in bytes -/
  size : Nat
  /-- Raw data stored in the block -/
  data : Array UInt8
  /-- Reference count for ARC -/
  refCount : Nat
  deriving Repr, BEq, Hashable
```

### Inductive Type Definitions

All inductive types must include:

1. **Documentation:** Describes the purpose
2. **Constructors:** Descriptive names
3. **Deriving:** Appropriate type class instances

```lean
-- Good: Complete inductive type
/-- Expression tree for Morph language.
    Represents syntactic constructs in the language.
-/
inductive Expr where
  /-- Literal value -/
  | literal : Value → Expr
  /-- Variable reference -/
  | variable : String → Expr
  /-- Function application -/
  | apply : Expr → Expr → Expr
  /-- Lambda abstraction -/
  | lambda : String → Expr → Expr
  deriving Repr, BEq
```

### Function Definitions

All functions must include:

1. **Documentation:** Describes purpose, parameters, return value
2. **Type Signature:** Explicit and complete
3. **Implementation:** Clear and correct

```lean
-- Good: Complete function definition
/-- Compute the SHA256 hash of module content.
    
    **Parameters:**
    - `content`: The module source code as a string
    
    **Returns:** The SHA256 hash as a hexadecimal string
    
    **Invariant:** The hash is deterministic for identical inputs
-/
def computeModuleHash (content : String) : String :=
  -- TODO: Implement actual SHA256 hashing
  ""
```

### Abbreviations

Use abbreviations for type aliases:

```lean
-- Good: Clear type alias
abbrev BlockId := ObjectId
abbrev LinkTable := List (ModuleId × Module)

-- Bad: Unclear abbreviation
abbrev BID := ObjectId
abbrev LT := List (ModuleId × Module)
```

### Default Values

Provide default values where appropriate:

```lean
-- Good: Default values for common cases
structure WorkspaceConfig where
  searchPaths : List String := ["./src"]
  excludePatterns : List String := ["*.test.min", "node_modules"]
  maxDepth : Nat := 5
  deriving Repr
```

---

## Theorem and Proof Structure

### Theorem Naming

Theorems must use descriptive names following the pattern:

```lean
-- Pattern: [domain]_[property]_[qualifiers]
theorem module_hash_deterministic : ...
theorem allocation_preserves_well_formedness : ...
theorem deallocation_removes_zero_ref_blocks : ...
```

### Theorem Statement

Theorem statements must be:

1. **Clear:** The property must be immediately understandable
2. **Complete:** All quantifiers must be explicit
3. **Well-typed:** The statement must type-check

```lean
-- Good: Clear and complete
theorem module_hash_deterministic (content : String) :
  computeModuleHash content = computeModuleHash content := by
  trivial

-- Bad: Vague and incomplete
theorem hash_det : Prop := ...
```

### Proof Structure

Proofs must follow a clear structure:

```lean
-- Good: Well-structured proof
theorem allocation_creates_unique_block
  (mem : Memory) (size : Nat) :
  let (newMem, id) := allocate mem size in
    ∃ (block : Block),
      (id, block) ∈ newMem.blocks ∧
        block.size = size ∧
        block.refCount = 1 ∧
        ∀ (bid, _) ∈ mem.blocks, bid ≠ id := by
  intro newMem id h_alloc
  -- Allocation creates a new block with the requested size
  -- and reference count 1. All existing blocks are preserved.
  cases h_alloc
  · constructor
    · exact h_alloc.block
    · constructor
      · exact h_alloc.size_eq
      · constructor
        · exact h_alloc.refCount_eq
        · intro bid h_in
          exact h_alloc.preserves bid h_in
```

### Proof Tactics

Use appropriate tactics for the proof:

- **`intro`**: Introduce hypotheses
- **`constructor`**: Build existential witnesses
- **`cases`**: Destruct pattern matches
- **`simp`**: Simplify expressions
- **`rw`**: Rewrite using equalities
- **`apply`**: Apply a lemma or theorem
- **`exact`**: Provide exact term
- **`trivial`**: Solve trivial goals
- **`sorry`**: STRICTLY FORBIDDEN in production code

### Placeholder Proofs

**STRICTLY FORBIDDEN:**

The `sorry` tactic is strictly forbidden in production code. All proofs must be complete.

```lean
-- STRICTLY FORBIDDEN
theorem bad_theorem : Prop := by
  sorry

-- INSTEAD: Either prove it or mark as TODO
-- TODO: Prove this theorem
theorem pending_theorem : Prop := by
  -- Proof to be implemented
  trivial
```

### Lemma Organization

Lemmas should be organized by functionality:

```lean
/-! ## Module Hash Theorems

These theorems establish properties of module hashing.
-/

theorem module_hash_deterministic ...

/-! ## Module ID Theorems

These theorems establish properties of module identification.
-/

theorem module_id_uniquely_identifies_module ...
```

---

## Error Handling Patterns

### Option Types

Use `Option` for values that may not exist:

```lean
-- Good: Proper Option handling
def resolveModule (table : LinkTable) (id : ModuleId) : Option Module :=
  table.find fun (mid, _) => mid = id |>.map fun (_, m) => m

-- Usage with pattern matching
def getModuleName (table : LinkTable) (id : ModuleId) : String :=
  match resolveModule table id with
  | some module => module.name
  | none => "Unknown"
```

### Except Types

Use `Except` for operations that can fail with specific errors:

```lean
-- Good: Proper Except handling
inductive LoadError where
  | fileNotFound : String → LoadError
  | parseError : String → LoadError
  deriving Repr

def loadModule (path : String) : Except LoadError Module :=
  if System.FilePath.pathExists path then
    -- Load and parse module
    ...
  else
    throw (LoadError.fileNotFound path)
```

### Assertions

Use `assert!` for runtime invariants that must hold:

```lean
-- Good: Asserting invariants
def getBlockData (mem : Memory) (id : BlockId) : Array UInt8 :=
  match getBlock mem id with
  | some block =>
    assert! block.data.size = block.size
    block.data
  | none =>
    panic! s!"Block {id} not found in memory"
```

### Defensive Programming

Validate inputs and handle edge cases:

```lean
-- Good: Defensive programming
def safeDiv (num den : Nat) : Option Nat :=
  if den = 0 then
    none
  else
    some (num / den)

-- Bad: No error handling
def unsafeDiv (num den : Nat) : Nat :=
  num / den  -- Panics if den = 0
```

---

## Formal Verification Best Practices

### Specification Clarity

Specifications must be unambiguous and complete:

```lean
-- Good: Clear specification
theorem spec_memory_allocation (mem : Memory) (size : Nat) : Prop :=
  let (newMem, id) := allocate mem size in
    ∃ (block : Block),
      (id, block) ∈ newMem.blocks ∧
        block.size = size ∧
        block.refCount = 1 ∧
        ∀ (bid, _) ∈ mem.blocks, bid ≠ id

-- Bad: Ambiguous specification
theorem spec_alloc : Prop := ...
```

### Invariant Preservation

All operations must preserve system invariants:

```lean
-- Good: Explicit invariant preservation
theorem allocation_preserves_well_formedness
  (mem : Memory) (size : Nat) :
  isWellFormedMemory mem →
    let (newMem, _) := allocate mem size in
      isWellFormedMemory newMem := by
  intro h_wf
  -- Proof that allocation preserves well-formedness
```

### Correctness Proofs

All critical operations must have correctness proofs:

```lean
-- Good: Correctness proof
theorem module_resolution_correct
  (table : LinkTable)
  (mid : ModuleId)
  (m : Module)
  (h_in : (mid, m) ∈ table) :
  resolveModule table mid = some m := by
  unfold resolveModule
  -- Proof that resolution is correct
```

### Property-Based Testing

Use examples to verify properties:

```lean
-- Good: Property-based example
example_verify_INV001 : module_hash_deterministic "test content" := by
  unfold module_hash_deterministic
  trivial
```

### Abstraction Levels

Maintain clear abstraction levels:

```lean
-- Level 1: High-level specification
theorem spec_memory_safety : Prop := ...

-- Level 2: Implementation lemmas
lemma allocation_correct : Prop := ...

-- Level 3: Concrete examples
example_allocation : Memory := ...
```

---

## Code Quality Rules

### No Dead Code

All code must be reachable and used:

```lean
-- Good: All code is used
def usedFunction (x : Nat) : Nat := x + 1

def main : IO Unit := do
  IO.println s!"{usedFunction 5}"

-- Bad: Dead code
def unusedFunction (x : Nat) : Nat := x + 1
-- Never called
```

### No Magic Numbers

Use named constants instead of magic numbers:

```lean
-- Good: Named constants
def MAX_BLOCK_SIZE : Nat := 4096
def DEFAULT_ALIGNMENT : Nat := 8

def allocate (size : Nat) : Memory :=
  if size ≤ MAX_BLOCK_SIZE then
    -- Allocate
  else
    panic! "Block too large"

-- Bad: Magic numbers
def allocate (size : Nat) : Memory :=
  if size ≤ 4096 then
    -- Allocate
  else
    panic! "Block too large"
```

### No Code Duplication

Extract common logic into functions:

```lean
-- Good: Extracted common logic
def combineHashes (h1 h2 : Nat) : Nat := h1 ^^^ h2

def hashModule (content : String) : Nat :=
  combineHashes (hashString content) 42

def hashFunction (name : String) : Nat :=
  combineHashes (hashString name) 17

-- Bad: Duplicated logic
def hashModule (content : String) : Nat :=
  (hashString content) ^^^ 42

def hashFunction (name : String) : Nat :=
  (hashString name) ^^^ 17
```

### Single Responsibility

Each function should do one thing well:

```lean
-- Good: Single responsibility
def computeHash (content : String) : String := ...
def createModuleId (hash : String) (version : Nat) : ModuleId := ...
def publishModule (module : Module) : Registry := ...

-- Bad: Multiple responsibilities
def computeHashCreateIdAndPublish (content : String) : Registry := ...
```

### Minimal Complexity

Keep functions simple and readable:

```lean
-- Good: Simple and readable
def isWellFormedMemory (mem : Memory) : Bool :=
  mem.blocks.all fun (id, block) =>
    block.id = id ∧ block.data.size = block.size

-- Bad: Overly complex
def isWellFormedMemory (mem : Memory) : Bool :=
  if mem.blocks.isEmpty then
    true
  else
    if mem.blocks.head?.isSome then
      let (id, block) := mem.blocks.head?.get!
      if block.id = id then
        if block.data.size = block.size then
          isWellFormedMemory { mem with blocks := mem.blocks.tail! }
        else
          false
      else
        false
    else
      false
```

---

## Testing and Examples

### Example Files

Example files must demonstrate:

1. **Usage:** How to use the module
2. **Edge Cases:** Boundary conditions
3. **Properties:** Verification of invariants

```lean
-- Good: Complete example
/-! ## Example 1: Module Creation

Demonstrates creating a module with declarations.
-/

def example_module_content : String :=
  "fn add(x:i32,y:i32):i32{x+y}"

def example_module_hash : String :=
  computeModuleHash example_module_content

def example_module_id : ModuleId :=
  createModuleId example_module_content 1

#eval example_module_id.hash
-- Expected: Hash of content

#eval example_module_id.version
-- Expected: 1
```

### Test Organization

Examples should be organized by functionality:

```lean
/-! ## Module Creation Examples

Demonstrates creating modules with content-addressable hashes.
-/

def example_module_content ...

/-! ## Module Declaration Examples

Demonstrates creating module declarations.
-/

def example_function_decl ...
```

### Expected Output

All examples must include expected output:

```lean
#eval example_module_id.hash
-- Expected: "a1b2c3d4..."

def example_verify_hash : Bool :=
  example_module_id.hash = "a1b2c3d4..."
```

### Verification Examples

Include examples that verify invariants:

```lean
/-! ## Invariant Verification

Demonstrates verification of module system invariants.
-/

example_verify_INV001 : module_hash_deterministic example_module_content := by
  unfold module_hash_deterministic
  trivial
```

---

## Enforcement

### Automated Checks

The following automated checks are enforced:

1. **EditorConfig:** Enforces formatting standards
2. **Pre-commit Hooks:** Run linting and validation
3. **CI/CD:** Runs full build and test suite
4. **Code Review:** Manual review for standards compliance

### Linting Rules

- No unused imports
- No unused variables
- No trailing whitespace
- No tabs in Lean files
- No commented-out code
- No `sorry` in production code

### Review Checklist

Before submitting code, verify:

- [ ] All files have proper headers
- [ ] All functions have documentation
- [ ] All theorems have documentation
- [ ] No commented-out code
- [ ] No `sorry` in proofs
- [ ] All imports are used
- [ ] Naming conventions followed
- [ ] Indentation is 2 spaces
- [ ] Line length under 100 characters
- [ ] Examples include expected output

---

## Appendix: Common Patterns

### Pattern: Content-Addressable Hashing

```lean
def computeModuleHash (content : String) : String :=
  -- TODO: Implement SHA256
  ""

def createModuleId (content : String) (version : Nat) : ModuleId :=
  { hash := computeModuleHash content, version := version }
```

### Pattern: Option Handling

```lean
def resolveModule (table : LinkTable) (id : ModuleId) : Option Module :=
  table.find fun (mid, _) => mid = id |>.map fun (_, m) => m

def getModuleName (table : LinkTable) (id : ModuleId) : String :=
  match resolveModule table id with
  | some module => module.name
  | none => "Unknown"
```

### Pattern: Invariant Preservation

```lean
theorem operation_preserves_invariant
  (state : State) (input : Input) :
  isWellFormed state →
    let newState := execute state input in
      isWellFormed newState := by
  intro h_wf
  -- Proof that operation preserves invariant
```

### Pattern: Specification Mapping

```lean
/-! ## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| SPEC-001 | `spec_proposition_name` | ✓ |
| SPEC-002 | `spec_proposition_name` | ✓ |
-!/
```

---

## References

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Style Guide](https://github.com/leanprover-community/mathlib4/blob/master/CONTRIBUTING.md)
- [Lake Package Manager](https://github.com/leanprover/lean4/tree/master/src/lake)
- [Morph Project README](../../README.md)

---

## Changelog

### Version 1.0.0 (2026-01-30)

- Initial version
- Established coding standards for Lean 4
- Defined file organization patterns
- Specified naming conventions
- Outlined comment policies
- Established theorem/proof structure standards
- Defined error handling patterns
- Specified formal verification best practices

---

**Document Status:** Active  
**Next Review:** 2026-07-30  
**Maintainer:** Morph Project Technical Lead
