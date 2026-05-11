# Morph Language Lean 4 Coding Standards

**Version:** 2.0.0
**Status:** Active
**Last Updated:** 2026-01-31
**Purpose:** Establish strict coding standards for Lean 4 formal verification files in the Morph project

---

## Table of Contents

1. [Overview](#overview)
2. [File Organization](#file-organization)
3. [Lean 4 Syntax Standards](#lean-4-syntax-standards)
4. [Formatting and Style](#formatting-and-style)
5. [Naming Conventions](#naming-conventions)
6. [Comment Policies](#comment-policies)
7. [Import Organization](#import-organization)
8. [Type and Definition Standards](#type-and-definition-standards)
9. [Theorem and Proof Structure](#theorem-and-proof-structure)
10. [Error Handling Patterns](#error-handling-patterns)
11. [Lean 4 Specific Guidelines](#lean-4-specific-guidelines)
12. [Formal Verification Best Practices](#formal-verification-best-practices)
13. [Code Quality Rules](#code-quality-rules)
14. [Testing and Examples](#testing-and-examples)


---

## Overview

This document defines the coding standards for Lean 4 files in the Morph project. These standards ensure consistency, maintainability, and correctness across all formal verification code. All contributors must follow these standards.

### Project Context

- **Lean Version:** v4.27.0 (as specified in [`lean-toolchain`](../../lean-toolchain:1))
- **Build System:** Lake (as configured in [`lakefile.lean`](../../lakefile.lean:1) and [`lakefile.toml`](../../lakefile.toml:1))
- **Dependencies:** mathlib4, aesop, batteries (as specified in [`lakefile.lean`](../../lakefile.lean:55-57))
- **Reference Documentation:** [`.stack_docs/lean4-manual/`](../../.stack_docs/lean4-manual/)

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
| SPEC-001 | `spec_proposition_name` | Done |
| SPEC-002 | `spec_proposition_name` | Done |

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

## Lean 4 Syntax Standards

### Comment Syntax

Lean 4 provides two comment syntaxes:

```lean
-- Single-line comment: extends to end of line

/- Block comment:
   Can span multiple lines
   and can be nested
-/

/-! Module-level documentation:
   Used for API documentation
-/

/--
Declaration-level documentation
-/
```

**Rules:**
- Use `--` for single-line comments
- Use `/- ... -/` for multi-line comments (supports nesting)
- Use `/-! ... -/` for module-level documentation
- Use `/-- ... -/` for declaration-level documentation
- Block comments may be nested; `-/` only terminates the comment if prior nested block comment openers `/-` have been terminated by a matching `-/`

### Whitespace Rules

```lean
-- Valid whitespace characters:
-- - Space (U+0020)
-- - Newline (U+000A) or CRLF (U+000D U+000A)
-- - Comments (treated as whitespace)

-- Invalid: Tab characters and standalone CR
```

**Rules:**
- Use spaces for indentation (as enforced by [`.editorconfig`](../../.editorconfig:15))
- Use 2 spaces per indentation level (as enforced by [`.editorconfig`](../../.editorconfig:16))
- No tab characters in Lean files
- Line endings are normalized to LF by Lean

### Identifier Syntax

#### Valid Identifier Components

```lean
-- Valid identifiers:
x
x1
x_1
α
ℕ
ℕ?
«custom identifier»

-- Invalid identifiers:
_        -- underscore alone is not a valid identifier
```

**Rules:**
- Identifier components start with a letter or letter-like character or underscore
- Continuation characters include letters, underscores, exclamation marks, question marks, subscripts, and single quotes
- Underscore alone is not a valid identifier
- Use guillemets `«...»` for identifiers containing special characters or keywords

#### Hierarchical Identifiers

```lean
-- Hierarchical identifiers use dots to separate components:
Morph.Specs.MemoryModel.BlockId
List.map
Nat.add
```

**Rules:**
- Use dots (`.`) to separate namespace components
- Hierarchical identifiers are used for both import names and names in namespaces

#### Leading Dot Notation

```lean
-- Leading dot uses expected type for resolution:
def replicate (n : Nat) (a : α) : List α := ...

-- Usage with leading dot:
#eval .replicate 3 ()  -- Resolves to List.replicate
```

**Rules:**
- Use leading dot (`.`) when you want to resolve an identifier in the expected type's namespace
- The expected type is used to resolve the identifier rather than current namespace

### Function Type Syntax

```lean
-- Non-dependent function type:
α → β

-- Dependent function type with explicit name:
(x : α) → β

-- Multiple parameters with same type:
(x y : α) → β

-- Curried syntax (equivalent):
α → β → γ
(x : α) → (y : β) → γ
```

### Implicit Parameters

```lean
-- Ordinary implicit parameters (synthesized via unification):
def f {α : Type} : α → α := fun x => x

-- Strict implicit parameters (only synthesized when explicit args provided):
def g ⦃α : Type⦄ : α → α := fun x => x

-- Instance implicit parameters (synthesized via type class synthesis):
def h [Add α] (x y : α) : α := x + y

-- Automatic parameters (synthesized automatically):
def map (f : α → β) : List α → List β
  -- α and β are automatically inserted as implicit parameters
```

**Rules:**
- Use `{...}` for ordinary implicit parameters (always synthesized)
- Use `⦃...⦄` or `{{...}}` for strict implicit parameters (only when explicit args provided)
- Use `[...]` for instance implicit parameters (type class synthesis)
- Automatic implicit parameters are inserted by default (controlled by `autoImplicit` option)

### Function Abstraction Syntax

```lean
-- Basic function abstraction:
fun x => x + 1

-- With type annotation:
fun (x : Nat) => x + 1

-- Multiple parameters:
fun x y => x + y

-- Curried with types:
fun (x : Nat) (y : Nat) => x + y

-- Using pattern matching:
fun | 0 => 0
   | n + 1 => n
```

**Rules:**
- Use `fun` for function abstractions
- Use `=>` or `↦` as the arrow (both are valid)
- Provide type annotations when types cannot be inferred
- Use pattern matching in function abstractions for destructuring

### Definition Syntax

```lean
-- Basic definition:
def add (x y : Nat) : Nat := x + y

-- With documentation:
/-- Add two natural numbers. -/
def add (x y : Nat) : Nat := x + y

-- With attributes:
@[simp]
def add (x y : Nat) : Nat := x + y

-- Pattern matching definition:
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- With modifiers:
private def helper (x : Nat) : Nat := ...
public def apiFunction (x : Nat) : Nat := ...
noncomputable def specFunction (x : Nat) : Nat := ...
```

**Rules:**
- Use `def` for function definitions
- Use `abbrev` for type aliases
- Use `theorem` for propositions with proofs
- Use `example` for documentation examples (not saved to environment)
- Use `opaque` for opaque definitions (cannot be unfolded)
- Apply modifiers in order: documentation, attributes, visibility, `noncomputable`, `unsafe`, recursion modifiers

### Inductive Type Syntax

```lean
-- Basic inductive type:
inductive Expr where
  | literal : Value → Expr
  | variable : String → Expr
  | apply : Expr → Expr → Expr

-- With documentation:
/-- Expression tree for Morph language. -/
inductive Expr where
  | literal : Value → Expr
  | variable : String → Expr
  | apply : Expr → Expr → Expr

-- With deriving:
inductive Expr where
  | literal : Value → Expr
  | variable : String → Expr
  | apply : Expr → Expr → Expr
  deriving Repr, BEq
```

**Rules:**
- Use `inductive` for algebraic data types
- Document each constructor
- Derive appropriate type class instances (`Repr`, `BEq`, `Hashable`)

### Structure Syntax

```lean
-- Basic structure:
structure Point where
  x : Float
  y : Float

-- With default values:
structure Point where
  x : Float := 0.0
  y : Float := 0.0

-- With documentation:
/-- 2D point with x and y coordinates. -/
structure Point where
  /-- X coordinate -/
  x : Float
  /-- Y coordinate -/
  y : Float

-- With deriving:
structure Point where
  x : Float
  y : Float
  deriving Repr, BEq
```

**Rules:**
- Use `structure` for record-like types
- Document each field
- Provide default values where appropriate
- Derive appropriate type class instances

### Module System Syntax

```lean
-- Module header (experimental, requires `set_option experimental.module true`):
module
import Std
public def greeting (name : String) : String :=
  s!"Hello, {name}"

-- Public import:
module
public import Morph.Core

-- Meta import:
module
meta import Lean.Meta

-- Import all (includes private scope):
module
import all Morph.Specs.MemoryModel

-- Export:
export Morph.Core (BlockId, Pointer)
```

**Rules:**
- Use `module` keyword to enable module system (experimental)
- Use `public` to expose declarations to importing modules
- Use `meta` to import at meta phase
- Use `import all` to include private scope
- Use `@[expose]` to expose definition bodies for unfolding
- Proofs are always private, even for public theorems

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

**Comment "Why," not "What":**

```lean
-- Good: Explains why we do this
-- Reverse iteration to handle index shifting during deletion
for i in List.reverse indices do
  ...

-- Bad: Describes what code does
-- Loop through array in reverse
for i in List.reverse indices do
  ...
```

### Module Documentation

- **Required:** Every module must have documentation
- **Format:** Use `/-! ... -/` for module-level docs
- **Content:** Include purpose, usage examples, and important invariants

### Function Documentation

- **Required:** Public functions must have documentation
- **Format:** Use `/-- ... -/` for declaration-level docs
- **Content:** Describe purpose, parameters, return value, and invariants

```lean
-- Good: Complete documentation
/--
Compute SHA256 hash of module content.
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
- **Format:** Use `/-- ... -/` for declaration-level docs
- **Content:** Describe the formal property being proven

```lean
-- Good: Describes the formal property
/--
INV-001: Module hash is deterministic
-/
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

1. **Standard Library Imports:** Lean 4 standard library (`Std`, `Lean`)
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

1. **Documentation:** Describes purpose
2. **Deriving:** Appropriate type class instances
3. **Fields:** Descriptive names with types

```lean
-- Good: Complete structure definition
/--
Memory block with size, data, and reference count.
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

1. **Documentation:** Describes purpose
2. **Constructors:** Descriptive names
3. **Deriving:** Appropriate type class instances

```lean
-- Good: Complete inductive type
/--
Expression tree for Morph language.
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
/--
Compute SHA256 hash of module content.

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

Use appropriate tactics for proof:

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

## Lean 4 Specific Guidelines

### Lean Version Compatibility

The Morph project targets **Lean v4.27.0**. All code must be compatible with this version.

### Breaking Changes from v4.10.0 to v4.27.0

#### Char.csize → Char.utf8Size

**Breaking Change (v4.10.0):** `Char.csize` has been replaced by `Char.utf8Size`.

```lean
-- Old (v4.10.0 and earlier)
def charSize (c : Char) : Nat := Char.csize c

-- New (v4.10.0+)
def charSize (c : Char) : Nat := Char.utf8Size c
```

#### GetElem Class Split

**Breaking Change (v4.10.0):** The `GetElem` class has been split into `GetElem` and `GetElem?`.

```lean
-- Old: Single GetElem class
instance : GetElem (α : Type) (n : Nat) (xs : List α) where
  getElem [xs] [n] h : n < xs.length => xs[n]

-- New: Split into GetElem and GetElem?
instance : GetElem (α : Type) (n : Nat) (xs : List α) where
  getElem [xs] [n] h : n < xs.length => xs[n]

instance : GetElem? (α : Type) (n : Nat) (xs : List α) where
  getElem? [xs] [n] : Option α :=
    if h : n < xs.length then some xs[n] else none
```

#### Indexing Normal Forms

**Breaking Change (v4.10.0):** Normal forms for indexing into `List` and `Array` are now `xs[n]` and `xs[n]?` instead of function calls.

```lean
-- Old (pre-v4.10.0)
def getElement (xs : List Nat) (n : Nat) : Nat :=
  List.get xs n

def getElement? (xs : List Nat) (n : Nat) : Option Nat :=
  List.get? xs n

-- New (v4.10.0+)
def getElement (xs : List Nat) (n : Nat) : Nat :=
  xs[n]

def getElement? (xs : List Nat) (n : Nat) : Option Nat :=
  xs[n]?
```

#### Eta Reduction Changes

**Breaking Change (v4.10.0):** Terms created via unification may be more eta-reduced than before. Proofs may require adaptation.

```lean
-- Some proofs that relied on non-eta-reduced forms
-- may need to be updated to account for additional eta reduction
```

#### Std.Range → Std.Legacy.Range

**Breaking Change (v4.28.0):** `Std.Range` has been renamed to `Std.Legacy.Range`. New range type `Std.Rco` and `a...b` notation should be used instead.

```lean
-- Old (pre-v4.28.0)
import Std.Range
def exampleRange := [1:10]

-- New (v4.28.0+)
import Std.Data.Range
def exampleRange := 1...10  -- Uses new Rco type
```

#### Iterator API Changes

**Breaking Change (v4.28.0):** Many iterator constants have been moved from `Std.Iterators` to `Std` namespace.

```lean
-- Old (pre-v4.28.0)
import Std.Iterators
def example := Iter.map ...

-- New (v4.28.0+)
open Std
def example := Iter.map ...  -- Iter is now in Std namespace
```

#### IteratorCollect Removal

**Breaking Change (v4.28.0):** The `IteratorCollect` type class has been removed to simplify the iterator API.

```lean
-- Old (pre-v4.28.0)
instance : IteratorCollect MyIter where ...

-- New (v4.28.0+)
-- IteratorCollect no longer exists; use alternative patterns
```

### Module System Guidelines

#### Module Visibility

The module system (experimental) provides fine-grained control over visibility:

```lean
-- Enable module system (experimental)
set_option experimental.module true

module
-- Private by default
def privateHelper (x : Nat) : Nat := x + 1

-- Public declaration
public def publicApi (x : Nat) : Nat := privateHelper x

-- Exposed body (can be unfolded in importing modules)
@[expose]
public def exposedDef (x : Nat) : Nat := x + 1
```

#### Import Modifiers

```lean
-- Public import (exposes public scope)
public import Morph.Core

-- Meta import (available at meta phase)
meta import Lean.Meta

-- Import all (includes private scope)
import all Morph.Specs.MemoryModel
```

#### Backward Compatibility Options

When transitioning to modules, use backward compatibility options:

```lean
-- Allow private definitions in public scope (transition only)
set_option backward.privateInPublic true

-- Make proofs public (transition only)
set_option backward.proofsInPublic true
```

### Type Class Instance Guidelines

#### Instance Declaration

```lean
-- Basic instance
instance : BEq BlockId where
  beq a b := a.id = b.id

-- Instance with priority
@[default_instance]
instance [Inhabited α] : Inhabited (Option α) where
  inhabited := none
```

#### Instance Resolution

- Lean resolves instances using type class synthesis
- Use `@[default_instance]` for fallback instances
- Use `@[priority 100]` to control instance priority

### Attribute Guidelines

#### Common Attributes

```lean
-- Simp attribute for simplification
@[simp]
theorem add_zero (n : Nat) : n + 0 = n := by
  cases n
  · rfl
  · exact Nat.succ_add n 0

-- Inline attribute for performance
@[inline]
def smallFunction (x : Nat) : Nat := x + 1

-- Expose attribute for module system
@[expose]
public def exposedDef (x : Nat) : Nat := x + 1
```

#### Custom Attributes

```lean
-- Register custom grind attribute
register_grind_attr my_grind

@[my_grind]
theorem customLemma : Prop := ...
```

### Option Guidelines

#### Compiler Options

```lean
-- Disable automatic implicit parameters
set_option autoImplicit false

-- Enable relaxed automatic implicit parameters (default)
set_option relaxedAutoImplicit true

-- Enable trace for debugging
set_option trace.Meta.isDefEq true

-- Skip kernel type checking (unsound, for debugging only)
set_option debug.skipKernelTC true
```

#### Linter Options

```lean
-- Disable constructor name as variable linter
set_option linter.constructorNameAsVariable false

-- Disable unused variable linter
set_option linter.unusedVariables false
```

### Proof Tactic Guidelines

#### Modern Tactic Preferences

```lean
-- Prefer `grind` over `linarith` for arithmetic
example (a b : Nat) : a + b = b + a := by
  grind

-- Prefer `simp?` to find needed simp lemmas
example (a b : Nat) : a + b = b + a := by
  simp?

-- Prefer `apply?` to find applicable theorems
example (a b : Nat) : a + b = b + a := by
  apply?
```

#### Tactic Combinators

```lean
-- Use `;` for sequential tactics
theorem example : Prop := by
  intro h
  cases h
  · constructor
    · exact h1
    · constructor
      · exact h2
      · intro h3
        exact h3

-- Use `·` for bullet points (same as `;`)
```

### Error Message Guidelines

#### Reading Lean Error Messages

Lean error messages follow a structured format:

```
error: type mismatch
  expr
  has type
  α
but is expected to have type
  β
```

**Key parts:**
1. **Error type:** What went wrong (type mismatch, unknown identifier, etc.)
2. **Expression:** The problematic code
3. **Actual type:** The type Lean inferred
4. **Expected type:** The type Lean expected

#### Common Error Patterns

```lean
-- Error: Unknown identifier
-- Fix: Check imports and spelling
def example : Nat := unknownFunction  -- Error

-- Error: type mismatch
-- Fix: Check types and add explicit annotations
def example (x : Nat) : String :=
  x  -- Error: Nat expected to be String

-- Error: don't know how to synthesize implicit argument
-- Fix: Provide explicit type or enable autoImplicit
set_option autoImplicit false
def example (α : Type) (x : α) : α := x  -- OK
def example (x : α) : α := x  -- Error: unknown identifier α
```

### Documentation Guidelines

#### Docstring Format

```lean
/--
Brief description of the declaration.

**Parameters:**
- `param1`: Description of parameter 1
- `param2`: Description of parameter 2

**Returns:** Description of return value

**Examples:**
```lean
example := ...
```

**Note:** Additional notes about usage

**See also:** Related declarations
-/
def example (param1 : Type1) (param2 : Type2) : ReturnType := ...
```

#### Verso Docstrings

Lean 4.28.0+ supports Verso docstrings in `where` clauses:

```lean
def mainFunction (x : Nat) : Nat :=
  x + 1
where
  /--
  Helper function for mainFunction.
  -/
  helper (y : Nat) : Nat := y + 1
```

### Performance Guidelines

#### Reducibility Hints

```lean
-- Mark definitions as semireducible for better performance
@[semireducible]
def expensiveFunction (x : Nat) : Nat := ...

-- Mark definitions as irreducible to prevent unfolding
@[irreducible]
def opaqueType : Type := ...
```

#### Inline Hints

```lean
-- Always inline small functions
@[inline]
def smallFunction (x : Nat) : Nat := x + 1

-- Never inline large functions
@[noinline]
def largeFunction (x : Nat) : Nat := ...
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
  createModuleId example_module_hash 1

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
| SPEC-001 | `spec_proposition_name` | Done |
| SPEC-002 | `spec_proposition_name` | Done |
-!/
```

---

## References

- [Lean 4 Manual](../../.stack_docs/lean4-manual/)
- [Lean 4 Release Notes](../../.stack_docs/lean4-manual/Manual/Releases.lean)
- [Mathlib4 Style Guide](https://github.com/leanprover-community/mathlib4/blob/master/CONTRIBUTING.md)
- [Lake Package Manager](https://github.com/leanprover/lean4/tree/master/src/lake)
- [Morph Project README](../../README.md)

---

## Changelog

### Version 2.0.0 (2026-01-31)

- Updated Lean version to v4.27.0
- Added comprehensive Lean 4 syntax standards
- Added breaking changes from v4.10.0 to v4.27.0
- Added module system guidelines
- Added Lean 4 specific error handling patterns
- Added performance guidelines
- Added Verso docstring support
- Updated references to `.stack_docs/lean4-manual/`

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
**Next Review:** 2026-07-31
**Maintainer:** Morph Project Technical Lead
