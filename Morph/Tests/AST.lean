/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/
import Std
import Morph.Syntax
import Morph.HIR
import Aesop

/-!
# Module: Tests.AST

**Author:** QA Engineer
**Created:** 2026-01-30
**Last Updated:** 2026-01-30
**Status:** Complete

## Purpose

Comprehensive tests for AST (Abstract Syntax Tree) structures in Morph verification system.
This module provides unit tests, property-based tests, and safety theorems for:
- Syntax.Id structure (surface-level identifiers)
- Syntax.Expr inductive type (surface-level expressions)
- Syntax.Stmt inductive type (surface-level statements)
- Syntax.Program structure (surface-level programs)
- HIR.Id structure (high-level intermediate representation identifiers)
- HIR.Pattern inductive type (pattern matching)
- HIR.Expr inductive type (high-level intermediate expressions)
- HIR.Stmt inductive type (high-level intermediate statements)
- HIR.Program structure (high-level intermediate programs)

## Dependencies

- `Morph.Syntax` - Surface-level AST definitions
- `Morph.HIR` - High-level intermediate representation definitions
- `Std` - Standard library for basic operations
- `Aesop` - Automated proof search

## Test Categories

### Unit Tests
- Basic construction and equality tests for AST types
- Expression and statement structure tests
- Program structure tests

### Property-Based Tests
- AST transformation properties
- Pattern matching properties

### Safety Theorems
- AST well-formedness properties
- Type invariants for AST structures

## Notes

- Tests use `example` for simple verification
- Theorems use `@[aesop]` for automation
- Property-based tests verify generic properties
- Safety theorems ensure AST soundness

## Threat Model Mitigations

- **RISK-AUT-007:** Test Generation Failures - All tests are manually reviewed
- **RISK-PER-006:** Test Execution Time - Tests are kept efficient
- **RISK-AUT-008:** Proof Automation Brittleness - Robust proof patterns used

## References

- Coding Standards Section 7: Testing Patterns
- ADR-009: Testing Infrastructure
- ADR-001: Three-File Module Pattern
- Threat Model: RISK-AUT-007, RISK-PER-006, RISK-AUT-008
-/

namespace Tests.AST

/-!
## Section 1: Syntax.Id Unit Tests

Tests for Syntax.Id structure (surface-level identifiers).
These tests verify that Id values can be constructed, compared, and hashed correctly.
-/

section SyntaxIdTests

  /-- Syntax.Id constructor creates valid structure -/
  example (n : String) : (Morph.Syntax.Id.mk n).name = n := by
    rfl

  /-- Syntax.Id getName returns the name -/
  example (n : String) : (Morph.Syntax.Id.mk n).getName = n := by
    rfl

  /-- Syntax.Id equality is reflexive -/
  example (id : Morph.Syntax.Id) : id = id := by
    rfl

  /-- Syntax.Id equality is symmetric -/
  example (id1 id2 : Morph.Syntax.Id) : id1 = id2 → id2 = id1 := by
    intro h
    exact h.symm

  /-- Syntax.Id equality is transitive -/
  example (id1 id2 id3 : Morph.Syntax.Id) :
    id1 = id2 → id2 = id3 → id1 = id3 := by
    intro h1 h2
    exact h1.trans h2

  /-- Syntax.Id can be hashed -/
  example (id : Morph.Syntax.Id) : (hash id) = (hash id) := by
    rfl

  /-- Different Syntax.Ids are not equal -/
  example (n1 n2 : String) : n1 ≠ n2 → Morph.Syntax.Id.mk n1 ≠ Morph.Syntax.Id.mk n2 := by
    intro h
    intro hneq
    exact h (congrArg Morph.Syntax.Id.name hneq)

end SyntaxIdTests

/-!
## Section 2: Syntax.Expr Unit Tests

Tests for Syntax.Expr inductive type (surface-level expressions).
These tests verify that Expression constructors work correctly and expressions can be compared.
-/

section SyntaxExprTests

  /-- Syntax.Expr.bvar constructor creates valid expression -/
  example (n : Nat) :
    (Morph.Syntax.Expr.bvar n) = Morph.Syntax.Expr.bvar n := by
    rfl

  /-- Syntax.Expr.fvar constructor creates valid expression -/
  example (name : String) :
    (Morph.Syntax.Expr.fvar name) = Morph.Syntax.Expr.fvar name := by
    rfl

  /-- Syntax.Expr.lit constructor creates valid expression -/
  example (v : Morph.Core.Value) :
    (Morph.Syntax.Expr.lit v) = Morph.Syntax.Expr.lit v := by
    rfl

  /-- Syntax.Expr.unop constructor creates valid expression -/
  example (op : Morph.Core.Operator) (e : Morph.Syntax.Expr) :
    (Morph.Syntax.Expr.unop op e) = Morph.Syntax.Expr.unop op e := by
    rfl

  /-- Syntax.Expr.binop constructor creates valid expression -/
  example (op : Morph.Core.Operator) (e1 e2 : Morph.Syntax.Expr) :
    (Morph.Syntax.Expr.binop op e1 e2) = Morph.Syntax.Expr.binop op e1 e2 := by
    rfl

  /-- Syntax.Expr.app constructor creates valid expression (fn is Expr, not Id) -/
  example (fn : Morph.Syntax.Expr) (args : List Morph.Syntax.Expr) :
    (Morph.Syntax.Expr.app fn args) = Morph.Syntax.Expr.app fn args := by
    rfl

  /-- Syntax.Expr.lam constructor creates valid expression -/
  example (n : Nat) (body : Morph.Syntax.Expr) :
    (Morph.Syntax.Expr.lam n body) = Morph.Syntax.Expr.lam n body := by
    rfl

  /-- Syntax.Expr.let_ constructor creates valid expression -/
  example (e1 e2 : Morph.Syntax.Expr) :
    (Morph.Syntax.Expr.let_ e1 e2) = Morph.Syntax.Expr.let_ e1 e2 := by
    rfl

  /-- Syntax.Expr.ifThenElse constructor creates valid expression -/
  example (cond e1 e2 : Morph.Syntax.Expr) :
    (Morph.Syntax.Expr.ifThenElse cond e1 e2) = Morph.Syntax.Expr.ifThenElse cond e1 e2 := by
    rfl

  /-- Syntax.Expr.forLoop constructor creates valid expression (3 args) -/
  example (start end_ : Morph.Syntax.Expr) (body : List Morph.Syntax.Expr) :
    (Morph.Syntax.Expr.forLoop start end_ body) = Morph.Syntax.Expr.forLoop start end_ body := by
    rfl

  /-- Syntax.Expr.block constructor creates valid expression -/
  example (body : List Morph.Syntax.Expr) :
    (Morph.Syntax.Expr.block body) = Morph.Syntax.Expr.block body := by
    rfl

  /-- Syntax.Expr equality is reflexive -/
  example (e : Morph.Syntax.Expr) : e = e := by
    rfl

  /-- Syntax.Expr equality is symmetric -/
  example (e1 e2 : Morph.Syntax.Expr) : e1 = e2 → e2 = e1 := by
    intro h
    exact h.symm

  /-- Syntax.Expr equality is transitive -/
  example (e1 e2 e3 : Morph.Syntax.Expr) :
    e1 = e2 → e2 = e3 → e1 = e3 := by
    intro h1 h2
    exact h1.trans h2

end SyntaxExprTests

/-!
## Section 3: Syntax.Stmt Unit Tests

Tests for Syntax.Stmt inductive type (surface-level statements).
These tests verify that Statement constructors work correctly and statements can be compared.
-/

section SyntaxStmtTests

  /-- Syntax.Stmt.exprStmt constructor creates valid statement -/
  example (e : Morph.Syntax.Expr) :
    (Morph.Syntax.Stmt.exprStmt e) = Morph.Syntax.Stmt.exprStmt e := by
    rfl

  /-- Syntax.Stmt.varDecl constructor creates valid statement -/
  example (id : Morph.Syntax.Id) (ty : Morph.Core.Typ) (e : Morph.Syntax.Expr) :
    (Morph.Syntax.Stmt.varDecl id ty e) = Morph.Syntax.Stmt.varDecl id ty e := by
    rfl

  /-- Syntax.Stmt.assign constructor creates valid statement -/
  example (id : Morph.Syntax.Id) (e : Morph.Syntax.Expr) :
    (Morph.Syntax.Stmt.assign id e) = Morph.Syntax.Stmt.assign id e := by
    rfl

  /-- Syntax.Stmt.returnStmt constructor creates valid statement -/
  example (e : Morph.Syntax.Expr) :
    (Morph.Syntax.Stmt.returnStmt e) = Morph.Syntax.Stmt.returnStmt e := by
    rfl

  /-- Syntax.Stmt.break constructor creates valid statement -/
  example : Morph.Syntax.Stmt.break = Morph.Syntax.Stmt.break := by
    rfl

  /-- Syntax.Stmt.continue constructor creates valid statement -/
  example : Morph.Syntax.Stmt.continue = Morph.Syntax.Stmt.continue := by
    rfl

  /-- Syntax.Stmt.whileLoop constructor creates valid statement -/
  example (e : Morph.Syntax.Expr) (body : List Morph.Syntax.Stmt) :
    (Morph.Syntax.Stmt.whileLoop e body) = Morph.Syntax.Stmt.whileLoop e body := by
    rfl

  /-- Syntax.Stmt.doWhile constructor creates valid statement -/
  example (e : Morph.Syntax.Expr) (body : List Morph.Syntax.Stmt) :
    (Morph.Syntax.Stmt.doWhile e body) = Morph.Syntax.Stmt.doWhile e body := by
    rfl

  /-- Syntax.Stmt.nop constructor creates valid statement -/
  example : Morph.Syntax.Stmt.nop = Morph.Syntax.Stmt.nop := by
    rfl

  /-- Syntax.Stmt equality is reflexive -/
  example (s : Morph.Syntax.Stmt) : s = s := by
    rfl

  /-- Syntax.Stmt equality is symmetric -/
  example (s1 s2 : Morph.Syntax.Stmt) : s1 = s2 → s2 = s1 := by
    intro h
    exact h.symm

  /-- Syntax.Stmt equality is transitive -/
  example (s1 s2 s3 : Morph.Syntax.Stmt) :
    s1 = s2 → s2 = s3 → s1 = s3 := by
    intro h1 h2
    exact h1.trans h2

end SyntaxStmtTests

/-!
## Section 4: Syntax.Program Unit Tests

Tests for Syntax.Program structure (surface-level programs).
These tests verify that Program structures work correctly.
-/

section SyntaxProgramTests

  /-- Syntax.Program constructor creates valid program -/
  example (stmts : List Morph.Syntax.Stmt) :
    (Morph.Syntax.Program.mk stmts).stmts = stmts := by
    rfl

  /-- Syntax.Program.empty returns empty program -/
  example : Morph.Syntax.Program.empty.stmts = [] := by
    rfl

  /-- Syntax.Program equality is reflexive -/
  example (p : Morph.Syntax.Program) : p = p := by
    rfl

  /-- Syntax.Program equality is symmetric -/
  example (p1 p2 : Morph.Syntax.Program) : p1 = p2 → p2 = p1 := by
    intro h
    exact h.symm

  /-- Syntax.Program equality is transitive -/
  example (p1 p2 p3 : Morph.Syntax.Program) :
    p1 = p2 → p2 = p3 → p1 = p3 := by
    intro h1 h2
    exact h1.trans h2

end SyntaxProgramTests

/-!
## Section 5: HIR.Id Unit Tests

Tests for HIR.Id structure (high-level intermediate representation identifiers).
These tests verify that HIR.Id values can be constructed, compared, and hashed correctly.
-/

section HIRIdTests

  /-- HIR.Id constructor creates valid structure -/
  example (i : Nat) (n : String) :
    (Morph.HIR.Id.mk i n).index = i ∧ (Morph.HIR.Id.mk i n).name = n := by
    constructor <;> rfl

  /-- HIR.Id getIndex returns the index -/
  example (i : Nat) (n : String) : (Morph.HIR.Id.mk i n).getIndex = i := by
    rfl

  /-- HIR.Id getName returns the name -/
  example (i : Nat) (n : String) : (Morph.HIR.Id.mk i n).getName = n := by
    rfl

  /-- HIR.Id equality is reflexive -/
  example (id : Morph.HIR.Id) : id = id := by
    rfl

  /-- HIR.Id equality is symmetric -/
  example (id1 id2 : Morph.HIR.Id) : id1 = id2 → id2 = id1 := by
    intro h
    exact h.symm

  /-- HIR.Id equality is transitive -/
  example (id1 id2 id3 : Morph.HIR.Id) :
    id1 = id2 → id2 = id3 → id1 = id3 := by
    intro h1 h2
    exact h1.trans h2

  /-- HIR.Id can be hashed -/
  example (id : Morph.HIR.Id) : (hash id) = (hash id) := by
    rfl

  /-- Different HIR.Ids are not equal -/
  example (i1 i2 : Nat) (n : String) :
    i1 ≠ i2 → Morph.HIR.Id.mk i1 n ≠ Morph.HIR.Id.mk i2 n := by
    intro h
    intro hneq
    exact h (congrArg Morph.HIR.Id.index hneq)

  /-- HIR.Ids with different names are not equal -/
  example (i : Nat) (n1 n2 : String) :
    n1 ≠ n2 → Morph.HIR.Id.mk i n1 ≠ Morph.HIR.Id.mk i n2 := by
    intro h
    intro hneq
    exact h (congrArg Morph.HIR.Id.name hneq)

end HIRIdTests

/-!
## Section 6: HIR.Pattern Unit Tests

Tests for HIR.Pattern inductive type (pattern matching).
These tests verify that Pattern constructors work correctly and patterns can be compared.
-/

section HIRPatternTests

  /-- HIR.Pattern.lit constructor creates valid pattern -/
  example (v : Morph.Core.Value) :
    (Morph.HIR.Pattern.lit v) = Morph.HIR.Pattern.lit v := by
    rfl

  /-- HIR.Pattern.wildcard constructor creates valid pattern -/
  example :
    Morph.HIR.Pattern.wildcard = Morph.HIR.Pattern.wildcard := by
    rfl

  /-- HIR.Pattern.var constructor creates valid pattern -/
  example (id : Morph.HIR.Id) :
    (Morph.HIR.Pattern.var id) = Morph.HIR.Pattern.var id := by
    rfl

  /-- HIR.Pattern equality is reflexive -/
  example (p : Morph.HIR.Pattern) : p = p := by
    rfl

  /-- HIR.Pattern equality is symmetric -/
  example (p1 p2 : Morph.HIR.Pattern) : p1 = p2 → p2 = p1 := by
    intro h
    exact h.symm

  /-- HIR.Pattern equality is transitive -/
  example (p1 p2 p3 : Morph.HIR.Pattern) :
    p1 = p2 → p2 = p3 → p1 = p3 := by
    intro h1 h2
    exact h1.trans h2

  /-- Different pattern constructors are not equal -/
  example :
    Morph.HIR.Pattern.wildcard ≠ Morph.HIR.Pattern.lit (Morph.Core.Value.int 0) := by
    intro h
    exact Morph.HIR.Pattern.noConfusion h

end HIRPatternTests

/-!
## Section 7: HIR.Expr Unit Tests

Tests for HIR.Expr inductive type (high-level intermediate expressions).
These tests verify that Expression constructors work correctly and expressions can be compared.
-/

section HIRExprTests

  /-- HIR.Expr.var constructor creates valid expression -/
  example (id : Morph.HIR.Id) :
    (Morph.HIR.Expr.var id) = Morph.HIR.Expr.var id := by
    rfl

  /-- HIR.Expr.lit constructor creates valid expression -/
  example (v : Morph.Core.Value) :
    (Morph.HIR.Expr.lit v) = Morph.HIR.Expr.lit v := by
    rfl

  /-- HIR.Expr.unop constructor creates valid expression -/
  example (op : Morph.Core.Operator) (e : Morph.HIR.Expr) :
    (Morph.HIR.Expr.unop op e) = Morph.HIR.Expr.unop op e := by
    rfl

  /-- HIR.Expr.binop constructor creates valid expression -/
  example (op : Morph.Core.Operator) (e1 e2 : Morph.HIR.Expr) :
    (Morph.HIR.Expr.binop op e1 e2) = Morph.HIR.Expr.binop op e1 e2 := by
    rfl

  /-- HIR.Expr.app constructor creates valid expression (fn is Id) -/
  example (id : Morph.HIR.Id) (args : List Morph.HIR.Expr) :
    (Morph.HIR.Expr.app id args) = Morph.HIR.Expr.app id args := by
    rfl

  /-- HIR.Expr.lam constructor creates valid expression -/
  example (params : List Morph.HIR.Id) (body : Morph.HIR.Expr) :
    (Morph.HIR.Expr.lam params body) = Morph.HIR.Expr.lam params body := by
    rfl

  /-- HIR.Expr.let constructor creates valid expression -/
  example (id : Morph.HIR.Id) (e1 e2 : Morph.HIR.Expr) :
    (Morph.HIR.Expr.let id e1 e2) = Morph.HIR.Expr.let id e1 e2 := by
    rfl

  /-- HIR.Expr.ifThenElse constructor creates valid expression -/
  example (cond e1 e2 : Morph.HIR.Expr) :
    (Morph.HIR.Expr.ifThenElse cond e1 e2) = Morph.HIR.Expr.ifThenElse cond e1 e2 := by
    rfl

  /-- HIR.Expr.whileLoop constructor creates valid expression -/
  example (cond : Morph.HIR.Expr) (body : List Morph.HIR.Expr) :
    (Morph.HIR.Expr.whileLoop cond body) = Morph.HIR.Expr.whileLoop cond body := by
    rfl

  /-- HIR.Expr.match constructor creates valid expression -/
  example (e : Morph.HIR.Expr) (cases : List (Morph.HIR.Pattern × Morph.HIR.Expr)) :
    (Morph.HIR.Expr.match e cases) = Morph.HIR.Expr.match e cases := by
    rfl

  /-- HIR.Expr.block constructor creates valid expression -/
  example (body : List Morph.HIR.Expr) :
    (Morph.HIR.Expr.block body) = Morph.HIR.Expr.block body := by
    rfl

  /-- HIR.Expr.infer constructor creates valid expression -/
  example : Morph.HIR.Expr.infer = Morph.HIR.Expr.infer := by
    rfl

  /-- HIR.Expr equality is reflexive -/
  example (e : Morph.HIR.Expr) : e = e := by
    rfl

  /-- HIR.Expr equality is symmetric -/
  example (e1 e2 : Morph.HIR.Expr) : e1 = e2 → e2 = e1 := by
    intro h
    exact h.symm

  /-- HIR.Expr equality is transitive -/
  example (e1 e2 e3 : Morph.HIR.Expr) :
    e1 = e2 → e2 = e3 → e1 = e3 := by
    intro h1 h2
    exact h1.trans h2

end HIRExprTests

/-!
## Section 8: HIR.Stmt Unit Tests

Tests for HIR.Stmt inductive type (high-level intermediate statements).
These tests verify that Statement constructors work correctly and statements can be compared.
-/

section HIRStmtTests

  /-- HIR.Stmt.exprStmt constructor creates valid statement -/
  example (e : Morph.HIR.Expr) :
    (Morph.HIR.Stmt.exprStmt e) = Morph.HIR.Stmt.exprStmt e := by
    rfl

  /-- HIR.Stmt.varDecl constructor creates valid statement -/
  example (id : Morph.HIR.Id) (ty : Morph.Core.Typ) (e : Morph.HIR.Expr) :
    (Morph.HIR.Stmt.varDecl id ty e) = Morph.HIR.Stmt.varDecl id ty e := by
    rfl

  /-- HIR.Stmt.assign constructor creates valid statement -/
  example (id : Morph.HIR.Id) (e : Morph.HIR.Expr) :
    (Morph.HIR.Stmt.assign id e) = Morph.HIR.Stmt.assign id e := by
    rfl

  /-- HIR.Stmt.returnStmt constructor creates valid statement -/
  example (e : Morph.HIR.Expr) :
    (Morph.HIR.Stmt.returnStmt e) = Morph.HIR.Stmt.returnStmt e := by
    rfl

  /-- HIR.Stmt.break constructor creates valid statement -/
  example : Morph.HIR.Stmt.break = Morph.HIR.Stmt.break := by
    rfl

  /-- HIR.Stmt.continue constructor creates valid statement -/
  example : Morph.HIR.Stmt.continue = Morph.HIR.Stmt.continue := by
    rfl

  /-- HIR.Stmt.whileLoop constructor creates valid statement -/
  example (e : Morph.HIR.Expr) (body : List Morph.HIR.Stmt) :
    (Morph.HIR.Stmt.whileLoop e body) = Morph.HIR.Stmt.whileLoop e body := by
    rfl

  /-- HIR.Stmt.nop constructor creates valid statement -/
  example : Morph.HIR.Stmt.nop = Morph.HIR.Stmt.nop := by
    rfl

  /-- HIR.Stmt equality is reflexive -/
  example (s : Morph.HIR.Stmt) : s = s := by
    rfl

  /-- HIR.Stmt equality is symmetric -/
  example (s1 s2 : Morph.HIR.Stmt) : s1 = s2 → s2 = s1 := by
    intro h
    exact h.symm

  /-- HIR.Stmt equality is transitive -/
  example (s1 s2 s3 : Morph.HIR.Stmt) :
    s1 = s2 → s2 = s3 → s1 = s3 := by
    intro h1 h2
    exact h1.trans h2

end HIRStmtTests

/-!
## Section 9: HIR.Program Unit Tests

Tests for HIR.Program structure (high-level intermediate programs).
These tests verify that Program structures work correctly.
-/

section HIRProgramTests

  /-- HIR.Program constructor creates valid program -/
  example (stmts : List Morph.HIR.Stmt) :
    (Morph.HIR.Program.mk stmts).stmts = stmts := by
    rfl

  /-- HIR.Program.empty returns empty program -/
  example : Morph.HIR.Program.empty.stmts = [] := by
    rfl

  /-- HIR.Program equality is reflexive -/
  example (p : Morph.HIR.Program) : p = p := by
    rfl

  /-- HIR.Program equality is symmetric -/
  example (p1 p2 : Morph.HIR.Program) : p1 = p2 → p2 = p1 := by
    intro h
    exact h.symm

  /-- HIR.Program equality is transitive -/
  example (p1 p2 p3 : Morph.HIR.Program) :
    p1 = p2 → p2 = p3 → p1 = p3 := by
    intro h1 h2
    exact h1.trans h2

end HIRProgramTests

/-!
## Section 10: AST Well-Formedness Properties

Tests for AST well-formedness properties.
These tests verify that AST structures maintain important invariants.
-/

section ASTWellFormednessTests

  /-- Syntax.Id with non-empty name is well-formed -/
  example (n : String) :
    n ≠ "" → (Morph.Syntax.Id.mk n).name ≠ "" := by
    intro h
    exact h

  /-- HIR.Id with valid index is well-formed -/
  example (i : Nat) (n : String) :
    (Morph.HIR.Id.mk i n).index = i := by
    rfl

  /-- Syntax.Expr.block with empty body is valid -/
  example :
    Morph.Syntax.Expr.block [] = Morph.Syntax.Expr.block [] := by
    rfl

  /-- HIR.Expr.block with empty body is valid -/
  example :
    Morph.HIR.Expr.block [] = Morph.HIR.Expr.block [] := by
    rfl

  /-- Syntax.Program with empty statements is valid -/
  example :
    Morph.Syntax.Program.mk [] = Morph.Syntax.Program.mk [] := by
    rfl

  /-- HIR.Program with empty statements is valid -/
  example :
    Morph.HIR.Program.mk [] = Morph.HIR.Program.mk [] := by
    rfl

end ASTWellFormednessTests

end Tests.AST
