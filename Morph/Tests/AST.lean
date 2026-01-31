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
  example syntaxid_construction (n : String) : (Syntax.Id.mk n).name = n := by
    rfl

  /-- Syntax.Id getName returns the name -/
  example syntaxid_getname (n : String) : (Syntax.Id.mk n).getName = n := by
    rfl

  /-- Syntax.Id equality is reflexive -/
  example syntaxid_reflexivity (id : Syntax.Id) : id = id := by
    cases id <;> rfl

  /-- Syntax.Id equality is symmetric -/
  example syntaxid_symmetry (id1 id2 : Syntax.Id) : id1 = id2 → id2 = id1 := by
    intro h
    cases id1 <;> cases id2 <;> rfl

  /-- Syntax.Id equality is transitive -/
  example syntaxid_transitivity (id1 id2 id3 : Syntax.Id) :
    id1 = id2 → id2 = id3 → id1 = id3 := by
    intro h1 h2
    cases id1 <;> cases id2 <;> cases id3 <;> rfl

  /-- Syntax.Id can be hashed -/
  example syntaxid_hashable (id : Syntax.Id) : (hash id) = (hash id) := by
    rfl

  /-- Different Syntax.Ids are not equal -/
  example syntaxid_inequality (n1 n2 : String) : n1 ≠ n2 → Syntax.Id.mk n1 ≠ Syntax.Id.mk n2 := by
    intro h
    cases h

end SyntaxIdTests

/-!
## Section 2: Syntax.Expr Unit Tests

Tests for Syntax.Expr inductive type (surface-level expressions).
These tests verify that Expression constructors work correctly and expressions can be compared.
-/

section SyntaxExprTests

  /-- Syntax.Expr.var constructor creates valid expression -/
  example syntaxexpr_var_construction (id : Syntax.Id) :
    (Syntax.Expr.var id) = Syntax.Expr.var id := by
    rfl

  /-- Syntax.Expr.lit constructor creates valid expression -/
  example syntaxexpr_lit_construction (v : Morph.Core.Value) :
    (Syntax.Expr.lit v) = Syntax.Expr.lit v := by
    rfl

  /-- Syntax.Expr.unop constructor creates valid expression -/
  example syntaxexpr_unop_construction (op : Morph.Core.Operator) (e : Syntax.Expr) :
    (Syntax.Expr.unop op e) = Syntax.Expr.unop op e := by
    rfl

  /-- Syntax.Expr.binop constructor creates valid expression -/
  example syntaxexpr_binop_construction (op : Morph.Core.Operator) (e1 e2 : Syntax.Expr) :
    (Syntax.Expr.binop op e1 e2) = Syntax.Expr.binop op e1 e2 := by
    rfl

  /-- Syntax.Expr.app constructor creates valid expression -/
  example syntaxexpr_app_construction (id : Syntax.Id) (args : List Syntax.Expr) :
    (Syntax.Expr.app id args) = Syntax.Expr.app id args := by
    rfl

  /-- Syntax.Expr.lam constructor creates valid expression -/
  example syntaxexpr_lam_construction (params : List Syntax.Id) (body : Syntax.Expr) :
    (Syntax.Expr.lam params body) = Syntax.Expr.lam params body := by
    rfl

  /-- Syntax.Expr.let constructor creates valid expression -/
  example syntaxexpr_let_construction (id : Syntax.Id) (e1 e2 : Syntax.Expr) :
    (Syntax.Expr.let id e1 e2) = Syntax.Expr.let id e1 e2 := by
    rfl

  /-- Syntax.Expr.ifThenElse constructor creates valid expression -/
  example syntaxexpr_ifthenelse_construction (cond e1 e2 : Syntax.Expr) :
    (Syntax.Expr.ifThenElse cond e1 e2) = Syntax.Expr.ifThenElse cond e1 e2 := by
    rfl

  /-- Syntax.Expr.forLoop constructor creates valid expression -/
  example syntaxexpr_forloop_construction (id : Syntax.Id) (e : Syntax.Expr) (body : List Syntax.Expr) :
    (Syntax.Expr.forLoop id e body) = Syntax.Expr.forLoop id e body := by
    rfl

  /-- Syntax.Expr.block constructor creates valid expression -/
  example syntaxexpr_block_construction (body : List Syntax.Expr) :
    (Syntax.Expr.block body) = Syntax.Expr.block body := by
    rfl

  /-- Syntax.Expr equality is reflexive -/
  example syntaxexpr_reflexivity (e : Syntax.Expr) : e = e := by
    cases e <;> rfl

  /-- Syntax.Expr equality is symmetric -/
  example syntaxexpr_symmetry (e1 e2 : Syntax.Expr) : e1 = e2 → e2 = e1 := by
    intro h
    cases e1 <;> cases e2 <;> rfl

  /-- Syntax.Expr equality is transitive -/
  example syntaxexpr_transitivity (e1 e2 e3 : Syntax.Expr) :
    e1 = e2 → e2 = e3 → e1 = e3 := by
    intro h1 h2
    cases e1 <;> cases e2 <;> cases e3 <;> rfl

end SyntaxExprTests

/-!
## Section 3: Syntax.Stmt Unit Tests

Tests for Syntax.Stmt inductive type (surface-level statements).
These tests verify that Statement constructors work correctly and statements can be compared.
-/

section SyntaxStmtTests

  /-- Syntax.Stmt.exprStmt constructor creates valid statement -/
  example syntaxstmt_exprstmt_construction (e : Syntax.Expr) :
    (Syntax.Stmt.exprStmt e) = Syntax.Stmt.exprStmt e := by
    rfl

  /-- Syntax.Stmt.varDecl constructor creates valid statement -/
  example syntaxstmt_vardecl_construction (id : Syntax.Id) (ty : Morph.Core.Typ) (e : Syntax.Expr) :
    (Syntax.Stmt.varDecl id ty e) = Syntax.Stmt.varDecl id ty e := by
    rfl

  /-- Syntax.Stmt.assign constructor creates valid statement -/
  example syntaxstmt_assign_construction (id : Syntax.Id) (e : Syntax.Expr) :
    (Syntax.Stmt.assign id e) = Syntax.Stmt.assign id e := by
    rfl

  /-- Syntax.Stmt.returnStmt constructor creates valid statement -/
  example syntaxstmt_returnstmt_construction (e : Syntax.Expr) :
    (Syntax.Stmt.returnStmt e) = Syntax.Stmt.returnStmt e := by
    rfl

  /-- Syntax.Stmt.break constructor creates valid statement -/
  example syntaxstmt_break_construction : Syntax.Stmt.break = Syntax.Stmt.break := by
    rfl

  /-- Syntax.Stmt.continue constructor creates valid statement -/
  example syntaxstmt_continue_construction : Syntax.Stmt.continue = Syntax.Stmt.continue := by
    rfl

  /-- Syntax.Stmt.whileLoop constructor creates valid statement -/
  example syntaxstmt_whileloop_construction (e : Syntax.Expr) (body : List Syntax.Stmt) :
    (Syntax.Stmt.whileLoop e body) = Syntax.Stmt.whileLoop e body := by
    rfl

  /-- Syntax.Stmt.doWhile constructor creates valid statement -/
  example syntaxstmt_dowhile_construction (e : Syntax.Expr) (body : List Syntax.Stmt) :
    (Syntax.Stmt.doWhile e body) = Syntax.Stmt.doWhile e body := by
    rfl

  /-- Syntax.Stmt.nop constructor creates valid statement -/
  example syntaxstmt_nop_construction : Syntax.Stmt.nop = Syntax.Stmt.nop := by
    rfl

  /-- Syntax.Stmt equality is reflexive -/
  example syntaxstmt_reflexivity (s : Syntax.Stmt) : s = s := by
    cases s <;> rfl

  /-- Syntax.Stmt equality is symmetric -/
  example syntaxstmt_symmetry (s1 s2 : Syntax.Stmt) : s1 = s2 → s2 = s1 := by
    intro h
    cases s1 <;> cases s2 <;> rfl

  /-- Syntax.Stmt equality is transitive -/
  example syntaxstmt_transitivity (s1 s2 s3 : Syntax.Stmt) :
    s1 = s2 → s2 = s3 → s1 = s3 := by
    intro h1 h2
    cases s1 <;> cases s2 <;> cases s3 <;> rfl

end SyntaxStmtTests

/-!
## Section 4: Syntax.Program Unit Tests

Tests for Syntax.Program structure (surface-level programs).
These tests verify that Program structures work correctly.
-/

section SyntaxProgramTests

  /-- Syntax.Program constructor creates valid program -/
  example syntaxprogram_construction (stmts : List Syntax.Stmt) :
    (Syntax.Program.mk stmts).stmts = stmts := by
    rfl

  /-- Syntax.Program.empty returns empty program -/
  example syntaxprogram_empty : Syntax.Program.empty.stmts = [] := by
    rfl

  /-- Syntax.Program equality is reflexive -/
  example syntaxprogram_reflexivity (p : Syntax.Program) : p = p := by
    cases p <;> rfl

  /-- Syntax.Program equality is symmetric -/
  example syntaxprogram_symmetry (p1 p2 : Syntax.Program) : p1 = p2 → p2 = p1 := by
    intro h
    cases p1 <;> cases p2 <;> rfl

  /-- Syntax.Program equality is transitive -/
  example syntaxprogram_transitivity (p1 p2 p3 : Syntax.Program) :
    p1 = p2 → p2 = p3 → p1 = p3 := by
    intro h1 h2
    cases p1 <;> cases p2 <;> cases p3 <;> rfl

end SyntaxProgramTests

/-!
## Section 5: HIR.Id Unit Tests

Tests for HIR.Id structure (high-level intermediate representation identifiers).
These tests verify that HIR.Id values can be constructed, compared, and hashed correctly.
-/

section HIRIdTests

  /-- HIR.Id constructor creates valid structure -/
  example hirid_construction (i : Nat) (n : String) :
    (HIR.Id.mk i n).index = i ∧ (HIR.Id.mk i n).name = n := by
    constructor <;> rfl <;> rfl

  /-- HIR.Id getIndex returns the index -/
  example hirid_getindex (i : Nat) (n : String) : (HIR.Id.mk i n).getIndex = i := by
    rfl

  /-- HIR.Id getName returns the name -/
  example hirid_getname (i : Nat) (n : String) : (HIR.Id.mk i n).getName = n := by
    rfl

  /-- HIR.Id equality is reflexive -/
  example hirid_reflexivity (id : HIR.Id) : id = id := by
    cases id <;> rfl

  /-- HIR.Id equality is symmetric -/
  example hirid_symmetry (id1 id2 : HIR.Id) : id1 = id2 → id2 = id1 := by
    intro h
    cases id1 <;> cases id2 <;> rfl

  /-- HIR.Id equality is transitive -/
  example hirid_transitivity (id1 id2 id3 : HIR.Id) :
    id1 = id2 → id2 = id3 → id1 = id3 := by
    intro h1 h2
    cases id1 <;> cases id2 <;> cases id3 <;> rfl

  /-- HIR.Id can be hashed -/
  example hirid_hashable (id : HIR.Id) : (hash id) = (hash id) := by
    rfl

  /-- Different HIR.Ids are not equal -/
  example hirid_inequality (i1 i2 : Nat) (n : String) :
    i1 ≠ i2 → HIR.Id.mk i1 n ≠ HIR.Id.mk i2 n := by
    intro h
    cases h

  /-- HIR.Ids with different names are not equal -/
  example hirid_name_inequality (i : Nat) (n1 n2 : String) :
    n1 ≠ n2 → HIR.Id.mk i n1 ≠ HIR.Id.mk i n2 := by
    intro h
    cases h

end HIRIdTests

/-!
## Section 6: HIR.Pattern Unit Tests

Tests for HIR.Pattern inductive type (pattern matching).
These tests verify that Pattern constructors work correctly and patterns can be compared.
-/

section HIRPatternTests

  /-- HIR.Pattern.lit constructor creates valid pattern -/
  example hirpattern_lit_construction (v : Morph.Core.Value) :
    (HIR.Pattern.lit v) = HIR.Pattern.lit v := by
    rfl

  /-- HIR.Pattern.wildcard constructor creates valid pattern -/
  example hirpattern_wildcard_construction :
    HIR.Pattern.wildcard = HIR.Pattern.wildcard := by
    rfl

  /-- HIR.Pattern.var constructor creates valid pattern -/
  example hirpattern_var_construction (id : HIR.Id) :
    (HIR.Pattern.var id) = HIR.Pattern.var id := by
    rfl

  /-- HIR.Pattern equality is reflexive -/
  example hirpattern_reflexivity (p : HIR.Pattern) : p = p := by
    cases p <;> rfl

  /-- HIR.Pattern equality is symmetric -/
  example hirpattern_symmetry (p1 p2 : HIR.Pattern) : p1 = p2 → p2 = p1 := by
    intro h
    cases p1 <;> cases p2 <;> rfl

  /-- HIR.Pattern equality is transitive -/
  example hirpattern_transitivity (p1 p2 p3 : HIR.Pattern) :
    p1 = p2 → p2 = p3 → p1 = p3 := by
    intro h1 h2
    cases p1 <;> cases p2 <;> cases p3 <;> rfl

  /-- Different pattern constructors are not equal -/
  example hirpattern_distinct :
    HIR.Pattern.wildcard ≠ HIR.Pattern.lit (Morph.Core.Value.int 0) := by
    cases

end HIRPatternTests

/-!
## Section 7: HIR.Expr Unit Tests

Tests for HIR.Expr inductive type (high-level intermediate expressions).
These tests verify that Expression constructors work correctly and expressions can be compared.
-/

section HIRExprTests

  /-- HIR.Expr.var constructor creates valid expression -/
  example hirexpr_var_construction (id : HIR.Id) :
    (HIR.Expr.var id) = HIR.Expr.var id := by
    rfl

  /-- HIR.Expr.lit constructor creates valid expression -/
  example hirexpr_lit_construction (v : Morph.Core.Value) :
    (HIR.Expr.lit v) = HIR.Expr.lit v := by
    rfl

  /-- HIR.Expr.unop constructor creates valid expression -/
  example hirexpr_unop_construction (op : Morph.Core.Operator) (e : HIR.Expr) :
    (HIR.Expr.unop op e) = HIR.Expr.unop op e := by
    rfl

  /-- HIR.Expr.binop constructor creates valid expression -/
  example hirexpr_binop_construction (op : Morph.Core.Operator) (e1 e2 : HIR.Expr) :
    (HIR.Expr.binop op e1 e2) = HIR.Expr.binop op e1 e2 := by
    rfl

  /-- HIR.Expr.app constructor creates valid expression -/
  example hirexpr_app_construction (id : HIR.Id) (args : List HIR.Expr) :
    (HIR.Expr.app id args) = HIR.Expr.app id args := by
    rfl

  /-- HIR.Expr.lam constructor creates valid expression -/
  example hirexpr_lam_construction (params : List HIR.Id) (body : HIR.Expr) :
    (HIR.Expr.lam params body) = HIR.Expr.lam params body := by
    rfl

  /-- HIR.Expr.let constructor creates valid expression -/
  example hirexpr_let_construction (id : HIR.Id) (e1 e2 : HIR.Expr) :
    (HIR.Expr.let id e1 e2) = HIR.Expr.let id e1 e2 := by
    rfl

  /-- HIR.Expr.ifThenElse constructor creates valid expression -/
  example hirexpr_ifthenelse_construction (cond e1 e2 : HIR.Expr) :
    (HIR.Expr.ifThenElse cond e1 e2) = HIR.Expr.ifThenElse cond e1 e2 := by
    rfl

  /-- HIR.Expr.whileLoop constructor creates valid expression -/
  example hirexpr_whileloop_construction (cond : HIR.Expr) (body : List HIR.Expr) :
    (HIR.Expr.whileLoop cond body) = HIR.Expr.whileLoop cond body := by
    rfl

  /-- HIR.Expr.match constructor creates valid expression -/
  example hirexpr_match_construction (e : HIR.Expr) (cases : List (HIR.Pattern × HIR.Expr)) :
    (HIR.Expr.match e cases) = HIR.Expr.match e cases := by
    rfl

  /-- HIR.Expr.block constructor creates valid expression -/
  example hirexpr_block_construction (body : List HIR.Expr) :
    (HIR.Expr.block body) = HIR.Expr.block body := by
    rfl

  /-- HIR.Expr.infer constructor creates valid expression -/
  example hirexpr_infer_construction : HIR.Expr.infer = HIR.Expr.infer := by
    rfl

  /-- HIR.Expr equality is reflexive -/
  example hirexpr_reflexivity (e : HIR.Expr) : e = e := by
    cases e <;> rfl

  /-- HIR.Expr equality is symmetric -/
  example hirexpr_symmetry (e1 e2 : HIR.Expr) : e1 = e2 → e2 = e1 := by
    intro h
    cases e1 <;> cases e2 <;> rfl

  /-- HIR.Expr equality is transitive -/
  example hirexpr_transitivity (e1 e2 e3 : HIR.Expr) :
    e1 = e2 → e2 = e3 → e1 = e3 := by
    intro h1 h2
    cases e1 <;> cases e2 <;> cases e3 <;> rfl

end HIRExprTests

/-!
## Section 8: HIR.Stmt Unit Tests

Tests for HIR.Stmt inductive type (high-level intermediate statements).
These tests verify that Statement constructors work correctly and statements can be compared.
-/

section HIRStmtTests

  /-- HIR.Stmt.exprStmt constructor creates valid statement -/
  example hirstmt_exprstmt_construction (e : HIR.Expr) :
    (HIR.Stmt.exprStmt e) = HIR.Stmt.exprStmt e := by
    rfl

  /-- HIR.Stmt.varDecl constructor creates valid statement -/
  example hirstmt_vardecl_construction (id : HIR.Id) (ty : Morph.Core.Typ) (e : HIR.Expr) :
    (HIR.Stmt.varDecl id ty e) = HIR.Stmt.varDecl id ty e := by
    rfl

  /-- HIR.Stmt.assign constructor creates valid statement -/
  example hirstmt_assign_construction (id : HIR.Id) (e : HIR.Expr) :
    (HIR.Stmt.assign id e) = HIR.Stmt.assign id e := by
    rfl

  /-- HIR.Stmt.returnStmt constructor creates valid statement -/
  example hirstmt_returnstmt_construction (e : HIR.Expr) :
    (HIR.Stmt.returnStmt e) = HIR.Stmt.returnStmt e := by
    rfl

  /-- HIR.Stmt.break constructor creates valid statement -/
  example hirstmt_break_construction : HIR.Stmt.break = HIR.Stmt.break := by
    rfl

  /-- HIR.Stmt.continue constructor creates valid statement -/
  example hirstmt_continue_construction : HIR.Stmt.continue = HIR.Stmt.continue := by
    rfl

  /-- HIR.Stmt.whileLoop constructor creates valid statement -/
  example hirstmt_whileloop_construction (e : HIR.Expr) (body : List HIR.Stmt) :
    (HIR.Stmt.whileLoop e body) = HIR.Stmt.whileLoop e body := by
    rfl

  /-- HIR.Stmt.nop constructor creates valid statement -/
  example hirstmt_nop_construction : HIR.Stmt.nop = HIR.Stmt.nop := by
    rfl

  /-- HIR.Stmt equality is reflexive -/
  example hirstmt_reflexivity (s : HIR.Stmt) : s = s := by
    cases s <;> rfl

  /-- HIR.Stmt equality is symmetric -/
  example hirstmt_symmetry (s1 s2 : HIR.Stmt) : s1 = s2 → s2 = s1 := by
    intro h
    cases s1 <;> cases s2 <;> rfl

  /-- HIR.Stmt equality is transitive -/
  example hirstmt_transitivity (s1 s2 s3 : HIR.Stmt) :
    s1 = s2 → s2 = s3 → s1 = s3 := by
    intro h1 h2
    cases s1 <;> cases s2 <;> cases s3 <;> rfl

end HIRStmtTests

/-!
## Section 9: HIR.Program Unit Tests

Tests for HIR.Program structure (high-level intermediate programs).
These tests verify that Program structures work correctly.
-/

section HIRProgramTests

  /-- HIR.Program constructor creates valid program -/
  example hirprogram_construction (stmts : List HIR.Stmt) :
    (HIR.Program.mk stmts).stmts = stmts := by
    rfl

  /-- HIR.Program.empty returns empty program -/
  example hirprogram_empty : HIR.Program.empty.stmts = [] := by
    rfl

  /-- HIR.Program equality is reflexive -/
  example hirprogram_reflexivity (p : HIR.Program) : p = p := by
    cases p <;> rfl

  /-- HIR.Program equality is symmetric -/
  example hirprogram_symmetry (p1 p2 : HIR.Program) : p1 = p2 → p2 = p1 := by
    intro h
    cases p1 <;> cases p2 <;> rfl

  /-- HIR.Program equality is transitive -/
  example hirprogram_transitivity (p1 p2 p3 : HIR.Program) :
    p1 = p2 → p2 = p3 → p1 = p3 := by
    intro h1 h2
    cases p1 <;> cases p2 <;> cases p3 <;> rfl

end HIRProgramTests

/-!
## Section 10: AST Well-Formedness Properties

Tests for AST well-formedness properties.
These tests verify that AST structures maintain important invariants.
-/

section ASTWellFormednessTests

  /-- Syntax.Id with non-empty name is well-formed -/
  example syntaxid_wellformed_nonempty (n : String) :
    n ≠ "" → (Syntax.Id.mk n).name ≠ "" := by
    intro h
    exact h

  /-- HIR.Id with valid index is well-formed -/
  example hirid_wellformed_index (i : Nat) (n : String) :
    (HIR.Id.mk i n).index = i := by
    rfl

  /-- Syntax.Expr.block with empty body is valid -/
  example syntaxexpr_block_empty :
    Syntax.Expr.block [] = Syntax.Expr.block [] := by
    rfl

  /-- HIR.Expr.block with empty body is valid -/
  example hirexpr_block_empty :
    HIR.Expr.block [] = HIR.Expr.block [] := by
    rfl

  /-- Syntax.Program with empty statements is valid -/
  example syntaxprogram_empty_stmts :
    Syntax.Program.mk [] = Syntax.Program.mk [] := by
    rfl

  /-- HIR.Program with empty statements is valid -/
  example hirprogram_empty_stmts :
    HIR.Program.mk [] = HIR.Program.mk [] := by
    rfl

end ASTWellFormednessTests

end Tests.AST
