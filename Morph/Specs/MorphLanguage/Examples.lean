/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.MorphLanguage.Lemmas

namespace Morph.Specs.MorphLanguage

open Morph.Syntax

/-!
## Examples

Concrete examples demonstrating the MorphLanguage specification.
-/

-- Edit operations
example : applyEdit "" (EditOperation.replace "hello") = "hello" := rfl

example : applyEdit "hello" (EditOperation.insert " world") = "hello world" := rfl

example : applyEdit "temp" EditOperation.delete = "" := rfl

example : applyEdit "data" (EditOperation.move 0 3) = "data" := rfl

-- Parsing: `parseCode` delegates to the total frontend parser, which accepts
-- expressions and rejects malformed text. (It does not yet parse statement
-- syntax such as `let x = 5`; that is a frontend gap, not a spec stub.)
example : (parseCode "1 + 2").isSome = true := by native_decide

example : (parseCode "").isNone = true := by native_decide

example : (parseCode "(").isNone = true := by native_decide

example : (parseCode "let x = 5").isNone = true := by native_decide

-- AST editing
example : applyEditToAst Morph.Syntax.Program.empty EditOperation.delete =
    some Morph.Syntax.Program.empty := rfl

example : (applyEditToAst Morph.Syntax.Program.empty
    (EditOperation.replace "1 + 2")).isSome = true := by native_decide

example : (applyEditToAst Morph.Syntax.Program.empty
    (EditOperation.insert "1")).isSome = true := by native_decide

example : (applyEditToAst Morph.Syntax.Program.empty
    (EditOperation.insert "(")).isNone = true := by native_decide

example : (applyEditToAst Morph.Syntax.Program.empty
    (EditOperation.move 0 1)).isSome = true := rfl

-- Statement reordering
example : moveStmt 0 1 [.exprStmt (.lit (.int 1)), .exprStmt (.lit (.int 2))] =
    [.exprStmt (.lit (.int 2)), .exprStmt (.lit (.int 1))] := by
  unfold moveStmt
  simp

example : moveStmt 7 0 [.exprStmt (.lit (.int 1))] =
    [.exprStmt (.lit (.int 1))] := by
  unfold moveStmt
  simp

-- Dialects
example : isCanonicalDialect Dialect.min = true := rfl

example : isCanonicalDialect Dialect.hum = false := rfl

example : isTransientDialect Dialect.hum = true := rfl

example : isTransientDialect Dialect.min = false := rfl

-- Rendering
example : renderCode Morph.Syntax.Program.empty Dialect.min = "" := rfl

example : renderCode Morph.Syntax.Program.empty Dialect.hum = "" := rfl

example : renderCode { stmts := [.exprStmt (.binop .add (.lit (.int 1)) (.lit (.int 2)))] }
    Dialect.min = "(1+2)" := by native_decide

example : renderCode { stmts := [.exprStmt (.binop .add (.lit (.int 1)) (.lit (.int 2)))] }
    Dialect.hum = "(1 + 2)" := by native_decide

example : renderCode { stmts := [.varDecl ⟨"x"⟩ .intType (.lit (.int 5))] }
    Dialect.min = "let x: int = 5" := by native_decide

example : renderCode
    { stmts := [.exprStmt (.lit (.int 1)), .exprStmt (.lit (.int 2))] } Dialect.min =
    "1;2" := by native_decide

-- Correctness properties. The two projectional claims are **false** for a real
-- parser/editor, so the examples are their refutations (loop 46).
example : ¬ projectionalOnlyMandate := projectionalOnlyMandate_refuted

example : ¬ projectional_only_mandate := projectional_only_mandate_refuted

example : min_is_canonical := by
  unfold min_is_canonical isCanonicalDialect; rfl

example : hum_is_transient := by
  unfold hum_is_transient isTransientDialect; rfl

example : error_handling_explicit := by
  intro α r
  cases r with
  | ok a => exact Or.inl ⟨a, rfl⟩
  | error e => exact Or.inr ⟨e, rfl⟩

-- Error BEq
example : ((Error.syntaxError "a") == (Error.syntaxError "a")) = true := rfl

example : ((Error.syntaxError "a") == (Error.syntaxError "b")) = false := rfl

-- Effect BEq
example : (Effect.pure == Effect.pure) = true := rfl

example : (Effect.pure == Effect.io) = false := rfl

example : (Effect.io == Effect.state) = false := rfl

-- Variance BEq
example : (Variance.covariant == Variance.covariant) = true := rfl

example : (Variance.covariant == Variance.contravariant) = false := rfl

-- Associativity BEq
example : (Associativity.left == Associativity.left) = true := rfl

example : (Associativity.left == Associativity.right) = false := rfl

-- EditOperation BEq
example : (EditOperation.delete == EditOperation.delete) = true := rfl

example : ((EditOperation.replace "a") == (EditOperation.replace "a")) = true := rfl

example : ((EditOperation.replace "a") == (EditOperation.replace "b")) = false := rfl

-- Dialect BEq
example : (Dialect.min == Dialect.min) = true := rfl

example : (Dialect.min == Dialect.hum) = false := rfl

end Morph.Specs.MorphLanguage
