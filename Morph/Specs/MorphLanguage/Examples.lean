/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.MorphLanguage.Spec

namespace Morph.Specs.MorphLanguage

/-!
## Examples

Concrete examples demonstrating the MorphLanguage specification.
-/

-- Edit operations
example : applyEdit "" (EditOperation.replace "hello") = "hello" := rfl

example : applyEdit "hello" (EditOperation.insert " world") = "hello world" := rfl

example : applyEdit "temp" EditOperation.delete = "" := rfl

example : applyEdit "data" (EditOperation.move 0 3) = "data" := rfl

-- Parsing
example : parseCode "" = some Morph.Syntax.Program.empty := rfl

example : parseCode "let x = 5" = some Morph.Syntax.Program.empty := rfl

-- AST editing
example : applyEditToAst Morph.Syntax.Program.empty (EditOperation.replace "new") =
    some Morph.Syntax.Program.empty := rfl

-- Dialects
example : isCanonicalDialect Dialect.min = true := rfl

example : isCanonicalDialect Dialect.hum = false := rfl

example : isTransientDialect Dialect.hum = true := rfl

example : isTransientDialect Dialect.min = false := rfl

-- Rendering
example : renderCode Morph.Syntax.Program.empty Dialect.min = "" := rfl

example : renderCode Morph.Syntax.Program.empty Dialect.hum = "" := rfl

-- Correctness properties
example : projectionalOnlyMandate := by intro _ _; trivial

example : projectional_only_mandate = True := rfl

example : min_is_canonical = True := rfl

example : hum_is_transient = True := rfl

example : error_handling_explicit = True := rfl

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
