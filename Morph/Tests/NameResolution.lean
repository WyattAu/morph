/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.NameResolution
import Morph.Frontend.Parser

/-!
# Name resolution tests (loop 82)

The executable counterpart of the extracted pass
(`Morph.Frontend.NameResolution`): the occurrence decision on concrete
scopes, the structural pass on concrete trees (including the `match_`-arm
scope extension that mirrors `parseMatchArms`), and the proven
projection properties instantiated. The last pin is end-to-end: real
parser output for `let x = 5 in x + 1` is already fully resolved (no
`fvar` remains), so re-resolution is the identity.
-/

namespace Morph.Tests.NameResolution

open Morph.Frontend.NameResolution
open Morph.Syntax
open Morph.Core

/-- Innermost binder wins: head of scope is index 0. -/
example : resolveIdent ["x"] "x" = .bvar 0 := by rfl

/-- Deeper binders get higher indices. -/
example : resolveIdent ["y", "x"] "x" = .bvar 1 := by rfl

/-- Unbound names stay free. -/
example : resolveIdent ["y"] "x" = .fvar "x" := by rfl

/-- The pass converts an in-scope occurrence. -/
example : resolveExpr ["x"] (.fvar "x") = .bvar 0 := by rfl

/-- ...but leaves out-of-scope names alone, even under binders. -/
example : resolveExpr ["x"] (.lam 1 (.fvar "y")) = .lam 1 (.fvar "y") := by rfl

/-- `let_` bodies resolve against the caller's scope (the slot is anonymous). -/
example : resolveExpr ["x"] (.let_ (.lit (.int 1)) (.fvar "x")) =
    .let_ (.lit (.int 1)) (.bvar 0) := by rfl

/-- `match_` arm bodies see the pattern's binders — the parser's
`patVars pat ++ scope` discipline (`parseMatchArms`). -/
example : resolveExpr [] (.match_ (.fvar "s") [(.var_ "x", .fvar "x")]) =
    .match_ (.fvar "s") [(.var_ "x", .bvar 0)] := by rfl

/-- The proven projection, instantiated: re-resolution is the identity. -/
example (e : Expr) : resolveExpr ["x"] (resolveExpr ["x"] e) = resolveExpr ["x"] e :=
  resolveExpr_idem _ e

/-- The proven fixed point, instantiated: name-free trees are untouched. -/
example (e : Expr) (h : hasFVar e = false) :
    resolveExpr ["x", "y"] e = e :=
  resolveExpr_closed _ e h

/-- End-to-end: parser output for `let x = 5 in x + 1` mentions no free
variable by name — it is already resolved, so the pass fixes it. -/
example : (match Morph.Frontend.parse "let x = 5 in x + 1" with
  | .ok e => hasFVar e
  | .error _ => true) = false := by
  native_decide

end Morph.Tests.NameResolution
