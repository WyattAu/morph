/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Specs.MorphLanguage.Spec

namespace Morph.Specs.MorphLanguage

/-!
## Lemmas

Lemmas and auxiliary results for the MorphLanguage specification.
-/

theorem applyEdit_replace (code newCode : String) :
    applyEdit code (EditOperation.replace newCode) = newCode := rfl

theorem applyEdit_insert (code newCode : String) :
    applyEdit code (EditOperation.insert newCode) = code ++ newCode := rfl

theorem applyEdit_delete (code : String) :
    applyEdit code EditOperation.delete = "" := rfl

theorem applyEdit_move (code : String) (src dst : Nat) :
    applyEdit code (EditOperation.move src dst) = code := rfl

theorem applyEditToAst_id (ast : Morph.Syntax.Program) (edit : EditOperation) :
    applyEditToAst ast edit = some ast := rfl

theorem parseCode_empty : parseCode "" = some Morph.Syntax.Program.empty := rfl

theorem parseCode_nonempty : parseCode "hello" = some Morph.Syntax.Program.empty := rfl

theorem parseCode_always_empty (code : String) :
    parseCode code = some Morph.Syntax.Program.empty := by
  unfold parseCode; split <;> rfl

theorem isCanonicalDialect_min : isCanonicalDialect Dialect.min = true := rfl

theorem isCanonicalDialect_hum : isCanonicalDialect Dialect.hum = false := rfl

theorem isTransientDialect_hum : isTransientDialect Dialect.hum = true := rfl

theorem isTransientDialect_min : isTransientDialect Dialect.min = false := rfl

theorem dialect_exhaustive (d : Dialect) :
    isCanonicalDialect d || isTransientDialect d = true := by
  cases d <;> rfl

theorem renderCode_const (ast : Morph.Syntax.Program) (d : Dialect) :
    renderCode ast d = "" := rfl

theorem projectionalOnlyMandate_holds : projectionalOnlyMandate := by
  intro _ _; trivial

theorem min_is_canonical_eq_true : min_is_canonical = True := rfl

theorem hum_is_transient_eq_true : hum_is_transient = True := rfl

theorem error_handling_explicit_eq_true : error_handling_explicit = True := rfl

theorem projectional_only_mandate_eq_true : projectional_only_mandate = True := rfl

end Morph.Specs.MorphLanguage
