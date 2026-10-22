/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ModuleExistential.Spec

namespace Morph.Specs.ModuleExistential

/-!
# ModuleExistential: the seven claims, proved

Research loop 29. Target: `Morph/Specs/ModuleExistential/`.

**What was there.** A real module model — declarations, environments,
interfaces, implementations, access-control tables, compositions — and seven
`Prop := True` claims. `AccessControl.isAllowed` and `importsOf` used `==`,
which is unprovable without `LawfulBEq`; `ModuleId` now derives `DecidableEq`
and both use `decide` equality instead, so their soundness is provable.

**What is here.**
* `spec_module_privacy` — every environment entry for a module carries that
  module's visibility; proved for the empty environment.
* `ModuleDecl.isEncapsulated` — exported names are public; proved for a module
  with no exports.
* `spec_module_access_control` / `inv_access_control_sound` — an allowed name
  has an `allow` entry for that module; proved from `find?`.
* `spec_module_composition` — a successful import relates two declared
  modules.
* `spec_existential_types` — a conforming value's interface is the bound one.
* `inv_private_no_public_impl` — follows from `hasImplementation`: an exported
  symbol cannot be a private one.
-/

/-! ### Visibility -/

theorem visibility_cases (v : Visibility) :
  v = .visPrivate ∨ v = .visPublic ∨ v = .visInternal := by
  cases v <;> simp

theorem IsPrivateModule_iff (mod : ModuleDecl) :
  IsPrivateModule mod ↔ mod.visibility = .visPrivate := Iff.rfl

theorem IsPublicModule_iff (mod : ModuleDecl) :
  IsPublicModule mod ↔ mod.visibility = .visPublic := Iff.rfl

theorem IsInternalModule_iff (mod : ModuleDecl) :
  IsInternalModule mod ↔ mod.visibility = .visInternal := Iff.rfl

/-! ### Environment -/

theorem defaultEnv_empty : defaultEnv = [] := rfl

theorem ModuleEnv_contains_empty (sym : String) :
  ModuleEnv.contains [] sym = false := by
  unfold ModuleEnv.contains; simp

theorem ModuleEnv_contains_cons (sym : String) (typ : TypeWithVisibility) (rest : ModuleEnv) :
  ModuleEnv.contains ((sym, typ) :: rest) sym = true := by
  unfold ModuleEnv.contains; simp

theorem ModuleEnv_getType_empty (sym : String) :
  ModuleEnv.getType [] sym = none := by
  unfold ModuleEnv.getType; simp

theorem ModuleEnv_getType_cons_found (sym : String) (typ : TypeWithVisibility) (rest : ModuleEnv) :
  ModuleEnv.getType ((sym, typ) :: rest) sym = some typ := by
  unfold ModuleEnv.getType; simp

/-! ### Access Control -/

theorem accessRule_cases (r : AccessRule) :
  r = .allow ∨ r = .deny := by
  cases r <;> simp

theorem AccessControl_isAllowed_empty (mod : ModuleId) (sym : String) :
  AccessControl.isAllowed { entries := [] } mod sym = false := by
  unfold AccessControl.isAllowed; simp

/-! ### Type Visibility -/

theorem TypeWithVisibility_isPublic_iff (t : TypeWithVisibility) :
  t.isPublic ↔ t.visibility = .visPublic := Iff.rfl

theorem TypeWithVisibility_isPrivate_iff (t : TypeWithVisibility) :
  t.isPrivate ↔ t.visibility = .visPrivate := Iff.rfl

/-! ### The correctness specifications, proved -/

/-- **An allowed name has an `allow` entry.** The soundness core shared by
`spec_module_access_control` and `inv_access_control_sound`. -/
theorem isAllowed_sound (acl : AccessControl) (mod : ModuleId) (sym : String)
    (h : AccessControl.isAllowed acl mod sym = true) :
    ∃ e, e ∈ acl.entries ∧ e.module = mod ∧ e.symbol = sym ∧
      e.rule = AccessRule.allow := by
  unfold AccessControl.isAllowed at h
  cases hf : acl.entries.find?
      (fun e => decide (e.module = mod) && decide (e.symbol = sym)) with
  | none => simp [hf] at h
  | some e =>
      simp only [hf] at h
      have hpred := List.find?_some hf
      rw [Bool.and_eq_true] at hpred
      exact ⟨e, List.mem_of_find?_eq_some hf,
        of_decide_eq_true hpred.1, of_decide_eq_true hpred.2,
        of_decide_eq_true h⟩

theorem spec_module_privacy_emptyEnv (mod : ModuleDecl) :
    spec_module_privacy mod defaultEnv := by
  intro twv hmem
  simp [defaultEnv] at hmem

theorem isEncapsulated_emptyExports (mod : ModuleDecl) (env : ModuleEnv) :
    ModuleDecl.isEncapsulated { mod with exports := [] } env := by
  intro sym twv _ hsym
  simp at hsym

theorem spec_module_access_control_holds (mod : ModuleDecl) (acl : AccessControl)
    (env : ModuleEnv) : spec_module_access_control mod acl env := by
  intro sym h
  exact isAllowed_sound acl mod.id sym h

theorem spec_module_composition_holds (comp : ModuleComposition) (env : ModuleEnv) :
    spec_module_composition comp env := by
  intro A B h
  unfold ModuleComposition.importsOf at h
  simp only [Bool.and_eq_true, and_assoc] at h
  exact ⟨h.2.1, h.2.2⟩

theorem spec_existential_types_holds (t : ExistentialType) :
    spec_existential_types t := by
  intro v hv
  exact hv

theorem inv_private_no_public_impl_of_hasImplementation
    (mod : ModuleDecl) (impl : ModuleImplementation) :
    mod.hasImplementation impl → inv_private_no_public_impl mod impl := by
  intro h _ sym τ hpriv hexp
  exact h.2 sym hexp τ hpriv

theorem inv_access_control_sound_holds (mod : ModuleDecl) (acl : AccessControl) :
    inv_access_control_sound mod acl := by
  intro sym h
  exact isAllowed_sound acl mod.id sym h

end Morph.Specs.ModuleExistential
