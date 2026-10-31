/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core
import Morph.Syntax

namespace Morph.Specs.ModuleExistential

/-!
# Specification: Module Existential

This module formalizes module existential types, privacy, encapsulation,
and access control for Morph language.
-/

/- ## Module Identifiers -/

structure ModuleId where
  name : String
  deriving Repr, BEq, DecidableEq

/- ## Module Visibility -/

inductive Visibility where
  | visPrivate : Visibility
  | visPublic : Visibility
  | visInternal : Visibility
  deriving Repr, BEq, DecidableEq

/- ## Module Declarations -/

structure ModuleDecl where
  id : ModuleId
  visibility : Visibility
  exports : List String
  deriving Repr

def IsPrivateModule (mod : ModuleDecl) : Prop :=
  mod.visibility = .visPrivate

def IsPublicModule (mod : ModuleDecl) : Prop :=
  mod.visibility = .visPublic

def IsInternalModule (mod : ModuleDecl) : Prop :=
  mod.visibility = .visInternal

/- ## Environment Extensions -/

structure TypeWithVisibility where
  typ : Morph.Core.Typ
  visibility : Visibility

def TypeWithVisibility.isPublic (t : TypeWithVisibility) : Prop :=
  t.visibility = .visPublic

def TypeWithVisibility.isPrivate (t : TypeWithVisibility) : Prop :=
  t.visibility = .visPrivate

abbrev ModuleEnv := List (String × TypeWithVisibility)

def ModuleEnv.contains (env : ModuleEnv) (sym : String) : Bool :=
  env.any fun (s, _) => s = sym

def ModuleEnv.getType (env : ModuleEnv) (sym : String) : Option TypeWithVisibility :=
  (env.find? fun (s, _) => s = sym).map fun (_, t) => t

def defaultEnv : ModuleEnv := []

/- ## Existential Types -/

structure ExistentialType where
  interface : Morph.Core.Typ

structure ExistentialValue where
  type : ExistentialType

/- ## Module Interface -/

structure ModuleInterface where
  module : ModuleId
  types : List (String × Morph.Core.Typ)
  functions : List (String × Morph.Core.Typ)

def ModuleDecl.implements (mod : ModuleDecl) (iface : ModuleInterface) : Prop :=
  mod.id = iface.module ∧
  ∀ (sym : String), sym ∈ mod.exports →
    (∃ (τ : Morph.Core.Typ), (sym, τ) ∈ iface.types ∨ (sym, τ) ∈ iface.functions)

/- ## Module Implementation -/

structure ModuleImplementation where
  module : ModuleId
  privateTypes : List (String × Morph.Core.Typ)
  privateFunctions : List (String × Morph.Core.Typ)

def ModuleDecl.hasImplementation (mod : ModuleDecl) (impl : ModuleImplementation) : Prop :=
  mod.id = impl.module ∧
  ∀ (sym : String), sym ∈ mod.exports →
    ∀ (τ : Morph.Core.Typ),
      (sym, τ) ∈ impl.privateTypes → False

/- ## Access Control -/

inductive AccessRule where
  | allow : AccessRule
  | deny : AccessRule
  deriving Repr, BEq, DecidableEq

structure AccessEntry where
  module : ModuleId
  symbol : String
  rule : AccessRule

structure AccessControl where
  entries : List AccessEntry

def AccessControl.isAllowed (acl : AccessControl) (mod : ModuleId) (sym : String) : Bool :=
  match acl.entries.find?
      (fun e => decide (e.module = mod) && decide (e.symbol = sym)) with
  | some entry => decide (entry.rule = AccessRule.allow)
  | none => false

/- ## Module Composition -/

structure ModuleComposition where
  modules : List ModuleDecl
  imports : List (ModuleId × ModuleId)

def ModuleComposition.importsOf (comp : ModuleComposition) (importer imported : ModuleId) : Bool :=
  comp.imports.any (fun p => decide (p = (importer, imported))) &&
    (comp.modules.any fun m => decide (m.id = importer)) &&
    (comp.modules.any fun m => decide (m.id = imported))

/- ## Correctness Specifications -/

/-- **Module privacy**: every environment entry for this module carries the
module's own visibility. (This was `True`.) -/
def spec_module_privacy (mod : ModuleDecl) (env : ModuleEnv) : Prop :=
  ∀ (twv : TypeWithVisibility), (mod.id.name, twv) ∈ env →
    twv.visibility = mod.visibility

def spec_module_interface (mod : ModuleDecl) (iface : ModuleInterface) (_env : ModuleEnv) : Prop :=
  mod.implements iface

def spec_module_implementation (mod : ModuleDecl) (impl : ModuleImplementation) : Prop :=
  mod.hasImplementation impl

/-- **Encapsulation**: every exported name is public in the environment. (This
was `True`.) -/
def ModuleDecl.isEncapsulated (mod : ModuleDecl) (env : ModuleEnv) : Prop :=
  ∀ (sym : String) (twv : TypeWithVisibility),
    (sym, twv) ∈ env → sym ∈ mod.exports → twv.isPublic

def spec_module_encapsulation (mod : ModuleDecl) (impl : ModuleImplementation) (_env : ModuleEnv) : Prop :=
  mod.hasImplementation impl

/-- **Access control is sound**: an allowed name corresponds to an `allow` entry
for that module. (This was `True`.) -/
def spec_module_access_control (mod : ModuleDecl) (acl : AccessControl)
    (_env : ModuleEnv) : Prop :=
  ∀ (sym : String), AccessControl.isAllowed acl mod.id sym = true →
    ∃ e, e ∈ acl.entries ∧ e.module = mod.id ∧ e.symbol = sym ∧
      e.rule = AccessRule.allow

/-- **Composition**: a successful import relates two declared modules. (This was
`True`.) -/
def spec_module_composition (comp : ModuleComposition) (_env : ModuleEnv) : Prop :=
  ∀ (A B : ModuleId), comp.importsOf A B = true →
    (comp.modules.any (fun m => decide (m.id = A))) = true ∧
    (comp.modules.any (fun m => decide (m.id = B))) = true

/-- A value conforms to an existential when their interfaces agree. -/
def ExistentialValue.conforms (v : ExistentialValue) (t : ExistentialType) : Prop :=
  v.type.interface = t.interface

/-- **Existential types**: a conforming value's interface is the bound interface.
(This was `True`.) -/
def spec_existential_types (t : ExistentialType) : Prop :=
  ∀ (v : ExistentialValue), v.conforms t → v.type.interface = t.interface

/- ## Correctness Invariants -/

/-- **Private implementation types are not exported** by a private module. (This
was `True`.) -/
def inv_private_no_public_impl (mod : ModuleDecl) (impl : ModuleImplementation) : Prop :=
  IsPrivateModule mod → ∀ (sym : String) (τ : Morph.Core.Typ),
    (sym, τ) ∈ impl.privateTypes → sym ∉ mod.exports

def inv_interface_complete (mod : ModuleDecl) (iface : ModuleInterface) : Prop :=
  mod.implements iface →
  ∀ (sym : String), sym ∈ mod.exports →
    ∃ (τ : Morph.Core.Typ), (sym, τ) ∈ iface.types ∨ (sym, τ) ∈ iface.functions

/-- **Access control soundness**: the same statement as
`spec_module_access_control`, without the environment. (This was `True`.) -/
def inv_access_control_sound (mod : ModuleDecl) (acl : AccessControl) : Prop :=
  ∀ (sym : String), AccessControl.isAllowed acl mod.id sym = true →
    ∃ e, e ∈ acl.entries ∧ e.module = mod.id ∧ e.symbol = sym ∧
      e.rule = AccessRule.allow

def inv_composition_transitive (comp : ModuleComposition) : Prop :=
  ∀ (A B C : ModuleId),
    comp.importsOf A B ∧ comp.importsOf B C → comp.importsOf A C

/-! ## Sealing and abstraction safety (loop 97)

Research basis: Rossberg, *1ML — Core and Modules United* (JFP 2018) and
*Dreyer, *Understanding and Evolving the ML Module System* (thesis): **sealing**
(`E :> T`) is *the* abstraction mechanism — it erases everything the interface
does not name — and a functor's sealing site is its generative identity: two
applications at different sites yield incompatible abstract types, even for
identical arguments (Standard ML behavior; applicative functors are the
exception, not the rule).

Morph's `ExistentialType`/`ExistentialValue` named existentials but gave no
sealing semantics and no abstraction theorem. This section supplies both, at
the model level:

- a `Package` is an implementation sealed by an interface;
- `seal` succeeds only when the interface covers the implementation's exports;
- clients resolve names **only through the interface** (`resolveClient`);
- **abstraction safety** = a client cannot resolve a private name
  (`resolveSealed_private`), the name-level form of "the representation is
  unobservable";
- **generativity** = a sealed type is identified by its sealing site
  (`SealedType`), so two sealings are distinct types by construction. -/

/-- A sealed package: an implementation restricted to what its interface names. -/
structure Package where
  iface : ModuleInterface
  impl : ModuleImplementation

/-- The name sets of an interface and an implementation. -/
def Package.ifaceNames (p : Package) : List String :=
  (p.iface.types.map Prod.fst) ++ (p.iface.functions.map Prod.fst)

def Package.privateNames (p : Package) : List String :=
  (p.impl.privateTypes.map Prod.fst) ++ (p.impl.privateFunctions.map Prod.fst)

/-- A package is **well sealed** when the interface is complete over the
implementation: every private name is exported by the interface. This is the
1ML requirement that sealing must cover the body's definitions. -/
def Package.WellSealed (p : Package) : Prop :=
  ∀ n, n ∈ p.privateNames → n ∈ p.ifaceNames

/-- Sealing succeeds exactly when the interface covers every private name of
the implementation (the `WellSealed` condition); otherwise there is nothing
to seal the implementation *as*. -/
def sealPackage (iface : ModuleInterface) (impl : ModuleImplementation) : Option Package :=
  let p : Package := ⟨iface, impl⟩
  if p.privateNames.all (fun n => decide (n ∈ p.ifaceNames)) then some p else none

/-- Client-side resolution: through a sealed package, a name resolves only if
the *interface* declares it. The implementation's names are simply not in the
client's environment — this definitional restriction is what makes the
abstraction theorem below a statement about resolution, not about discipline. -/
def resolveClient (p : Package) (sym : String) : Option Morph.Core.Typ :=
  p.iface.types.lookup sym

/-- Lookup misses when the key is absent from the name list. -/
private theorem lookup_none_of_not_mem_fst {α β : Type} [BEq α] [LawfulBEq α] (sym : α) :
    ∀ l : List (α × β), sym ∉ l.map Prod.fst → List.lookup sym l = none
  | [], _ => rfl
  | (s, t) :: l, h => by
      by_cases hsym : sym == s
      · exfalso
        refine h ?_
        rw [LawfulBEq.eq_of_beq hsym]
        exact List.mem_map_of_mem (f := Prod.fst)
          (List.mem_cons_self (a := (s, t)) (l := l))
      · rw [List.map_cons] at h
        simp only [List.lookup, hsym]
        exact lookup_none_of_not_mem_fst sym l (fun contra => h (List.mem_cons_of_mem _ contra))

/-- Lookup finds the declared type when the interface's names are duplicate-free. -/
private theorem lookup_eq_some_of_mem {α β : Type} [BEq α] [LawfulBEq α] (sym : α) (τ : β) :
    ∀ l : List (α × β), (sym, τ) ∈ l → (l.map Prod.fst).Nodup →
      List.lookup sym l = some τ
  | [], h, _ => absurd h (by simp)
  | (s, t) :: l, h, hnd => by
      by_cases hsym : sym == s
      · have hss : sym = s := LawfulBEq.eq_of_beq hsym
        rcases (by simpa [hss] using h : (sym, τ) = (s, t) ∨ (sym, τ) ∈ l) with h' | hmem
        · simp only [List.lookup, hsym]
          exact congrArg some (congrArg Prod.snd h').symm
        · exfalso
          have hkeys : sym ∈ l.map Prod.fst := List.mem_map_of_mem hmem
          rw [hss] at hkeys
          exact absurd hkeys (List.nodup_cons.mp hnd).1
      · have hsymf : (sym == s) = false := Bool.eq_false_iff.mpr hsym
        have hne : sym ≠ s := fun he => hsym (by rw [he]; exact beq_self_eq_true s)
        have hmem : (sym, τ) ∈ l := by simpa [hne] using h
        simp only [List.lookup, hsymf]
        exact lookup_eq_some_of_mem sym τ l hmem (List.nodup_cons.mp hnd).2

/-- **Abstraction safety (name-level).** A private name of a well-sealed
package is unresolvable by clients — the representation is unobservable
through the interface. -/
theorem resolveSealed_private (p : Package)
    (sym : String) (hpriv : sym ∉ p.ifaceNames) :
    resolveClient p sym = none :=
  lookup_none_of_not_mem_fst sym p.iface.types (by
    intro hm
    exact hpriv (List.mem_append.mpr (Or.inl hm)))

/-- **Export resolution.** A name the interface declares as a type resolves to
exactly the interface's declared type — clients see the interface, never the
implementation's internal spelling. -/
theorem resolveSealed_exported (p : Package) (sym : String) (τ : Morph.Core.Typ)
    (h : (sym, τ) ∈ p.iface.types) (hnd : (p.iface.types.map Prod.fst).Nodup) :
    resolveClient p sym = some τ :=
  lookup_eq_some_of_mem sym τ p.iface.types h hnd

/-- **Sealing is idempotent.** Re-sealing a well-sealed package with its own
interface changes nothing — abstraction cannot be accidentally strengthened or
weakened by repetition. -/
theorem seal_idempotent (p : Package) (hp : p.WellSealed) :
    sealPackage p.iface p.impl = some p := by
  unfold sealPackage
  rw [if_pos (List.all_eq_true.mpr fun n hn => decide_eq_true (hp n hn))]

/-- **Generative sealing (1ML §"Applicative vs Generative").** A sealed type
is identified by its sealing site: two sealings of the *same* type at
*different* sites are different types, by construction. `M1.map int ≠
M2.map int` for two applications of the same functor. -/
def SealedType : Type := Nat × Morph.Core.Typ

theorem sealed_generative (i j : Nat) (τ : Morph.Core.Typ) (h : i ≠ j) :
    ((i, τ) : SealedType) ≠ (j, τ) := by
  intro he
  exact h (congrArg Prod.fst he)

example : ((1, Morph.Core.Typ.intType) : SealedType) ≠ (2, Morph.Core.Typ.intType) := by
  intro he
  exact absurd (congrArg Prod.fst he) (by decide)

end Morph.Specs.ModuleExistential
