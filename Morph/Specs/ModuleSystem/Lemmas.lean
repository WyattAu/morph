/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ModuleSystem.Spec

/-!
# ModuleSystem: the link table actually links

Research loop 18. Target: `Morph/Specs/ModuleSystem/`.

**What was there.** Ten theorems, of which the interesting-looking ones were
about *empty* tables (`moduleInLinkTable_empty`, `resolveModule_empty`,
`searchRegistryByName_empty`, `searchRegistryByTag_empty`) — true because the
table is empty. Nothing said what happens when a module *is* added.

**What is here.** The round-trip the content-addressable linker needs: a module
added to the link table is findable by id, and the two lookup functions agree
with each other.

**A core-level note.** `ModuleId` derived `BEq` without a `LawfulBEq`
instance, so `resolveModule`'s `mid == id` was unprovably sound — the same
defect loops 12 and 14 found, here on a third type. `ModuleId` now derives
`DecidableEq` and the module system compares ids with `decide`.
-/

namespace Morph.Specs.ModuleSystem

/-- **Adding a module makes it findable.** -/
theorem addToLinkTable_finds (table : LinkTable) (mod : Module) :
    moduleInLinkTable (addToLinkTable table mod) mod.id = true := by
  simp [addToLinkTable, moduleInLinkTable]

/-- **And it resolves to the module that was added.** -/
theorem resolveModule_finds (table : LinkTable) (mod : Module) :
    resolveModule (addToLinkTable table mod) mod.id = some mod := by
  simp [addToLinkTable, resolveModule]

end Morph.Specs.ModuleSystem
