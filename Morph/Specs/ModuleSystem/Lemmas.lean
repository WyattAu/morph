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

## Loop 70: the four remaining TODOs

`Spec.lean` carried four TODOs — module ID uniqueness, link-table
consistency, workspace root validity, and symbol mangling injectivity.
This file closes all four against the `WellFormed` / `workspaceWellFormed`
models `Spec.lean` now defines:

- **Module ID uniqueness** (`wellFormed_key_unique`): two entries in a
  well-formed table with the same id *are* the same module. The proof indexes
  both occurrences and cancels them with `List.getElem?_inj` on the nodup key
  list.
- **Link consistency** (`wellFormed_deps_resolve`): every dependency of every
  stored module resolves to `some` module. `wellFormed_add` shows the
  predicate is preserved by `addToLinkTable` when the added module's own
  dependencies are resolved.
- **Workspace validity** (`workspace_root_nonempty`,
  `resolveModuleByName_eq_some_of_mem_of_namesNodup`): a well-formed
  workspace has a non-empty root, and name resolution finds exactly the
  module stored under that name (uniqueness of names is part of
  `workspaceWellFormed`).
- **Mangling injectivity** (`mangleName_injective`,
  `mangleSymbol_not_injective`): the *structured* name is injective; the
  textual form's general injectivity claim is **false** — `renderMangled`
  erases the boundary between a hash and a symbol that itself contains the
  separator — and is recorded as its refutation, the same honest move as
  loops 8 and 30.
-/

namespace Morph.Specs.ModuleSystem

/-! ## Lookup round-trips (loop 18) -/

/-- **Adding a module makes it findable.** -/
theorem addToLinkTable_finds (table : LinkTable) (mod : Module) :
    moduleInLinkTable (addToLinkTable table mod) mod.id = true := by
  simp [addToLinkTable, moduleInLinkTable]

/-- **And it resolves to the module that was added.** -/
theorem resolveModule_finds (table : LinkTable) (mod : Module) :
    resolveModule (addToLinkTable table mod) mod.id = some mod := by
  simp [addToLinkTable, resolveModule]

/-! ## Well-formed link tables -/

theorem wellFormed_keysMatch {t : LinkTable} (h : WellFormed t) : keysMatch t := h.1

theorem wellFormed_keyNodup {t : LinkTable} (h : WellFormed t) : keyNodup t := h.2.1

theorem wellFormed_depsResolved {t : LinkTable} (h : WellFormed t) :
    depsResolved t := h.2.2

theorem moduleInLinkTable_iff {t : LinkTable} {id : ModuleId} :
    moduleInLinkTable t id = true ↔ ∃ m, (id, m) ∈ t := by
  unfold moduleInLinkTable
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, hb⟩
    obtain ⟨a, b⟩ := p
    have : a = id := of_decide_eq_true hb
    subst this
    exact ⟨b, hp⟩
  · rintro ⟨m, hm⟩
    exact ⟨(id, m), hm, by simp⟩

theorem resolveModule_isSome_of_mem {t : LinkTable} {id : ModuleId} {m : Module}
    (hm : (id, m) ∈ t) : (resolveModule t id).isSome = true := by
  unfold resolveModule
  rw [Option.isSome_map]
  exact (List.find?_isSome).mpr ⟨(id, m), hm, by simp⟩

/-- **Two occurrences of one id are the same module.** -/
theorem key_unique {t : LinkTable} (hnd : keyNodup t)
    {id : ModuleId} {m1 m2 : Module}
    (h1 : (id, m1) ∈ t) (h2 : (id, m2) ∈ t) : m1 = m2 := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨j, hj, hget2⟩ := List.mem_iff_getElem.mp h2
  have hget? : t[i]? = some (id, m1) := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  have hget2? : t[j]? = some (id, m2) := List.getElem?_eq_some_iff.mpr ⟨hj, hget2⟩
  have hmap1 : (t.map Prod.fst)[i]? = some id := by
    rw [List.getElem?_map, hget?]; rfl
  have hmap2 : (t.map Prod.fst)[j]? = some id := by
    rw [List.getElem?_map, hget2?]; rfl
  have hlen : i < (t.map Prod.fst).length := by simpa using hi
  have hij : i = j := List.getElem?_inj hlen hnd (by rw [hmap1, hmap2])
  have heq : (id, m1) = (id, m2) := by
    apply Option.some.inj
    rw [← hget?, ← hget2?, hij]
  exact congrArg Prod.snd heq

/-- **Module ID uniqueness in a well-formed link table.** -/
theorem wellFormed_key_unique {t : LinkTable} (h : WellFormed t)
    {m1 m2 : Module} (h1 : (m1.id, m1) ∈ t) (h2 : (m2.id, m2) ∈ t)
    (hid : m1.id = m2.id) : m1 = m2 := by
  have h2' : (m1.id, m2) ∈ t := by rw [hid]; exact h2
  exact key_unique h.2.1 h1 h2'

/-- A member of a table with unique keys resolves to itself. -/
theorem resolveModule_eq_some_of_mem_of_keyNodup {t : LinkTable} (hnd : keyNodup t)
    {id : ModuleId} {m : Module} (hm : (id, m) ∈ t) :
    resolveModule t id = some m := by
  unfold resolveModule
  cases hf : t.find? (fun p => decide (p.1 = id)) with
  | none =>
      have his : (t.find? (fun p => decide (p.1 = id))).isSome = true :=
        (List.find?_isSome).mpr ⟨(id, m), hm, by simp⟩
      rw [hf] at his
      simp at his
  | some q =>
      obtain ⟨a, b⟩ := q
      have hqmem : (a, b) ∈ t := List.mem_of_find?_eq_some hf
      have hqid : a = id :=
        of_decide_eq_true
          (List.find?_some (p := fun p : ModuleId × Module => decide (p.1 = id)) hf)
      subst hqid
      have hbm : b = m := key_unique hnd hqmem hm
      simp [hbm]

/-- **Link consistency**: in a well-formed table, every dependency of every
stored module resolves. -/
theorem wellFormed_deps_resolve {t : LinkTable} (h : WellFormed t)
    {m : Module} (hm : m ∈ t.map Prod.snd) {d : ModuleId}
    (hd : d ∈ m.dependencies) : (resolveModule t d).isSome = true := by
  have hlink : moduleInLinkTable t d = true := h.2.2 m hm d hd
  obtain ⟨m', hm'⟩ := moduleInLinkTable_iff.mp hlink
  exact resolveModule_isSome_of_mem hm'

theorem moduleInLinkTable_add (t : LinkTable) (m : Module) (id : ModuleId) :
    moduleInLinkTable (addToLinkTable t m) id = true ↔
      id = m.id ∨ moduleInLinkTable t id = true := by
  unfold moduleInLinkTable addToLinkTable
  rw [List.any_cons, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h

theorem keyNodup_add_iff (t : LinkTable) (m : Module) :
    keyNodup (addToLinkTable t m) ↔ m.id ∉ t.map Prod.fst ∧ keyNodup t := by
  unfold keyNodup addToLinkTable
  simp [List.nodup_cons]

theorem depsResolved_add (t : LinkTable) (m : Module)
    (hdep : ∀ d ∈ m.dependencies, moduleInLinkTable (addToLinkTable t m) d = true)
    (ht : depsResolved t) : depsResolved (addToLinkTable t m) := by
  intro m' hm' d hd
  rw [addToLinkTable, List.map_cons] at hm'
  rcases List.mem_cons.mp hm' with rfl | hm't
  · exact hdep d hd
  · exact (moduleInLinkTable_add t m d).mpr (Or.inr (ht m' hm't d hd))

/-- **Well-formedness is preserved by adding a module** whose own dependencies
are resolved in the extended table (a diamond is fine: each version lists its
own dependencies, and both versions are present). -/
theorem wellFormed_add (t : LinkTable) (m : Module)
    (hkey : m.id ∉ t.map Prod.fst)
    (hdep : ∀ d ∈ m.dependencies, moduleInLinkTable (addToLinkTable t m) d = true)
    (ht : WellFormed t) : WellFormed (addToLinkTable t m) := by
  refine ⟨?_, (keyNodup_add_iff t m).mpr ⟨hkey, ht.2.1⟩, depsResolved_add t m hdep ht.2.2⟩
  intro id m' hm'
  rw [addToLinkTable, List.mem_cons] at hm'
  rcases hm' with hEq | hm'
  · cases hEq; rfl
  · exact ht.1 id m' hm'

/-! ## Workspace resolution -/

/-- **The workspace root is valid**: non-empty. -/
theorem workspace_root_nonempty {w : Workspace} (h : workspaceWellFormed w) :
    w.root ≠ "" := h.1

theorem workspace_maxDepth_pos {w : Workspace} (h : workspaceWellFormed w) :
    0 < w.config.maxDepth := h.2.1

theorem workspace_modules_wellFormed {w : Workspace} (h : workspaceWellFormed w) :
    WellFormed w.modules := h.2.2.1

theorem workspace_namesNodup {w : Workspace} (h : workspaceWellFormed w) :
    namesNodup w.modules := h.2.2.2

/-- A name resolution returns a module that is actually in the workspace. -/
theorem resolveModuleByName_mem {w : Workspace} {name : String} {m : Module}
    (h : resolveModuleByName w name = some m) : m ∈ w.modules.map Prod.snd := by
  unfold resolveModuleByName at h
  obtain ⟨q, hq, hq2⟩ := Option.map_eq_some_iff.mp h
  subst hq2
  exact List.mem_map_of_mem (f := Prod.snd) (List.mem_of_find?_eq_some hq)

/-- **And every dependency of a name-resolved module resolves** — workspace
resolution composes with link-table consistency. -/
theorem resolveModuleByName_deps_resolve {w : Workspace} (hw : workspaceWellFormed w)
    {name : String} {m : Module} (h : resolveModuleByName w name = some m)
    {d : ModuleId} (hd : d ∈ m.dependencies) :
    (resolveModule w.modules d).isSome = true :=
  wellFormed_deps_resolve hw.2.2.1 (resolveModuleByName_mem h) hd

/-- Two same-named entries in a table with unique names are the same module. -/
theorem name_unique {t : LinkTable} (hnd : namesNodup t)
    {m1 m2 : Module} (h1 : (m1.id, m1) ∈ t) (h2 : (m2.id, m2) ∈ t)
    (hn : m1.name = m2.name) : m1 = m2 := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨j, hj, hget2⟩ := List.mem_iff_getElem.mp h2
  have hget? : t[i]? = some (m1.id, m1) := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  have hget2? : t[j]? = some (m2.id, m2) := List.getElem?_eq_some_iff.mpr ⟨hj, hget2⟩
  have hmap1 : (t.map (fun p => p.2.name))[i]? = some m1.name := by
    rw [List.getElem?_map, hget?]; rfl
  have hmap2 : (t.map (fun p => p.2.name))[j]? = some m2.name := by
    rw [List.getElem?_map, hget2?]; rfl
  have hlen : i < (t.map (fun p => p.2.name)).length := by simpa using hi
  have hij : i = j := List.getElem?_inj hlen hnd (by rw [hmap1, hmap2, hn])
  have heq : (m1.id, m1) = (m2.id, m2) := by
    apply Option.some.inj
    rw [← hget?, ← hget2?, hij]
  exact congrArg Prod.snd heq

/-- **Name resolution finds the module stored under that name.** -/
theorem resolveModuleByName_eq_some_of_mem_of_namesNodup {w : Workspace}
    (hkeys : keysMatch w.modules) (hnd : namesNodup w.modules)
    {m : Module} (hm : (m.id, m) ∈ w.modules) :
    resolveModuleByName w m.name = some m := by
  unfold resolveModuleByName
  cases hf : w.modules.find? (fun p => p.2.name == m.name) with
  | none =>
      have his : (w.modules.find? (fun p => p.2.name == m.name)).isSome = true :=
        (List.find?_isSome).mpr ⟨(m.id, m), hm, by simp⟩
      rw [hf] at his
      simp at his
  | some q =>
      obtain ⟨a, b⟩ := q
      have hqmem : (a, b) ∈ w.modules := List.mem_of_find?_eq_some hf
      have hqmem' : (b.id, b) ∈ w.modules := by
        rw [hkeys a b hqmem]; exact hqmem
      have hqname : b.name = m.name :=
        beq_iff_eq.mp
          (List.find?_some (p := fun p : ModuleId × Module => p.2.name == m.name) hf)
      have hbm : b = m := name_unique hnd hqmem' hm hqname
      simp [hbm]

theorem resolveModuleByName_isSome_of_mem {w : Workspace} {m : Module}
    (hm : (m.id, m) ∈ w.modules) :
    (resolveModuleByName w m.name).isSome = true := by
  unfold resolveModuleByName
  rw [Option.isSome_map, List.find?_isSome]
  exact ⟨(m.id, m), hm, by simp⟩

/-! ## Symbol mangling -/

/-- **The structured name is injective**: hash, version and symbol can be
recovered, so `mangleName` is a faithful encoding of the pair. -/
theorem mangleName_injective {mid1 mid2 : ModuleId} {s1 s2 : String}
    (h : mangleName mid1 s1 = mangleName mid2 s2) :
    mid1 = mid2 ∧ s1 = s2 := by
  have hh : mid1.hash = mid2.hash := congrArg MangledName.hash h
  have hv : mid1.version = mid2.version := congrArg MangledName.version h
  have hs : s1 = s2 := congrArg MangledName.symbol h
  constructor
  · cases mid1; cases mid2; simp_all
  · exact hs

/-- The shipped textual form is the rendering of the structured name. -/
theorem mangleSymbol_eq_render (mid : ModuleId) (s : String) :
    mangleSymbol mid s = renderMangled (mangleName mid s) := rfl

/-- **The textual form is not injective in general** — recorded as its
refutation. A hash of `"a"` with symbol `"b_v2_c"` collides with a hash of
`"a_v1_b"` and symbol `"c"`, because `renderMangled` erases the boundary the
separator was supposed to carry. -/
theorem mangleSymbol_not_injective :
    ¬ ∀ (mid1 mid2 : ModuleId) (s1 s2 : String),
        mangleSymbol mid1 s1 = mangleSymbol mid2 s2 → mid1 = mid2 ∧ s1 = s2 := by
  intro h
  have heq : mangleSymbol { hash := "a", version := 1 } "b_v2_c" =
      mangleSymbol { hash := "a_v1_b", version := 2 } "c" := by native_decide
  have hne : ({ hash := "a", version := 1 } : ModuleId) ≠
      { hash := "a_v1_b", version := 2 } := by decide
  exact hne (h _ _ _ _ heq).1

end Morph.Specs.ModuleSystem
