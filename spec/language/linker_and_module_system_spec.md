# Linker and Module System — Specification

* File:* `language/linker_and_module_system_spec.md`
* Version:* 1.0.0
* Context:* Build system — linking, symbol resolution, module tables
* Formalism:* Lists of objects and modules; binding priority
* Status:* Active
* Machine-checked in:* `Morph/Specs/LinkerLogic/`, `Morph/Specs/ModuleSystem/`

---

## 1. Purpose and Scope

Two build-system specifications whose theorems were trivia, replaced by the
properties their subjects actually have — and, in both cases, by *findings* about
advertised properties that do not hold.

## 2. Definitions: LinkerLogic

**What was there:** ten theorems — `Option.map`, `Option.bind`, `List.append`
lemmas — with no theorem about linking.

### The finding: `acyclic` does not check cycles

The specification's own comment says it:

```lean
def acyclic (objects : List ObjectFile) : Bool :=
  -- Simple cycle check: no object imports itself directly or transitively
  -- Full transitive closure deferred
  objects.all (fun obj => ¬ obj.imports.contains obj.name)
```

"directly or transitively" — but the code checks only **directly**: an object
importing *itself*. A two-object cycle (A imports B, B imports A) is reported as
**acyclic** (`acyclic_misses_transitive_cycles`). The function's name promises a
property it does not have, and nothing in the module said so.

### The finding: `ltoSafe` is a stub

`ltoSafe _objects := true` — "a no-op in the current model" (the comment says
so). The module advertised a link-time-optimization safety property it does not
check (`ltoSafe_is_a_stub`).

### Properties that do hold

| Theorem | Statement |
|---|---|
| `resolveBinding_strong_beats_weak` | strong beats weak |
| `resolveBinding_global_beats_local` | global beats local |
| `resolveBinding_weak_beats_local` | weak beats local |
| `resolveBinding_tie_keeps_first` | on a tie the first definition wins |
| `resolveBinding_total` | the resolution is always one of the two bindings |
| `acyclic_catches_self_import` | a direct self-import *is* caught |

## 3. Requirements: ModuleSystem

**What was there:** ten theorems, of which the interesting-looking ones were
about *empty* tables — true because the table is empty. Nothing said what
happens when a module **is** added.

| Theorem | Statement |
|---|---|
| `addToLinkTable_finds` | a module added to the link table is findable by id |
| `resolveModule_finds` | and it resolves to the module that was added |

**A core-level note.** `ModuleId` derived `BEq` without a `LawfulBEq`
instance, so `resolveModule`'s `mid == id` was unprovably sound — the same
defect loops 12 and 14 found, here on a third type. `ModuleId` now derives
`DecidableEq` and the module system compares ids with `decide`.

## 4. Scope: explicit non-claims

1. **No transitive cycle detection** — the named fix. A proper `acyclic` needs
   the transitive closure of the import graph.
2. **No LTO safety check** — `ltoSafe` remains a stub.
3. **No symbol-table merging theorem.** `resolveSymbols` is unproved; only the
   per-pair `resolveBinding` rules are.
4. **No workspace resolution, no version constraints, no hashing.** The module
   system's other functions are unproved.
5. **No registry search.** `searchRegistryByName`/`ByTag` are unproved.

## 5. Traceability

| Artifact | Location |
|---|---|
| Binding rules, the two findings | `Morph/Specs/LinkerLogic/Lemmas.lean` |
| Link-table round-trip | `Morph/Specs/ModuleSystem/Lemmas.lean` |
| Decidable equality for `ModuleId` | `Morph/Specs/ModuleSystem/Spec.lean` |
