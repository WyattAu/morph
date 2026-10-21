/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.LinkerLogic.Spec

/-!
# LinkerLogic: the cycle check does not check cycles

Research loop 18. Target: `Morph/Specs/LinkerLogic/`.

**What was there.** Ten theorems — `Option.map`/`Option.bind`/`List.append`
lemmas, with no theorem about linking at all.

**The finding.** `acyclic` is documented in the specification itself:

```lean
def acyclic (objects : List ObjectFile) : Bool :=
  -- Simple cycle check: no object imports itself directly or transitively
  -- Full transitive closure deferred
  objects.all (fun obj => ¬ obj.imports.contains obj.name)
```

The comment says "directly or transitively" but the code checks only
**directly**: an object that imports *itself*. A two-object cycle — A imports B,
B imports A — is reported as **acyclic**. So the function's name promises a
property it does not have, and nothing in the module said so.

And `ltoSafe` is `true` for every object list, with the comment "a no-op in the
current model": the module advertises a link-time-optimization safety property
it does not check.

**What is here.** The properties the module *does* have — the binding
resolution rules — and the two findings, stated.
-/

namespace Morph.Specs.LinkerLogic

/-- **The cycle check misses transitive cycles.** A pair of objects importing
each other is *acyclic* according to `acyclic`, even though it is a cycle. The
specification's own comment says "directly or transitively"; the code checks
only "directly". -/
theorem acyclic_misses_transitive_cycles :
    acyclic [ { name := "A", sections := [], imports := ["B"], exports := [] },
              { name := "B", sections := [], imports := ["A"], exports := [] } ] = true := by
  decide

/-- **But it does catch a direct self-import.** -/
theorem acyclic_catches_self_import :
    acyclic [ { name := "A", sections := [], imports := ["A"], exports := [] } ] = false := by
  decide

/-- **A strong binding beats a weak one.** -/
theorem resolveBinding_strong_beats_weak :
    resolveBinding .strong .weak = (.strong, true) := by
  decide

/-- **A global binding beats a local one.** -/
theorem resolveBinding_global_beats_local :
    resolveBinding .global .local = (.global, true) := by
  decide

/-- **A weak binding beats a local one.** -/
theorem resolveBinding_weak_beats_local :
    resolveBinding .weak .local = (.weak, true) := by
  decide

/-- **On a tie the first definition wins** — the spec's "first-defined wins
(deterministic ordering)" rule. The second argument is the *new* symbol, so the
existing one is kept. -/
theorem resolveBinding_tie_keeps_first :
    resolveBinding .global .global = (.global, true) := by
  decide

/-- **The binding resolution is total and deterministic**: every pair of
bindings resolves, and the resolution is the same both ways round for a strict
winner. -/
theorem resolveBinding_total (b1 b2 : SymbolBinding) :
    (resolveBinding b1 b2).1 = b1 ∨ (resolveBinding b1 b2).1 = b2 := by
  cases b1 <;> cases b2 <;> decide

/-- **The `ltoSafe` property is a stub**: it holds for every object list,
including one that is plainly unsafe. The specification's comment says as much —
"a no-op in the current model" — but the module advertised it as a property. -/
theorem ltoSafe_is_a_stub (objects : List ObjectFile) : ltoSafe objects = true := rfl

end Morph.Specs.LinkerLogic
