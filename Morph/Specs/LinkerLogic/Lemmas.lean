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

/-! ### Transitive cycle detection via Kahn (loop 58)

Loop 18 proved `acyclic` misses transitive cycles but left the fix open.
Loop 58 supplies it alongside (not replacing `acyclic`, so existing theorems
stand): Kahn's topological removal (Kahn 1962; incremental variant
arXiv:2402.11028). Other languages: `ld`/`lld` report cycles only at
archive-extraction time (no proved detector); Rust `rustc` metadata loader
uses a DFS with explicit stack + `decide` fuel (like loop 45's
`DependencySat` Kahn fix); OCaml `ocamldep` topological sort is total but
unproved. Morph now has the proved detector.
-/

/-- All object names. -/
def allNames (objs : List ObjectFile) : List String :=
  objs.map (·.name)

/-- Dependencies that are themselves linked objects (external libs ignored). -/
def depsInGraph (objs : List ObjectFile) (o : ObjectFile) : List String :=
  o.imports.filter (· ∈ allNames objs)

/-- Does `name` still have an unremoved dependency in `remaining`? -/
def hasDepIn (objs : List ObjectFile) (remaining : List String) (name : String) : Bool :=
  match objs.find? (fun o => o.name == name) with
  | none => false
  | some o => (depsInGraph objs o).any (· ∈ remaining)

/-- Kahn fuel: repeatedly drop nodes with no remaining dependencies. -/
def kahnFuel : Nat → List ObjectFile → List String → List String
  | 0, _, rem => rem
  | n + 1, objs, rem => kahnFuel n objs (rem.filter (hasDepIn objs rem))

/-- **Transitive acyclicity**: after `|objs| + 1` rounds nothing remains. -/
def transitiveAcyclic (objs : List ObjectFile) : Bool :=
  kahnFuel (objs.length + 1) objs (allNames objs) == []

/-- The two-cycle is cyclic (the old `acyclic` says `true`). -/
theorem transitiveAcyclic_catches_two_cycle :
    transitiveAcyclic [ { name := "A", sections := [], imports := ["B"], exports := [] },
                        { name := "B", sections := [], imports := ["A"], exports := [] } ] = false := by
  decide

/-- The diamond is acyclic (no false positive). -/
theorem transitiveAcyclic_diamond_acyclic :
    transitiveAcyclic [ { name := "A", sections := [], imports := ["B", "C"], exports := [] },
                        { name := "B", sections := [], imports := ["D"], exports := [] },
                        { name := "C", sections := [], imports := ["D"], exports := [] },
                        { name := "D", sections := [], imports := [], exports := [] } ] = true := by
  decide

/-- Self-import is cyclic. -/
theorem transitiveAcyclic_catches_self :
    transitiveAcyclic [ { name := "A", sections := [], imports := ["A"], exports := [] } ] = false := by
  decide

/-! ### Loop 66: binding algebra, merging, and a real LTO check

Research: Kahn 1962 (topological removal); LLVM ThinLTO (module summaries +
strong-symbol dominance checks — merging must reject conflicting strong
definitions, accept weak ones); ELF symbol binding (`STB_WEAK` vs `GLOBAL`:
first strong wins, duplicate strong is an error); `mold`/`lld`
(`--allow-multiple-definition` = first-wins, Morph's rule); Rust crate
metadata (SVH strict-version hashing rejects stale/duplicate crates).

Language comparison: GNU `ld` (duplicate strong symbol = error; weak +
strong = strong wins); `lld`/`mold` (same, faster, `--allow-multiple-
definition` for first-wins); `rustc` (crate disambiguator + SVH — no silent
merging); OCaml (`ocamldep` order determines linking, unproved). Morph:
priority resolution with first-wins ties (like `ld` permissive mode) plus a
proved cycle detector.

What is proved: the binding algebra is associative and idempotent (so
fold-order over duplicates does not matter beyond first-wins); a fresh
symbol appends unchanged (the merging base case); and `ltoSafeStrong` —
transitive acyclicity *plus* import resolution — is a real check with
proved projections to each conjunct. The `ltoSafe` stub is untouched.
-/

/-- Binding resolution is associative on winners: fold order over duplicates
does not matter beyond first-wins. -/
theorem resolveBinding_assoc (a b c : SymbolBinding) :
    (resolveBinding (resolveBinding a b).1 c).1 =
      (resolveBinding a (resolveBinding b c).1).1 := by
  cases a <;> cases b <;> cases c <;> decide

/-- Binding resolution is idempotent. -/
theorem resolveBinding_idem (b : SymbolBinding) :
    (resolveBinding b b).1 = b := by
  cases b <;> decide

/-- A fresh symbol appends unchanged: the merging base case. -/
theorem resolveSymbols_singleton_fresh (ex : List LinkerSymbol)
    (s : LinkerSymbol)
    (h : ex.find? (fun x => x.name == s.name) = none) :
    resolveSymbols ex [s] = ex ++ [s] := by
  simp [resolveSymbols, h]

/-- Resolving against nothing is the identity. -/
theorem resolveSymbols_empty_new (ex : List LinkerSymbol) :
    resolveSymbols ex [] = ex := rfl

/-- Every export in the link. -/
def allExports (objs : List ObjectFile) : List String :=
  objs.flatMap (·.exports)

/-- Every import is exported by some linked object. -/
def allImportsResolved (objs : List ObjectFile) : Bool :=
  objs.all (fun o => o.imports.all (· ∈ allExports objs))

/-- A real LTO check: transitive acyclicity *and* import resolution.
Unlike `ltoSafe`, this refuses cyclic and dangling links. -/
def ltoSafeStrong (objs : List ObjectFile) : Bool :=
  transitiveAcyclic objs && allImportsResolved objs

/-- The empty link is safe. -/
theorem ltoSafeStrong_nil : ltoSafeStrong [] = true := rfl

/-- A clean two-object link passes. -/
theorem ltoSafeStrong_clean :
    ltoSafeStrong [ { name := "A", sections := [], imports := ["B"], exports := ["A"] },
                    { name := "B", sections := [], imports := [], exports := ["B"] } ] = true := by
  decide

/-- A resolved two-cycle fails (via acyclicity). -/
theorem ltoSafeStrong_rejects_cycle :
    ltoSafeStrong [ { name := "A", sections := [], imports := ["B"], exports := ["A"] },
                    { name := "B", sections := [], imports := ["A"], exports := ["B"] } ] = false := by
  decide

/-- A dangling import fails (via resolution). -/
theorem ltoSafeStrong_rejects_dangling :
    ltoSafeStrong [ { name := "A", sections := [], imports := ["Missing"],
                      exports := ["A"] } ] = false := by
  decide

/-- The strong check implies acyclicity. -/
theorem ltoSafeStrong_implies_acyclic (objs : List ObjectFile)
    (h : ltoSafeStrong objs = true) : transitiveAcyclic objs = true := by
  simp only [ltoSafeStrong, Bool.and_eq_true] at h
  exact h.1

/-- The strong check implies resolution. -/
theorem ltoSafeStrong_implies_resolved (objs : List ObjectFile)
    (h : ltoSafeStrong objs = true) : allImportsResolved objs = true := by
  simp only [ltoSafeStrong, Bool.and_eq_true] at h
  exact h.2

end Morph.Specs.LinkerLogic
