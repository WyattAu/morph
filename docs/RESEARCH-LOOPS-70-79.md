# Research Loops 70–79 — Implementation Track

Loop 70 closes the last `Morph/Specs` TODOs. From here the track turns toward
*implementation*: the specifications are now dense enough that the most
valuable next iterations land their guarantees in the shipped compiler, not
only in `Morph/Specs`.

## Loop 70 — ModuleSystem: link tables, workspaces, mangling (DONE, Lean)

**Target.** `Morph/Specs/ModuleSystem/Spec.lean`'s four TODOs: module ID
uniqueness in well-formed link tables, link-table consistency, workspace root
validity, and symbol mangling injectivity (the last marked "Blocked on: String
reasoning in Lean 4").

**Model.** Three predicates on a `LinkTable`, composed into
`WellFormed t := keysMatch t ∧ keyNodup t ∧ depsResolved t`; a workspace
predicate `workspaceWellFormed w := w.root ≠ "" ∧ 0 < w.config.maxDepth ∧
WellFormed w.modules ∧ namesNodup w.modules`; and a structured
`MangledName (hash, version, symbol)` whose `renderMangled` is the shipped
textual form.

**Proved.**
- `wellFormed_key_unique` — two entries in a well-formed table with the same
  id *are* the same module. The proof indexes both occurrences and cancels
  them with `List.getElem?_inj` on the nodup key list.
- `wellFormed_deps_resolve` — every dependency of every stored module resolves
  to `some` module; `wellFormed_add` shows `addToLinkTable` preserves
  well-formedness when the added module's own dependencies resolve in the
  extended table (so the §5.2 diamond — `Log v1` and `Log v2` side by side —
  is fine: each version lists its own dependencies).
- `workspace_root_nonempty`, `resolveModuleByName_eq_some_of_mem_of_namesNodup`
  (name resolution finds exactly the stored module),
  `resolveModuleByName_deps_resolve` (workspace resolution composes with link
  consistency).
- `mangleName_injective` — the structured name is a faithful encoding.

**Refuted.** The textual mangling claim as the TODO stated it:
`mangleSymbol_not_injective`. Hash `"a"` at version 1 with symbol `"b_v2_c"`
collides with hash `"a_v1_b"` at version 2 with symbol `"c"` — both render to
`"a_v1_b_v2_c"` — because the rendering erases the separator boundary the
format was supposed to carry. The fix is the structured name; the textual form
is proved to be its rendering (`mangleSymbol_eq_render`), so every collision of
the string form is visible as a merge of two distinct structured names.

## Verification

- `lake build Morph.Specs.ModuleSystem.Spec / .Lemmas / .Examples` ✔.
- Full `lake build Morph` and `lake build Morph.Tests` ✔; zero `sorry`.
