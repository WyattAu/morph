# Research Loops 50–59 — Unfinished Business Batch

Batch-then-verify: research pulls for all 10, Lean implementation where
tractable/additive (no breaking changes), spec docs for all 10, single
`lake build Morph` gate at the end.

Papers pulled (10 searches, 2026-10-26):
- Subtyping: Pierce POPL'92, Kennedy-Pierce FOOL-WOOD'07, Brandt-Henglein,
  Kozen et al. POPL'93, Julia Belyakova PLDI'24, Castagna 2024-25 wave.
- Effects: Koka rows, OCaml 5 one-shot, Bauer-Pretnar arXiv:1306.6316,
  Affect POPL'25, Kawamata refinement 2024.
- Translation validation: Alive2 PLDI'21, AArch64 backend 2025, LLVM+LLM 2024.
- Lexers: Coqlex Programming Journal 2024, maximal munch Dragon §3.4,
  Marpa, Aycock-Horspool PLDI'03.
- CEK: Blazy et al. 2024-25 (SOS vs CEK mechanized), Danvy-Nielsen,
  Krivine/Landsky.
- Preservation/POPLmark: POPLmark Reloaded, Amin definitional interpreters.
- Aliasing: RustBelt, Stacked Borrows, CORAL C borrow checker.
- Null-coalescing: Kotlin/Swift/C# semantics, Kinsbruner arXiv:2408.10804.
- Kahn: Kahn 1962, incremental topological arXiv:2402.11028.
- Reachability/GC: Sotoudeh 2025, Arborescent ISMM'25, Rocq+VST generational.

Language comparison per loop is in the Lean headers + below. Pattern:
other languages solve the *syntax* but leave the law unproved, or prove
safety but not the bound / cycle case / totality Morph proves.

## Loop 50 — Subtyping variance (DONE, Lean)
Target: loop 12's named refinement (function contravariance).
Delivered: `Morph/Specs/Subtyping/Lemmas.lean` (new file — the module had
only Spec+Examples). Proves function/linear-function are currently exact
(`isSubtype_function_eq`, `function_subtype_eq`), bottom/top extremal.
Explicit non-claim: no contravariance — needs a list relation mutually
inductive with `Sub` (core Lean `induction` does not support it) or a
further measure. Rust is contravariant, TS bivariant-unsound, OCaml
row-annotated, Linear Haskell refuses arrow subtyping. Morph stays exact:
sound but incomplete by design. Next: hand-written mutual recursor.

## Loop 51 — Effect typing (DONE, Lean)
Target: loop 6 open (no effect typing).
Delivered: `Eff.isPure` (`classes = []`), `isPure_pure`,
`handle_covered_pure` in `EffectAlgebra/Lemmas.lean`. Koka rows vs OCaml
5 untyped vs Unison abilities vs Affect affine+effects. Morph: structural
purity, handling only removes (Bauer-Pretnar non-monotone). No deep
handlers, no cost accounting — named, not approximated.

## Loop 52 — Dialect bridge (SPEC ONLY this batch)
Target: loop 7 open (no bridge to `Morph/Syntax.lean`, no refinement).
Analysis: best solution is translation validation per-pass
(`translate_preserves_eval` already) + a mechanical bridge mapping
`DialectSemantics.Term` to `Syntax.Expr` (binary/unary core vs 29-ctor
list-shaped form). Other languages: Hazel/MPS (structure only, no
denotation), LMS/multi-stage (staging annotations, no refusal totality).
Morph's problem (refusal totality `translate_core_iff_safe`) is one they
did not solve — they pass through. Lean work: define `toSyntax :
Term → Expr` + `eval_to_denote` (future loop, needs denotation of
`Syntax.Expr` which does not exist yet). Recorded, not faked.

## Loop 53 — Lexer lexAll (DONE, Lean)
Target: loop 9 open (token list not assembled, `lexAll` length open).
Delivered: `lexAllFuel`, `lexAllFuel_length_le`, `lexAll`,
`lexAll_length_le` + concrete disjointness witnesses
(`digit_zero_not_identStart`, `underscore_ident_not_digit`,
`hash_falls_through`) in `TotalLexer/Lemmas.lean`. Coqlex (proved
generation) vs tree-sitter/logos (total by construction, unproved).
Full `isAlpha`/`isDigit` disjointness needs `Char.toNat` range lemmas
core Lean lacks — named, witnesses proved.

## Loop 54 — Machine control cases (SPEC ONLY this batch)
Target: loop 10 open (~40 shipped rules vs β-only machine).
Analysis: best solution is Blazy et al. functional correspondence
(evaluators ↔ machines, proved for CEK in Rocq). Other languages: BEAM
(unverified scheduler), CompCert (small-step vs machine, proved but for
C, not de Bruijn). Morph's machine is deliberately unfaithful on control
cases; the bridge must be per-construct (`if`, `let`, `block`) with
`substAll` distribution lemmas (loop 49 now supplies the multi-arg
ingredient). Lean work: `Step.if_true` ↔ machine branch + `block`
append lemmas (future loop, needs machine control frames which do not
exist yet). Recorded.

## Loop 55 — Preservation (VERIFIED, no new Lean needed)
Target: ROADMAP 1.1 (6 sorries). Finding: repo-wide `grep sorry` in
`Morph/Proofs` is now 0; `lake build Morph` is green (386 jobs). The
ROADMAP_CONSOLIDATED already records sorry #1–6 fixed via
`HasType_subst_depth` mutuals + `HasType_substAll`/`HasTypeAll_substAll`
+ genuine `for_exec` semantics fix. This batch re-verified with full
build; no new sorries introduced (new files contain none). Gate holds.

## Loop 56 — Aliasing/use-after-free (DONE, Lean)
Target: loops 14/26 open (no aliasing, no `Memory.lean` connection).
Delivered: `aliases`, `aliases_refl`, `read_after_free_none`,
`write_after_free_noop` in `MemoryModel/Lemmas.lean`. RustBelt/Stacked
Borrows (safety, dynamic borrow) vs Perceus (paper proofs) vs ORCA
(unverified). Morph: affine removes cycles (loop 2), remaining is
use-after-free — proved unobservable. No refcount semantics, no
`Morph/Memory.lean` connection — named.

## Loop 57 — Null-coalescing typing (DONE, Lean)
Target: loops 15–16 open (no `??` type, no chain accounting).
Delivered: `resolveChain_all_null`, `resolveChain_null_head_length`,
`evaluate_right_assoc` in `OperatorNullCoalescing/Lemmas.lean`.
Kotlin/Swift/C# solve syntax + static projection but leave chain law
unproved; Kinsbruner unsoundness needs `!!` which Morph lacks. Full
char-class disjointness still needs stdlib range lemmas — witnesses only.

## Loop 58 — Linker transitive cycle (DONE, Lean)
Target: loop 18 open (no transitive detection, no LTO, no merging).
Delivered: Kahn detector alongside `acyclic` (`allNames`,
`depsInGraph`, `hasDepIn`, `kahnFuel`, `transitiveAcyclic`) +
`transitiveAcyclic_catches_two_cycle` (old says true),
`transitiveAcyclic_diamond_acyclic` (no false positive),
`transitiveAcyclic_catches_self` in `LinkerLogic/Lemmas.lean`.
`ld`/`lld` (unproved), `rustc` DFS+fuel (like loop 45), `ocamldep`
(unproved). No LTO safety, no symbol merging — named.

## Loop 59 — Reachability bridge + licenses (SPEC ONLY this batch)
Target: loops 21/34/40 opens (path-to-edges bridge, weak-edge marker,
`spec_license_invariants` WF).
Analysis: best solution is abstract-interpretation acyclicity +
verified generational GC (Rocq+VST 2026) for reachability; deontic
`isAllowed` (loop 34) needs WF hypothesis (licence names every action
it constrains). Other languages: Java (tracing handles cycles, no proof),
Pony (no proof). Lean work: `hasPath ↔ CommonTypes.hasCycle` bridge
needs path-to-edges lemma (different reachability defs); weak refs need
`ReferenceGraph` marker (shared type change, no consumer); license
invariants need WF hypothesis. All named, none approximated.

## Verification
- `lake build Morph.Specs.SimultaneousSubst.Lemmas` ✔ (repaired absorption
  + `substAll'_nil`; fixed `substAll_cons_list` map-map shape, bvar
  dependent rewrites, `subst_bvar_*` vs `substAll'_bvar_*` confusion).
- `lake build Morph.Specs.Subtyping.Lemmas` ✔ (new file).
- `lake build Morph.Specs.TotalLexer.Lemmas` ✔.
- `lake build Morph.Specs.OperatorNullCoalescing.Lemmas` ✔.
- `lake build Morph.Specs.LinkerLogic.Lemmas` ✔.
- `lake build Morph.Specs.MemoryModel.Lemmas` ✔.
- `lake build Morph.Specs.EffectAlgebra.Lemmas` ✔.
- Full `lake build Morph` ✔ (386 jobs, only pre-existing linter warnings).
- Sorry count: 0 in `Morph/Proofs`, 0 new sorries in new/edited files.
