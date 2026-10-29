# Research Loops 60–69 — Machine, Memory, Linker, End-to-End Soundness

Follow-up decade to `RESEARCH-LOOPS-50-59.md`: close loop 54's open machine
control cases, loop 56's aliasing remainder, loop 58/59's linker and
reachability work, and finish with the checker's end-to-end soundness plus a
full-project verification gate. Lean implementation where tractable/additive
(no breaking changes); `lake build` green at the end.

Pattern (same as loops 26–59): find the property the module names, prove it
if true, refute it if false, replace the stub if it is an advertisement —
and where the shipped artifact already does the right thing, prove the
bridge rather than rewriting the artifact.

## Loop 60 — Execution machine model (DONE, Lean)

Target: the machine module had Spec but no Lemmas (loop 54's analysis
assumed machine control frames "do not exist yet" — the machine itself
needed its base lemmas first).

Delivered: `Morph/Specs/ExecutionMachine/Lemmas.lean` (new file).
`step_deterministic` (definitional — `step` is a function), `run_zero` /
`run_succ` / `run_add` (fuel algebra), `final_lit_int` / `final_lit_bool` /
`final_lam` (final-state denotations), `final_not_nil_kont`,
`step_lit_control` / `step_lit_cases`, `Env.lookup_nil` /
`Env.extend_lookup_hit`.

## Loop 61 — Contravariant function subtyping (DONE, Lean)

Target: loop 50's explicit non-claim (no contravariance — "needs a list
relation mutually inductive with `Sub`").

Delivered: additive extension in `Morph/Specs/Subtyping/Lemmas.lean`.
`isSubtypeList` (decidable argument-list relation) with `refl` and
`sound`; `SubX` (the extended relation: `refl`, `of_never`, `to_unit`);
`isSubtypeFun` (decidable contravariant arrow check) with
`isSubtypeFun_sound` and `isSubtypeFun_extends` (accepts everything the
exact `isSubtype` accepts). The shipped checker stays exact; the
contravariant relation lives alongside it with a soundness proof, not a
rewrite.

## Loop 62 — Effect row typing + deep handlers (DONE, Lean)

Target: loop 51's row/handler remainder (loop 51 proved purity; rows and
handler depth were named, not proved).

Delivered: `Eff.hasRow` (the row is `EffectSet`, containment is the
typing), `hasRow_pure` / `hasRow_mono` / `hasRow_extend` (row polymorphism
is weakening/extension), `handle_op_deep` (the fold equation for the deep
handler `denote` already is) contrasted with `shallowHead` (head-operation
only). Research: Koka rows, OCaml 5 one-shot deep handlers, Hillerström &
Lindley shallow-vs-deep, Plotkin & Pretnar. Morph: rows inferred by
containment, handlers deep.

## Loop 63 — Dialect bridge refinement (DONE, Lean)

Target: loop 52's SPEC-ONLY bridge (`toSyntax` + `eval_to_denote`
deferred for lack of a denotation target).

Delivered: `toExpr : Term → Option Morph.Syntax.Expr` in
`Morph/Specs/DialectSemantics/Lemmas.lean` — partial by honesty
(`rawptr`/`inlineAsm` have no surface counterpart and map to `none`),
total on the `safe` fragment, refusal on `¬safe`, and commuting with every
accepted `translate` (embedding factors through translation since
translation only retags and `toExpr` erases tags). Boundary (named, not
approximated): denotational correspondence is still deferred —
`Morph/Semantics.lean` has a small-step relation but no big-step evaluator
to state it against. What is proved is the structural refinement.

## Loop 64 — Machine control cases (DONE, Lean)

Target: loop 54's SPEC-ONLY analysis (the bridge "needs machine control
frames which do not exist yet").

Delivered: the frames now exist. `Morph/Specs/ExecutionMachine/Spec.lean`
extends `Frame` with `letBody` and `seqRest` (plus `arg`/`ifThenElse`
coverage), and `Lemmas.lean` proves `step_if_pushes` (condition evaluates
under a pushed branch frame), `step_let_pushes` (init under a pushed body
frame), and `step_block_nil`. The per-construct correspondence loop 54
prescribed is now stated against real machine structure.

## Loop 65 — Memory connection + aliasing safety (DONE, Lean)

Target: loop 56's remainder (connect `Morph.Specs.MemoryModel` to the
shipped `Morph.Memory`, prove the aliasing story).

Delivered: `projectBlock_wellformed`, `project_mem`, `freeBlock_not_allocated`,
`project_free_fst` / `project_free_none`, `read_after_morph_free_none`,
`allocate_fresh_present`, `allocate_noninterfering` in
`Morph/Specs/MemoryModel/Lemmas.lean`. The `BlockId` bridge uses the
core-level `LawfulBEq` (loops 12/14/18/33 fixed instances locally; the
source types now carry them). Boundary: the strong write-then-read value
statement needs a uniqueness hypothesis on the block list and is recorded
as such — proved for the missing-id case, named for the general case.

## Loop 66 — Linker binding algebra + LTO (DONE, Lean)

Target: loop 58's transitive-cycle remainder (merging and the real LTO
check).

Delivered: `resolveBinding_assoc` / `resolveBinding_idem` (binding
algebra), `resolveSymbols_singleton_fresh` (singleton-merge freshness),
`resolveSymbols_empty_new`, and a real whole-program check —
`allExports` / `allImportsResolved` / `ltoSafeStrong` with
`ltoSafeStrong_nil`, `ltoSafeStrong_clean`, `ltoSafeStrong_rejects_cycle`,
`ltoSafeStrong_rejects_dangling`, and the two implication directions
(`ltoSafeStrong_implies_acyclic`, `ltoSafeStrong_implies_resolved`) in
`Morph/Specs/LinkerLogic/Lemmas.lean`.

## Loop 67 — Reachability bridge + weak refs + GC (DONE, Lean)

Target: loop 59's SPEC-ONLY reachability bridge.

Delivered: the `Collected` collector contract as a *relation* (survivors
were present and root-reachable, edges preserved, reachable vertices
survive), the repaired `spec_deterministic_deallocation` (the old
statement concluded deallocation for *reachable* objects — backwards; it
now concludes it for the unreachable ones), and `reference_count_consistency`
pinning `weakReferences := 0` (the model has no weak edges: every incoming
edge is strong). Reachability transitivity and acyclicity/no-self-reachability
in `Morph/Specs/MemoryAcyclicity/`.

## Loop 68 — MemoryBounds examples + bounds safety (DONE, Lean)

Target: the module had Spec + Lemmas but no Examples (computed witnesses).

Delivered: `Morph/Specs/MemoryBounds/Examples.lean` (new file) — the
allocation bound and the quiescence headline on concrete heaps, kernel-checked
by evaluation. Bounds safety is witnessed, not just stated.

## Loop 69 — TypeSystem end-to-end soundness (DONE, Lean)

Target: compose the two halves that already existed — checker soundness
(`checkType_sound_true`, `InferenceSound.lean`) and store-free progress /
preservation (`Morph.Proofs.TypeSoundness`) — into one stated guarantee,
then verify the whole project and record the decade.

Delivered in `Morph/Specs/TypeSystem/StoreTyping.lean`: `checked_progress`
(a program the shipped checker accepts is a value or it steps),
`checked_preservation` (its step result is still well-typed), and
`checked_multistep_sound` (induction on the locally-defined `Run`
closure — this toolchain's core has no `ReflTransGen` — stepping through
`preservation` at each step). The store-aware counterparts remain
`progressS` / `preservationS`; bridging `HasType` to `HasTypeS` needs a
store typing for the locations involved and stays in the safety
corollaries' hypotheses. No sorries introduced.

## Verification

- `lake build Morph.Specs.TypeSystem.StoreTyping` — clean (the
  `Relation.ReflTransGen` reference failed: Lean 4.27 core does not know
  that identifier, hence the local `Run` inductive).
- Full `lake build` — completed successfully, exit 0.
- `.reports/spec-status.md` regenerated via `scripts/gen-spec-status.sh`
  (the root `SPEC_STATUS.md` is a stale 2026-05-18 snapshot in a different
  format; the script writes `.reports/spec-status.md`).
