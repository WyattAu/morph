# Lean modularity: diagnosis and restructuring plan

Measured 2026-11-22 (288 files, 93,503 lines). This doc diagnoses the
maintainability bottlenecks and sequences the fixes. Estate rule it serves:
leaves compose, never depend upward; the public surface is explicit.

## Diagnosis (measured, not stylistic)

1. **One file is a quarter of the codebase.** `Morph/HIRToMIRBranch.lean` is
   22,869 lines (24%); the next largest file is 2,175. 137 theorems live in
   it (~167 lines each). Everything else scales; this file does not.
2. **The external surface is tiny.** Only `Driver` and `ClifCfgEncode`
   import Branch, using ~3 definitions (`lowerProgramCFG`, `ifProg`,
   `runLowered`). 99% of the file is internal proof with no external
   readers — ideal leaf material, zero consumer migration.
3. **Proof scripts are copy-paste, not composition.** `simp only
   [lowerStmtsCFG] at h` appears 100×, `cases hr : lowerStmtsCFG` 86×,
   `obtain rfl := Option.some.inj h` 112×. Phase B touched ~30 if-case
   scripts by hand; each was a bespoke edit of the same 10-line shape.
   Cost of the next lowering change scales with site count, not with
   concept count.
4. **Parallel inductions over parallel grammars.** `runHIRStmts_arm_lookup`
   (`ArmStmts`), `loopBody_lookup_*` (~10 theorems, `LoopStmts`), and now
   `runHIRStmts_bindArm_lookup_diff` (`BindArmStmts`) prove the same shape
   three times. The grammars differ, but the HIR-step equations they case
   on are identical.
5. **Specs are healthy.** 68 spec dirs; 67 have the full
   `Spec`/`Lemmas`/`Examples` triple (only `BatchBCD` has 2 files).
   The triple pattern works — Stage C proofs are the exception, and the
   `Proofs.Branch.*` leaves are converging them to it.

## Plan (cheapest green cut first)

1. ✅ **Leaf-split the context-free definitions** (done, 4 leaves:
   `Merge`, `Fragments`, `Fuel`, `LoopAlloc`). Pattern is proven: move,
   import back, build, commit. Remaining candidates: block-assembly
   lemmas (`if_asm_*`, `while_assembly_nodup` — pure list reasoning) and
   the C3 worker helpers.
2. **Equation lemmas for the lowering (highest leverage).** The `Fuel`
   leaf already establishes the discipline: `armBlockBound_nil/if/while`
   simp equations, "never cite the definition name". Do the same for
   `lowerStmtsCFG` (one `@[simp]` equation per statement ctor) and for
   `runHIRStmts` (one per ctor). Then the 100 unfold-then-case scripts
   collapse to single rewrites, and the next lowering change touches 8
   equations instead of 100 scripts. Per-constructor equation first as
   pure addition; migrate scripts opportunistically (each migration is a
   small green commit, never a flag day).
3. **Unify the lookup inductions.** With `runHIRStmts` equations in place,
   each of the three lookup inductions becomes ~8 one-line cases. Then
   factor the shared case scripts (or a single parametric lemma over a
   "lookup-preserving step" relation). Do not unify the fragments
   themselves: `ArmStmts`/`LoopStmts`/`BindArmStmts` differ load-bearingly
   (the 2b unsoundness proved the gate cannot move).
4. **Thin the facade.** `HIRToMIRBranch.lean` becomes imports + lowering +
   top-level theorems, re-exporting leaves. Header documents the stable
   API (`lowerProgramCFG`, `ifProg`, `*_correct`) — the estate "public
   API surface" discipline. Consumers already use only these.
5. **Gates (extend `PROOF-CRATES.md` checklist):** no raw
   `lowerStmtsCFG`/`runHIRStmts` unfolding outside the equation file;
   every new induction cites the equation set; leaf layer check stays
   manual until CI.

## Non-goals (explicit)

- No fragment unification (`ArmStmts` vs `LoopStmts` vs `BindArmStmts`).
- No tactic framework beyond equation lemmas (no custom `macro` until
  (2) proves insufficient — equation lemmas compose with everything,
  macros compose with nothing).
- No file moves for readers (`Driver`, `ClifCfgEncode` keep importing
  `Morph.HIRToMIRBranch`, which re-exports).
