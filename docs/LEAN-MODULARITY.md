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
2. ✅ **Equation lemmas for the lowering (highest leverage).** Done:
   `Proofs.Branch.Equations` holds one `@[simp]` equation per
   `lowerStmtsCFG`/`runHIRStmts` constructor (31 total), proved from each
   definition's own `eq_def`/split lemmas. The lowering itself moved to
   `Morph/HIRToMIRLower` (byte-identical, Branch imports it back) so the
   leaf can cite the definitions without an import cycle. Migrated so
   far: 28 `have … := rfl` pins in the lookup families → equation
   rewrites, plus 47 `simp [lowerStmtsCFG, …]` sites whose explicit arg
   the ledger made redundant (linter-certified). `simp only
   [lowerStmtsCFG]` unfold sites stay: they use the auto lemmas and are
   already body-edit-robust.
3. **Unify the lookup inductions — verdict: shared vocabulary, not
   shared induction.** The three inductions cannot collapse, and the
   attempt proved it twice over: `arm_lookup` needs its own induction
   because `returnStmt` is terminal with an unconstrained tail
   (`boundIds` can be nonempty while every lookup is preserved —
   terminality, not binding-freedom — so no derivation via the binding
   lemma); the `loopBody` family needs its own because `varDecl` under
   `loop = some` is vacuous only via the lowering-refusal hypothesis
   threaded through each case. Same lesson as 2b: do not unify what the
   gate distinguishes. What unified: the equation vocabulary (2) plus
   the boilerplate shape; each family documents why it stands alone.
   Loop 185's corollary: matcher sharing is module-local (see facades).
4. **Thin the facade (started).** `Lowered`/`lowerStmtsCFG`/
   `lowerProgramCFG` moved to `Morph/HIRToMIRLower` (−283 lines from
   Branch); `backEdgePreds` (the back-edge filterMap lambda) was named
   as a shared def in the same move. Lesson from loop 185: Lean shares
   equation-compiler matchers only within a module, so an inlined
   `match`-containing term elaborated in two modules produces two
   matcher constants and `rw` silently stops matching. Rule: any
   `match`-containing term cited by both a definition and a proof in
   different modules must be a named def cited by both. Same-module
   copies keep working via interning and are out of scope.
   Remaining: Branch is still ~22k lines; continue per
   `PROOF-CRATES.md` extraction order.
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
