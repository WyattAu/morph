# Morph Research Program: Whole-Repo Iterative Adjudication

## Status
**Active** — 10 full loops planned. Loop 1 in progress.

## Purpose

The spec has accumulated decisions made under time pressure (ADRs 008–011, the
capability system, the binder representation, the memory model). Several are
now known to have structural problems — the clearest being the consumption/
binder interaction that has stalled Phase 1c-β-2 six times. This program runs
**10 full research loops** over the *whole repo* (not domain-focused passes):

each loop surveys current academic + industrial practice for every open problem
in the register, adjudicates whether Morph's approach is (a) solved better
elsewhere → adopt/adapt, (b) genuinely novel → document what others could not
solve, or (c) unnecessary → drop, then updates the spec and adjusts the Lean
proofs to match.

## Loop Protocol (every loop, every problem)

1. **Survey** — for each open problem `P` in the register, consult ≥2 external
   sources not yet consulted (papers, PLDI/POPL/ICFP proceedings, language
   docs, compiler internals). Record: mechanism, what it assumes, what it
   proves, what it cost them.
2. **Adjudicate** — classify:
   - `ADOPT` — their mechanism replaces ours outright.
   - `ADAPT` — their mechanism is the right shape; needs translation to our
     setting (state the translation and what breaks).
   - `NOVEL` — we are solving a problem they did not (document why, and what
     evidence exists that it is hard for them too).
   - `REJECT` — our approach is wrong; theirs doesn't apply; drop the feature
     or the claim.
   Every adjudication must cite what was consulted, and must state the
   **spec impact** and the **Lean impact** (or "none").
3. **Spec update** — ADRs and specs patched to match the adjudication. No
   spec text may claim a mechanism the proofs don't support.
4. **Proof adjustment** — Lean changes required by the spec update, keeping
   `lake build Morph` at 0 errors / 0 sorry.
5. **Log** — `loops/loop-NN.md` records: sources consulted (with links),
   adjudications, changes made, and the open questions carried into the next
   loop.

## Problem Register (v1)

| # | Problem | Current approach | Known weakness | Status after loop |
|---|---------|------------------|----------------|-------------------|
| P1 | Consumption discipline in binders | `Usage` threading in `HasType`; `bvar_type` consumes; substitution lemma stalled 6× | Erasure of the binder's slot does not compose under prefix growth (ADR-010 "remaining piece") | **Loop 1: superseded by ADR-014** (multiplicity on binders; Linear Haskell mechanism) |
| P2 | Variable/context representation | de Bruijn indices + hand-written lift/subst lemmas (~921 lines in Lemmas.lean) | Substitution proofs are the dominant cost; every language extension re-opens them | **Loop 2: closed** — resolved by P1/ADR-014 (non-consuming substitution only); autosubst2 re-evaluated only if a future feature re-opens substitution |
| P3 | Where borrow checking lives | ADR-011: MIR dataflow analysis (stage 2), surface `HasType` supplies discipline only | Unexamined whether a declarative (non-CFG) formulation exists that would let it live in the type system | **Loop 6: refined** — Oxide (fetched) proves borrow checking via progress+preservation as a substructural typing judgment; stage 2's correctness theorem should be Oxide-shaped; MIR stays the implementation path |
| P4 | Capability model completeness | 3 capabilities: iso/val/ref; `refStore` requires `cap ≠ .val` | Compare against Pony's 6-capability matrix; no construction-time capability (`trn`); no deny-capabilities matrix | **Loop 3: IMPLEMENTED** — `SafeCast` + `refCast` end-to-end; `safety_frozen_not_writable` proven; deny-matrix enforced by typing |
| P5 | Memory model verification level | CompCert-style typed store (`Store.lean`); freed list | No GC story for actors; store not related to a byte-level model for FFI | **Loop 4: ADJUDICATED** — Perceus-style RC primary (formalized in a linear calculus, proven sound+garbage-free; Morph now has the linearity substrate), CakeML verified GC as fallback; RC formalization belongs to the runtime milestone |
| P6 | Effects | `EffectSet` in Core.lean, unused | Decide: build an effect system (Koka/Unison-style) or delete `EffectSet` | **Loop 5: REJECT executed** — `Effect`, `EffectSet` and `Typ.effectFunctionType` deleted from Core.lean (they were referenced only by each other and by `eqTyp`/`WellTyped`/one test arm); an effect system would be designed together with the MIR stage-2 pass, not retrofitted onto the surface `Typ` |
| P7 | Verified compilation boundary | ADR-011: verify stages 1–3, trust backends at instruction selection | CakeML verifies end-to-end incl. GC; is our boundary justified or convenience? | **Loop 2: boundary justified as team-size trade** (CakeML falsifies impossibility); ADR-011 annotated |
| P8 | Actor/async verification | `Runtime.lean` actors; spec has process algebra | No verification story (Actris exists for Iris; Pony's ORCA unverified) | open |
| P9 | Generics + parametricity under capabilities | Not formalized | Variance/parametricity for capability-typed code is exactly where Rust struggled (RustBelt §) | open |
| P10 | Error handling | `Result`/`Option` types; error propagation as surface sugar | Interaction with effects (P6) unexamined | open |
| P11 | Conformance testing | `Executable.lean` interpreter as oracle | No differential-testing program against the Rust implementation | open |
| P12 | Binder syntax features blocked on P1 | Walrus deferred (ADR-008) | Unblocks with P1 | **Loop 1: unblocks with ADR-014** (non-consuming substitution) |
| P13 | Type-inference soundness | `inferType`/`synthType` executable checkers, no soundness theorem | CakeML proves its inferencer sound AND complete against declarative specs | **Loop 2: added** — prove `synthType ctx Γ e = some τ → HasType ctx Γ e τ` (Loop 3+) |

## Ground Rules

- **No sorry.** Any proof adjustment keeps `lake build Morph` at 0 errors,
  0 sorry. If a loop's adjudication requires proofs that can't be completed in
  the loop, the spec change is deferred with the proofs, never ahead of them.
- **Specs may not claim unproven mechanisms.** If we adopt a design whose
  soundness we have not formalized, the ADR says "proposed, formalization
  pending" and the gap is tracked here.
- **Every `NOVEL` claim must survive a search.** "We solve what they couldn't"
  is the most expensive claim in the register; it requires having actually
  looked.
- **Whole repo each loop.** No problem is dropped from the sweep because it is
  boring; `REJECT` is a result.

## Loop Index

| Loop | Date | Sources | Adjudications | Spec changes | Proof changes |
|------|------|---------|---------------|--------------|---------------|
| 1 | 2026-09-19 | 7 (2 fetched+verified, 5 knowledge/queued) | P1 ADOPT Linear-Haskell multiplicity (ADR-014 proposed); P2 ADAPT (deferred, autosubst2 fetch owed); P3 framing corrected (stage 2 = expressiveness); P4–P6 queued | ADR-014 proposed; ADR-011 annotated | none (Loop 2 implements ADR-014) |
| 2 | 2026-09-19 | 4 (1 fetched+verified [CakeML], 1 fetched nav-only [Pony], 2 knowledge/queued) | P2 closed (resolved by P1); P4 ADAPT (SafeCast specified); P5 constraint recorded; P6 defer w/ default-REJECT; P7 boundary justified; P13 added | ADR-010 amended (SafeCast); ADR-011 honesty note | ADR-014 stage 1 (linear arrows + countUses) started |
| 3 | 2026-09-19 | 2 fetched (George/Stark LFMTP'26 verified; Autosubst2 not on arXiv) | P4 SafeCast IMPLEMENTED (3 model-level findings: Δ-based cast, cap'≠.iso, preservationS transport); P2 tooling annotated | ADR-010 amendment upgraded to implemented | SafeCast end-to-end; `safety_frozen_not_writable` |
| 4 | 2026-09-19 | 1 fetched+verified (Perceus MSR); Oxide deferred | Residual ADR-014 strictness FIXED; P5 ADJUDICATED (RC primary, GC fallback); loop-03 self-audit correction | Register: P5 adjudicated | All judgment/checker pushes unified to `.many`; HT-36 acceptance test |
| 5 | 2026-09-19 | 0 (deferred to 6) | P6 REJECT executed; ADR-014 stage 2 executed; ADR-014 -> Accepted | ADR-014 status; register | Context revert (net -1,612 lines) |
| 6 | 2026-09-19 | 1 fetched+verified (Oxide arXiv:1903.00982); Pony deferred | P3 refined (stage-2 theorem should be Oxide-shaped: progress+preservation); P6 executed noted | ADR-011 stage-2 annotation | ROADMAP 1.9a: Morph/MIR.lean (CFG IR + WF + eval oracle) |
| 5 | 2026-10-08 | 0 fetched (sources deferred: Oxide/Pony full texts owed to Loop 6) | P6 REJECT executed (Effect/EffectSet/effectFunctionType deleted); ADR-014 stage 2 executed (context revert to `List Typ`; `LinCtx`/`Usage` machinery, `LinearId.lean`, `LinearContext.lean` deleted; P13 checker/inference-soundness restated on plain lists) | ADR-014 → Accepted (stage 1 + 2); register P6 closed | Full revert: Spec/Lemmas/Preservation/Progress/Soundness/StoreTyping/InferenceSound/TypeChecker + tests back on plain `List Typ`, keeping `linearFunctionType`+`countUses`, `SafeCast`/`refCast` end-to-end, and the P13 soundness fixes (`.loc`/`ok`/`err` literals → none, annotation checks) |
