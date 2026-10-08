# Loop 06 — 2026-09-19

Whole-repo sweep. Construction loop: ROADMAP 1.9a (MIR data type) delivered;
owed research fetches partially cleared; one major P3 refinement.

## Sources consulted

| Source | Problem | Access | Key finding used |
|--------|---------|--------|------------------|
| Weiss, Gierczak, Patterson, Ahmed — *Oxide: The Essence of Rust* (PLDI 2019; v4 2021), [arXiv:1903.00982](https://arxiv.org/abs/1903.00982) | P3 | **fetched, abstract verified** (author list corrected: v4 is Weiss/Gierczak/Patterson/Ahmed) | Two findings: (a) borrow checking is a **substructural typing judgment** that *automatically computes* lifetime/provenance information — no CFG required for the soundness story; (b) it comes with "**the first syntactic proof of type safety for borrow checking using progress and preservation**" — the exact proof architecture Morph already runs for `HasType`/`HasTypeS`. |
| Pony paper full text | P4 | **deferred to Loop 7** (the SafeCast implementation already encodes the matrix entries Morph needs; the paper would refine `trn`/`tag`/`box` expressiveness questions only) | — |

## Adjudications

### P3 — refined: the borrow-checker soundness path has two viable shapes

Loop 1 recorded ADR-011's framing (MIR dataflow) and the RustBelt correction
(soundness = semantic typing). Oxide adds the missing middle option:

1. **Oxide path**: extend the typing judgment substructurally (Oxide-style);
   soundness by progress + preservation — Morph's existing proof architecture,
   in its existing prover.
2. **ADR-011 path**: keep the surface judgment simple; check ownership in MIR
   by dataflow; soundness by `HasTypeS` semantics (RustBelt arrangement).

These are not mutually exclusive: Oxide is the *verification* path, MIR
dataflow is the *implementation/engineering* path (Rust ships Datalog-over-CFG
precisely because the declarative judgment alone underspecifies the
algorithm). **Decision for the register**: keep ADR-011's MIR placement for
stages 1–2 implementation, but record that stage 2's *soundness argument*
should be Oxide-shaped — i.e. when stage 2 lands, its correctness theorem
should be stated as a typing-like judgment with progress/preservation-style
lemmas, not as raw dataflow-correctness. ADR-011 annotated.

### P6 — EffectSet REJECT: **EXECUTED (this loop's spec/proof change)**

Per the Loop 2 disposition and Loop 4 confirmation: `Effect`, `EffectSet`,
and `Typ.effectFunctionType` deleted. The frozen `MonadicEffect` aspirational
spec carries its own string-based vocabulary and is untouched (separate
design, out of scope). If a future loop wants effects, the Granule-graded
route (effects as grades alongside multiplicity on arrows) is the recorded
starting point.

### 1.9a — MIR data type: **DELIVERED (this loop's construction)**

`Morph/MIR.lean` (namespace `Morph.MIR`): `ValId`/`BlockId`/`FnId`, `BinOp`/
`UnOp` (with `toOperator` surface mappings), `Instr` (const/copy/unop/binop/
load/store/alloc/free/call/phi), `Terminator` (goto/branch/return_/switch),
`Block`, `Func`, `Program`; computable well-formedness (`wfBlockUse`,
`WFCFG`, `WFParams`, `WF` — use-before-def within blocks, CFG target/entry/
uniqueness checks) with a proven soundness statement
(`wfBlockUse_sound`); an evaluation oracle for the pure instructions that
*delegates to `Morph.Executable`* so the MIR oracle cannot drift from the
surface interpreter. The superseded tree-IR sketch in the old `Morph/MIR.lean`
is replaced. Tests: WF positive/negative cases including the documented
single-block assumption.

## Spec changes made this loop

1. ADR-011 annotated: stage 2's correctness theorem should be Oxide-shaped
   (typing judgment with progress/preservation lemmas), not raw dataflow.
2. Register updated (P3 refinement, P6 executed, 1.9a delivered).

## Proof changes made this loop

1. `Morph/MIR.lean` + `Morph/Tests/MIR.lean` (1.9a, above).

## Open questions carried to Loop 7

1. Owed full texts: Pony paper (P4 refinement), Oxide §judgment details (for
   the stage-2 shape) — Loop 7.
2. **ROADMAP 1.9 stage 1** — lambda lowering `Expr → MIR` with
   `lowering_correct` (the first real correctness theorem of the pipeline).
   Scope note: pure subset first (no closures — ADR-012 blocking question).
3. P13 completeness (stretch, unscheduled).
