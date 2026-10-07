# Loop 01 — 2026-09-19

Whole-repo sweep, first pass. Focus problems this loop: P1, P2, P3 (where we
have concrete pain). P4–P12 swept for register completeness; their dedicated
sources land in Loop 2.

## Sources consulted

| Source | Problem | Access | Key finding used |
|--------|---------|--------|------------------|
| Bernardy, Boespflug, Newton, Peyton Jones, Spiwack — *Linear Haskell: practical linearity in a higher-order polymorphic language* (POPL 2018), [arXiv:1710.09756](https://arxiv.org/abs/1710.09756) | P1 | **fetched, abstract verified** | Linearity is attached to **function arrows** (multiplicity-annotated binders/arguments), *not* to context consumption. GHC-deployed. The paper's stated motivation is exactly our failure mode: prior linear systems lacked "a clear path forward to integrate." |
| Jung, Jourdan, Krebbers, Dreyer — *RustBelt: Securing the Foundations of the Rust Programming Language* (POPL 2018), [plv.mpi-sws.org/rustbelt/popl18](https://plv.mpi-sws.org/rustbelt/popl18/) | P3, P4, P9 | **fetched, abstract verified** | Soundness is proved for the *language semantics* via semantic typing in Iris (RustBelt). The borrow *checker* is not verified; soundness of accepted programs comes from the semantic model. |
| Weiss, Grier-Harvey, Harvey, Weirich — *Oxide: The Essence of Rust* (PLDI 2019) | P1, P3 | knowledge-based, **full-text fetch deferred to Loop 2** | Borrow checking stated as an axiomatic **typed relation** (environment with loans + framing), not a dataflow analysis — handles NLL "problem case 3" declaratively. |
| Matsakis — *Polonius* series + Datalog formulation (2018–2023) | P3 | knowledge-based, **fetch deferred to Loop 2** | The *implementable* borrow checker is Datalog over a CFG; this is what Rust actually ships, and it found bugs the non-Datalog NLL had. |
| Stark, Schäfer, Lochbihler — *Autosubst 2: Reasoning with Multi-Sorted Syntactic Algebras* (POPL 2021) | P2 | **fetch failed (404), retry via arXiv in Loop 2** | Automation for de Bruijn substitution reasoning, in Lean/Coq. |
| Clebsch et al. — *Deny Capabilities for Safe, Fast Actors* (Pony) | P4 | **fetch deferred to Loop 2** | 6-capability matrix incl. `trn` (construction) — comparison table owed. |
| Brady — *Koka/Perceus* (PLDI 2021) | P5, P6 | knowledge-based, **fetch deferred to Loop 2** | Linear/owned values enable precise reference counting with reuse; effects as first-class rows. |

## Adjudications

### P1 — Consumption discipline in binders: **ADAPT (design-changing)**

We have been formalizing consumption *in the context*: `bvar_type` advances a
usage slot; binders must erase their slot on exit. Six attempts at the
substitution lemma failed because slot-erasure does not compose under prefix
growth (ADR-010). Linear Haskell's central design move dissolves the problem
rather than solving it: **multiplicity lives on the binder/arrow, not in the
context**. The context is immutable during typing; a linear parameter's
single-use obligation is discharged at the *application site* (the argument
must match the arrow's multiplicity), and the only proof obligation involving
multiplicity is non-consuming substitution — which is exactly the lemma we
already have (`HasType_subst_depth`).

Disposition: adopt arrow/binder multiplicity. Consequences:

- `LinCtx` entries revert toward plain types; `Usage` moves into
  `functionType` (per-parameter multiplicity) and into the capability rules
  (`refFree` demands its argument be owned — an *argument-position* check, not
  a context mutation).
- `bvar_type`/`bvar_type_many` merge back into one rule.
- The stalled consumption-aware substitution lemma is **dropped, not
  proven** — the correct outcome when the design that demanded it is
  superseded.
- `HasTypeS`/`StoreTyped`/`safety_*` are untouched: capability discipline in
  the store layer is orthogonal and stays (it is our RustBelt-style semantic
  layer).

Honest cost: this re-opens `HasType` a third time. But it *deletes* machinery
(LinCtx threading, consume, merge-for-branches, the LinearId module) rather
than adding it, and it unblocks ADR-008 (walrus) for free, since substitution
is non-consuming.

Action: **ADR-014** (proposed, Loop 1) — "Multiplicity on binders, not
consumption in contexts." Implementation = Loop 2's proof adjustment.

### P2 — Variable/context representation: **ADAPT (second-line)**

Autosubst 2 automates exactly the de Bruijn substitution proofs that dominate
our cost, and targets Lean. Fetch failed; verify via arXiv in Loop 2 before
adopting tooling. Note the first-line fix for the *pain* is P1's redesign:
with non-consuming substitution, `HasType_subst_depth` already covers
everything and no new lemma class appears. `LinearId.lean` (levels/keyed
erasure) becomes unnecessary under P1 — mark it for deletion if ADR-014 is
accepted.

### P3 — Where borrow checking lives: **NOVEL claim withdrawn; ADAPT framing**

ADR-011 justified MIR placement by "path sensitivity needs an explicit CFG."
Oxide contradicts the strong version of that claim: borrow checking *can* be a
declarative relation. But the implemented, shipped technology (Polonius) is
Datalog over a CFG, and RustBelt shows the *soundness* argument does not need
the checker at all — semantic typing suffices. Correction to our register:
our `HasTypeS` + store invariant is already the RustBelt-style semantic layer;
ADR-011 stage 2 is therefore about **expressiveness** (accepting more good
programs), not soundness. ADR-011 to be annotated (Loop 1 action, small).

### P4 — Capability model: **ADAPT, comparison owed**

Pony's matrix adds `tag` (no read/write), `box` (read-only), `trn`
(transitional→val). Our `refCreate` produces `iso` directly and `refStore`
requires `cap ≠ .val`, which covers the safety core; `trn` is the one
capability with no Morph analogue (construction-then-freeze). Fetch the paper
in Loop 2 and produce the deny-capabilities matrix for Morph's `iso/val/ref`.

### P5 — Memory model: **open, candidate identified**

Koka's Perceus: owned/linear values enable precise, GC-free reference counting
with reuse. Morph's `iso` linearity is the same precondition. If Morph's
target story includes "no GC," Perceus-style RC is the natural match; actors
complicate it (cross-actor references). Loop 2: fetch Perceus + Pony ORCA.

### P6 — Effects: **open**

`EffectSet` is dead weight today. Decision queued behind Loop 2 (Koka/
Unison sources). Default if unresolved by Loop 4: delete `EffectSet` (REJECT)
rather than carry unused machinery.

### P7–P12 — carried to Loop 2

No adjudication this loop; sources queued (CakeML for P7, Actris for P8,
parametricity literature for P9).

## Spec changes made this loop

1. **ADR-014 proposed** — multiplicity on binders (P1 ADAPT). Status
   *Proposed*; implementation scheduled as Loop 2's proof adjustment.
2. **ADR-011 annotated** — stage 2 is an expressiveness pass; soundness rests
   on `HasTypeS` semantics (P3).
3. Register table updated in `RESEARCH_PROGRAM.md`.

## Proof changes made this loop

None. Loop 1 is adjudication; the P1 implementation is Loop 2's proof work
(and it *removes* blocked machinery rather than adding new proofs).

## Open questions carried to Loop 2

1. Fetch Autosubst 2 (arXiv) and decide tooling adoption for P2.
2. Fetch Oxide full text; extract the relation's exact judgment shape for the
   ADR-014 comparison section.
3. Fetch Pony paper → deny-capabilities matrix (P4).
4. Fetch Perceus + ORCA → memory/GC decision input (P5).
5. Begin ADR-014 implementation: multiplicity on `functionType`, drop
   `LinCtx` threading, delete `LinearId.lean`, re-prove progress/preservation
   (non-consuming substitution only).
