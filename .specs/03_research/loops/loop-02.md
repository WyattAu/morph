# Loop 02 — 2026-09-19

Whole-repo sweep. Focus: the problems Loop 1 queued — P2 follow-up, P4
(capability matrix), P5 (memory/GC), P6 (effects), P7 (compiler boundary).
P1's ADR-014 implementation begins this loop as the proof adjustment.

## Sources consulted

| Source | Problem | Access | Key finding used |
|--------|---------|--------|------------------|
| Pony — *Reference Capabilities* docs (ponylang.io/learn/reference-capabilities/) | P4 | fetched — nav only; capability semantics from Clebsch et al. paper (full text owed, Loop 3) | 6-capability matrix: iso/val/ref/tag/box/trn. Morph has the safety core (iso/val/ref); `trn` (construction-then-freeze) is the one capability with no Morph analogue. |
| CakeML — cakeml.org | P7, P11 | **fetched, content verified** | Verified compiler backend to machine code for **6 architectures** through 8 intermediate languages; parser and type inferencer **proved sound and complete** against declarative specs; bootstrapped compiler; PureCake (lazy FP) and Pancake (systems) verified compilers built on it. |
| Granule project (granule-project.github.io) | P6 | fetch failed (404 body), knowledge-based | Graded modal types: linearity as one grade among several (effects, intervals). Relevant to how Morph might unify `Mult` (ADR-014) with effects later. |
| Koka / Perceus (PLDI 2021) | P5 | knowledge-based, fetch deferred | Owned/linear values enable precise, GC-free reference counting with reuse. |

## Adjudications

### P2 — Variable representation: **RESOLVED BY P1 (ADR-014)**

The consuming-substitution wall was the sole reason the representation hurt.
Under ADR-014 (non-consuming substitution), `HasType_subst_depth` is the only
substitution soundness requirement and is already proven. Autosubst 2 remains
worth evaluating as *tooling* to shrink Lemmas.lean, but it is an optimization,
not a need: **status closed** (re-evaluate automation only if a future language
feature re-opens substitution proofs).

### P4 — Capability model: **ADAPT — add safe capability transitions**

Pony's matrix exposes a real gap that is *not* about missing capabilities but
about missing **transitions**. ADR-010 named "capability transitions
(iso → val, iso → ref)" and no rule exists. The Pony deny-matrix restricted to
Morph's three capabilities:

| from \ to | iso | val | ref |
|-----------|-----|-----|-----|
| **iso**   | ✓   | ✓ safe: uniqueness ⇒ no other observer can read while frozen | ✓ safe: alias within the region |
| **val**   | ✗   | ✓   | ✗ (val is deeply immutable; a mutable alias is unsound) |
| **ref**   | ✗   | ✗ unsafe: other `ref` aliases may still write | ✓ |

The load-bearing entry is **iso → val** (freeze): uniqueness makes freezing
sound without scan. `ref → val` must stay denied — this is exactly the
soundness property our `StoreInv` already tracks (uniqueness ⇒ no other
in-flight reference). `tag`/`box`/`trn` are expressiveness features, not
safety features: defer, revisit after the first demo milestone.

Action (Loop 3): `SafeCast : Capability → Capability → Prop` (reflexive on
iso/val/ref plus iso→val, iso→ref), a `refCast` step rule that rewrites the
store entry's type, a typing rule, and the preservation case — bounded.

### P5 — Memory model / GC: **open — RC vs GC decision deferred with a constraint**

Perceus gives GC-free precise RC *given* linearity — which ADR-014's linear
arrows now provide at the value level. Actors break pure RC (cross-actor
references need ORCA-style deferred reclamation). CakeML demonstrates a
*verified* GC is obtainable if we go that way. Decision deferred until a demo
needs large heaps; constraint recorded: **the store design must not preclude
either option** (current `Store` with explicit `freed` is compatible with both —
RC decrements on `refFree`, GC treats `freed` as a GC hint).

### P6 — Effects: **DEFER with a default**

Granule unifies linearity and effects as grades; Koka/Unison are the mature
row-effect designs. For Morph, effects interact with ADR-014's arrows
(effect rows would live on `functionType` next to multiplicity). Decision
deferred to Loop 4. **Default if undecided by Loop 5: REJECT — delete the
unused `EffectSet`** rather than carry vestigial machinery.

### P7 — Compiler verification boundary: **boundary justified — but honestly**

CakeML falsifies any "verification to machine code is infeasible" claim: they
verify end-to-end, including GC, for 6 architectures, and PureCake/Pancake show
the pattern generalizes to language front-ends. ADR-011's boundary (trust
instruction selection) is therefore a **team-size trade, not an impossibility
argument** — the ADR must say so. Adopted from CakeML: their **verified parser
and type inferencer against declarative specs** maps directly onto
`inferType`/`synthType`, which currently have no soundness theorem.

New register entry **P13**: prove `synthType`/`inferType` sound with respect to
`HasType` (`synthType ctx Γ e = some τ → HasType ctx Γ e τ`), completeness as a
stretch goal. This is CakeML-frontend-2 discipline and is prerequisite for
trusting compiler-rejects-programs arguments.

### P11 — Conformance: **noted (CakeML pattern)**

CakeML's proof-producing synthesis is out of scope, but their
"declarative spec → verified checker" discipline (P13) plus differential
testing against the interpreter oracle (existing plan) matches their structure.

## Spec changes made this loop

1. **ADR-010 amended** — capability safe-cast relation (`SafeCast`) specified
   with the deny-matrix above; Loop 3 implements in Lean.
2. **ADR-011 amended** — CakeML/PureCake falsify impossibility; boundary is a
   documented team-size trade; P13 queued.
3. Register updated (P2 closed, P13 added).

## Proof changes made this loop

1. **ADR-014 implementation started** — linear arrow type with syntactic
   single-use checking (`countUses`), non-consuming contexts. This is the
   accepted replacement for the stalled consumption design; it makes
   `let r = ref … in r`-style programs expressible and enforced.

## Open questions carried to Loop 3

1. Implement `SafeCast` (P4) in Lean + safety theorem.
2. P13: `inferType`/`synthType` soundness theorem.
3. Fetch: Autosubst 2 (arXiv), Oxide full text, Pony paper, Perceus (owed
   full-text verifications).
4. ADR-014 stage 2: revert `HasType`'s signature to non-threading (cleanup
   after the additive stage lands).
