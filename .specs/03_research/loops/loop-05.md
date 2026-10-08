# Loop 05 — 2026-10-08

Whole-repo sweep. Focus: ADR-014 stage 2 (context revert) and the P6
default-REJECT. No new external sources this loop — the owed Oxide and Pony
full-text reviews are deferred to Loop 6 (stated honestly; neither
adjudication executed this loop depended on them).

## Sources consulted

| Source | Problem | Access | Key finding used |
|--------|---------|--------|------------------|
| — (none fetched) | — | Oxide full text and Pony capability matrix **deferred to Loop 6** (context budget consumed by the revert; no P-register adjudication this loop needed them) | — |

The loop's work was execution of two already-adjudicated decisions
(ADR-014 stage 2: Loop 1 proposal + Loop 2 stage 1 + Loop 4 residual fix; P6
REJECT: Loop 2 defer with default-REJECT, confirmed by Loop 4). The only
"survey" input was the repo's own history: the pre-1c-α commit `d5f9306`
supplied the exact target shapes for `HasType`/`HasTypeAll`/`ArmsTyped`, the
weakening family, canonical forms, and tests.

## Adjudications

### P6 (Effects): **REJECT executed**

The default fired. `Effect`, `EffectSet`, and — necessarily —
`Typ.effectFunctionType` (its third field was `EffectSet`; it was the only
in-Core reference) are deleted from `Morph/Core.lean`, together with the
`DecidableEq Effect` deriving added in P13. External references checked first
(`rg "\bEffect" Morph/`): `Morph/Specs/MorphLanguage` and
`Morph/Specs/MonadicEffect` define their *own* namespaced `Effect` types and
are unaffected. Fall-out handled: `eqTyp`/`tS` cases and
`WellTyped.effectFunctionType_wf` in Spec.lean, one test arm in
Tests/Core.lean. Rationale recorded in the register row: an effect system,
if ever built, belongs to the MIR stage-2 design, not retrofitted onto the
surface `Typ`.

### ADR-014 stage 2 (context revert): **IMPLEMENTED**

`HasType : List Typ → TypEnv → Expr → Typ → Prop` — plain contexts, no
output context, no `Usage` anywhere in the typing path. What was deleted,
kept, and restored:

- **Deleted:** `LinCtx`/`LinEntry`/`Usage` (`Morph/LinearContext.lean` deleted
  outright — nothing referenced it after the revert), `Morph/LinearId.lean`
  (level-keyed erasure, moot), `linPushMany` and every entry-level index
  bridge, `HasType_ctx_step`/`HasType_empty_ctx_out`, `bvar_type_many` /
  `bvar_type` split (single non-consuming `bvar_type` again), the
  entries-frame weakening/substitution family (`weakening_entries_at`,
  `HasType_substAll_entries`, `HasType_iterSubst_lin`),
  `HasType_subst_consuming_bvar0` and `value_does_not_consume` (the consuming
  lemma ADR-014 drops; without context threading the latter is vacuous),
  `inferTypeC`/`inferTypesC`/`binopResult`'s mid-context threading, and the
  output-context component of every judgment/checker/soundness statement.
- **Kept against `d5f9306` (post-d5f9306 features preserved):**
  `Typ.linearFunctionType` with `lam_linear_type` (countUses premise) and
  `app_linear_type` in the judgment; the countUses lift/subst lemmas
  (`countUses_liftUnder_below/_above`, `countUses_substAll'_below`) and
  `substAll'_singleton` — restated context-free, exactly as they were; the
  `lam_linear` case of `WellTypedValue`; the P13 checker soundness fixes
  (`.loc`/`.ok`/`.err`/tuple/array value literals → `none`, `typeAsc`/
  `refCreate` annotation checks, `refStore` capability + type checks,
  empty-`for`-body and empty-block rejection); ADR-010's `SafeCast` +
  `refCast` end-to-end (Semantics/Store untouched; `HasTypeS` restated on
  plain lists; `safety_frozen_not_writable` intact); `eqTyp`-based
  `DecidableEq Typ`.
- **Checker:** `inferType : List Typ → TypEnv → Expr → Option Typ`
  (non-threading), `checkType_sound_true : checkType ctx Γ e expected = true
  → HasType ctx Γ e expected`, `inferType`'s `.app` branch accepts both arrow
  kinds, `checkType` pushes `paramTys.reverse ++ bvs` for both and keeps the
  `countUses` side condition for the linear arrow.
- **`app_lam` under preservation:** closes via the plain-list
  `HasType_iterSubst` for both arrows — on plain lists `lam_linear_type`'s
  body premise has the same shape as `lam_type`'s, so the countUses premise
  is discharged by construction (no reconstruction needed).
- **Deliberate checker restructures** (behavior-preserving, proof-driven):
  `ifThenElse`/`pipe`/`arrayIndex` use nested matches instead of paired
  matches, and `.app` uses `inferTypes` + list equality instead of
  length/zip checks — the inferred types and accept/reject behavior are
  unchanged.

Acceptance tests: HT-33–36 restated on `List Typ` spellings; HT-27/29 stay
`none` (P13 fixes); HT-01–32, HT-ALL-01–03 and the inversion tests restored
to the `d5f9306` shapes.

## Spec changes

- `ADR-014`: Status → **Accepted (implemented, stage 1 + stage 2)**; Follow-up
  records both implementation loops and the deletions.
- ADR-013 does not exist as a file (never written); the register/ADR-014 text
  carries the withdrawal. ADR-011's reference to `LinCtx.merge` is moot under
  ADR-014 (no merge operator exists anywhere now).

## Proof changes

See above. `lake build Morph Morph.Tests`: **347 jobs, 0 errors, 0 warnings,
0 sorry, 0 axioms.**

## Open questions carried into Loop 6

- Oxide full-text review (P3, owed since Loop 4) and Pony capability-matrix
  review (P4 comparison) — now owed with interest.
- MIR stage-2 vocabulary: with `LinearContext.lean` deleted, the MIR borrow
  checker designs its own lattice (ADR-011 stage 2); the walrus feature
  (ADR-008/P12) is unblocked on the non-consuming substitution machinery.
