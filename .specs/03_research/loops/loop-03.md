# Loop 03 — 2026-09-19

Whole-repo sweep. Focus: implement Loop 2's adjudications (P4 SafeCast, P13
queued), plus the owed source verifications.

## Sources consulted

| Source | Problem | Access | Key finding used |
|--------|---------|--------|------------------|
| George & Stark — *Work-in-Progress: A Tactic for Pattern Matching in Autosubst* (LFMTP 2026, [arXiv:2607.12657](https://arxiv.org/abs/2607.12657)) | P2 | **fetched via arXiv API, abstract verified** | The Autosubst line is active: the newest work targets exactly the gap Autosubst 1/2 left — *matching against typing rules and reduction relations*, evaluated on POPLMark (Reloaded). Confirms P2's closed disposition was right to defer tooling (the tooling now exists for the problem we no longer have), and gives a live citation should substitution pain return. |
| Autosubst 2 (POPL 2021, Stark/Schäfer/Lochbihler) | P2 | **not on arXiv** (ACM); knowledge-based | Tool existence corroborated via the 2026 successor. |
| Pony reference-capabilities docs | P4 | fetched — nav only (content is in the paper) | Matrix semantics from Clebsch et al. stands as knowledge-based; full paper text still owed. |
| Oxide full text | P3 | **deferred to Loop 4** (context budget) | P3's adjudication did not depend on it. |

## Adjudications

### P4 — SafeCast: **IMPLEMENTED (this loop)**

End-to-end in Lean, with three substantive findings recorded as deviations:

1. **The capability lives in Δ, not in the heap cell.** In the ADR-010 store
   model the cell holds the *pointee* type+value; the capability is a
   declaration in the store typing. The faithful `refCast` is therefore a
   **Δ re-declaration** (`StoreTyp.cast`), not a heap rewrite — a heap rewrite
   would have broken `StoreTyped`. The step rule checks liveness; typing
   enforces the deny-matrix.
2. **`cap' ≠ .iso` on the cast target.** `ValueType.loc` forbids `iso` (that
   forbidding is what makes `free_invalidates` work), so a cast *to* `iso` is
   rejected at typing. `refl_iso` is thus effectively unused for casting
   *between locations* — the reflexive iso entry survives only in the relation.
3. **`preservationS_gen`'s same-store component weakened**: a cast changes a
   location value's *type* without touching the store, so "same store ⟹ same
   typing" is false across a cast. The transport is sound
   (`valueType_cast_stable`: a value mentioning the cast location forces a
   non-iso declared capability, and the only SafeCast out of a non-iso
   capability is reflexive).

New safety corollary, proven: **`safety_frozen_not_writable`** — after
`iso → val` on `loc`, the store invariant holds, Δ declares `loc : refType val`,
and *no* well-typed `refStore` may target `loc`. The deny-matrix is enforced by
typing, not by runtime checks.

### P13 — inference soundness: **queued (next)**

`synthType ctx Γ e = some τ → HasType ctx Γ e τ` — CakeML frontend-2
discipline. `inferType` returns `none` for store-typed forms (`refLoad` etc.),
so the theorem is over the surface subset only; completeness is a stretch
goal.

### P2 — tooling note (closed, annotated)

The George/Stark LFMTP 2026 tactic is the tool to revisit **if** a future
language feature re-opens de Bruijn matching pain. Register stays closed.

## Spec changes made this loop

1. **ADR-010 amendment upgraded to implemented**: `SafeCast` exists in Lean
   (`Morph/Store.lean`) with the exact ADR shape; deviations recorded
   (Δ-based cast; typing-only deny-matrix enforcement) — the ADR's sketch of a
   heap rewrite was wrong and the implementation is the correction.

## Proof changes made this loop

1. **SafeCast end-to-end** (see adjudication): `Expr.refCast`, step rules
   (`ref_cast_step`/`ref_cast_done`/`ref_cast_eval`), `Store.castType` +
   invariant lemmas, `HasTypeS.refCast`/`refCast_cong`, `progressS`/
   `preservationS` extension, `safety_frozen_not_writable`.
2. Tests: store-layer step/preservation instances, the frozen corollary
   end-to-end, `SafeCast .val .ref → False`.

## Open questions carried to Loop 4

1. **P13 implementation** (inference soundness) — next proof item.
2. **ADR-014 stage 2**: revert `HasType`'s signature threading (the plumbing
   is inert and now blocks nothing, but it is unused complexity).
3. Owed full texts: Oxide, Pony paper, Perceus (Loop 4).
4. P6 default-REJECT for `EffectSet` fires at Loop 5 if still undecided.
