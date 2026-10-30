# Research Loops 80–89 — Property Testing Track

Loop 79 closed the last named surface item (`fix`). From here the track turns
toward *properties of the shipped implementation*: universal statements over
the evaluator and the parse/pretty-print round trip, checked by Plausible
sampling (`#test`), `native_decide`, and proof — instead of single-example
driver pins.

## Loop 80 — property tests over the evaluator and the round trip (DONE, Lean)

**Target.** The `Morph/Tests/Property.lean` module sampled four `#test`
properties but proved nothing about the shipped pipeline: no universal
statement over `evalWithFuel`, and no check that `exprStr` output reparses
to the same tree. This loop closes both, in the style the file already uses
(sampling where types lack decidability, proof/examples where they do).

**Delivered.**
- `Arbitrary`/`Shrinkable` instances for `Phase`, `BlockId`,
  `ProvenanceId`, `Pointer`, `Value` (constructor-discriminated shrink),
  `Typ` (base types), and `Operator` (full 24-constructor enumeration), so
  `plausible` can generate random test values. No `lakefile.lean` change
  was needed: `Plausible` resolves through the existing
  mathlib/batteries/aesop dependency closure (pinned in
  `lake-manifest.json`).
- `EvalLawProperties` (new): five *universal* theorems over the shipped
  evaluator, all with explicit `k + n` fuel so the equation lemmas fire
  (`fuel 0` evaluates nothing, so the statements need positive fuel):
  literals evaluate at any positive fuel; negation is involutive
  (`- -n = n` via `omega`); addition commutes on evaluated literals;
  a `for` loop whose bounds already meet runs zero iterations without
  touching the body (even a stuck one); `none ?? e` is `e` up to one fuel
  unit for the dispatch.
- `RoundTripProperties` (new): six `native_decide` pins that `exprStr`
  output reparses to the same tree — nested mixed-precedence operators,
  unary minus through its parentheses, `if`, `for` through its bare
  surface (loop 78b), single-level `??`, single-level `|>`. Same style as
  `Morph.Tests.Driver` (seeded `parse`, `==` on the tree).
- Pre-existing sections untouched: `CoreProperties`, `OperatorProperties`
  (disjointness + `Semantics`/`TypeSystem` classification agreement),
  `TypeInversionProperties` (now noting the `lit_int_width` disjunction),
  `EvalProperties` (div/mod-by-zero `none`), `LiftSubstProperties`
  (concrete `substAll' ... []` identity cases; the general law lives in
  `Lemmas.lean` as `liftUnder_zero_eq` because `substAll'` uses
  well-founded recursion and resists `rfl`).

**Still named.** `Expr` has neither `BEq`-lawful equality bridges nor
`Arbitrary`, so inversion/lift properties stay concrete examples rather
than sampled `#test`s (same `DecidableEq`-vs-`BEq` gap `Core.lean` and
loop 79 document). Value comparison in `tests/differential` stays future
work: the Lean/Rust top-level intersect is still empty and Rust `run`
still does not execute, so verdicts — not values — compare.

## Verification

- `lake build Morph Morph.Tests morph` ✔ (408 + 229 jobs); zero `sorry`,
  zero `axiom`, zero `example : True` stubs repo-wide.
- `Morph.Tests.Property` reports 4× `Unable to find a counter-example`
  (the `#test` sample pins); the 5 eval laws + 6 round-trip pins typecheck
  as theorems/examples.
- `tests/differential/diff.sh` ✔ 8/8 cases match the manifest (4 Lean-ok /
  Rust-reject, 4 Rust-ok / Lean-reject — the documented divergence map).
- `spec-tools` pytest ✔ 803 passed, 96.04% coverage.
- Counts at commit: 209 `.lean` files / ~42.3k lines, 1130
  `theorem`/`lemma` declarations.
