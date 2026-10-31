# Stability policy

Morph versions semantically (`MAJOR.MINOR.PATCH`). Pre-1.0, the minor
number is the breaking-change boundary; patch releases change no
user-visible behavior except bug fixes. This policy covers what each tier
promises as of 0.1.0.

## Stable (breaking changes only at a minor bump)

- **CLI surface.** The commands `eval`, `parse`, `check`, `run`
  (with and without `--hir`), `fmt`, `doc`, `version`; the exit-code
  contract (values exit 0, everything else exits 1).
- **Error text.** Every user-visible error report is pinned by golden
  tests (`Morph/Tests/Driver.lean`, `Morph/Tests/Typing.lean`). Changing
  one byte of a report is a breaking change and must update the golden
  deliberately.
- **Core surface syntax.** The expression and statement forms the parser
  accepts today keep parsing with the same ASTs. The proved-total parser
  is the compatibility anchor: sinking behavior must stay total.
- **`fmt` canonical form.** The `hum` rendering of any program that parses
  today keeps rendering identically (fixpoint goldens pin this).
- **Proof invariants.** 0 `sorry`, 0 axioms, 0 build warnings; the
  regression snapshot must show no regressions on any release.

## Experimental (may change in any release)

- **`run --hir` fragment membership.** Which programs lower is expected to
  grow; the unsupported *message text* is golden-pinned, the membership
  boundary is not.
- **`doc` Markdown shape.** The `///` convention (document the next
  statement) is stable; the exact Markdown layout may evolve.
- **Spec Props.** Formal spec statements may be weakened when refutations
  demand it; every weakening is logged in `SPEC_CONTRADICTIONS.md`
  (see #11 for the current instance).

## Policy mechanics

- Every release ships a `CHANGELOG.md` entry and a regression snapshot
  (`scripts/regression-snapshot.sh`) with no regressions.
- Deprecations: one minor release of warning (golden updated in the same
  change that introduces the replacement) before removal.
- Long-term target (per `LONGTERM_ROADMAP.md`): 3-version compatibility
  window once the language reaches 1.0.
