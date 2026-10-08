# ADR-014: Multiplicity on Binders, Not Consumption in Contexts

## Status
**Accepted (implemented, stage 1 + stage 2)** (Loop 1 adjudication, research
program; stage 1 — linear arrows + `countUses` — Loop 2; stage 2 — context
revert to plain `List Typ` — Loop 5). If accepted, supersedes the consumption
design of ADR-010 Phase 1c-β-2 for the binder problem; does **not** touch the
store model, `HasTypeS`, or the `safety_*` theorems. Supersedes ADR-010's
`Usage`-in-context design; ADR-013 (branch merge operator) is withdrawn — no
merge exists in this design.

## Context

ADR-010 Phase 1c put a usage discipline in the typing *context*: entries carry
a `Usage` (zero/one/many), `bvar_type` consumes its slot, binder rules erase
their slot on exit. Six attempts at the resulting substitution lemma stalled
on a concrete obstacle: removing the binder's slot does not compose under
prefix growth (verified counter-example in ADR-010 — nested `let` under
`pfx = [A, B]` erases a prefix entry instead of the slot). A level-keyed
erasure operation was built (`Morph/LinearId.lean`) and also proved
insufficient: the relation between a derivation's input and output context
requires erasure to compose with itself across recursion, and positional or
level-keyed single-slot removal does not.

Loop 1 of the research program consulted how deployed linear type systems
handle this. Linear Haskell (POPL 2018, GHC-deployed) makes the design move we
did not: **linearity is attached to function arrows and binder annotations,
and the context is never mutated during typing.** There is no slot to consume
and nothing to erase; a linear parameter's single-use obligation is discharged
at the application site, where the argument must match the arrow's declared
multiplicity. The only substitution lemma required is non-consuming — which
Morph already has and has already proven (`HasType_subst_depth`).

RustBelt (POPL 2018) independently supports the reframing on the ownership
side: soundness is proved for the *semantics* (semantic typing in Iris), not
for the checking algorithm. Morph's `HasTypeS` + store invariant already is
that semantic layer; the surface discipline feeds it but does not have to carry
the entire burden by itself.

## Decision

### 1. Multiplicity on binder positions in `functionType`

```lean
-- multiplicity of a parameter binding
inductive Mult where
  | zero    -- may be discarded (ignored parameter)
  | one     -- linear: used exactly once
  | many    -- unrestricted

-- per-parameter multiplicity, alongside the parameter type
structure Param where
  ty  : Typ
  mult : Mult

| lam_type : ∀ ctx Γ n body params retTy cbody,
    n = params.length →
    HasType ctx Γ body retTy cbody →
    HasType ctx Γ (.lam n body) (.functionType params retTy) ctx
```

The typing context reverts to plain types (`List Typ`). There is no `Usage`
in the context and no context threading: `HasType : List Typ → TypEnv →
Expr → Typ → Prop`, as it was before Phase 1c.

### 2. Use-site checks discharge the obligation

Each use of a parameter is checked against its binder's multiplicity *at the
place of use*, syntactically:

- A `one`-parameter must occur **exactly once** in the body, checked by the
  (executable) occurrence count — the same single-use check Koka/Granule-style
  systems perform on syntax, sound here because the check is per-binder
  syntactic occurrence, and sound *in general* because `HasTypeS` + the store
  invariant remain the semantic guarantee.
- A `many`-parameter may occur any number of times.
- A `zero`-parameter may not occur at all.

Capability operations keep their argument-position requirements
(`refFree` demands an `iso` argument; `refStore` demands `cap ≠ .val`), as
today.

### 3. What is deleted

- `LinCtx`, `Usage`-in-context, `bvar_type` consumption split, `consume`,
  `merge`, the context-threading `HasType` signature (Phase 1c-β), and
  `Morph/LinearId.lean` (level-keyed erasure — rendered moot: there is no slot
  to erase).
- The consumption-aware substitution lemma, as an *open problem*: it is
  dropped. Under this decision no such lemma is needed; `HasType_subst_depth`
  (non-consuming) is the only substitution soundness requirement and is
  already proven.

### 4. What is kept

- Store model, store-typed `HasTypeS`, `progressS`/`preservationS`, the five
  `safety_*` theorems (ADR-010 Phase 1d) — untouched.
- `HasTypeAll`/`ArmsTyped` revert to non-threading forms.
- ADR-008 (walrus) unblocks: substitution is non-consuming, so `x := e` and
  shadowing follow the existing substitution machinery.

## Consequences

### Positive
- The six-time-stalled proof obligation disappears by construction.
- Contexts become immutable during typing; every binder rule is context-blind
  again, so future language features stop re-opening the substitution proofs.
- Single-use checking becomes executable (`countUses`-style), matching the
  MIR stage-2 story in ADR-011: surface check for fast feedback, MIR analysis
  for path-sensitive acceptance, `HasTypeS` semantics for the soundness
  guarantee (RustBelt arrangement).

### Negative
- Single-use checking by syntactic occurrence is path-insensitive at the
  surface: `if c then f x else (g x; drop x)` is *rejected* (two occurrences)
  even though each branch uses `x` once. Rust handles this in MIR; ADR-011
  stage 2 is exactly where Morph recovers it. Documented as a known
  expressiveness gap, recovered at stage 2, guaranteed by `HasTypeS`.
- Third re-opening of `HasType`. Each prior re-opening shrank the machinery;
  this one deletes a subsystem.

### Follow-up
- Loop 2 implemented the decision (stage 1: `linearFunctionType`,
  `lam_linear_type`/`app_linear_type`, `countUses`).
- Loop 5 implemented stage 2 (context revert): `HasType : List Typ → TypEnv →
  Expr → Typ → Prop`, all post-1c context machinery deleted
  (`LinCtx`/`Usage`-in-context, `linPushMany`, `Morph/LinearId.lean`,
  `Morph/LinearContext.lean`), and P6's default-REJECT fired
  (`Effect`/`EffectSet`/`Typ.effectFunctionType` deleted).
- ADR-013 (branch merge operator) is withdrawn — no merge exists in this
  design.
- `RESEARCH_PROGRAM.md` register updated: P1 closes as `ADOPT` (Linear
  Haskell's mechanism), P12 (walrus) unblocks.

## References
- Bernardy, Boespflug, Newton, Peyton Jones, Spiwack — *Linear Haskell*
  (POPL 2018), arXiv:1710.09756.
- Jung, Jourdan, Krebbers, Dreyer — *RustBelt* (POPL 2018).
- Weiss, Grier-Harvey, Harvey, Weirich — *Oxide* (PLDI 2019) — declarative
  borrow relation; full-text review owed in Loop 2.
- ADR-010 §"Implementation Status" — the failure this supersedes.

## Date
2026-09-19

## Author
Wyatt (with Nexus research program, Loop 1)
