# ADR-015: Decidable Structural Subtyping

## Status
**Accepted (implemented)** (Research loop 1 of the spec-hardening program;
see `docs/RESEARCH-LOOPS.md`). This ADR replaces the previous vacuous
`Subtype` relation (which had only `refl` and `trans`) with a structural,
decidable subtyping relation over `Morph.Core.Typ`, proved sound and complete
against an executable decision procedure.

## Context

Before loop 1, `Subtype` derived nothing beyond equality: it had no
structural rules, nothing in `HasType`/`typeCheck` consumed it, and GA-005
("the type system is decidable") recorded decidability as *assumed* over a
relation with no content (SG-005).

The research pass (papers + language survey, recorded in
`docs/RESEARCH-LOOPS.md`) established:

- Pierce (POPL 1992): F-sub subtyping is undecidable through quantifier
  re-bounding. Morph has no bounded quantification, so it stays in the
  decidable first-order (Brandt-Henglein) class.
- The correct algorithmic template is coinductive structural subtyping with
  definition-site variance; semantic subtyping (Castagna/CDuce) is the wrong
  fit because `Typ` has no union/intersection/negation connectives.
- Every surveyed language (Rust, Scala 3, TypeScript, OCaml, F*, Swift, C++,
  Linear Haskell) keeps integer widths out of subtyping; width changes are
  coercions.
- Linear Haskell deliberately refuses any subtyping between `⊸` and `→`;
  Granule solves grade ordering with SMT, not structural subtyping.
- **Genuinely unpublished corner** (recorded for future research, not
  attempted here): decidable subtyping *through* linear arrows with
  capability obligations. Morph takes the safe fallback (no rule between
  `linearFunctionType` and `functionType`).

## Decision

1. **Relation** (`Morph/Specs/TypeSystem/Spec.lean`): `Subtype` gains
   `never_bot` (bottom), covariance for `optionType`/`resultType`/`tupleType`
   (pointwise, same length)/`arrayType` element (length invariant),
   contravariant-parameter/covariant-result rules for `functionType` and
   `linearFunctionType` (same arity), and nominal `structType` (same name,
   same field order, pointwise fields) via the auxiliary pointwise relations
   `Subtypes` and `FieldsSub`.
2. **Invariant by design** (no rules): `intWidthType`, `floatType`
   (coercions, not subtyping), `refType` (mutable references are unsound
   under covariance; revisit when SecurityOCap grows a read-only capability),
   `pointerType`, `typeVar` (reflexive only).
3. **Algorithm**: executable `isSubtype`/`subTypes`/`fieldsSub` decide the
   relation by structural recursion (contravariance by argument swap);
   well-founded on summed type sizes.
4. **Proofs** (`Lemmas.lean`): `isSubtype_sound`, `isSubtype_complete`
   (with algorithm-level transitivity), and the
   `instDecidableSubtype` instance discharging GA-005.
5. **Infrastructure**: `Typ` gets a hand-written `instDecidableEqTyp`
   (Core.lean) — `deriving DecidableEq` cannot handle recursion through
   `List`, and the algorithm's equality guard requires lawful decidable
   equality, not bare `BEq`.

## Consequences

- GA-005 moves from "Assumed" to "Validated" (decision procedure + proof).
- `decide` works on `Subtype` goals; all examples in
  `TypeSystem/Examples.lean` are machine-checked through the instance.
- Subsumption is not yet wired into `HasType`/`typeCheck` (typing still
  infers exactly). Wiring subsumption into inference is deferred until the
  effects-system loop decides how inference failures should surface.
- 6 sorries recorded in older documents are already gone; the build is
  sorry-free.

## Verification

`lake build Morph`: 352 jobs, 0 errors, 0 sorry warnings. `grep -r sorry
Morph/` returns nothing.
