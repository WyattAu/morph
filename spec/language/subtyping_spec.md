# Subtyping Specification

* File:* `language/subtyping_spec.md`
* Version:* 1.1.0
* Context:* Type system — subtyping and its decidability
* Formalism:* Preorder on `Typ` with a decision procedure
* Status:* Active
* Machine-checked in:* `Morph/Specs/Subtyping/`
* Closes:* SG-005

---

## 1. Purpose and Scope

Morph had **no subtyping**. `Morph/Specs/TypeSystem/Spec.lean` declared a
relation called `Subtype` that derived only equality, and nothing in
`HasType`, `inferType` or `typeCheck` consumed it. This specification supplies a
relation worth having, and proves it **decidable** — which is what SG-005 asked
for.

## 2. The gap, and the contradiction in the gap table

`SPEC_GAPS_AND_BASIS.md` marked GA-005 "Subtyping over `Typ` is decidable —
**Validated** — `instDecidableSubtype` (ADR-015): `isSubtype` decision
procedure", while SG-005 listed "Decidability proof for subtyping" as an
**open, High-priority** gap.

Both were about the same object, and both were wrong about it:

- `isSubtype` and `instDecidableSubtype` **do not exist** in the repository —
  not in the type system, not anywhere. No ADR-015 exists either. GA-005 was
  *Validated* against a decision procedure that was never written.
- The shipped `Subtype` relation is **exactly equality** (`subtype_iff_eq`):
  `refl` and `trans` over reflexivity derive nothing else, and nothing
  consumes it. Loop 1 recorded this.

This loop supplies the missing decision procedure, for a relation that means
something.

## 3. Definitions: the subtyping relation

`Sub` is a preorder on `Typ`:

| Rule | Meaning |
|---|---|
| `Sub.refl` | reflexivity |
| `Sub.never` | `neverType` is the **bottom** type |
| `Sub.unit` | `unitType` is the **top** type |
| `Sub.option` | `optionType` is covariant |
| `Sub.result` | `resultType` is covariant in both components |
| `Sub.array` | `arrayType` is covariant in its element; the length is exact |
| `Sub.tuple` | `tupleType` is covariant pointwise; the length is exact |
| `Sub.struct` | `structType` is covariant pointwise in field types; the struct name, field names (in order), and field count are exact |

`refType` is **invariant** in both capability and payload: handing a
`refType .iso (optionType τ)` where a `refType .iso τ` is expected would *widen*
what the holder may do with it, which is unsound in a capability system.

## 4. Requirements: what is proved

| Theorem | Statement |
|---|---|
| `isSubtype` | a total, structural decision procedure |
| `isSubtype_sound` | `isSubtype τ σ = true → Sub τ σ` |
| `isSubtype_complete` | `Sub τ σ → isSubtype τ σ = true` |
| `instDecidableSub` | **`Decidable (Sub τ σ)`** — the decidability SG-005 asks for |
| `isSubtypeList_sound` / `isSubtypeFields_sound` | soundness for the tuple-element and struct-field list relations |
| `isSubtypeList_refl` / `isSubtypeFields_refl` | pointwise reflexivity of the list relations |
| `sub_refl`, `sub_never`, `sub_unit` | the preorder's ends |
| `subtype_iff_eq` | the *old* `Subtype` relation is exactly equality |

## 5. Why this was hard: `Typ` has no derived decidable equality

`Typ` is a *nested* inductive (its `List Typ` fields make the `DecidableEq`
deriving handler inapplicable), and the derived `BEq` is **not lawful** — there
is no `LawfulBEq` instance, so `x == y` cannot be used to decide `x = y`. This
is why the shipped code had to build `eqTyp` by hand, prove it lawful against
propositional `=`, and derive the `DecidableEq` instance from *that* (§73–§83
and §412–418 of `Morph/Specs/TypeSystem/Spec.lean`).

`Subtyping` reuses exactly that machinery: `isSubtype` compares with `eqTyp`,
and the soundness proof uses `eqTyp_iff` to turn a comparison into an equality.
**SG-005 was not a missing proof; it was a missing decision procedure, and the
procedure was blocked on a missing lawful equality — which already existed, two
hundred lines away, in a module nobody had connected.**

## 6. Scope: explicit non-claims

1. **No function contravariance.** `functionType` and `linearFunctionType` are
   compared *exactly* here, not contravariantly. Adding variance needs a list
   relation `SubList` that is mutually inductive with `Sub` — and core Lean's
   `induction` does not support mutual inductives, so the completeness proof
   needs either a hand-written mutual recursor or a further measure argument.
   This is the single most important refinement left, and it is named here
   rather than approximated with a weaker relation.
   (Update: done in `Morph/Specs/Subtyping/Lemmas.lean` — loop 61 as the
   conservative extension `SubX`/`isSubtypeFun`, loop 70 as the full
   internalization `SubV`/`isSubV` with soundness and completeness. The
   shipped `Sub`/`isSubtype` specified here stay exact.)
2. **Not used by the type checker.** `HasType` and `inferType` still compute and
   compare *exact* types. This specification supplies the relation and its
   decidability; wiring it into the checker is a separate change.
3. **No algorithmic subtyping rules** (no subsumption in `HasType`).
4. **No type-variable rules** (no unification); `typeVar` is exact.

## 7. Traceability

| Artifact | Location |
|---|---|
| Relation, decision procedure, theorems | `Morph/Specs/Subtyping/Spec.lean` |
| Decidability, computed | `Morph/Specs/Subtyping/Examples.lean` |
| The lawful equality this builds on | `Morph/Specs/TypeSystem/Spec.lean` (§73, §412) |
| The relation it replaces | `Morph/Specs/TypeSystem/Spec.lean` (line 681) |
| SG-005 | `SPEC_GAPS_AND_BASIS.md` |
| Tuple/struct covariance (§8) | §8 of this file — machine-checked alongside §§3–4 |

---

## 8. Amendment (checked): covariant tuples and structs

*Status:* **Machine-checked.** `Sub.tuple`/`Sub.struct`, the two
`isSubtype` arms, and their soundness/completeness cases are proved in
`Morph/Specs/Subtyping/Spec.lean`; worked examples (including a nested
`optionType`-of-struct witness) are decided in
`Morph/Specs/Subtyping/Examples.lean`. What follows is the rule set as
shipped, with the soundness argument that justifies it.

### 8.1 Precedent

The `arrayType` rule (§3) is the template: **covariant payload, exact
shape** — `Sub.array` recurses into the element type while the length
is compared with `decide (n = m)`. Tuples and structs get the same
treatment: variance in the payload positions, exactness everywhere
else. No new measure machinery is needed: tuple elements shrink `tSl`,
struct fields shrink `tSlF`.

### 8.2 Rules (as shipped)

| Rule | Meaning |
|---|---|
| `Sub.tuple` | `tupleType` is covariant pointwise; the length is exact |
| `Sub.struct` | `structType` is covariant pointwise in field types; the struct name, the field-name list (in order), and the field count are exact |

In words: `tupleType ts <: tupleType ts'` iff the lists have equal
length and each `ts[i] <: ts'[i]`; `structType nm fs <: structType nm'
fs'` iff `nm = nm'`, the field names agree pairwise in order, and each
field type is pointwise related. Both recurse through `Sub` itself.

### 8.3 What stays exact, and why

- **Struct names.** Field lookup (`field_ e name`, `structFieldType`) is
  by name *within a named struct*. Dropping the name requirement would
  turn structs into row types — a separate feature with its own
  exhaustiveness story in `match_type` arms.
- **Lengths and field-name lists (in order).** Mirrors the array
  rule and the shape of `eqTyps`/`eqTypFields`, keeping the future
  decision-procedure arms one line each. Field permutation and width
  subtyping (extra fields) are separable extensions; use sites are
  by-name, so neither is needed for the first step.
- **`refType` payloads.** Recursion through `Sub` preserves refType
  invariance (§3): a field of type `refType .mut τ` can only be related
  exactly, so mutable payloads never widen. Tuples and structs carry no
  capability annotation of their own, so covariant reads are sound.
- **`typeVar`, function arrows.** Unchanged (exact here; arrows vary
  only in `SubX`/`SubV`).

### 8.4 Decidability (as shipped)

Two new `isSubtype` arms following the existing equation-compiler style
(`isSubtypeList`, `isSubtypeFields` as sibling `mutual def`s, since
core Lean's equation compiler does not see through the `Bool.and`
partial application):

- tuples: `decide (ts.length = ts'.length) && isSubtypeList ts ts'`;
- structs: `decide (nm = nm') && isSubtypeFields fs fs'`.

Termination is by the shipped measures (elements shrink `tSl`, field
types shrink `tSlF`). Soundness extends the fuel induction with one
case per new arm; completeness goes through the generated mutual
recursor `Sub.rec` (motives `motive_1/2/3`), the same technique as loop
70. Slotting the two rules into `SubV`/`isSubV` (tuples via
`SubListV`, structs via a fields relation) remains future work.

### 8.5 Non-goals

1. **No width subtyping** (a struct with more fields is not a subtype
   of one with fewer).
2. **No field permutation** (in-order comparison only).
3. **No structural structs** (the name requirement stays).
4. **No checker wiring** (still §6.2).

---

## 9. Transitivity — the preorder claim, discharged (loop 96)

Section 3 called `Sub` a preorder; reflexivity shipped with the relation, but
transitivity was never proved — so subsumption chains (the reason subtyping
is usable at depth) had no warrant. Machine-checked now in
`Morph/Specs/Subtyping/Lemmas.lean` (loop 96):

| Theorem | Statement |
|---|---|
| `Sub_trans` | `Sub τ σ → Sub σ υ → Sub τ υ` — by mutual recursion on derivations through the joint recursor, with trans-shaped auxiliary motives for `SubList`/`SubFields` |
| `SubList_trans` | pointwise transitivity on tuple elements (derived by inversion: `sub_tuple_inv (Sub_trans (.tuple h1) (.tuple h2))`) |
| `SubFields_trans` | pointwise transitivity on struct fields (inversion at a fixed struct name) |
| `SubList_refl` / `SubFields_refl` | pointwise reflexivity, structurally |
| `SubX_trans` | transitivity through the loop-61 contravariant function extension |

Proof-shape notes for future loops: `Sub`/`SubList`/`SubFields` are mutually
inductive, so plain `induction` is unavailable; the proof goes through
`Morph.Specs.Subtyping.Sub.rec` (the joint recursor) with `motive_2`/`motive_3`
instantiated to the corresponding transitivity statements. In `cases` on the
second derivation, the target type is substituted away — inversion hypotheses
must be applied with `_` in the refined position.

## 10. Relation to algebraic and set-theoretic subtyping (loop 96, non-claims)

Research position (papers pulled and analyzed in loop 96):

- **Dolan, MLsub** (POPL 2017) and **Parreaux, Simple-sub** (ICFP 2020):
  *algebraic* subtyping — types as elements of a distributive lattice,
  biunification for inference, union/intersection types, compact principal
  types. The strongest known inference story for subtyping.
- **Castagna et al., semantic/set-theoretic subtyping** (CDuce lineage;
  Laurent, *Implementing Set-Theoretic Types*): subtyping as set inclusion
  over a value interpretation; decidable, but the decision problem requires
  coinductive regular types and is far more expensive (EXPTIME-class in
  general) than structural comparison.
- **Brandt & Henglein** (TLCA 1997): the coinductive closure underlying both
  schools has as its finite fragment exactly the derivability relation —
  which is why a finite derivation system must prove transitivity explicitly
  (§9).

Morph's relation is the *syntactic structural* school (Parreaux's third
school: inference rules over type syntax). Deliberate non-adoptions, with
reasons:

1. **No union/intersection types.** They buy principal types with subtyping,
   at the cost of semantic interpretation, negation, and DNF-based decision
   procedures. Morph's rows (effects) and closed class set give the needed
   expressiveness for the language Morph is; nothing in the runtime or ABI
   consumes union types.
2. **No equirecursive types.** Set-theoretic subtyping needs regular
   coinductive terms; Morph's affine discipline keeps data finite and
   acyclic by construction (memory-model spec §2.6.7), so recursive type
   comparison is not required for soundness.
3. **No polar (input/output) type separation.** MLsub's polarity discipline
   conflicts with `refType`'s invariance (§3): a capability reference is
   neither strictly positive nor negative. Invariance is the price of the
   capability system and is kept.
4. **Principal types with subtyping** remain future work for the inference
   module (loop 101's target); when attempted, Simple-sub (not MLsub's
   biunification) is the reference algorithm, per Parreaux's own evaluation
   showing the two agree on a million generated programs.

## 11. Change Log

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.1.0 | 2026-10-31 | Research loop 96 | **Transitivity proved (§9):** `Sub_trans`, `SubList_trans`, `SubFields_trans`, `SubX_trans` machine-checked — the preorder claim of §3 is now fully discharged; **position paper §10:** relation to MLsub/Simple-sub algebraic subtyping and Castagna set-theoretic subtyping recorded with four reasoned non-adoptions |
| 1.0.0 | 2026-05-29 | Research loop 12 | Initial version: structural `Sub` relation, `isSubtype` decision procedure, soundness + completeness + decidability (`instDecidableSub`), closing SG-005 |
