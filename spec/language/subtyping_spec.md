# Subtyping Specification

* File:* `language/subtyping_spec.md`
* Version:* 1.0.0
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

## 3. The relation

`Sub` is a preorder on `Typ`:

| Rule | Meaning |
|---|---|
| `Sub.refl` | reflexivity |
| `Sub.never` | `neverType` is the **bottom** type |
| `Sub.unit` | `unitType` is the **top** type |
| `Sub.option` | `optionType` is covariant |
| `Sub.result` | `resultType` is covariant in both components |
| `Sub.array` | `arrayType` is covariant in its element; the length is exact |

`refType` is **invariant** in both capability and payload: handing a
`refType .iso (optionType τ)` where a `refType .iso τ` is expected would *widen*
what the holder may do with it, which is unsound in a capability system.

## 4. What is proved

| Theorem | Statement |
|---|---|
| `isSubtype` | a total, structural decision procedure |
| `isSubtype_sound` | `isSubtype τ σ = true → Sub τ σ` |
| `isSubtype_complete` | `Sub τ σ → isSubtype τ σ = true` |
| `instDecidableSub` | **`Decidable (Sub τ σ)`** — the decidability SG-005 asks for |
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
