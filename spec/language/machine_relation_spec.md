# Machine ↔ Relation Specification

* File:* `language/machine_relation_spec.md`
* Version:* 1.0.0
* Context:* Core semantics — two semantics, connected
* Formalism:* Equational theory of de Bruijn substitution
* Status:* Active
* Machine-checked in:* `Morph/Specs/MachineRelation/`
* Completes:* loop 10 (`machine_iff_step`)

---

## 1. Purpose and Scope

This specification closes the gap left by loop 10: `Morph/Semantics.lean` and
`Morph/Specs/ExecutionMachine/` were **two different semantics**, connected by
nothing. This document proves the one fact that makes their disagreement
impossible for β-reduction.

## 2. Definitions: the finding (simultaneous vs single substitution)

The shipped β-rule is

```lean
| app_lam : ∀ σ n body args,
    args.length = n →
    Step σ (.app (.lam n body) args) σ (substAll args.reverse body)
```

`substAll' : Nat → List Expr → Expr → Expr` is a *simultaneous* substitution: it
takes an explicit offset `k` and a **list** of values, and at an index hit it
applies `lift k (vs[n - k])`.

The CEK machine's β-rule uses `subst' : Nat → Expr → Expr → Expr` — a *single*
substitution with an implicit offset, which folds the offset into the traversal
and applies `lift b v` at the hit site.

Different functions. So the two β-rules were not obviously the same, and nothing
in the repository said they were.

## 3. Requirements: the equivalence theorem

> **`substAll_single`** — for every offset `k`, value `v` and term `e`:
> `substAll' k [v] e = subst' k e v`

Proved for **every offset**, not just offset 0. That is what makes the statement
worth having: under a `lam` both recursions raise the offset, and that is exactly
where a disagreement would surface. The proof is a strong induction on `nodeCount`
(same shape as loop 5, because `match_` arm bodies sit two constructors deep),
with two helper lemmas for the list-shaped and arm-shaped subterms.

**Consequence.** `app_lam` with `args = [v]`, `n = 1` — and therefore
`args.reverse = [v]` — reaches exactly the expression the machine's β-step
computes. The two semantics cannot disagree about β-reduction.

## 4. Worked examples (`Examples.lean`)

`subst' 0 (.bvar 0) (.lit 3) = substAll [(.lit 3)] (.bvar 0) = .lit 3`, and the
same agreement at offset 1 (inside a binder).

## 5. Scope: explicit non-claims

1. **β only.** `app_lam` is one of ~40 rules in `Morph/Semantics.lean`. `binop`,
   `field_`, `refStore` and the rest are **not** related to the machine, and the
   machine's own control cases are deliberately unfaithful (loop 10, §6).
2. **Single argument.** `app_lam` takes a list; this covers only `|args| = 1`.
   The multi-argument case is where the two substitutions would *really* differ —
   `substAll` substitutes simultaneously, `subst'` only ever one value — and it
   needs a genuine lemma relating sequential to simultaneous substitution, not
   this one.
3. **Not the store.** `Morph/Semantics.lean`'s `Step` is indexed by a `Store`; the
   relation above is between the *expression* components only.
4. **No theorem about stores, memory or effects.**

## 6. Traceability

| Artifact | Location |
|---|---|
| The theorem and its helpers | `Morph/Specs/MachineRelation/Spec.lean` |
| Both β-rules, computed | `Morph/Specs/MachineRelation/Examples.lean` |
| The machine | `Morph/Specs/ExecutionMachine/` (loop 10) |
| The shipped relation | `Morph/Semantics.lean` |
| The substitution algebra reused | `Morph/Specs/SubstTheory/` (loop 5) |
