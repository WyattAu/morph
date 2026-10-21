# Simultaneous Substitution Specification

* File:* `language/simultaneous_substitution_spec.md`
* Version:* 1.0.0
* Context:* Core semantics — the two substitution operations
* Formalism:* De Bruijn substitution, simultaneous and sequential
* Status:* Active (one law proved; the multi-argument result is open)
* Machine-checked in:* `Morph/Specs/SimultaneousSubst/`

---

## 1. Purpose and Scope

Morph has **two** substitution operations, and until now nothing related them:

- `subst' : Nat → Expr → Expr → Expr` — a *single* substitution with an implicit
  offset (used by the CEK machine);
- `substAll' : Nat → List Expr → Expr → Expr` — a *simultaneous* substitution
  with an explicit offset and a list of values (used by `Morph/Semantics.lean`'s
  β-rule `app_lam`).

Loop 10 proved they agree for a single argument. This specification states the
law that governs their interaction, and discharges the part of the multi-argument
result that is ready.

## 2. The lifting law (proved)

> **`subst_lifted`** — `subst' (k + m) (liftUnder m (k+1) w) v = liftUnder m k w`

Substituting into a term whose indices are all above the substitution point
merely shifts them down; and the shift is exactly the one the lift would have
performed. The indices below `m` are untouched, because they are below the
substitution point `k + m`.

This is **the law loop 5 explicitly declined to claim** (§6.3 of
`spec/language/subst_equational_theory_spec.md`): "the law 'lifting a
substituted term equals substituting the lifted term' needs the map-distribution
lemmas over `args.map`, which the current helpers do not yet provide". The
statement needed was sharper than loop 5 guessed: the law is about substituting
*into* a lifted term, and it holds at every offset.

It is what the multi-argument result needs, because a value inserted at a higher
level is shifted down by the next substitution — which is precisely what the
simultaneous substitution does to it.

## 3. Proof engineering

The proof is a strong induction on `nodeCount`, because `match_` arm bodies sit
two constructors deep — the same shape as loops 5 and 10, and the third time
this shape has been needed.

Two details worth recording:

- The lift produces `n + (k + 1)`, not `n + k + 1`, so side conditions must be
  stated in the *parenthesised* form or `simp` will not match them.
- The arms case needs `liftUnderArms`/`substAllArms`, whose per-arm offset is
  `m + vars.length` — the law has to be instantiated at that offset, not at `m`.

## 4. Worked examples (`Examples.lean`)

`subst_lifted` at offset zero, under a binder, and concretely:
`subst' 1 (liftUnder 1 2 (.bvar 0)) 7 = .bvar 0`.

## 5. Scope: explicit non-claims

1. **The multi-argument result is open.** The statement is
   `substAll' k vs e = seqSubst k vs e`, where `seqSubst` (defined in
   `Spec.lean`) applies the substitutions one at a time from the highest level
   down. The missing piece is the **absorption step**
   `substAll' k (v :: rest) e = subst' k (substAll' (k+1) rest e) v`; its `bvar`
   case must relate `n - k`, `j + 1` and `n - (k+1)` through `substAll'`'s
   *proof-carrying* `getElem` (`vs[n - k]` under `if h : n - k < vs.length`),
   and then invoke `subst_lifted`. The ingredient is proved; the index
   arithmetic that feeds it is not.
2. **Not a change to either operation.** Both `subst'` and `substAll'` are
   shipped and unchanged; this specification only relates them.
3. **No statement about the store, effects, or evaluation.** The correspondence
   for the *rest* of `Morph/Semantics.lean`'s rules is out of scope, as it was
   in loop 10.

## 6. Traceability

| Artifact | Location |
|---|---|
| The law, and `seqSubst` | `Morph/Specs/SimultaneousSubst/Spec.lean` |
| The law, computed | `Morph/Specs/SimultaneousSubst/Examples.lean` |
| Single-argument correspondence | `Morph/Specs/MachineRelation/` (loop 10) |
| The two operations | `Morph/Syntax.lean` |
