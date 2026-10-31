# Simultaneous Substitution Specification

* File:* `language/simultaneous_substitution_spec.md`
* Version:* 1.0.0
* Context:* Core semantics — the two substitution operations
* Formalism:* De Bruijn substitution, simultaneous and sequential
* Status:* Active (both laws proved)
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
two laws that govern their interaction — the lifting law and the
multi-argument absorption law — and both are now proved.

## 2. Requirements: the lifting law (proved)

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

## 3. Requirements: the multi-argument law (proved)

> **`substAll'_eq_seqSubst`** — `substAll' k vs e = seqSubst k vs e`

`seqSubst` (defined in `Spec.lean`) applies the substitutions one at a time
from the highest level down. The proof goes through the **absorption step**

> **`substAll_cons`** — `substAll' k (v :: rest) e =
>   subst' k (substAll' (k + 1) rest e) v`

and then inducts on the value list. `substAll_eq_seqSubst` is the shipped
offset-zero form (`substAll`).

## 4. Proof engineering

Both proofs are strong inductions on `nodeCount`, because `match_` arm bodies
sit two constructors deep — the same shape as loops 5 and 10, and the third
time this shape has been needed.

Details worth recording:

- The lift produces `n + (k + 1)`, not `n + k + 1`, so side conditions must be
  stated in the *parenthesised* form or `simp` will not match them.
- The arms case needs `liftUnderArms`/`substAllArms`, whose per-arm offset is
  `m + vars.length` — the law has to be instantiated at that offset, not at `m`.
- `substAll'`'s fallback is `n - vs.length`, *not* `n - k - vs.length`. In the
  "above the value list" branch of absorption the two sides are therefore
  `.bvar (n - (rest.length + 1))` and `.bvar ((n - rest.length) - 1)`; `omega`
  closes the equality once the list length is exposed.
- In the "hit in `rest`" branch, the index identity
  `n - k = (n - (k + 1)) + 1` feeds `List.getElem_cons_succ`, and the value is
  then shifted back with `subst_lifted`.

## 5. Worked examples (`Examples.lean`)

`subst_lifted` at offset zero, under a binder, and concretely:
`subst' 1 (liftUnder 1 2 (.bvar 0)) 7 = .bvar 0`. For the multi-argument law:
the three `bvar` cases (`n = k`, `n = k + 1`, `n` above the list), a term with
two holes and a free variable, a substitution under a binder, and the generic
`substAll = seqSubst` equation.

## 6. Scope: explicit non-claims

1. **Not a change to either operation.** Both `subst'` and `substAll'` are
   shipped and unchanged; this specification only relates them.
2. **No statement about the store, effects, or evaluation.** The correspondence
   for the *rest* of `Morph/Semantics.lean`'s rules is out of scope, as it was
   in loop 10.

## 7. Traceability

| Artifact | Location |
|---|---|
| The laws, and `seqSubst` | `Morph/Specs/SimultaneousSubst/Spec.lean` |
| The proofs | `Morph/Specs/SimultaneousSubst/Lemmas.lean` |
| The laws, computed | `Morph/Specs/SimultaneousSubst/Examples.lean` |
| Single-argument correspondence | `Morph/Specs/MachineRelation/` (loop 10) |
| The two operations | `Morph/Syntax.lean` |
