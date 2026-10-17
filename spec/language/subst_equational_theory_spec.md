# Substitution Equational Theory Specification

* File:* `language/subst_equational_theory_spec.md`
* Version:* 1.0.0
* Context:* Core semantics — de Bruijn substitution and lifting
* Formalism:* $\lambda$-calculus with explicit de Bruijn indices
* Status:* Active
* Machine-checked in:* `Morph/Specs/SubstTheory/`

---

## 1. Purpose

This specification states and mechanizes the **equational theory of Morph's
substitution operation**: the equations and properties that must hold for
`subst'` and `liftUnder` to be a sound implementation of β-reduction.

Prior to this document, substitution had *no* stated theory. The equations
existed only as `example`s in `Morph/Tests/Semantics.lean`, and the preservation
proof (`Morph/Proofs/TypeSoundness/Preservation.lean`) routed around them using
private *depth* helpers. This document makes the theory explicit, reusable, and
machine-checked.

## 2. Research basis

| Source | Contribution to this specification |
|---|---|
| **POPLmark** (Aydemir, Bohannon, Fairbairn, Foster, Pierce, Sewell, Vytiniotis, Washburn, Weirich, Zdancewic; TPHOLs 2005) | Frames substitution lemmas as benchmark obligations — the "equational theory" section of the challenge. |
| **Autosubst** (Stark & Setzer; J. Log. Comput. 2018) | Generates, from a substitution signature, both the substitution operation *and* several equational lemmas. Establishes that the lemmas are *derivable by construction*, not by hand. |
| **Autosubst 2** (Stark & Setzer; IJDART 2021) | Extends Autosubst to multi-sorted de Bruijn terms. Morph requires this: named `fvar`s and de Bruijn `bvar`s coexist in one syntax. |
| **Well-scoped locally nameless** (recent WSLN representations) | The alternative that *removes* most of these lemmas by using free variables for bound ones. A representation change, not a proof addition; recorded as future work (§7). |

**Why not use Autosubst?** It is a Coq code generator, and `Morph.Syntax.Expr`
is a 29-constructor inductive with nested lists, match arms carrying pattern
variable lists, and two sorts of variable. The theory is therefore stated by
hand, in the shape Autosubst would have generated.

## 3. Syntax and operations

De Bruijn indices are natural numbers. `Expr` carries both sorts of variable:

- `.bvar n` — bound variable at index `n`, relative to the innermost binder.
- `.fvar s` — free (named) variable; never substituted.

| Operation | Definition | Meaning |
|---|---|---|
| `liftUnder b k e` | `Syntax.lean` | Add `k` to every index `≥ b`. |
| `lift k e` | `liftUnder 0 k e` | Lift all free indices — i.e. move `e` one context outward. |
| `subst' b e v` | `Syntax.lean` | Replace the variable at index `b` by `lift b v`, renumbering higher indices down. |

Both operations cross binders by raising the counter: under `lam n` the counter
becomes `b + n`, under `let_` and `forLoop` it becomes `b + 1`, and under a
`match_` arm it becomes `b + |pattern vars|`.

### 3.1 The measure that matters: scoping, not binder count

A natural first guess is `boundCount e` ("how many binders does `e` introduce")
with the law `i ≥ boundCount e → subst' i e v = e`. **That law is false**, and
the reason is instructive:

```lean
boundCount (.bvar n) = 0
```

A bare `.bvar n` introduces no binders, so `i ≥ boundCount e` constrains
nothing about `n` — yet substitution still needs `n < i` before it may leave the
index alone. The correct judgement is the standard scoping predicate:

```lean
Scoped i (.bvar n)        := n < i
Scoped i (lam n body)     := Scoped (i + n) body
Scoped i (let_ e1 e2)     := Scoped i e1 ∧ Scoped (i + 1) e2
Scoped i (match_ s arms)  := Scoped i s ∧ ∀ (vars, body) ∈ arms,
                                              Scoped (i + vars.length) body
```

`Scoped i e` says: every de Bruijn index *occurring* in `e` is below `i`. This
is the POPLmark/Autosubst "well-scoped at `i`" judgement, and it is precisely
the permission substitution needs. `boundCount` is retained in `Spec.lean` as
the binder-depth measure, but `Scoped` is what drives the theory.

## 4. Obligations discharged

### 4.1 The defining equations (`Lemmas.lean`)

| Theorem | Statement |
|---|---|
| `liftUnder_bvar_below` | `n < b → liftUnder b k (.bvar n) = .bvar n` |
| `liftUnder_bvar_above` | `b ≤ n → liftUnder b k (.bvar n) = .bvar (n + k)` |
| `subst_bvar_below` | `n < i → subst' i (.bvar n) v = .bvar n` — below the variable: untouched |
| `subst_bvar_hit` | `subst' i (.bvar i) v = lift i v` — the variable itself: replaced by the **lifted** substitute |
| `subst_bvar_above` | `i < n → subst' i (.bvar n) v = .bvar (n - 1)` — above: renumbered down |
| `subst_fvar`, `subst_lit` | named variables and literals are inert |
| `subst_lam`, `subst_let_`, `subst_ifThenElse` | the binder equations |

`subst_bvar_hit` is where the lifting discipline shows: the substitute is stored
*unlifted* and lifted only at the hit site (`lift b v`), so recursing under a
binder re-derives the correct depth instead of shifting the substitute twice.

### 4.2 No capture (`subst_above`)

> **`subst_above`** — `Scoped i e → subst' i e v = e`

If `e` only uses indices below `i`, substitution at `i` cannot reach any of
them, so it is the identity. This is the theorem POPLmark's β-case needs, and
the reason the existing preservation development resorted to depth helpers.

The proof is a strong induction on `nodeCount` (not a structural induction on
`Expr`), because `match_` arm bodies sit **two constructors deep** and a
structural induction cannot reach them. Two helper lemmas carry the list-typed
constructors (`app` arguments, `block`, `forLoop` body, `tuple_`, `arrayLit`) and
the match arms; each takes the term-level law restricted to list members, which
is exactly what the list induction can justify.

### 4.3 Worked examples (`Examples.lean`)

Substitution is checked to *compute* β-reduction, not merely to satisfy an
equation. The examples pin the index arithmetic:

- `subst' 1 (.lam 2 (.bvar 3)) (.bvar 0) = .lam 2 (.bvar 3)` — a reference to the
  enclosing context inside a two-parameter arrow is body index `k + n`; the
  lifted substitute keeps it pointing at the right slot. **This is the
  no-capture step, computed.**
- `subst' 1 (.lam 2 (.bvar 1)) (.bvar 0) = .lam 2 (.bvar 1)` — the arrow's own
  second parameter is not touched.
- `subst' 0 (.let_ (.bvar 0) (.bvar 1)) (.bvar 0) = .let_ (.bvar 0) (.bvar 1)` —
  `let` adds one binder.
- A two-variable `match` pattern pushes the arm body two levels below the
  scrutinee.

## 5. Invariant preserved

`Scoped i e` — substitution at `i` does not change the set of indices `e` uses
below `i`, hence never rebinds a variable `e` does not bind.

## 6. Scope: explicit non-claims

This specification discharges the **no-capture** obligation. It does **not**
claim:

1. **The typing substitution lemma.** `Γ, v : A ⊢ w ⟹ Γ, Γ' ⊢ subst' i w : A`.
   This needs the typing rules, not just the substitution algebra, and is proved
   by `HasType_subst` inside `Preservation.lean` today. Stating it here would
   duplicate rather than clarify.
2. **Composition.** `subst' i (subst' j e v) w = subst' j e (subst' i v w)`. The
   composition law for Morph's `subst'` is *not* the textbook one: because the
   substitute is lifted at the hit site rather than stored lifted, the naive
   statement is false and the correct one is index-shift-heavy. Worth a dedicated
   loop; deliberately not claimed here.
3. **Interaction with lifting.** The law "lifting a substituted term equals
   substituting the lifted term" needs `subst' i (liftUnder i k e) v =
   liftUnder (i+k) k (subst' (i+k) e v)`; proving it needs the map-distribution
   lemmas over `args.map`, which the current helpers do not yet provide. Not
   claimed.
4. **Algebraic laws about `fvar` renaming.** Named variables are inert by
   design; no renaming theory is stated.

## 7. Future work

- **Composition and lifting interaction** (§6.2–6.3): the two remaining
  POPLmark obligations, worth their own loop.
- **Well-scoped locally nameless**: representing open terms with free variables
  for bound ones makes most of §4.2 *unnecessary* — substitution becomes the
  identity on free variables and no shift/lift interaction is needed at all.
  This is the representation change that would let Morph delete rather than add
  lemmas.
- **Machine-checking the composition law against a model**: a decidable
  small-step semantics, with the algebra checked against it.

## 8. Traceability

| Artifact | Location |
|---|---|
| Measure and scoping predicate | `Morph/Specs/SubstTheory/Spec.lean` |
| Equations and `subst_above` | `Morph/Specs/SubstTheory/Lemmas.lean` |
| β-reduction examples | `Morph/Specs/SubstTheory/Examples.lean` |
| Consumer (β-case of preservation) | `Morph/Proofs/TypeSoundness/Preservation.lean` |
| Loop log | `docs/RESEARCH-LOOPS.md` |
