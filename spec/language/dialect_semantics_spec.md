# Dialect Semantics Specification

* File:* `language/dialect_semantics_spec.md`
* Version:* 1.0.0
* Context:* Multi-dialect pipeline — cross-dialect translation
* Formalism:* Translation validation over a denotational semantics
* Status:* Active
* Machine-checked in:* `Morph/Specs/DialectSemantics/`
* Closes:* SG-001

---

## 1. Purpose and Scope

This specification gives Morph's dialects a **denotational semantics** and
discharges **SG-001** — "Formal semantics for cross-dialect translation" — by
machine-checked *translation validation*: every accepted translation preserves
the denotation, and everything a target dialect may not perform is refused.

## 2. The gap this closes

`Morph/Specs/DialectProjection/` declares dialects, capability flags and a
lowering pass, and stops there:

| Defect | Evidence |
|---|---|
| No semantics | `lower` is documented "a structural pass-through; full lowering is dialect-specific" |
| No legality check | `lower` retags values without asking whether the *target* may perform the operations it is handed |
| Ad-hoc validity | `Projection.isValid` answers `True` for three hard-coded pairs, `False` otherwise, with no capability argument |
| No theorems | `DialectProjection/Lemmas.lean` contains only `rfl` facts about `List` and `Option` |

## 3. Definitions

### 3.1 Terms

`Term` is the binary/unary core of `DialectExpr`: a value tagged with the dialect
it is written in (`val`), arithmetic (`add`, `mul`, `sub`, `neg`), and the two
primitives that require authority (`rawptr`, `inlineAsm`).

The restriction to a binary/unary core is deliberate. With a denotational
semantics there is no list nesting to fight, so the entire theory is proved by
structural induction; the list-shaped `DialectExpr` is covered by the same
statements.

### 3.2 Capabilities

```lean
def permits (d : Dialect) (t : Term) : Bool
  | .val .. | .add .. | .mul .. | .sub .. | .neg .. => true
  | .rawptr .. | .inlineAsm .. => !decide (d = .core)
```

`core` is the restrictive endpoint; `unsafe` and `ffi` permit everything. This
is the capability test `lower` never made.

### 3.3 Denotation

```lean
def eval (d : Dialect) : Term → Option Nat
```

Two facts do the work:

1. **The dialect tag of a value is irrelevant to its denotation** — `eval (.val r d)`
   is `some r` for every `d`. Retagging is therefore safe.
2. **An authority-requiring primitive has no denotation** — `rawptr` and
   `inlineAsm` denote `none`. They manipulate machine state, which this
   semantics does not model. This is precisely *why* translation must refuse
   them rather than pass them through.

### 3.4 Translation

`translate target e : Option Term` retags every leaf to `target` and returns
`none` — *refuses* — when the target may not perform an operation it meets.
Refusal is what makes the preservation theorem say something: there is no path
that smuggles a forbidden operation into a permissive-looking term.

## 4. Requirements

| Theorem | Statement | Why |
|---|---|---|
| `translate_preserves_eval` | `translate t e = some e' → eval t e = eval t e'` | **the translation-validation obligation** |
| `translate_in_target` | `translate t e = some e' → dialectOf e' = t` | an accepted translation is entirely in the target dialect |
| `translate_unsafe_total` | every term translates into `unsafe` | the permissive endpoint refuses nothing |
| `translate_core_refuses_unsafe` | `¬ safe e → translate core e = none` | refusal is **total**, at any depth |
| `translate_core_accepts_safe` | `safe e → ∃ e', translate core e = some e'` | the check is not one-sided |
| `translate_core_iff_safe` | `(∃ e', translate core e = some e') ↔ safe e` | the capability check is **exact** |
| `lower_smuggles` | the old pass-through produces an accepted-but-illegal term | the counterexample motivating refusal |

## 5. Worked examples (`Examples.lean`)

`1 + 2 * 3` denotes `7` in both dialects, and the validation obligation is
discharged for it by computation. A `rawptr` program denotes nothing, is
refused by `core`, and is accepted by `unsafe`. Retagging is shown to be
invisible to `eval`.

## 6. Scope: explicit non-claims

1. **No operational semantics.** This is denotational; step-indexed refinement,
   loops and divergence are not modelled.
2. **No `ffi`/`core` distinction beyond capabilities.** The three dialects differ
   only in what they permit; there is no per-dialect value or memory model.
3. **`safe` is syntactic.** It is the *judgement* the `core` check performs, not a
   proof that a program is memory-safe.
4. **Not connected to `Morph/Syntax.lean`.** `Term` is a verification language,
   not the compiler's IR; the bridge to `DialectExpr` is mechanical but absent.
5. **No refinement**, only equality of denotations. A translation that computes
   *more* would be rejected here although it might be desirable.

## 7. Traceability

| Artifact | Location |
|---|---|
| Terms, capabilities, denotation, translation | `Morph/Specs/DialectSemantics/Spec.lean` |
| Validation obligations, refusal totality | `Morph/Specs/DialectSemantics/Lemmas.lean` |
| Discharged obligations, computed | `Morph/Specs/DialectSemantics/Examples.lean` |
| Superseded module (defects in §2) | `Morph/Specs/DialectProjection/` |
| SG-001 | `SPEC_GAPS_AND_BASIS.md` |
