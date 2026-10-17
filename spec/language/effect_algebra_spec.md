# Effect Algebra Specification

* File:* `language/effect_algebra_spec.md`
* Version:* 1.0.0
* Context:* Core semantics — effects and handlers
* Formalism:* Algebraic effects, free-model monad
* Status:* Active
* Machine-checked in:* `Morph/Specs/EffectAlgebra/`

---

## 1. Purpose and Scope

This specification formalizes Morph's effect set `{IO, Net, Time, System}` as an
**algebraic theory**, with a free-model monad over it and handlers as models of
the theory.

### 1.1 Motivation

`Morph/Specs/MonadicEffect/Spec.lean` already declares a syntax for effectful
computations. That module has three defects, each of which makes it unusable as
a specification:

1. **There is no monad.** `EffectfulComputation.seq` is
   `seq (first : EffectfulComputation) (cont : String → EffectfulComputation)` —
   the continuation is keyed by `String`, not by the computation's result type.
   There is no `bind`, so no monadic laws can even be stated.
2. **There is no semantics.** Nothing defines what an effectful computation
   *means*. No reduction relation, no interpretation.
3. **`Lemmas.lean` contains no effect content.** Its two theorems are `rfl`
   facts about `Option.bind`.

And the effect collection function is documented as "shallow, one level":

```lean
/-- Collect all effect names from a computation (shallow, one level) -/
def EffectfulComputation.effectNames : EffectfulComputation -> EffectSet
  | ... | EffectfulComputation.seq c _ => c.effectNames
```

so it reports **none** of the effects performed under a continuation. Since the
continuation is exactly where a program's effects live, the function is wrong
for every non-trivial computation.

### 1.2 Scope

This specification covers:

- the operation signature of Morph's four effect classes;
- the free-model monad over that signature;
- the induced interpretation (`denote`) and its homomorphism property;
- effect-set collection, complete through continuations;
- handler coverage, and the non-monotonicity of the effect system.

This specification does **not** cover: effect *typing* (an effect system that
rejects programs which perform unhandled effects), the `IO`/`Net`/`Time`/`System`
surface syntax of `Morph/Syntax.lean`, or cost accounting for effects.

## 2. Definitions

### 2.1 Operations and their classes

`Op` is the signature of the theory; `Op.class` projects each operation to its
effect class. The projection is what the old flat `EffectOp` lacked — without it
"which effects may this program perform" has no answer.

| Class | Operations | Character |
|---|---|---|
| `io` | `read`, `write` | stateful; a deterministic answer set |
| `net` | `connect`, `send`, `raise` | partial — the answer set may be **empty** |
| `time` | `now`, `sleep` | nondeterministic — the answer set may be a **singleton or more** |
| `system` | `exec` | escalating; requires authority |

Each operation's argument is the *continuation taken after the effect resolves*,
which is what makes these operations of an algebraic theory rather than monadic
actions.

### 2.2 The free monad

```lean
inductive Eff (σ : Type) where
  | pure (v : σ) : Eff σ
  | op (o : Op) (k : σ → Eff σ) : Eff σ
  | andThen (m : Eff σ) (f : σ → Eff σ) : Eff σ
```

`andThen` is the freer monad's explicit sequencing node. It is included because
without it `bind` must collapse through the syntax, and the monad laws become
statements about a rewriting system rather than about the model. With it, the
laws hold in the model — which is the only place they can be observed.

### 2.3 Models

```lean
structure Model (σ : Type) where
  answer : Op → List σ
```

`List σ` and not `σ` because `Net` and `Time` are nondeterministic. This one
field is where nondeterminism lives; a *model* is a program-definable
interpretation of the theory, exactly as in Plotkin & Pretnar.

```lean
def denote (M : Model σ) : Eff σ → List σ
  | .pure v        => [v]
  | .op o k        => (M.answer o).flatMap (fun v => denote M (k v))
  | .andThen m f   => (denote M m).flatMap (fun v => denote M (f v))
```

## 3. Requirements

### 3.1 The model is a homomorphism

> **`denote_bind`** — `denote M (bind m f) = (denote M m).flatMap (denote M ∘ f)`

This is the algebraic-effects claim in form: the computation monad is the
free-model monad, so interpreting by a model turns `bind` into the monadic
operation of `List`. Handling is then just `denote` with the handler's model —
the homomorphism the free model's universal property induces.

### 3.2 The monad laws hold in the model

> **`bind_assoc_denote`**, **`pure_bind_denote`**, **`bind_pure_denote`**

Nothing distinguishes `bind (bind m f) g` from `bind m (fun v => bind (f v) g)`
under `denote`. These are theorems, not definitions, precisely because the
sequencing node is explicit.

### 3.3 Failure is absence of an answer

> **`denote_unanswered`** — `answer o = [] → denote M (.op o k) = []`

There is no `fail` case: a failing `Net.connect` denotes the empty set. This is
why `IO`, `Net` and `Time` need only one effect type between them, and it is
checked in the examples by computing the empty result.

### 3.4 Effect sets accumulate under bind

> **`classes_bind_subset`** — every class of `m.bind f` occurs in `m` or in some `f v`

`Eff.classes` is now **complete**: it traverses continuations, fixing the
"shallow, one level" defect. Accumulation is what makes it a sound static upper
bound.

### 3.5 Handling only removes effects

Bauer & Pretnar's non-monotonicity, in the one direction an effect *system* must
guarantee. `Handler.residual` is the classes still outstanding after handling.

> **`residual_subset`** — residual ⊆ classes
> **`covered_residual_empty`** — a covering handler leaves nothing outstanding

A handler *deletes* effects — that is its purpose — but it can never introduce
one a static analysis never saw. Without this, an effect system is unsound for
handler-containing programs.

## 4. Worked examples (`Examples.lean`)

| Example | Point |
|---|---|
| `denote ioModel prog = ["contents"]` | a deterministic model gives one answer |
| `denote nondetModel netProg = []` | a failing `Net.connect` gives **no** answer — failure is absence |
| `denote nondetModel tick = ["t0","t1"]` | one syntax, **two** answers: `Time` is nondeterministic |
| `ioTimeHandler.residual prog = []` | a covering handler discharges both `IO` effects |
| `ioOnlyHandler.residual netProg = [.net]` | a non-covering handler leaves `Net` outstanding |

## 5. Scope: explicit non-claims

1. **No effect typing.** Nothing here rejects a computation that performs an
   unhandled effect. That is an effect *system*, and it is the natural next loop;
   the present module supplies the operational content a system would be stated
   over.
2. **No cost or termination accounting.** `denote` is total; nothing here says
   what an operation costs or that a computation terminates.
3. **No handler semantics.** `handle` is `denote` with the handler's model. Deep
   handlers — re-installing a handler inside a continuation, the
   `effect handlers in scope` (2014) question — are not modelled.
4. **No `System`/`IO` surface.** The operations here are the algebraic signature;
   they are not yet connected to `Morph/Syntax.lean`'s runtime intrinsics.
5. **`System` is not distinguished from `IO` semantically.** `exec` is modelled
   like any other operation; escalation is a policy concern, not a semantic one.

## 6. Traceability

| Artifact | Location |
|---|---|
| Signature, free monad, models, handlers | `Morph/Specs/EffectAlgebra/Spec.lean` |
| Homomorphism, laws, effect sets, monotonicity | `Morph/Specs/EffectAlgebra/Lemmas.lean` |
| One model per effect class | `Morph/Specs/EffectAlgebra/Examples.lean` |
| Superseded module (defects listed in §1.1) | `Morph/Specs/MonadicEffect/` |
| Loop log | `docs/RESEARCH-LOOPS.md` |
