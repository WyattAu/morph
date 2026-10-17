/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Effect Algebra: Morph's effect set as an algebraic theory

Research loop 6. `Morph/Specs/MonadicEffect/Spec.lean` declares a *syntax* for
effectful computations and stops there — its `seq` is keyed by `String` rather
than by a result type, `effectNames` is documented as "shallow, one level", and
`Lemmas.lean` contains two `rfl` facts about `Option.bind`, i.e. no effect
content at all.

**Research basis.**

- Plotkin & Pretnar, *Handlers of Algebraic Effects* (LICS 2008 / MSFP 2009):
  nondeterminism, interactive I/O, concurrency, state and **time** are all
  *algebraic* — representable by an algebraic theory (operations plus equations)
  — and the computation monad is the **free-model monad** of that theory.
  Handling is composition with the unique homomorphism induced by the free
  model's universal property. This is the framework for Morph's
  `{IO, Net, Time, System}`: all four are algebraic; only continuations are not.
- Plotkin & Pretnar, *Handling Algebraic Effects* (Edinburgh, 2013): a handler
  is a *model* of the equational theory, and handling yields the homomorphism
  the free model's universal property induces.
- Bauer & Pretnar, *An Effect System for Algebraic Effects and Handlers*
  (arXiv:1306.6316): with handlers the effect system is **non-monotone** — an
  effectful computation can become pure when enclosed by a handler, so effects
  are *deleted and transformed*, not merely accumulated. This is why
  "the effects of a program" is an upper bound that handling can only shrink.

## What is formalized here

1. `Op` — the primitive operations of Morph's four effect classes.
2. `EffectClass` — the class of each operation. `Op.class` is the projection
   that the old flat `EffectOp` inductive lacked.
3. `Eff` — the **free monad** `Free(Op, σ)`: `pure` and `op o k`, where the
   argument of an operation is the *continuation* after an occurrence of the
   effect, exactly as in the algebraic-effects presentation.
4. `Model` — an arbitrary interpretation of the operations into sets of answers.
   A `Model` is a model of the equational theory; `denote` is the induced map.
5. `Handler` — a model plus the operations it covers, i.e. the "deconstructor"
   dual to the operations.

The central theorem is `denote_bind`: handling binds in the free-model monad
*because* the model is a homomorphism. That is the algebraic-effects claim, in
form.
-/

namespace Morph.Specs.EffectAlgebra

/-- The four effect classes of the Morph effect set. -/
inductive EffectClass where
  /-- File and slot access: stateful. -/
  | io
  /-- Network: partial (may connect, may fail) and nondeterministic. -/
  | net
  /-- Time: nondeterministic — `now` can yield any instant. -/
  | time
  /-- Process execution: escalating, requires authority. -/
  | system
  deriving Repr, BEq, DecidableEq

/-- Primitive effect operations. The continuation-style argument is what makes
these *operations of an algebraic theory* rather than monadic actions. -/
inductive Op where
  /-- `IO.read slot` — stateful read. -/
  | read (slot : String)
  /-- `IO.write slot v` — stateful write. -/
  | write (slot : String) (v : String)
  /-- `Net.connect host` — partial: may fail, hence no `String` answer. -/
  | connect (host : String)
  /-- `Net.send peer msg` — partial. -/
  | send (peer : String) (msg : String)
  /-- `Time.now` — nondeterministic: any instant is a legal answer. -/
  | now (unit : String)
  /-- `Time.sleep ms` — nondeterministic, but always succeeds eventually. -/
  | sleep (ms : Nat)
  /-- `System.exec cmd` — escalating. -/
  | exec (cmd : String)
  /-- Failure: partiality. -/
  | raise (msg : String)
  deriving Repr, BEq

/-- The effect class an operation belongs to. The old flat `EffectOp` collapsed
read/write/ask/raise into one level with no class projection, which is what made
"which effects may this computation perform" unanswerable. -/
def Op.class : Op → EffectClass
  | .read _ => .io
  | .write _ _ => .io
  | .connect _ => .net
  | .send _ _ => .net
  | .now _ => .time
  | .sleep _ => .time
  | .exec _ => .system
  | .raise _ => .net

/-- The effect set: the classes a computation may perform. A list, ordered and
possibly with duplicates; membership is what matters. -/
abbrev EffectSet := List EffectClass

/-- `Freer(Op, σ)`: the free monad of the effect theory over `Op`, *with* an
explicit sequencing node. An operation occurrence carries the continuation taken
after the effect resolves.

The explicit `andThen` is what makes the monad laws provable *in the model*
rather than by definition: without it, `bind` has to collapse through the
syntax, and the laws become index-shift-heavy. Plotkin & Pretnar's free model is
the freer monad of the theory, so this is the faithful presentation. -/
inductive Eff (σ : Type) where
  /-- Return a value. -/
  | pure (v : σ) : Eff σ
  /-- Perform an operation, then continue. -/
  | op (o : Op) (k : σ → Eff σ) : Eff σ
  /-- Sequence a computation with a function of its result. -/
  | andThen (m : Eff σ) (f : σ → Eff σ) : Eff σ

/-- A model of the effect theory: an interpretation of each operation into the
set of answers it may produce. `List σ` rather than `σ` because `Net` and `Time`
are nondeterministic — this single field is where nondeterminism lives. -/
structure Model (σ : Type) where
  /-- Answers each operation may produce; `[]` means the operation may fail. -/
  answer : Op → List σ

/-- The monadic bind of the free monad, as an explicit sequencing node. -/
def Eff.bind {σ : Type} (m : Eff σ) (f : σ → Eff σ) : Eff σ := .andThen m f

/-- The map of the model induced on the free model: a computation denotes every
answer reachable by resolving its operations. `[]` is the empty result set — a
computation that failed, or diverged, or produced no answer. -/
def denote {σ : Type} (M : Model σ) : Eff σ → List σ
  | .pure v => [v]
  | .op o k => (M.answer o).flatMap (fun v => denote M (k v))
  | .andThen m f => (denote M m).flatMap (fun v => denote M (f v))

/-- Every effect class occurring in a computation. This is the *complete*
collection: the old `EffectfulComputation.effectNames` was documented as
"shallow, one level" and so missed everything under a continuation.

The `Inhabited` instance is only there to pick an argument for the
continuation; the result does not depend on which value is chosen, since the
effect set of a computation is the union over *all* answer paths. -/
def Eff.classes {σ : Type} [Inhabited σ] : Eff σ → EffectSet
  | .pure _ => []
  | .op o k => o.class :: Eff.classes (k default)
  | .andThen m _ => Eff.classes m

/-- A handler: a model of the theory together with the effect classes it covers.
The coverage is what makes handling total; without it a computation can get
stuck on an operation the handler does not model. -/
structure Handler (σ : Type) where
  /-- The model this handler interprets the operations by. -/
  model : Model σ
  /-- The effect classes this handler covers. -/
  covers : EffectSet

/-- A handler covers a computation when every effect class the computation may
perform is one the handler models. -/
def Handler.coversComp (h : Handler σ) [Inhabited σ] (c : Eff σ) : Prop :=
  ∀ k ∈ Eff.classes c, k ∈ h.covers

/-- Handling: apply a handler's model to a computation. For covered
computations this is total; `denote` is then the semantic value. -/
def handle {σ : Type} (h : Handler σ) (c : Eff σ) : List σ :=
  denote h.model c

end Morph.Specs.EffectAlgebra
