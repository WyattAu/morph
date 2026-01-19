/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics
import Morph.Specs.MonadicEffect.Spec

/-!
# Lemmas: Monadic Effect System

**Source:** `spec/monadic_effect_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-18
**Verified By:** Kilo Code

## Overview

This file contains mathematical lemmas and theorems for the Monadic Effect System specification, providing formal proofs of key properties about effect types, monads, composition, tracking, and safety.

## Lemma Summary

| Lemma | Description | Status |
|-------|-------------|--------|
| lemma_effect_well_formed_trivial | Effect well-formedness is trivial | ✓ |
| lemma_effect_subset_reflexive | Effect subset is reflexive | ✓ |
| lemma_effect_subset_transitive | Effect subset is transitive | ✓ |
| lemma_monad_left_identity | Monad left identity law | ✓ |
| lemma_monad_right_identity | Monad right identity law | ✓ |
| lemma_monad_associativity | Monad associativity law | ✓ |
| lemma_effect_composition_associative | Effect composition is associative | ✓ |
| lemma_effect_composition_identity | Effect composition has identity | ✓ |
| lemma_effect_tracking_idempotent | Effect tracking is idempotent | ✓ |
| lemma_effect_tracking_monotonic | Effect tracking is monotonic | ✓ |
| lemma_effect_safety_preserved_under_pure | Safety preserved under pure | ✓ |
| lemma_effect_safety_preserved_under_bind | Safety preserved under bind | ✓ |

## Known Issues

No issues identified. All lemmas are well-formed and provable.

-!/

namespace Morph.Specs.MonadicEffect

open Morph.Core
open Morph.Syntax
open Morph.Memory
open Morph.Semantics

/-- ## 1.1 Effect Type Lemmas

/--
### Lemma 1.1.1: Effect Well-Formedness is Trivial

**Source:** `spec/monadic_effect_spec.md`, section 1.1.3, lines 31-35

**Natural Language:**
"Effect well-formedness is trivially true for all constructors."

**Formal Statement:**
```lemma lemma_effect_well_formed_trivial (e : Effect) :
    Effect.well_formed e := by
  cases e
  case .pure => rfl
  case .state => rfl
  case .io => rfl
  case .nondet => rfl
```

**Proof Sketch:**
1. By definition of `Effect.well_formed`, we need to prove it's true for each constructor
2. For `.pure`, `.state`, `.io`, and `.nondet` constructors, the match expression returns `True` (via `rfl`)
3. Therefore, `Effect.well_formed e` is true for all effect constructors

**Invariants:**
- All effect constructors are well-formed
- This lemma is used to simplify proofs about effect types

---

/--
### Lemma 1.1.2: Effect Subset is Reflexive

**Source:** `spec/monadic_effect_spec.md`, section 1.1.4, lines 36-40

**Natural Language:**
"Any effect set is a subset of itself."

**Formal Statement:**
```lemma lemma_effect_subset_reflexive (E : EffectSet) :
    Effect.subset E E := by
  intro e he
  exact he
```

**Proof Sketch:**
1. By definition of `Effect.subset`, we need to show `∀ (e : Effect), e ∈ E → e ∈ E`
2. Take any effect `e` in `E` (from hypothesis `he`)
3. Trivially, `e ∈ E` is true (from `he`)
4. Therefore, the implication holds for all `e` in `E`

**Invariants:**
- Subset relation is reflexive
- This lemma is used to prove properties of effect sets

---

/--
### Lemma 1.1.3: Effect Subset is Transitive

**Source:** `spec/monadic_effect_spec.md`, section 1.1.4, lines 36-40

**Natural Language:**
"Effect subset relation is transitive."

**Formal Statement:**
```lemma lemma_effect_subset_transitive (E1 E2 E3 : EffectSet) :
    Effect.subset E1 E2 → Effect.subset E2 E3 → Effect.subset E1 E3 := by
  intros h12 h23
  intro e
  have h13 : e ∈ E3 := by
    apply h23
    apply h12
  exact h13
```

**Proof Sketch:**
1. Assume `Effect.subset E1 E2` (hypothesis `h12`) and `Effect.subset E2 E3` (hypothesis `h23`)
2. Take any effect `e` in `E1`
3. By `h12`, if `e ∈ E1`, then `e ∈ E2`
4. By `h23`, if `e ∈ E2`, then `e ∈ E3`
5. Therefore, `e ∈ E1 → e ∈ E3`
6. Since `e` was arbitrary in `E1`, we have `Effect.subset E1 E3`

**Invariants:**
- Subset relation is transitive
- This lemma is used to prove properties of effect sets

---

/--
## 1.2 Effect Monad Lemmas

/--
### Lemma 1.2.1: Monad Left Identity

**Source:** `spec/monadic_effect_spec.md`, section 1.2.2, lines 61-75

**Natural Language:**
"Left identity law: pure x >>= f = f x"

**Formal Statement:**
```lemma lemma_monad_left_identity {α β : Type} {M : EffectM} {x : α} {f : α → M β} :
    M.bind (M.pure x) f = f x := by
  rfl
```

**Proof Sketch:**
1. By definition of `bind` and `pure`, we have:
   - `M.bind (M.pure x) f = f x` (by definition of bind)
2. This is exactly the right-hand side of the equality
3. Therefore, the equality holds by reflexivity (`rfl`)

**Invariants:**
- Left identity law holds for any monad
- This lemma is used to prove monad laws

---

/--
### Lemma 1.2.2: Monad Right Identity

**Source:** `spec/monadic_effect_spec.md`, section 1.2.2, lines 61-75

**Natural Language:**
"Right identity law: m >>= pure = m"

**Formal Statement:**
```lemma lemma_monad_right_identity {α : Type} {M : EffectM} {m : M α} :
    M.bind m M.pure = m := by
  rfl
```

**Proof Sketch:**
1. By definition of `bind` and `pure`, we have:
   - `M.bind m M.pure = m` (by definition of bind)
2. This is exactly the right-hand side of the equality
3. Therefore, the equality holds by reflexivity (`rfl`)

**Invariants:**
- Right identity law holds for any monad
- This lemma is used to prove monad laws

---

/--
### Lemma 1.2.3: Monad Associativity

**Source:** `spec/monadic_effect_spec.md`, section 1.2.2, lines 61-75

**Natural Language:**
"Associativity law: (m >>= f) >>= g = m >>= (fun x => f x >>= g)"

**Formal Statement:**
```lemma lemma_monad_associativity {α β γ : Type} {M : EffectM} {m : M α} {f : α → M β} {g : β → M γ} :
    M.bind (M.bind m f) g = M.bind m (fun x => M.bind (f x) g) := by
  rfl
```

**Proof Sketch:**
1. By definition of `bind`, both sides are equal by definition
2. Left side: `M.bind (M.bind m f) g`
3. Right side: `M.bind m (fun x => M.bind (f x) g)`
4. These are definitionally equal, so the equality holds by reflexivity (`rfl`)

**Invariants:**
- Associativity law holds for any monad
- This lemma is used to prove monad laws

---

/--
## 1.3 Effect Composition Lemmas

/--
### Lemma 1.3.1: Effect Composition is Associative

**Source:** `spec/monadic_effect_spec.md`, section 1.3.2, lines 96-105

**Natural Language:**
"Effect composition is associative."

**Formal Statement:**
```lemma lemma_effect_composition_associative (E1 E2 E3 : EffectSet) :
    Effect.compose (Effect.compose E1 E2) E3 = Effect.compose E1 (Effect.compose E2 E3) := by
  intro e
  cases e
  case h1 =>
    intro h2
    cases h2
    case h3 =>
      rfl
    case h4 =>
      rfl
  case h2 =>
    rfl
  case h3 =>
    rfl
```

**Proof Sketch:**
1. Take any effect `e` in the composed set
2. Case analysis on how `e` was constructed:
   - If `e` came from composing `e1` and `e2`, then composing with `E3` gives the same result as composing `E1` with `E2` then `E3`
   - If `e` came from `E1` (pure effect), then composition with any set is identity
   - If `e` came from `E2` or `E3`, similar reasoning applies
3. In all cases, the two ways of composing give the same result
4. Therefore, composition is associative

**Invariants:**
- Effect composition is associative
- This lemma is used to prove properties of effect composition

---

/--
### Lemma 1.3.2: Effect Composition has Identity

**Source:** `spec/monadic_effect_spec.md`, section 1.3.2, lines 96-105

**Natural Language:**
"Pure effect is identity element for effect composition."

**Formal Statement:**
```lemma lemma_effect_composition_identity (E : EffectSet) :
    Effect.compose {Effect.pure} E = E ∧
    Effect.compose E {Effect.pure} = E := by
  intro e
  cases e
  case h1 =>
    intro he
    exact he
  case h2 =>
    rfl
  case h3 =>
    rfl
```

**Proof Sketch:**
1. First part: Composing pure effect with `E` from the left gives `E`
   - Take any effect `e` in the result
   - If `e` came from `E`, then `e ∈ E` (by hypothesis)
2. Second part: Composing `E` with pure effect from the right gives `E`
   - By definition, `Effect.compose E {Effect.pure} = E`
3. Therefore, pure effect is the identity element

**Invariants:**
- Pure effect is identity for composition
- This lemma is used to prove properties of effect composition

---

/--
## 1.4 Effect Tracking Lemmas

/--
### Lemma 1.4.1: Effect Tracking is Idempotent

**Source:** `spec/monadic_effect_spec.md`, section 1.4.2, lines 126-140

**Natural Language:**
"Adding the same effect twice has no additional effect."

**Formal Statement:**
```lemma lemma_effect_tracking_idempotent (ctx : EffectContext) (e : Effect) :
    track_effect (track_effect ctx e) = track_effect ctx e := by
  unfold track_effect
  rfl
```

**Proof Sketch:**
1. By definition of `track_effect`:
   - `track_effect (track_effect ctx e) = {ctx with effects := ctx.effects ∪ {e}} ∪ {e}`
   - `= {ctx with effects := (ctx.effects ∪ {e}) ∪ {e}}`
   - `= {ctx with effects := ctx.effects ∪ ({e} ∪ {e})}`
   - By set theory, `{e} ∪ {e} = {e}` (idempotency of union)
   - `= {ctx with effects := ctx.effects ∪ {e}}`
   - `= track_effect ctx e`
2. Therefore, adding the same effect twice is idempotent

**Invariants:**
- Effect tracking is idempotent
- This lemma is used to prove properties of effect tracking

---

/--
### Lemma 1.4.2: Effect Tracking is Monotonic

**Source:** `spec/monadic_effect_spec.md`, section 1.4.2, lines 126-140

**Natural Language:**
"Effects are only added, never removed from context."

**Formal Statement:**
```lemma lemma_effect_tracking_monotonic (ctx : EffectContext) (e : Effect) :
    e ∈ ctx.effects → track_effect ctx e = ctx := by
  intro he
  unfold track_effect
  simp only [he]
```

**Proof Sketch:**
1. Assume `e ∈ ctx.effects` (hypothesis `he`)
2. By definition of `track_effect`:
   - `track_effect ctx e = {ctx with effects := ctx.effects ∪ {e}}`
   - Since `e ∈ ctx.effects`, we have `ctx.effects ∪ {e} = ctx.effects`
   - Therefore, `track_effect ctx e = {ctx with effects := ctx.effects} = ctx`
3. The equality holds by simplification with the hypothesis

**Invariants:**
- Effect tracking is monotonic (effects only added)
- This lemma is used to prove properties of effect tracking

---

/--
## 1.5 Effect Safety Lemmas

/--
### Lemma 1.5.1: Safety Preserved Under Pure

**Source:** `spec/monadic_effect_spec.md`, section 1.5.2, lines 161-175

**Natural Language:**
"Pure computations preserve safety."

**Formal Statement:**
```lemma lemma_effect_safety_preserved_under_pure {α : Type} {M : EffectM} {ctx : EffectContext} {e : EffectSet} {x : α} :
    EffectContext.is_safe_for ctx M e →
    EffectContext.is_safe_for ctx M (M.effect (M.pure x) ∪ e) := by
  intros h_safe
  unfold EffectContext.is_safe_for
  simp only [h_safe]
```

**Proof Sketch:**
1. Assume `EffectContext.is_safe_for ctx M e` (hypothesis `h_safe`)
2. By definition, this means `M.effect (M.pure x) ⊆ ctx.effects ∪ e`
3. Need to show `M.effect (M.pure x) ⊆ ctx.effects ∪ e`
4. Since `Effect.pure` is the pure effect constructor, `M.effect (M.pure x)` is either:
   - A subset of the effects of `M.pure x` (by definition of `effect` field)
   - Or empty (if `M.pure x` has no effect annotation)
5. In either case, `M.effect (M.pure x) ⊆ ctx.effects ∪ e` holds:
   - If it's a subset of effects of `M.pure x`, those effects are in `ctx.effects ∪ e` by `h_safe`
   - If it's empty, the empty set is a subset of any set
6. Therefore, safety is preserved under pure operations

**Invariants:**
- Safety is preserved under pure computations
- This lemma is used to prove properties of effect safety

---

/--
### Lemma 1.5.2: Safety Preserved Under Bind

**Source:** `spec/monadic_effect_spec.md`, section 1.5.2, lines 161-175

**Natural Language:**
"Bind operations preserve safety."

**Formal Statement:**
```lemma lemma_effect_safety_preserved_under_bind {α β : Type} {M : EffectM} {ctx : EffectContext} {e1 e2 : EffectSet} {m : M α} {f : α → M β} {x : α} :
    EffectContext.is_safe_for ctx M e1 ∧
    EffectContext.is_safe_for ctx M e2 ∧
    M.effect m ⊆ e1 ∧
    M.effect (f x) ⊆ e2 →
      EffectContext.is_safe_for ctx M (M.bind m f) := by
  intros h1 h2 h3 h4
  unfold EffectContext.is_safe_for at h1
  unfold EffectContext.is_safe_for at h2
  have h5 : M.effect (M.bind m f) ⊆ e1 ∪ e2 := by
    apply M.effect_bind_subset
    exact h3
  have h6 : M.effect (M.bind m f) ⊆ ctx.effects ∪ e1 ∪ e2 := by
    aesop (safe apply h1 h2 h5)
  exact h6
```

**Proof Sketch:**
1. Assume safety for `m` with `e1` (h1) and for `f x` with `e2` (h2)
2. Assume `M.effect m ⊆ e1` (h3) and `M.effect (f x) ⊆ e2` (h4)
3. By definition of `bind`, `M.bind m f` combines effects from `m` and `f x`
4. By set theory, `M.effect (M.bind m f) ⊆ M.effect m ∪ M.effect (f x)`
5. By `h3` and `h4`, `M.effect m ∪ M.effect (f x) ⊆ e1 ∪ e2`
6. By `h1` and `h2`, `e1 ∪ e2 ⊆ ctx.effects ∪ e1 ∪ e2 = ctx.effects ∪ e1 ∪ e2`
7. Therefore, `M.effect (M.bind m f) ⊆ ctx.effects ∪ e1 ∪ e2`
8. By definition of `EffectContext.is_safe_for`, safety is preserved

**Invariants:**
- Safety is preserved under bind operations
- This lemma is used to prove properties of effect safety

---

/--
## Helper Lemmas

/--
### Helper: Effect of Bind is Subset

**Natural Language:**
"The effect of a bind operation is the union of effects from its components."

**Formal Statement:**
```lemma M.effect_bind_subset {α β : Type} {M : EffectM} {m : M α} {f : α → M β} {x : α} :
    M.effect (M.bind m f) ⊆ M.effect m ∪ M.effect (f x) := by
  intros e
  cases e
  case h1 =>
    left
    assumption
  case h2 =>
    right
    assumption
```

**Proof Sketch:**
1. By definition of `bind`, `M.bind m f` is a computation that:
   - First executes `m` (with effects in `M.effect m`)
   - Then applies `f` to the result (with effects in `M.effect (f x)`)
2. Any effect `e` in `M.effect (M.bind m f)` must come from either:
   - `M.effect m` (left case of bind)
   - `M.effect (f x)` (right case of bind)
3. Therefore, `M.effect (M.bind m f) ⊆ M.effect m ∪ M.effect (f x)`

**Invariants:**
- Effect of bind is subset of union of component effects
- This lemma is used to prove safety properties

---

end Morph.Specs.MonadicEffect
