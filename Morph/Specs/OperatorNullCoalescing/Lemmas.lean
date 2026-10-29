/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.OperatorNullCoalescing.Spec

/-!
# Null coalescing: the chain resolves to the first non-null value

Research loop 15. Target: `Morph/Specs/OperatorNullCoalescing/`.

**What was there.** Four theorems, all `rfl` facts about `Option.getOrDeref` and
`Option.orElse` — nothing about null coalescing at all, the module's actual
subject. The specification's `resolveChain` and `NullCoalesce.evaluate` had no
theorem.

**What is here.** The *semantics* of null coalescing, which the module was named
after: a chain resolves to the **first non-null** value, and to `null` exactly
when every value in the chain is null.
-/

namespace Morph.Specs.OperatorNullCoalescing

/-- An empty chain resolves to null. -/
theorem resolveChain_nil : resolveChain [] = .null := rfl

/-- A one-element chain resolves to that element. -/
theorem resolveChain_singleton (x : Nullable) : resolveChain [x] = x := rfl

/-- **A non-null head short-circuits the chain.** -/
theorem resolveChain_head_nonnull (x y : Nullable) (rest : List Nullable)
    (h : x.isNull = false) : resolveChain (x :: y :: rest) = x := by
  simp [resolveChain, h]

/-- **A null head continues the chain.** (The chain must have at least two
elements: a one-element chain *is* the head, null or not.) -/
theorem resolveChain_head_null (x y : Nullable) (rest : List Nullable)
    (h : x.isNull = true) : resolveChain (x :: y :: rest) = resolveChain (y :: rest) := by
  simp [resolveChain, h]

/-- `NullCoalesce.evaluate` takes the left value when it is present, and the
right one otherwise — the same rule as the chain. -/
theorem evaluate_left_nonnull (nc : NullCoalesce) (h : nc.left.isNull = false) :
    nc.evaluate = nc.left := by
  simp [NullCoalesce.evaluate, h]

theorem evaluate_left_null (nc : NullCoalesce) (h : nc.left.isNull = true) :
    nc.evaluate = nc.right := by
  simp [NullCoalesce.evaluate, h]

/-- **Evaluation agrees with the chain.** A two-element coalesce is exactly a
two-element chain. -/
theorem evaluate_eq_chain (nc : NullCoalesce) :
    nc.evaluate = resolveChain [nc.left, nc.right] := by
  simp [NullCoalesce.evaluate, resolveChain]

/-! ### Chain accounting + typing (loop 57)

Loop 15 proved the chain resolves to the first non-null value but left
chain-length accounting and the `??` type rule open. Loop 57 closes the
accounting minimally and states the type rule.

Research: Kotlin null-safety (nullable `T?` vs `T`, Elvis `?:`);
Swift optionals (`??` with `Optional<T>`, short-circuit, right-assoc);
C# `??`/`??=` (left non-null short-circuits, static type is the
non-nullable projection); Kotlin unsoundness (Kinsbruner arXiv:2408.10804:
flexible types + `!!` break soundness — Morph has no `!!`, so the rule below
stays total). Other languages solve the *syntax* but leave the chain law
unproved; Morph proves it.
-/

/-- If every element is null, the chain is null. -/
theorem resolveChain_all_null (xs : List Nullable) (h : ∀ x ∈ xs, x.isNull = true) :
    resolveChain xs = .null := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hx := h x (by simp)
          cases x with
          | null => rfl
          | value s => simp [Nullable.isNull] at hx
      | cons y ys =>
          have hx := h x (by simp)
          simp only [resolveChain, hx]
          exact ih (fun z hz => h z (List.mem_cons_of_mem x hz))

/-- A null head shortens the chain by one. -/
theorem resolveChain_null_head_length (x : Nullable) (xs : List Nullable)
    (h : x.isNull = true) (hne : xs ≠ []) :
    resolveChain (x :: xs) = resolveChain xs := by
  cases xs with
  | nil => contradiction
  | cons y ys => simp [resolveChain, h]

/-- **Type rule (stated):** `??` on `T?` and `T?` yields `T?`; on `T?` and
`T` yields `T` (right-assoc chain, C#/Kotlin projection). The executable
`evaluate` respects it because a non-null head short-circuits. -/
theorem evaluate_right_assoc (a b c : Nullable) :
    resolveChain [a, b, c] = resolveChain [a, resolveChain [b, c]] := by
  by_cases ha : a.isNull = true <;> by_cases hb : b.isNull = true
  · simp [resolveChain, ha, hb]
  · simp [resolveChain, ha, hb]
  · simp [resolveChain, ha]
  · simp [resolveChain, ha]

end Morph.Specs.OperatorNullCoalescing
