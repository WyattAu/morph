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

end Morph.Specs.OperatorNullCoalescing
