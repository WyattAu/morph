/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryBounds.Lemmas

/-!
# Worked examples: the bounds, computed

Loop 68. The allocation bound and the quiescence headline, on concrete
configurations — every example below computes.
-/

namespace Morph.Specs.MemoryBounds

/-- The empty heap: nothing is live. -/
def emptyHeap : Heap := fun _ => none

/-- The empty configuration is precise: nothing is live, so nothing is
unreachable and every (zero) root is live. -/
example : Precise (⟨emptyHeap, [], [], 0⟩ : Config) := by
  constructor
  · intro a ha; simp [emptyHeap] at ha
  · intro r hr; simp at hr

/-- One allocation step, computed: block `0` appears with empty fields and
becomes a root, and the counter advances by one. -/
example : Steps 1 (⟨emptyHeap, [], [], 0⟩ : Config)
    ⟨hUpd emptyHeap 0 (some []), [0], [], 0 + 1⟩ :=
  .tail _ _ _ _ (.refl _) (.alloc _ 0 rfl (by decide) (by decide))

/-- Growth is paid for by allocation: after one step from empty, at most one
allocation has happened. This is `allocs_bound`, instantiated. -/
example (cₙ : Config)
    (h : Steps 1 (⟨emptyHeap, [], [], 0⟩ : Config) cₙ) :
    cₙ.allocs ≤ 1 :=
  allocs_bound 1 _ _ h

/-- Reachability in one step: `0` is a root and points at `1`. -/
example : Reach (hUpd emptyHeap 0 (some [1])) [0] (1 : Addr) :=
  .edge_ 0 1 [1] (hUpd_self _ _ _) (by decide) (.base_ 0 (by decide))

/-- Roots reach themselves. -/
example : Reach emptyHeap [(0 : Addr)] 0 :=
  .base_ 0 (by decide)

/-- No leaks at quiescence, on the empty heap: every live address (there are
none) is reachable from the roots. -/
example : ∀ a : Addr, emptyHeap a ≠ none →
    Reach emptyHeap ([] : List Addr) a := by
  intro a ha
  simp [emptyHeap] at ha

end Morph.Specs.MemoryBounds
