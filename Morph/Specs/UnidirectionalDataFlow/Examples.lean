/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.UnidirectionalDataFlow.Lemmas

namespace Morph.Specs.UnidirectionalDataFlow

/-!
## Examples

Concrete checks for the Unidirectional Data Flow models: polarity, acyclicity,
feedback, reducers, backpressure and fusion.
-/

/-! ### Polarity -/

example : allows .source .read = true := source_can_read

example : allows .source .write = false := source_read_only

example : allows .sink .read = false := sink_write_only

example : allows .sink .write = true := sink_can_write

/-- A source and a sink declared with their legal access. -/
example : WellPolarized [⟨.source, .read⟩, ⟨.sink, .write⟩] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

/-- A source declared writable is not well polarized. -/
example : ¬ WellPolarized [⟨.source, .write⟩] := by
  intro h
  have := h ⟨.source, .write⟩ (by simp)
  exact Bool.false_ne_true this

/-! ### Acyclic graphs -/

/-- `0 → 1 → 2`, ranked by the node number. -/
def chainGraph : List Edge :=
  [{ src := 0, dst := 1 }, { src := 1, dst := 2 }]

example : Acyclic chainGraph :=
  acyclic_of_rank (rank := fun n => n) (by
    intro e he
    simp [chainGraph] at he
    rcases he with rfl | rfl <;> simp)

/-- `0 → 1 → 0` is a cycle: the edge `0 → 1` can be followed back. -/
example : ¬ Acyclic [{ src := 0, dst := 1 }, { src := 1, dst := 0 }] := by
  intro h
  have hcyc : Reaches [{ src := 0, dst := 1 }, { src := 1, dst := 0 }] 1 0 :=
    .step (by simp) (.refl 0)
  exact h 0 1 (by simp) hcyc

/-- The same loop is acyclic once the back edge is declared feedback. -/
def loopGraph : List Edge :=
  [{ src := 0, dst := 1 }, { src := 1, dst := 0 }]

example : Acyclic (immediate loopGraph [⟨1, 0⟩]) :=
  immediate_acyclic (rank := fun n => n) (by
    intro e he hfb
    simp [loopGraph] at he
    rcases he with rfl | rfl
    · simp
    · exact absurd hfb (by decide))

/-- The feedback edge really is removed from the instantaneous graph. -/
example : immediate loopGraph [⟨1, 0⟩] = [{ src := 0, dst := 1 }] := by
  native_decide

/-! ### Reducers -/

/-- A running-sum reducer: state and output are both the running total. -/
def runningSum : Reducer Nat Nat Nat := fun s a => (s + a, s + a)

example : runState runningSum 0 [1, 2, 3] = 6 := by native_decide

example : runOut runningSum 0 [1, 2, 3] = [1, 3, 6] := by native_decide

example : (runOut runningSum 0 [1, 2, 3]).length = 3 := by native_decide

/-- Concatenating inputs concatenates outputs. -/
example : runOut runningSum 0 ([1, 2] ++ [3]) =
    runOut runningSum 0 [1, 2] ++ runOut runningSum (runState runningSum 0 [1, 2]) [3] :=
  runOut_append runningSum 0 [1, 2] [3]

/-! ### Backpressure -/

def empty2 : Stream := { buffer := [], capacity := 2 }

example : (send empty2 1).isSome = true := by native_decide

/-- A full buffer refuses the third send. -/
example : (send { buffer := [1, 2], capacity := 2 } 3).isNone = true := by native_decide

example : receive { buffer := [1, 2], capacity := 2 } =
    some (1, { buffer := [2], capacity := 2 }) := by native_decide

/-- Two sends from an empty capacity-2 stream still respect the bound. -/
example : ∀ st', send { buffer := [1], capacity := 2 } 2 = some st' →
    st'.buffer.length ≤ st'.capacity := by
  intro st' h
  have hb := send_bounded { buffer := [1], capacity := 2 } 2 st' h
  have hc := send_capacity { buffer := [1], capacity := 2 } 2 st' h
  omega

/-! ### Fusion -/

def inc (n : Nat) : Nat := n + 1

def dbl (n : Nat) : Nat := n * 2

example : chain [inc, dbl] 3 = 8 := by native_decide

example : chain ([inc] ++ [dbl]) 3 = chain [dbl] (chain [inc] 3) :=
  chain_append [inc] [dbl] 3

example : chain [inc, dbl] 3 = fuse dbl inc 3 :=
  chain_two inc dbl 3

end Morph.Specs.UnidirectionalDataFlow
