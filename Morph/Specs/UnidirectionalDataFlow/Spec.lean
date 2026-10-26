/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Core

/-!
# Specification: Unidirectional Data Flow (UDF)

**Source:** `spec/language/unidirectional_data_flow_spec.md`
**Status:** Complete (loop 48)
**Last Updated:** 2026-10-26

## Overview

The UDF specification constrains a data-flow graph so that information moves in
one direction only. This module builds the smallest models that make the
specification's guarantees stateable and provable:

| Spec item | Model | Guarantee |
|---|---|---|
| UDF-INV-001/002, UDF-REQ-004 | `Polarity`, `Access`, `allows` | sources are read-only, sinks are write-only |
| UDF-INV-004 | `Endpoint`, `WellPolarized` | every endpoint's access matches its polarity |
| UDF-THM-001/005, UDF-INV-011 | `Edge`, `Reaches`, `Acyclic` | a graph with a rank function is acyclic |
| UDF-REQ-002 | `isFeedback`, `immediate` | feedback edges are excluded from the instantaneous graph |
| UDF-THM-002/006, UDF-INV-007 | `Reducer`, `runState`, `runOut` | state evolution is a pure function of the input sequence |
| UDF-THM-003/007, UDF-INV-010 | `Stream`, `send`, `receive` | credit-based sending keeps the buffer bounded |
| UDF-THM-004, UDF-REQ-007 | `fuse`, `chain` | linear chains fuse associatively and preserve semantics |

## Known Issues

None: every theorem below is proved in `Lemmas.lean`. The models are
deliberately small — they capture the *shape* of each guarantee (polarity,
acyclicity, purity, boundedness, fusion) rather than the concrete runtime,
which §1.2 of the spec puts out of scope.
-/

namespace Morph.Specs.UnidirectionalDataFlow

/-!
## Polarity (UDF-INV-001, UDF-INV-002, UDF-REQ-004)
-/

/-- Direction of a stream endpoint: a `source` produces, a `sink` consumes. -/
inductive Polarity where
  | source : Polarity
  | sink : Polarity
  deriving Repr, BEq, DecidableEq

/-- What an operation does with an endpoint. -/
inductive Access where
  | read : Access
  | write : Access
  deriving Repr, BEq, DecidableEq

/-- The access policy: sources may only be read, sinks may only be written. -/
def allows : Polarity → Access → Bool
  | .source, .read => true
  | .source, .write => false
  | .sink, .read => false
  | .sink, .write => true

/-- An endpoint declared with a polarity and the access the program uses. -/
structure Endpoint where
  polarity : Polarity
  access : Access
  deriving Repr, BEq, DecidableEq

/-- A list of endpoints is well polarized when every declared access is one the
polarity allows. -/
def WellPolarized (eps : List Endpoint) : Prop :=
  ∀ e ∈ eps, allows e.polarity e.access = true

/-!
## Graphs (UDF-THM-001, UDF-THM-005, UDF-INV-011, UDF-REQ-002)
-/

/-- A directed data-flow edge. -/
structure Edge where
  src : Nat
  dst : Nat
  deriving Repr, BEq, DecidableEq

/-- Transitive reachability in a graph. -/
inductive Reaches (g : List Edge) : Nat → Nat → Prop where
  | refl (u : Nat) : Reaches g u u
  | step {u v w : Nat} : (⟨u, v⟩ : Edge) ∈ g → Reaches g v w → Reaches g u w

/-- A graph is acyclic when no edge can be followed back to its source. -/
def Acyclic (g : List Edge) : Prop :=
  ∀ u v, (⟨u, v⟩ : Edge) ∈ g → ¬ Reaches g v u

/-- A rank function respects every edge when it strictly increases along it.
Such a function is a topological order written as levels. -/
def Respects (g : List Edge) (rank : Nat → Nat) : Prop :=
  ∀ e, e ∈ g → rank e.src < rank e.dst

/-- A feedback edge is one the program marks as delayed (UDF-REQ-002): it is
allowed to close a loop because it crosses a time step. -/
def isFeedback (feedback : List Edge) (e : Edge) : Bool :=
  feedback.contains e

/-- The instantaneous graph: every edge that is *not* a feedback edge. -/
def immediate (g feedback : List Edge) : List Edge :=
  g.filter (fun e => !isFeedback feedback e)

/-!
## Reducers (UDF-THM-002, UDF-THM-006, UDF-INV-007)
-/

/-- A Mealy reducer: state and input determine the next state and the output. -/
abbrev Reducer (σ α β : Type) := σ → α → σ × β

/-- The state after one step. -/
def stepState {σ α β : Type} (r : Reducer σ α β) (s : σ) (a : α) : σ :=
  (r s a).1

/-- The output of one step. -/
def stepOut {σ α β : Type} (r : Reducer σ α β) (s : σ) (a : α) : β :=
  (r s a).2

/-- Fold the reducer over an input sequence, keeping only the final state. -/
def runState {σ α β : Type} (r : Reducer σ α β) : σ → List α → σ
  | s, [] => s
  | s, a :: as => runState r (stepState r s a) as

/-- Fold the reducer over an input sequence, keeping only the outputs. -/
def runOut {σ α β : Type} (r : Reducer σ α β) : σ → List α → List β
  | _, [] => []
  | s, a :: as => stepOut r s a :: runOut r (stepState r s a) as

/-- The full run: final state and output sequence. -/
def run {σ α β : Type} (r : Reducer σ α β) (s : σ) (as : List α) : σ × List β :=
  (runState r s as, runOut r s as)

/-!
## Backpressure (UDF-THM-003, UDF-THM-007, UDF-INV-010)
-/

/-- A bounded stream buffer. `capacity` is the credit the producer has. -/
structure Stream where
  buffer : List Nat
  capacity : Nat
  deriving Repr, BEq, DecidableEq

/-- Sending is allowed only while the buffer is below capacity. -/
def canSend (st : Stream) : Bool :=
  st.buffer.length < st.capacity

/-- Push one element, or refuse when the buffer is full. -/
def send (st : Stream) (x : Nat) : Option Stream :=
  if canSend st then some { st with buffer := st.buffer ++ [x] } else none

/-- Pop one element, or refuse when the buffer is empty. -/
def receive (st : Stream) : Option (Nat × Stream) :=
  match st.buffer with
  | [] => none
  | x :: xs => some (x, { st with buffer := xs })

/-!
## Fusion (UDF-THM-004, UDF-REQ-007)
-/

/-- Compose two linear transducers. -/
def fuse {α β γ : Type} (g : β → γ) (f : α → β) : α → γ :=
  fun a => g (f a)

/-- Run a chain of transducers left to right. -/
def chain : List (Nat → Nat) → Nat → Nat
  | [], x => x
  | f :: fs, x => chain fs (f x)

end Morph.Specs.UnidirectionalDataFlow
