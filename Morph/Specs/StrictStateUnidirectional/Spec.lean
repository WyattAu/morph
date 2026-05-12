/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.StrictStateUnidirectional

/-!
# Strict State Unidirectional Specification

Strict state machines with unidirectional transitions and
monotonic progress guarantees.

## Overview

This module formalizes strict state machines:
- **StateId:** Unique identifier for a state
- **Transition:** A directed edge between states
- **StateGraph:** The complete state transition graph
- **ProgressGuarantee:** Monotonic progress properties
- **Trace:** Execution trace through the state machine

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| State identifier | `StateId` | Done |
| Transition | `Transition` | Done |
| State graph | `StateGraph` | Done |
| Progress guarantee | `ProgressGuarantee` | Done |
| Reachability | `StateGraph.reachable` | Done |
-/

/-- Unique identifier for a state in the machine -/
structure StateId where
  id : Nat
  deriving Repr, BEq, Hashable

instance : ToString StateId where
  toString s := "S" ++ toString s.id

/-- A directed transition between states -/
structure Transition where
  src : StateId
  dst : StateId
  label : String
  deriving Repr, BEq

/-- The complete state transition graph -/
structure StateGraph where
  states : List StateId
  transitions : List Transition
  initial : StateId
  deriving Repr

namespace StateGraph

/-- Check if a state exists in the graph -/
def hasState (g : StateGraph) (s : StateId) : Bool :=
  g.states.any (fun x => x == s)

/-- Get all successors of a given state -/
def successors (g : StateGraph) (s : StateId) : List StateId :=
  g.transitions.filterMap (fun t =>
    if t.src == s then some t.dst else none)

/-- Get all predecessors of a given state -/
def predecessors (g : StateGraph) (s : StateId) : List StateId :=
  g.transitions.filterMap (fun t =>
    if t.dst == s then some t.src else none)

/-- Check reachability via BFS -/
partial def reachable (g : StateGraph) (start target : StateId) : Bool :=
  let rec bfs (visited : List StateId) (frontier : List StateId) : Bool :=
    match frontier with
    | [] => false
    | h :: rest =>
      if h == target then true
      else if visited.any (fun x => x == h) then bfs visited rest
      else bfs (h :: visited) (rest ++ g.successors h)
  bfs [] [start]

/-- Check if the graph has no cycles (all transitions go to higher states) -/
def isAcyclic (g : StateGraph) : Bool :=
  g.transitions.all (fun t => t.src.id < t.dst.id)

end StateGraph

/-- A progress guarantee for a state machine -/
inductive ProgressGuarantee where
  | alwaysTerminates : ProgressGuarantee
  | boundedSteps (max : Nat) : ProgressGuarantee
  | monotonic : ProgressGuarantee
  deriving Repr, BEq

/-- An execution trace through the state machine -/
abbrev Trace := List StateId

/-- Check if a trace is valid (consecutive states are connected by transitions) -/
def Trace.isValid (g : StateGraph) (t : Trace) : Bool :=
  match t with
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    g.transitions.any (fun tr => tr.src == a && tr.dst == b) &&
    Trace.isValid g (b :: rest)

end Morph.Specs.StrictStateUnidirectional
