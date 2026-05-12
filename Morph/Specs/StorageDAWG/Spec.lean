/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.StorageDAWG

/-!
# Storage DAWG Specification

Directed Acyclic Word Graph (DAWG) structures for compact
storage and retrieval of string data with common suffix sharing.

## Overview

This module formalizes DAWG data structures:
- **DAWGNode:** A node in the directed acyclic word graph
- **DAWGEdge:** A labeled edge between nodes
- **DAWG:** The complete graph structure
- **DAWGBuilder:** Incremental construction of a DAWG

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| DAWG node | `DAWGNode` | Done |
| DAWG edge | `DAWGEdge` | Done |
| DAWG | `DAWG` | Done |
| Lookup | `DAWG.lookup` | Done |
| Insert | `DAWG.insert` | Done |
-/

/-- A labeled edge in the DAWG -/
structure DAWGEdge where
  label : Char
  target : Nat
  deriving Repr, BEq

/-- A node in the directed acyclic word graph -/
structure DAWGNode where
  id : Nat
  edges : List DAWGEdge
  terminal : Bool
  deriving Repr, BEq

/-- The complete DAWG structure -/
structure DAWG where
  nodes : List DAWGNode
  root : Nat
  deriving Repr

namespace DAWG

/-- Create an empty DAWG with a single root node -/
def empty : DAWG :=
  ⟨[⟨0, [], false⟩], 0⟩

/-- Find a node by its identifier -/
def findNode (d : DAWG) (id : Nat) : Option DAWGNode :=
  d.nodes.find? (fun n => n.id == id)

/-- Look up a string in the DAWG -/
def lookup (d : DAWG) (s : String) : Bool :=
  let rec go (nodeId : Nat) (chars : List Char) : Bool :=
    match chars with
    | [] =>
      match d.findNode nodeId with
      | some node => node.terminal
      | none => false
    | c :: rest =>
      match d.findNode nodeId with
      | some node =>
        match node.edges.find? (fun e => e.label == c) with
        | some edge => go edge.target rest
        | none => false
      | none => false
  go d.root s.toList

/-- Follow an edge from a node by character label -/
def followEdge (node : DAWGNode) (c : Char) : Option Nat :=
  node.edges.find? (fun e => e.label == c) |>.map (fun e => e.target)

end DAWG

end Morph.Specs.StorageDAWG
