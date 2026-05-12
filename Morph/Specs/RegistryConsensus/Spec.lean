/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.RegistryConsensus

/-!
# Registry Consensus Specification

Consensus protocols, quorum requirements, and registry
consistency guarantees for distributed Morph registries.

## Overview

This module formalizes consensus mechanisms:
- **NodeId:** Unique identifier for a registry node
- **NodeState:** State of a registry node
- **Vote:** A single vote in the consensus protocol
- **Quorum:** Quorum requirements and computation
- **RegistryEntry:** An entry in the distributed registry
- **Proposal:** A proposed change to the registry

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Node identifier | `NodeId` | Done |
| Node state | `NodeState` | Done |
| Vote | `Vote` | Done |
| Quorum | `Quorum` | Done |
| Registry entry | `RegistryEntry` | Done |
| Proposal | `Proposal` | Done |
-/

/-- Unique identifier for a registry node -/
structure NodeId where
  id : Nat
  deriving Repr, BEq, Hashable

/-- State of a registry node in the consensus protocol -/
inductive NodeState where
  | follower : NodeState
  | candidate : NodeState
  | leader : NodeState
  deriving Repr, BEq, Hashable

/-- A single vote in the consensus protocol -/
structure Vote where
  voter : NodeId
  candidate : NodeId
  term : Nat
  granted : Bool
  deriving Repr, BEq

/-- Quorum configuration for consensus -/
structure Quorum where
  totalNodes : Nat
  requiredVotes : Nat
  deriving Repr, BEq

namespace Quorum

/-- Create a majority quorum for a given cluster size -/
def majority (totalNodes : Nat) : Quorum :=
  let required := (totalNodes + 1) / 2
  ⟨totalNodes, required⟩

/-- Check if a vote count meets the quorum requirement -/
def hasQuorum (q : Quorum) (votes : Nat) : Bool :=
  votes >= q.requiredVotes

/-- Validate that the quorum is well-formed -/
def isValid (q : Quorum) : Bool :=
  q.requiredVotes <= q.totalNodes && q.totalNodes > 0

end Quorum

/-- An entry in the distributed registry -/
structure RegistryEntry where
  key : String
  value : String
  version : Nat
  deriving Repr, BEq

/-- A proposed change to the registry -/
structure Proposal where
  proposer : NodeId
  term : Nat
  entry : RegistryEntry
  deriving Repr, BEq

/-- Check if a single vote is a granted vote for a given term and candidate -/
def Vote.isGrantedFor (v : Vote) (candidateId : NodeId) (term : Nat) : Bool :=
  v.candidate == candidateId && v.term == term && v.granted

/-- Count granted votes for a given term and candidate -/
def countGranted (votes : List Vote) (candidateId : NodeId) (term : Nat) : Nat :=
  votes.foldl (fun acc v =>
    if v.isGrantedFor candidateId term then acc + 1 else acc) 0

end Morph.Specs.RegistryConsensus
