/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0


import Morph.Specs.ASTGraph.Spec
import Morph.Specs.ASTGraph.Lemmas

/-!
# AST Graph Examples

This module provides concrete examples and test cases for the AST graph system,
demonstrating Merkle DAG structure, hash recomputation, node taxonomy,
and refactoring operations.

## Overview

Examples illustrate:
- Merkle DAG construction
- Node taxonomy with type safety
- Hash recomputation rules
- Incremental hash updates
- Refactoring operations with provenance tracking

-!/
# Example 1: Simple Merkle DAG

def simpleMerkleDAG : ASTGraph :=
  let rootId : ASTNodeId := 0
  let child1Id : ASTNodeId := 1
  let child2Id : ASTNodeId := 2
  let child3Id : ASTNodeId := 3
  
  let rootHash : Hash := Hash.compute (ByteArray.mk #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]) SHA256
  
  let child1Hash : Hash := Hash.compute (ByteArray.mk #[0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]) SHA256
  let child2Hash : Hash := Hash.compute (ByteArray.mk #[0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f]) SHA256
  let child3Hash : Hash := Hash.compute (ByteArray.mk #[0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f]) SHA256
  
  let rootNode : MerkleNode := {
    id := rootId,
    kind := NodeKind.Block,
    children := [child1Id, child2Id, child3Id],
    hash := rootHash,
    depth := 0,
    provenance := []
  }
  
  let child1Node : MerkleNode := {
    id := child1Id,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := child1Hash,
    depth := 1,
    provenance := [rootId]
  }
  
  let child2Node : MerkleNode := {
    id := child2Id,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := child2Hash,
    depth := 1,
    provenance := [rootId]
  }
  
  let child3Node : MerkleNode := {
    id := child3Id,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := child3Hash,
    depth := 1,
    provenance := [rootId]
  }
  
  let nodes : HashMap ASTNodeId MerkleNode := [
    (rootId, rootNode),
    (child1Id, child1Node),
    (child2Id, child2Node),
    (child3Id, child3Node)
  ]
  
  let edges : HashMap ASTNodeId (List ASTNodeId) := [
    (rootId, [child1Id, child2Id, child3Id]),
    (child1Id, []),
    (child2Id, []),
    (child3Id, [])
  ]
  
  {
    nodes := nodes,
    edges := edges,
    root := rootId
  }

example_simple_merkle_dag : Prop :=
  by
    apply ASTGraph.wellFormed simpleMerkleDAG

/-!
# Example 2: Merkle Hash Property

def merkleHashPropertyExample : ASTGraph := ASTGraph.wellFormed simpleMerkleDAG := by
  merkleHashProperty simpleMerkleDAG
-!/

/-!
# Example 3: Node Taxonomy Type Safety

def nodeTaxonomyExample : Prop :=
  by
    apply node_type_safety (NodeKind.Literal (Unit))
-!/

/-!
# Example 4: Incremental Hash Recomputation

def incrementalHashExample : ASTGraph :=
  let initialGraph : ASTGraph := {
    nodes := HashMap.empty,
    edges := HashMap.empty,
    root := 0
  }
  
  let graphWithRoot := ASTGraph.insert initialGraph 0 {
    id := 0,
    kind := NodeKind.Block,
    children := [],
    hash := Hash.compute (ByteArray.mk #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]) SHA256,
    depth := 0,
    provenance := []
  }
  
  let graphWithChild := ASTGraph.insert graphWithRoot 1 {
    id := 1,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := Hash.compute (ByteArray.mk #[0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]) SHA256,
    depth := 1,
    provenance := [0]
  }
  
  let affected : List ASTNodeId := affectedSubtree graphWithChild 1
  let newGraph := recomputeHashes graphWithChild affected
  
  example_incremental_hash_recomputation incrementalHashExample
-!/

/-!
# Example 5: Refactoring Operation

def refactoringExample : ASTGraph :=
  let initialGraph : ASTGraph := {
    nodes := HashMap.empty,
    edges := HashMap.empty,
    root := 0
  }
  
  let graphWithFunction := ASTGraph.insert initialGraph 0 {
    id := 0,
    kind := NodeKind.FunctionCall,
    children := [],
    hash := Hash.compute (ByteArray.mk #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]) SHA256,
    depth := 0,
    provenance := []
  }
  
  let graphWithInline := applyRefactoring graphWithFunction (RefactoringOperation.InlineFunction 0 0)
  
  example_refactoring_provenance refactoringExample
-!/

/-!
# Example 6: Content Addressability

def contentAddressabilityExample : ASTGraph :=
  let graph1 : ASTGraph := {
    nodes := HashMap.empty,
    edges := HashMap.empty,
    root := 0
  }
  
  let graph2 : ASTGraph := {
    nodes := HashMap.empty,
    edges := HashMap.empty,
    root := 1
  }
  
  let node1Id : ASTNodeId := 0
  let node2Id : ASTNodeId := 1
  
  let node1Hash : Hash := Hash.compute (ByteArray.mk #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]) SHA256
  let node2Hash : Hash.compute (ByteArray.mk #[0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]) SHA256
  
  let graph1 : ASTGraph.insert graph1 0 {
    id := node1Id,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := node1Hash,
    depth := 0,
    provenance := []
  }
  
  let graph2 : ASTGraph.insert graph1 1 {
    id := node2Id,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := node2Hash,
    depth := 0,
    provenance := []
  }
  
  example_content_addressability hash_equality_content graph1 graph2
-!/

/-!
# Example 7: DAG Acyclicity

def dagAcyclicityExample : Prop :=
  let cyclicGraph : ASTGraph := {
    nodes := HashMap.empty,
    edges := HashMap.empty,
    root := 0
  }
  
  let node1Id : ASTNodeId := 0
  let node2Id : ASTNodeId := 1
  let node3Id : ASTNodeId := 2
  
  let graphWithCycle : ASTGraph.insert cyclicGraph 0 {
    id := node1Id,
    kind := NodeKind.Block,
    children := [node2Id],
    hash := Hash.compute (ByteArray.mk #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]) SHA256,
    depth := 0,
    provenance := []
  }
  
  let graphWithReverseCycle : ASTGraph.insert graphWithCycle 1 {
    id := node3Id,
    kind := NodeKind.Block,
    children := [node1Id],
    hash := Hash.compute (ByteArray.mk #[0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]) SHA256,
    depth := 1,
    provenance := [0]
  }
  
  ¬ASTGraph.wellFormed graphWithCycle

example_dag_acyclicity dagAcyclicityExample
-!/

/-!
# Example 8: Merkle Node Validity

def merkleNodeValidityExample : Prop :=
  let validNode : MerkleNode := {
    id := 0,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := Hash.compute (ByteArray.mk #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]) SHA256,
    depth := 1,
    provenance := []
  }
  
  let invalidNode : MerkleNode := {
    id := 1,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := Hash.empty,
    depth := 0,
    provenance := []
  }
  
  let graphWithValid : ASTGraph := {
    nodes := HashMap.empty,
    edges := HashMap.empty,
    root := 0
  }
  
  let graph1 : ASTGraph.insert graphWithValid 0 {
    id := 0,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := validNode.hash,
    depth := 1,
    provenance := []
  }
  
  let graph2 : ASTGraph.insert graphWithValid 1 {
    id := 1,
    kind := NodeKind.Literal (Unit),
    children := [],
    hash := invalidNode.hash,
    depth := 1,
    provenance := []
  }
  
  MerkleNode.valid validNode ∧ ¬MerkleNode.valid invalidNode

example_merkle_node_validity merkleNodeValidityExample

-!/
end Morph.Specs.ASTGraph
-/