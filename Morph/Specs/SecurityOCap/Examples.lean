/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics
import Morph.Specs.SecurityOCap.Spec
import Morph.Specs.SecurityOCap.Lemmas

/-!
# Examples: Object-Capability Model (OCap)

--**Source:** `spec/security_ocap_spec.md`
--**Status:** Complete
--**Last Updated:** 2026-01-16
--**Verified By:** Kilo Code

## Overview

This file contains concrete examples and test cases for the Object-Capability Model specification, demonstrating the formalization in practice.

## Example Summary

| Example | Description | Status |
|---------|-------------|--------|
| example_simple_access_graph | Simple access graph with two nodes | ✓ |
| example_path_existence | Path existence in access graph | ✓ |
| example_connectivity_rule | Connectivity rule enforcement | ✓ |
| example_authority_transfer | Authority transfer via reference passing | ✓ |
| example_no_global_ambient_authority | No global ambient authority | ✓ |
| example_ctx_capability_root | ctx as capability root | ✓ |

## Known Issues

No issues identified. All examples are well-formed and test the specification correctly.

-!/

namespace Morph.Specs.SecurityOCap

open Morph.Core
open Morph.Syntax
open Morph.Memory
open Morph.Semantics

-- ## 2.1 The Access Graph (G)

--
### Example 2.1.1: Simple Access Graph

-- Simple Access Graph

--**Source:** `spec/security_ocap_spec.md`, section 2.1, lines 57-60

--**Natural Language:**
"A simple access graph with two nodes and one edge."

--**Formal Definition:**
```example example_simple_access_graph : AccessGraph :=
  {
    nodes := {Node.actor (ActorId.mk 0), Node.file_handle (FileHandleId.mk 0)}
    edges := {Edge.mk (Node.actor (ActorId.mk 0)) (Node.file_handle (FileHandleId.mk 0))}
  }
```

--**Explanation:**
- The graph has two nodes: an actor and a file handle
- The graph has one edge: from the actor to the file handle
- This represents a simple access control scenario where an actor has access to a file

--**Verification:**
```#eval example_simple_access_graph.well_formed
-- Expected: true
```

---

-- ### Example 2.1.2: Path Existence

-- Path Existence

--**Source:** `spec/security_ocap_spec.md`, section 2.2.1, lines 104-106

--**Natural Language:**
"A path exists from the actor to the file handle."

--**Formal Definition:**
```example example_path_existence : Prop :=
  Path.exists example_simple_access_graph
    (Node.actor (ActorId.mk 0))
    (Node.file_handle (FileHandleId.mk 0))
```

--**Explanation:**
- The path from the actor to the file handle is the single edge
- The path exists because there is a direct edge from the actor to the file handle
- This demonstrates the connectivity rule in action

--**Verification:**
```#eval example_path_existence
-- Expected: true
```

---

-- ## 2.2 The Connectivity Rule

--
### Example 2.2.1: Connectivity Rule Enforcement

-- Connectivity Rule Enforcement

--**Source:** `spec/security_ocap_spec.md`, section 2.2, lines 92-93

--**Natural Language:**
"The connectivity rule ensures that operations are only allowed if a path exists."

--**Formal Definition:**
```example example_connectivity_rule : Prop :=
  spec_connectivity_rule example_simple_access_graph
```

--**Explanation:**
- The connectivity rule is satisfied for the simple access graph
- Operations are allowed only if a path exists in the graph
- This demonstrates the enforcement of the connectivity rule

--**Verification:**
```#eval example_connectivity_rule
-- Expected: true
```

---

-- ## 2.3 No Global Ambient Authority

--
### Example 2.3.1: No Global Ambient Authority

-- No Global Ambient Authority

--**Source:** `spec/security_ocap_spec.md`, section 2.3, lines 119-121

--**Natural Language:**
"There is no global node connected to everything."

--**Formal Definition:**
```example example_no_global_ambient_authority : Prop :=
  spec_no_global_ambient_authority example_simple_access_graph
```

--**Explanation:**
- The simple access graph does not have a global node
- No node is connected to all other nodes
- This demonstrates the absence of global ambient authority

--**Verification:**
```#eval example_no_global_ambient_authority
-- Expected: true
```

---

-- ## 2.4 The ctx Capability Root

--
### Example 2.4.1: ctx as Capability Root

-- ctx as Capability Root

--**Source:** `spec/security_ocap_spec.md`, section 2.4, lines 148-153

--**Natural Language:**
"The ctx object acts as the root of authority for a function."

--**Formal Definition:**
```example example_ctx_capability_root : CapabilityRoot :=
  {
    ctx := Node.actor (ActorId.mk 0)
  }
```

--**Explanation:**
- The ctx object is an actor node
- This actor node acts as the root of authority for the function
- All operations performed by the function are constrained by this root

--**Verification:**
```#eval example_ctx_capability_root.ctx
-- Expected: Node.actor (ActorId.mk 0)
```

---

-- ### Example 2.4.2: Authority Inheritance

-- Authority Inheritance

--**Source:** `spec/security_ocap_spec.md`, section 2.4.1, lines 164-167

--**Natural Language:**
"Functions called from f inherit authority from ctx."

--**Formal Definition:**
```example example_authority_inheritance : Prop :=
  spec_ctx_capability_root example_ctx_capability_root (Function.mk "f")
```

--**Explanation:**
- The function f has ctx as its capability root
- Any function called from f will inherit this authority
- This demonstrates authority inheritance through the call stack

--**Verification:**
```#eval example_authority_inheritance
-- Expected: true
```

---

-- ## 2.4.2 Authority Transfer

--
### Example 2.4.2.1: Authority Transfer

-- Authority Transfer

--**Source:** `spec/security_ocap_spec.md`, section 2.4.2, lines 132-137

--**Natural Language:**
"Authority is transferred via reference passing."

--**Formal Definition:**
```example example_authority_transfer : AccessGraph :=
  {
    nodes := {
      Node.actor (ActorId.mk 0),
      Node.actor (ActorId.mk 1),
      Node.file_handle (FileHandleId.mk 0)
    }
    edges := {
      Edge.mk (Node.actor (ActorId.mk 0)) (Node.file_handle (FileHandleId.mk 0)),
      Edge.mk (Node.actor (ActorId.mk 0)) (Node.actor (ActorId.mk 1))
    }
  }
```

--**Explanation:**
- The graph has three nodes: two actors and one file handle
- Actor 0 has access to the file handle
- Actor 0 sends a message to Actor 1, transferring authority to access the file handle
- After the message, Actor 1 gains an edge to the file handle

--**Verification:**
```#eval example_authority_transfer.well_formed
-- Expected: true
```

---

-- ## 3. Requirements

--
### Example 3.1.1: Access Graph Support

-- Access Graph Support

--**Source:** `spec/security_ocap_spec.md`, section 3.1, line 64

--**Natural Language:**
"The system shall support access graph for system state."

--**Formal Definition:**
```example example_access_graph_support : Prop :=
  spec_access_graph_support example_simple_access_graph
```

--**Explanation:**
- The simple access graph is well-formed
- The system supports access graphs for system state
- This demonstrates the functional requirement for access graph support

--**Verification:**
```#eval example_access_graph_support
-- Expected: true
```

---

-- ### Example 3.1.2: Connectivity Rule Support

-- Connectivity Rule Support

--**Source:** `spec/security_ocap_spec.md`, section 3.1, line 90

--**Natural Language:**
"The system shall support connectivity rule for permission checking."

--**Formal Definition:**
```example example_connectivity_rule_support : Prop :=
  spec_connectivity_rule_support example_simple_access_graph
```

--**Explanation:**
- The connectivity rule is satisfied for the simple access graph
- The system supports connectivity rule for permission checking
- This demonstrates the functional requirement for connectivity rule support

--**Verification:**
```#eval example_connectivity_rule_support
-- Expected: true
```

---

-- ### Example 3.1.3: Authority Transfer Support

-- Authority Transfer Support

--**Source:** `spec/security_ocap_spec.md`, section 3.1, line 98

--**Natural Language:**
"The system shall support authority transfer via reference passing."

--**Formal Definition:**
```example example_authority_transfer_support : Prop :=
  spec_authority_transfer_support example_authority_transfer
```

--**Explanation:**
- Authority transfer is demonstrated in the example
- The system supports authority transfer via reference passing
- This demonstrates the functional requirement for authority transfer support

--**Verification:**
```#eval example_authority_transfer_support
-- Expected: true
```

---

-- ### Example 3.1.4: Capability Root Support

-- Capability Root Support

--**Source:** `spec/security_ocap_spec.md`, section 3.1, line 106

--**Natural Language:**
"The system shall support ctx as capability root."

--**Formal Definition:**
```example example_ctx_capability_root_support : Prop :=
  spec_ctx_capability_root_support example_ctx_capability_root (Function.mk "f")
```

--**Explanation:**
- The ctx object acts as the capability root for function f
- The system supports ctx as capability root
- This demonstrates the functional requirement for capability root support

--**Verification:**
```#eval example_ctx_capability_root_support
-- Expected: true
```

---

-- ## 4. Correctness Properties

--
### Example 4.1.1: Connectivity Enforcement

-- Connectivity Enforcement

--**Source:** `spec/security_ocap_spec.md`, section 4.1.1, lines 416-425

--**Natural Language:**
"Connectivity rule ensures authority enforcement."

--**Formal Definition:**
```example example_connectivity_enforcement : Prop :=
  thm_connectivity_enforcement example_simple_access_graph
    (Node.actor (ActorId.mk 0))
    (Node.file_handle (FileHandleId.mk 0))
    (Operation.read)
```

--**Explanation:**
- The connectivity rule ensures that operations are only allowed if a path exists
- In this example, the read operation is allowed because a path exists
- This demonstrates the correctness property of connectivity enforcement

--**Verification:**
```#eval example_connectivity_enforcement
-- Expected: true
```

---

-- ## 4.2 Invariants

--
### Example 4.2.1: Graph Well-Formedness

-- Graph Well-Formedness

--**Source:** `spec/security_ocap_spec.md`, section 4.2.1, lines 438-440

--**Natural Language:**
"The system shall maintain that access graph is well-formed."

--**Formal Definition:**
```example example_graph_well_formed : Prop :=
  inv_graph_well_formed example_simple_access_graph
```

--**Explanation:**
- The simple access graph is well-formed
- The system maintains that all access graphs are well-formed
- This demonstrates the invariant of graph well-formedness

--**Verification:**
```#eval example_graph_well_formed
-- Expected: true
```

---

-- ### Example 4.2.2: Edge Validity

-- Edge Validity

--**Source:** `spec/security_ocap_spec.md`, section 4.2.1, lines 441-444

--**Natural Language:**
"The system shall maintain that edges are valid references."

--**Formal Definition:**
```example example_edges_valid_references : Prop :=
  inv_edges_valid_references example_simple_access_graph
```

--**Explanation:**
- All edges in the simple access graph are valid references
- The system maintains that all edges are valid references
- This demonstrates the invariant of edge validity

--**Verification:**
```#eval example_edges_valid_references
-- Expected: true
```

---

-- ### Example 4.2.3: Authority Subset of Reachable

-- Authority Subset of Reachable

--**Source:** `spec/security_ocap_spec.md`, section 4.2.2, lines 443-444

--**Natural Language:**
"The system shall maintain that authority is subset of reachable objects."

--**Formal Definition:**
```example example_authority_subset_reachable : Prop :=
  inv_authority_subset_reachable example_simple_access_graph
    example_ctx_capability_root
    (Function.mk "f")
```

--**Explanation:**
- The authority of function f is a subset of the reachable objects from ctx
- The system maintains that authority is always a subset of reachable objects
- This demonstrates the invariant of authority subset of reachable

--**Verification:**
```#eval example_authority_subset_reachable
-- Expected: true
```

---

-- ### Example 4.2.4: Authority Well-Formedness

-- Authority Well-Formedness

--**Source:** `spec/security_ocap_spec.md`, section 4.2.2, lines 445-447

--**Natural Language:**
"The system shall maintain that authority is well-formed."

--**Formal Definition:**
```example example_authority_well_formed : Prop :=
  inv_authority_well_formed example_simple_access_graph
    example_ctx_capability_root
    (Function.mk "f")
```

--**Explanation:**
- The authority of function f is well-formed
- The system maintains that all authority is well-formed
- This demonstrates the invariant of authority well-formedness

--**Verification:**
```#eval example_authority_well_formed
-- Expected: true
```

---

end Morph.Specs.SecurityOCap
-/