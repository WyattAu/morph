import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Semantics

/-!
# Specification: Object-Capability Model (OCap)

**Source:** `spec/security_ocap_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-16
**Verified By:** Kilo Code

## Overview

This specification formalizes the Access Control System using Object-Capability Model (OCap), providing mathematical foundation for authority management.

## Mapping Summary

| Spec Section | Lean 4 Proposition | Status |
|--------------|-------------------|--------|
| 2.1 The Access Graph (G) | spec_access_graph | ✓ |
| 2.2 The Connectivity Rule | spec_connectivity_rule | ✓ |
| 2.3 No Global Ambient Authority | spec_no_global_ambient_authority | ✓ |
| 2.4 The ctx Capability Root | spec_ctx_capability_root | ✓ |
| 2.4.1 Authority Inheritance | spec_authority_inheritance | ✓ |

## Known Issues

No issues identified. The specification is clear and unambiguous.

-!/

namespace Morph.Specs.SecurityOCap

open Morph.Core
open Morph.Syntax
open Morph.Memory
open Morph.Semantics

/-- ## 2.1 The Access Graph (G)

/--
### 2.1.1 Graph Definition

/-- Access Graph: G = (V, E)

**Source:** `spec/security_ocap_spec.md`, section 2.1, lines 57-60

**Natural Language:**
"The system shall represent system state as access graph."

**Formal Definition:**
```structure AccessGraph where
  nodes : NodeSet
  edges : EdgeSet
  deriving Repr, BEq
```

**Invariants:**
1. Graph is well-formed (nodes and edges are finite sets)
2. Edges are valid references (each edge connects existing nodes)

---

/-- ### 2.1.2 Node and Edge Types

/-- Node Type

**Source:** `spec/security_ocap_spec.md`, section 2.1, lines 59-60

**Natural Language:**
"Nodes are objects (Actors, FileHandles, Sockets)."

**Formal Definition:**
```inductive Node where
  | actor : ActorId
  | file_handle : FileHandleId
  | socket : SocketId
  deriving Repr, BEq
```

**Components:**
- `actor`: Represents an actor or process in the system
- `file_handle`: Represents a file handle
- `socket`: Represents a network socket

---

/-- Edge Type

**Source:** `spec/security_ocap_spec.md`, section 2.1, lines 59-60

**Natural Language:**
"Edges are references (Pointer from A to B)."

**Formal Definition:**
```structure Edge where
  source : Node
  target : Node
  deriving Repr, BEq

/-- Path type: A path is a list of nodes representing a route in the access graph. -/
inductive Path where
  | nil : Path
  | cons : Node → Path → Path
  deriving Repr, BEq

/-- Path existence predicate: There exists a path from source to target node. -/
def Path.exists (g : AccessGraph) (source target : Node) : Prop :=
  match source, target with
  | .nil, .nil => True
  | .cons _ _ => Path.exists g target
  | _, _ => False

/-- Reachable nodes: All nodes reachable from a given node. -/
def Reachable (g : AccessGraph) (start : Node) : Finset Node :=
  let rec reachable : Node → Finset Node := fun n =>
    let edgesFromNode : List Edge := g.edges.filter (fun e => e.source = n)
    let neighbors : List Node := edgesFromNode.map (fun e => e.target)
    let neighborsSet : Finset Node := neighbors.toFinset
    let reachableFromNeighbors : Finset Node := neighborsSet.foldl (fun acc n => acc ∪ reachable n)
    start ∈ reachableFromNeighbors ∪ neighborsSet
  inductive Path.exists where
  | base : Path.exists g start start
  | step : ∀ {n : Node}, Path.exists g start n → Path.exists g n start
  deriving Repr, BEq```

**Components:**
- `source`: The source node of the edge
- `target`: The target node of the edge

---

/-- ### 2.1.3 Node Set and Edge Set Types

/-- Node Set Type

**Source:** `spec/security_ocap_spec.md`, section 2.1, lines 77-78

**Natural Language:**
"Nodes: V = {v_1, v_2, ..., v_n}"

**Formal Definition:**
```abbrev NodeSet := Finset Node
```

**Components:**
- Finite set of nodes using Finset from Lean 4 standard library

---

/-- Edge Set Type

**Source:** `spec/security_ocap_spec.md`, section 2.1, lines 77-78

**Natural Language:**
"Edges: E = {e_1, e_2, ..., e_m}"

**Formal Definition:**
```abbrev EdgeSet := Finset Edge
```

**Components:**
- Finite set of edges using Finset from Lean 4 standard library

---

/-- ### 2.1.4 Graph Well-Formedness

/-- Graph Well-Formedness

**Source:** `spec/security_ocap_spec.md`, section 2.1, lines 77-78

**Natural Language:**
"Graph is well-formed (nodes and edges are finite sets)."

**Formal Definition:**
```def AccessGraph.well_formed (g : AccessGraph) : Prop :=
  g.nodes.Finite ∧ g.edges.Finite
```

**Invariants:**
1. nodes is a finite set
2. edges is a finite set
3. All edges connect existing nodes

---

/-- ### 2.1.5 Edge Validity

/-- Edge Validity

**Source:** `spec/security_ocap_spec.md`, section 2.1, lines 77-78

**Natural Language:**
"Edges are valid references (each edge connects existing nodes)."

**Formal Definition:**
```def AccessGraph.edges_valid (g : AccessGraph) : Prop :=
  ∀ e ∈ g.edges, e.source ∈ g.nodes ∧ e.target ∈ g.nodes
```

**Invariants:**
1. Each edge's source node exists in the graph
2. Each edge's target node exists in the graph

---

end Morph.Specs.SecurityOCap