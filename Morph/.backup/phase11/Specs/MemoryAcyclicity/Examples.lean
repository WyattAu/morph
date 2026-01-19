/-
- Source: spec/memory/memory_acyclicity_spec.md
- Status: Active
- Mapping Summary: Structural Acyclicity Specification
- Known Issues: None

import Morph.Specs.MemoryAcyclicity.Spec

namespace Morph.Specs.MemoryAcyclicity

/- # 6. Examples -/

/-- Simple example type for demonstrating memory acyclicity concepts -/
structure Example where
  description : String
  graph : ReferenceGraph
  deriving Repr

/- ### 6.1 Simple DAG -/

/-- Example: Simple DAG: Linear chain -/
def simple_dag_example : Example :=
  { description := "Linear chain DAG",
    graph := {
      vertices := {1, 2, 3},
      edges := {(1, 2), (2, 3)}
    }
  }

/- ### 6.2 Tree Structure -/

/-- Example: Tree structure: Root with children -/
def tree_structure_example : Example :=
  { description := "Root with children tree",
    graph := {
      vertices := {1, 2, 3},
      edges := {(1, 2), (1, 3)}
    }
  }

/- ### 6.3 Actor Isolation -/

/-- Example: Actor isolation: Separate memory spaces -/
def actor_isolation_example : Example :=
  { description := "Actor isolation example",
    graph := {
      vertices := {1, 2},
      edges := {(1, 2)}
    }
  }

/- ### 6.4 Edge Cases -/

/-- Example: Edge case: Attempted mutation (prevented) -/
def attempted_mutation_example : Example :=
  { description := "Attempted mutation prevented",
    graph := {
      vertices := {1},
      edges := {}
    }
  }

/-- Example: Edge case: Shared mutability (prevented) -/
def shared_mutability_prevented_example : Example :=
  { description := "Shared mutability prevented",
    graph := {
      vertices := {1},
      edges := {}
    }
  }

/- ### 6.5 Reference Counting Example -/

/-- Example: Reference counting lifecycle -/
def ref_counting_example : Example :=
  { description := "Reference counting lifecycle",
    graph := {
      vertices := {1, 2, 3, 4, 5},
      edges := {(1, 2), (1, 3), (1, 4), (1, 5)}
    }
  }

/- ### 6.6 Acyclicity Verification -/

/-- Example: Acyclicity verification -/
def acyclicity_verification_example : Example :=
  { description := "Acyclicity verification",
    graph := {
      vertices := {1, 2, 3, 4},
      edges := {(1, 2), (2, 3), (3, 4)}
    }
  }

end Morph.Specs.MemoryAcyclicity
