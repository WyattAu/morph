/-
- Source: spec/memory/arc_affine_integration_spec.md
- Status: Active
- Mapping Summary: ARC with Affine Types Integration
- Known Issues: None

import Morph.Specs.ArcAffineIntegration.Spec

namespace Morph.Specs.ArcAffineIntegration

/- # 6. Examples -/

/- ### 6.1 ARC Basic Operations -/

/-- Example: ARC basic operations -/
def arc_basic_operations_example : Example :=
  let data := #Val { value := 42 }
  let copy1 := data
  let copy2 := data
  -- copy1 goes out of scope: ref_count = 1
  -- copy2 goes out of scope: ref_count = 0, deallocated

/- ### 6.2 Affine Type Move Semantics -/

/-- Example: Affine type move semantics -/
def affine_move_example : Example :=
  let original := ^Data { value := 42 }
  let result := process original
  -- original is no longer available - compile error if used

def process (data : ^Data) : ^Data' :=
  let processed := transform data
  processed

/- ### 6.3 Cycle Prevention with Affine Types -/

/-- Example: Cycle prevention with affine types -/
def cycle_prevention_example : Example :=
  let n1 := ^Node { value := 1, next := none }
  let n2 := ^Node { value := 2, next := n1 }
  -- n1.next = n2;  -- Compile error: n1 already moved

def valid_chain_example : Example :=
  let n1 := ^Node { value := 1, next := none }
  let n2 := ^Node { value := 2, next := n1 }
  ret n2
  -- Valid: linear chain (acyclic)

/- ### 6.4 Weak Reference Cycle Breaking -/

/-- Example: Weak reference cycle breaking -/
def weak_cycle_breaking_example : Example :=
  let parent := ^Parent { children := [] }
  let child := ^Child { parent := Weak.new parent }
  parent.children.push child
  ret parent

/- ### 6.5 Capability Transitions -/

/-- Example: Capability transitions -/
def freeze_data_example : Example :=
  let isoData := ^Data { value := 42 }
  let valData := freeze isoData
  -- Zero-copy transition: Iso -> Val

def borrow_data_example : Example :=
  let valData := #Data { value := 42 }
  let refData := borrow valData
  -- Zero-copy borrow: Val -> Ref

/- ### 6.6 Edge Cases -/

/-- Example: Use after move error -/
def use_after_move_error_example : Example :=
  let x := ^i32
  let y := x
  -- x is moved
  -- ret x  -- ERROR: use after move

/-- Example: Copying Iso type -/
def copy_iso_error_example : Example :=
  let x := ^i32
  let y := x
  -- x is moved
  -- let z := x  -- ERROR: cannot use moved value

/-- Example: Ref escaping region -/
def ref_escapes_region_example : Example :=
  fn example () -> &i32 :=
    let x := 42
    ret &x
  -- ERROR: ref escapes function

/- ### 6.7 Performance Example -/

/-- Example: Zero-copy message passing -/
def zero_copy_messaging_example : Example :=
  actor Producer
    fn produce () -> ^Iso LargeData :=
      ret createLargeData
  
  actor Consumer
    fn consume (data : ^Iso LargeData) :=
      process data
      -- data received without copy
  
  let producer := spawn Producer
  let consumer := spawn Consumer
  consumer.consume producer.produce
  -- Zero-copy transfer

/- ### 6.8 Reference Counting Example -/

/-- Example: Reference counting lifecycle -/
def ref_counting_example : Example :=
  let obj := #Val::new
  let owner1 := obj.clone
  let owner2 := obj.clone
  -- obj.ref_count = 2
  drop owner1
  -- obj.ref_count = 1
  drop owner2
  -- obj.ref_count = 0, deallocated

/- ### 6.9 Memory Safety Example -/

/-- Example: Memory safety with affine types -/
def memory_safety_example : Example :=
  let data := ^Data { value := 42 }
  let processed := transform data
  -- data is consumed, cannot be used again
  -- No use-after-free, no double-free, no data races

/- ### 6.10 Acyclicity Example -/

/-- Example: DAG structure -/
def dag_structure_example : Example :=
  let root1 := #Val { value := 1 }
  let root2 := #Val { value := 2 }
  let node1 := #Val { value := 3, next := root1 }
  let node2 := #Val { value := 4, next := root2 }
  let node3 := #Val { value := 5, next := node1 }
  let node4 := #Val { value := 6, next := node2 }
  -- Graph: root1 -> node1 -> node3
  --         root2 -> node2 -> node4
  -- Acyclic DAG structure

/- ### 6.11 Weak Reference Upgrade Example -/

/-- Example: Weak reference upgrade -/
def weak_upgrade_example : Example :=
  let weakRef : Weak #Data := Weak.new data
  match weakRef.upgrade with
    | Some strongRef => 
      -- Use strong reference
      process strongRef
    | None =>
      -- Object deallocated
      -- Handle gracefully

/- ### 6.12 Context Splitting Example -/

/-- Example: Context splitting for affine operations -/
def context_splitting_example : Example :=
  let Γ := { "x" : ^i32, "y" : ^i32, "z" : ^i32 }
  let Γ₁ := { "x" : ^i32 }
  let Γ₂ := { "y" : ^i32, "z" : ^i32 }
  -- Disjoint contexts for function call f(x, y, z)

/- ### 6.13 Capability Properties Example -/

/-- Example: Capability properties -/
def capability_properties_example : Example :=
  let isoVal : ^Data := createData
  -- Iso: unique ownership, mutable, sendable
  -- Cannot be copied, can be moved
  
  let valData := #Data := createData
  -- Val: shared ownership, immutable, sendable
  -- Can be copied, cannot be mutated
  
  let refData : &Data := borrow valData
  -- Ref: borrowed ownership, mutable, not sendable
  -- Cannot escape borrow scope

/- ### 6.14 Memory Ordering Example -/

/-- Example: Memory ordering -/
def memory_ordering_example : Example :=
  let obj := #Val::new
  let ref1 := obj.clone
  let ref2 := obj.clone
  -- Both references see consistent state
  -- Acquire-release semantics ensure visibility

/- ### 6.15 Complete Example -/

/-- Example: Complete ARC with affine types -/
def complete_example : Example :=
  let data := ^Data { value := 42 }
  let shared := freeze data
  -- Iso -> Val transition (zero-copy)
  
  let borrowed := borrow shared
  -- Val -> Ref transition (zero-copy)
  
  let copy1 := shared
  let copy2 := shared
  -- Val can be copied arbitrarily
  
  let weakRef : Weak #Data := Weak.new shared
  -- Weak reference for cycle breaking
  
  -- Final state:
  -- - data: consumed (moved)
  -- - shared: ref_count = 3 (copy1, copy2, weakRef)
  -- - borrowed: valid within borrow scope
  -- - weakRef: does not prevent deallocation

end Morph.Specs.ArcAffineIntegration
