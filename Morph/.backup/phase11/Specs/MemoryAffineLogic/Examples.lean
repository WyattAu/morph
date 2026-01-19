/-
- Source: spec/memory/memory_affine_logic_spec.md
- Status: Active
- Mapping Summary: Linear & Affine Logic Specification
- Known Issues: None

import Morph.Specs.MemoryAffineLogic.Spec

namespace Morph.Specs.MemoryAffineLogic

/- # 6. Examples -/

/- ### 6.1 Move Semantics Example -/

/-- Example: Affine type move semantics -/
def move_semantics_example : Example :=
  { description := "Affine type move semantics",
    expr := 
      let x := ^i32
      let y := x
      -- x is moved
      -- y is no longer available - compile error if used
    }

/- ### 6.2 Shared Immutable Example -/

/-- Example: Shared immutable type -/
def shared_immutable_example : Example :=
  { description := "Shared immutable type",
    expr :=
      let data := #i32 { value := 42 }
      let copy1 := data
      let copy2 := data
      -- Val type can be copied arbitrarily
      -- data.ref_count = 3 (copy1, copy2, data)
    }

/- ### 6.3 Borrowing Example -/

/-- Example: Borrowing semantics -/
def borrowing_example : Example :=
  { description := "Borrowing semantics",
    expr :=
      let data := #i32 { value := 42 }
      let process := (val : #i32) -> &i32 :=
        let borrowed := &val
        -- Borrowed reference is valid within borrow scope
        borrowed.value = borrowed.value + 1
        -- Returns borrowed reference (automatic return)
      process data
    }

/- ### 6.4 Error Cases -/

/-- Example: Use after move error -/
def use_after_move_error_example : Example :=
  { description := "Use after move error",
    expr :=
      let example := (x : ^i32) -> i32 :=
        let y := x
        -- x is moved
        -- ret x  -- ERROR: use after move
      example
    }

/-- Example: Copying Iso type -/
def copy_iso_error_example : Example :=
  { description := "Copying Iso type",
    expr :=
      let example := (x : ^i32) -> i32 :=
        let y := x
        -- x is moved
        -- let z := x  -- ERROR: cannot use moved value
      example
    }

/-- Example: Ref escaping region -/
def ref_escapes_region_example : Example :=
  { description := "Ref escaping region",
    expr :=
      let example := () -> &i32 :=
        let x := 42
        ret &x
        -- ERROR: ref escapes function
      example
    }

/- ### 6.5 Zero-Copy Message Passing -/

/-- Example: Zero-copy message passing -/
def zero_copy_messaging_example : Example :=
  { description := "Zero-copy message passing",
    expr :=
      let produce := (data : ^Iso LargeData) -> ^Iso LargeData :=
        createLargeData
      let consume := (data : ^Iso LargeData) -> Unit :=
        process data
      let producer := spawn Producer
      let consumer := spawn Consumer
      consumer.consume producer.produce
      -- Zero-copy transfer
    }

/- ### 6.6 Context Splitting Example -/

/-- Example: Context splitting for affine operations -/
def context_splitting_example : Example :=
  { description := "Context splitting for affine operations",
    expr :=
      let Γ := { "x" : ^i32, "y" : ^i32, "z" : ^i32 }
      let Γ₁ := { "x" : ^i32 }
      let Γ₂ := { "y" : ^i32, "z" : ^i32 }
      -- Disjoint contexts for function call f(x, y, z)
      -- Each variable appears in at most one context
    }

/- ### 6.7 Capability Properties Example -/

/-- Example: Capability properties -/
def capability_properties_example : Example :=
  { description := "Capability properties",
    expr :=
      let isoData := ^Data { value := 42 }
      let valData := #Data { value := 42 }
      let refData := &Data { value := 42 }
      -- Iso: unique ownership, mutable, sendable
      -- Val: shared ownership, immutable, sendable
      -- Ref: borrowed ownership, mutable, not sendable
    }

/- ### 6.8 Type Safety Example -/

/-- Example: Type safety with affine types -/
def type_safety_example : Example :=
  { description := "Type safety with affine types",
    expr :=
      let data := ^Data { value := 42 }
      let processed := transform data
      -- data is consumed, cannot be used again
      -- No use-after-free, no double-free, no data races
    }

/- ### 6.9 Memory Leak Prevention Example -/

/-- Example: Memory leak prevention -/
def memory_leak_prevention_example : Example :=
  { description := "Memory leak prevention",
    expr :=
      let obj := #Data::new
      let owner1 := obj.clone
      let owner2 := obj.clone
      -- obj.ref_count = 3
      drop owner1
      -- obj.ref_count = 2
      drop owner2
      -- obj.ref_count = 1
      drop obj
      -- obj.ref_count = 0, deallocated
      -- No memory leak
    }

/- ### 6.10 Complete Example -/

/-- Example: Complete affine logic example -/
def complete_example : Example :=
  { description := "Complete affine logic example",
    expr :=
      let isoValue := ^i32 { value := 42 }
      let valValue := #isoValue
      -- Iso -> Val transition (zero-copy)
      let borrowed := &valValue
      -- Val -> Ref transition (zero-copy)
      let copy1 := valValue
      let copy2 := valValue
      -- Val can be copied arbitrarily
      let weakRef := Weak valValue
      -- Val -> Weak transition (zero-copy)
      -- Final state:
      -- isoValue: consumed (moved)
      -- valValue: ref_count = 3 (copy1, copy2, weakRef)
      -- borrowed: valid within borrow scope
      -- weakRef: does not prevent deallocation
    }

end Morph.Specs.MemoryAffineLogic
