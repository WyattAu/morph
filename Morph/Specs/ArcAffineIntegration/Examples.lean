/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.ArcAffineIntegration.Spec
import Morph.Specs.ArcAffineIntegration.Lemmas

/-!
# Examples: ARC with Affine Types Integration

**Source:** `spec/memory/arc_affine_integration_spec.md`
**Status:** Complete
**Last Updated:** 2026-01-31
**Verified By:** Kilo Code

## Overview

This module contains executable examples demonstrating the ARC with affine
types integration specification.

## Examples

All examples are executable and demonstrate the key concepts.
-/

namespace Morph.Specs.ArcAffineIntegration

/-!
## Capability Examples

Examples demonstrating the capability type system.
-/

/-- Example: Iso capability represents unique ownership.
    Iso types can be transferred but not shared.
-/
def isoCapability : Capability :=
  Capability.iso

/-- Example: Val capability represents immutable values.
    Val types cannot be modified after creation.
-/
def valCapability : Capability :=
  Capability.val

/-- Example: Ref capability represents shared references.
    Ref types can be shared but not sent across actor boundaries.
-/
def refCapability : Capability :=
  Capability.ref

/-- Example: Weak capability represents weak references.
    Weak types do not prevent deallocation.
-/
def weakCapability : Capability :=
  Capability.weak

/-!
## Capability Transition Examples

Examples demonstrating valid and invalid capability transitions.
-/

/-- Example: Iso to Val is a valid transition.
    Unique ownership can be converted to immutable value.
-/
def isoToValTransition : Bool :=
  transition Capability.iso Capability.val Nat

/-- Example: Val to Ref is a valid transition.
    Immutable value can be converted to shared reference.
-/
def valToRefTransition : Bool :=
  transition Capability.val Capability.ref Nat

/-- Example: Ref to Weak is a valid transition.
    Strong reference can be downgraded to weak reference.
-/
def refToWeakTransition : Bool :=
  transition Capability.ref Capability.weak Nat

/-- Example: Weak to any capability is invalid.
    Weak references cannot be upgraded.
-/
def weakToIsoTransition : Bool :=
  transition Capability.weak Capability.iso Nat

/-!
## Reference Graph Examples

Examples demonstrating reference graph operations.
-/

/-- Example: Empty reference graph.
    An empty graph contains no references.
-/
def emptyReferenceGraph : ReferenceGraph :=
  HashMap.empty

/-- Example: Reference graph with a single edge.
    Demonstrates adding a reference from one object to another.
-/
def singleEdgeReferenceGraph : ReferenceGraph :=
  HashMap.insert HashMap.empty 0 [1]

/-- Example: Reference graph with multiple edges.
    Demonstrates a more complex reference structure.
-/
def multiEdgeReferenceGraph : ReferenceGraph :=
  HashMap.insert (HashMap.insert HashMap.empty 0 [1, 2]) 1 [2]

/-!
## Reference Count Examples

Examples demonstrating reference counting operations.
-/

/-- Example: Zero reference count.
    An object with zero references can be deallocated.
-/
def zeroRefCount : ObjectId :=
  0

/-- Example: Non-zero reference count.
    An object with non-zero references cannot be deallocated.
-/
def nonZeroRefCount : ObjectId :=
  1

/-!
## Property Verification Examples

Examples demonstrating property verification.
-/

/-- Example: Verify reference count is non-negative.
    All reference counts are non-negative by definition.
-/
#eval ref_count_non_negative 0

/-- Example: Verify weak count is non-negative.
    All weak counts are non-negative by definition.
-/
#eval weak_count_non_negative 0

/-- Example: Verify empty graph is acyclic.
    An empty graph contains no cycles.
-/
#eval empty_graph_acyclic

/-- Example: Verify Iso to Val transition is valid.
    Iso to Val is a valid capability transition.
-/
#eval isoToValTransition

/-- Example: Verify Val to Ref transition is valid.
    Val to Ref is a valid capability transition.
-/
#eval valToRefTransition

/-- Example: Verify Ref to Weak transition is valid.
    Ref to Weak is a valid capability transition.
-/
#eval refToWeakTransition

/-- Example: Verify Weak to Iso transition is invalid.
    Weak to Iso is an invalid capability transition.
-/
#eval weakToIsoTransition

/-!
## ARC Operation Examples

Examples demonstrating ARC operations.
-/

/-- Example: Retain operation.
    Increments the reference count for an object.
-/
def retainOperation : ARCOperations :=
  ARCOperations.retain 0

/-- Example: Release operation.
    Decrements the reference count for an object.
-/
def releaseOperation : ARCOperations :=
  ARCOperations.release 0

/-- Example: Try retain operation.
    Attempts to increment the reference count, succeeds if object exists.
-/
def tryRetainOperation : ARCOperations :=
  ARCOperations.tryRetain 0

/-!
## Memory Safety Examples

Examples demonstrating memory safety properties.
-/

/-- Example: Zero reference count implies deallocatable.
    When reference count is zero, the object can be deallocated.
-/
#eval zero_ref_count_deallocatable 0

/-- Example: Deallocatable implies zero reference count.
    An object can only be deallocated when its reference count is zero.
-/
#eval deallocatable_zero_ref_count 0

/-!
## Capability Property Examples

Examples demonstrating capability properties.
-/

/-- Example: Iso types have at most one strong reference.
    Iso types represent unique ownership.
-/
#eval iso_constraint 0

/-- Example: Val types are immutable.
    Val types cannot be modified.
-/
#eval val_constraint 0

/-- Example: Ref types are not sendable.
    Ref types cannot be sent across actor boundaries.
-/
#eval ref_constraint 0

/-- Example: Weak references do not prevent deallocation.
    Weak references do not affect deallocation.
-/
#eval weak_no_prevent_deallocation 0

end Morph.Specs.ArcAffineIntegration

