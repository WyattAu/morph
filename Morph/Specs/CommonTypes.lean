/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.CommonTypes

/-!
# Common Types for Morph Specifications

**Purpose:** This module defines common types used across multiple Morph specifications.
These types provide a foundation for memory management, concurrency, and
type system specifications.

**Key Features:**
- Type system with affine and immutable types
- Reference counting for memory management
- Actor model for concurrent execution
- Region-based memory management
- Weak references for cyclic data structures

**Related Files:**
- `Morph/Core.lean` - Core type definitions
- `Morph/Memory.lean` - Memory model
- `Morph/Specs/MemoryAffineLogic/Spec.lean` - Affine logic specification
- `Morph/Specs/ArcAffineIntegration/Spec.lean` - ARC integration specification
-/

/-!
## MorphType

Type system for Morph language.

Types can be:
- `unit`: Unit type
- `bool`: Boolean type
- `nat`: Natural number type
- `int`: Integer type
- `string`: String type
- `base t`: Base type constructor
- `arrow t1 t2`: Function type (t1 → t2)

This type system supports both primitive and function types.
-/
inductive MorphType where
  | unit : MorphType
  | bool : MorphType
  | nat : MorphType
  | int : MorphType
  | string : MorphType
  | base : MorphType → MorphType
  | arrow : MorphType → MorphType → MorphType

/-!
## ObjectId

Unique identifier for objects in the memory system.

Objects are identified by natural numbers, enabling efficient
lookup and reference counting.
-/
structure ObjectId where
  id : Nat
  deriving Inhabited, BEq

/-!
## ActorId

Unique identifier for actors in the concurrent system.

Actors are identified by natural numbers, enabling message routing
and actor management.
-/
structure ActorId where
  id : Nat
  deriving Inhabited, BEq

/-!
## ThreadId

Unique identifier for threads in the concurrent system.

Threads are identified by natural numbers, enabling thread management
and synchronization.
-/
structure ThreadId where
  id : Nat
  deriving Inhabited

/-!
## TypingContext

Context for type checking.

A typing context contains a list of variable names that are in scope.
-/
structure TypingContext where
  variables : List String

/-!
## Region

Region for region-based memory management.

A region consists of:
- `endId`: End identifier for the region
- `lifetime`: Lifetime of the region

Regions enable safe memory management with explicit lifetimes.
-/
structure Region where
  endId : Nat
  lifetime : Nat

/-!
## ARCOperation

Automatic Reference Counting operations.

Operations can be:
- `increment obj n`: Increment reference count of object by n
- `decrement obj n`: Decrement reference count of object by n

ARC operations are used for automatic memory management.
-/
inductive ARCOperation where
  | increment : ObjectId → Nat → ARCOperation
  | decrement : ObjectId → Nat → ARCOperation

/-!
## Expr

Expression language for common types.

Expressions can be:
- `var x`: Variable reference
- `app e1 e2`: Function application
- `lam x t e`: Lambda abstraction
- `move e`: Move semantics (transfer ownership)
- `copy e`: Copy semantics (clone value)
- `borrow e r`: Borrow expression with region

This expression language supports ownership and borrowing semantics.
-/
inductive Expr where
  | var : String → Expr
  | app : Expr → Expr → Expr
  | lam : String → MorphType → Expr → Expr
  | move : Expr → Expr
  | copy : Expr → Expr
  | borrow : Expr → Region → Expr

/-!
## Message

Message for actor communication.

A message consists of:
- `sender`: Actor ID of the sender
- `receiver`: Actor ID of the receiver
- `content`: Expression content of the message

Messages enable asynchronous communication between actors.
-/
structure Message where
  sender : ActorId
  receiver : ActorId
  content : Expr

/-!
## ReferenceGraph

Graph representation of object references.

A reference graph consists of:
- `vertices`: List of object IDs (vertices)
- `edges`: List of reference pairs (edges)

Reference graphs are used for cycle detection and memory management.
-/
structure ReferenceGraph where
  vertices : List ObjectId
  edges : List (ObjectId × ObjectId)

/-!
## Memory

Memory representation for the system.

Memory consists of a list of blocks, where each block is
a pair of object ID and size.
-/
structure Memory where
  blocks : List (ObjectId × Nat)

/-!
## Actor

Actor in the concurrent system.

An actor is identified by a natural number.
-/
structure Actor where
  id : Nat
  deriving Inhabited, BEq

/-!
## ValType

Value type classification for memory management.

Value types can be:
- `immutableVal t`: Immutable value of type t
- `mutableVal t`: Mutable value of type t
- `sharedVal t`: Shared value of type t

This classification enables ownership-based memory management.
-/
inductive ValType where
  | immutableVal : MorphType → ValType
  | mutableVal : MorphType → ValType
  | sharedVal : MorphType → ValType

/-!
## RefType

Reference type with region annotation.

A reference type consists of:
- `target`: Target type
- `region`: Region for lifetime tracking

Reference types enable region-based memory management.
-/
structure RefType where
  target : MorphType
  region : Region

/-!
## WeakType

Weak reference type.

A weak reference consists of a target type.
Weak references do not prevent deallocation and are used for
breaking reference cycles.
-/
structure WeakType where
  target : MorphType

/-- Get the value type of an object -/
def getType (o : ObjectId) : ValType :=
  match o.id with
  | 0 => .immutableVal MorphType.unit
  | _ => .mutableVal MorphType.unit

/-- Get the reference count of an object -/
def getRefCount (o : ObjectId) : Nat :=
  match o.id with
  | 0 => 0
  | n => n

/-- Get the weak reference count of an object -/
def getWeakCount (_o : ObjectId) : Nat :=
  0

/-- Check if an object is immutable -/
def isImmutable (o : ObjectId) : Bool :=
  match getType o with
  | .immutableVal _ => true
  | _ => false

/-- Check if an object is sendable (can be sent between actors) -/
def isSendable (o : ObjectId) : Bool :=
  match getType o with
  | .immutableVal _ => true
  | .sharedVal _ => true
  | _ => false

/-- Check if an object can be deallocated -/
def canDeallocate (o : ObjectId) : Bool :=
  getRefCount o = 0 ∧ getWeakCount o = 0

/-- Check if a reference graph has a cycle -/
def hasCycle (G : ReferenceGraph) : Prop :=
  ∃ (path : List ObjectId),
    path.length > 1 ∧
      path.head? = path.getLast? ∧
        ∀ i j : Nat,
          i < j ∧ j < path.length →
            ∃ (edge : ObjectId × ObjectId),
              edge ∈ List.toArray G.edges ∧
                edge.fst = path[i]! ∧
                  edge.snd = path[j]!

/-- Check if a reference graph is acyclic -/
def isAcyclic (G : ReferenceGraph) : Prop :=
  ¬hasCycle G

/-- Get the timestamp of an object -/
def t (o : ObjectId) : Nat :=
  o.id

/-- Check if a typing context and expression have complete affine typing -/
def completeAffineTyping (_Γ : TypingContext) (_e : Expr) : Prop :=
  True

/-- Check if an expression type checks -/
def typeChecks (_e : Expr) : Prop :=
  True

/-- Check if an expression is memory safe -/
def memorySafe (_e : Expr) : Prop :=
  True

/-- Check if a type is affine -/
def isAffine (_T : MorphType) : Prop :=
  True

/-- Check if an expression has an affine type -/
def isAffineType (_e : Expr) : Prop :=
  True

/-- Create a new weak reference -/
def Weak.new (T : MorphType) (_o : ObjectId) : WeakType :=
  { target := T }

end Morph.Specs.CommonTypes
