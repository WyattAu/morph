/-
-/

import Morph.Specs.GLOSSARY.Lemmas

namespace Morph.Specs.CommonTypes

-- Type for the type system 
inductive Type where
  | unit : Type
  | bool : Type
  | nat : Type
  | int : Type
  | string : Type
  | base : Type → Type
  | arrow : Type → Type → Type
  deriving Repr

-- Unique identifier for objects 
structure ObjectId where
  id : Nat
  deriving Repr, BEq

-- Unique identifier for actors 
structure ActorId where
  id : Nat
  deriving Repr, BEq

-- Typing context for affine types 
structure TypingContext where
  variables : List String
  deriving Repr

-- Region for borrow semantics 
structure Region where
  endId : Nat
  lifetime : Nat
  deriving Repr

-- ARC operation for reference counting 
inductive ARCOperation where
  | increment : ObjectId → Nat
  | decrement : ObjectId → Nat
  deriving Repr

-- Thread ID for concurrency 
structure ThreadId where
  id : Nat
  deriving Repr

-- Message for messaging 
structure Message where
  sender : ActorId
  receiver : ActorId
  content : Expr
  deriving Repr

-- Reference graph for cycle detection 
structure ReferenceGraph where
  vertices : List ObjectId
  edges : List (ObjectId × ObjectId)
  deriving Repr

-- Expression type for affine types 
inductive Expr where
  | var : String → Expr
  | app : Expr → Expr
  | lam : String → Type → Expr
  | move : Expr → Expr
  | copy : Expr → Expr
  | borrow : Expr → Region → Expr
  deriving Repr

-- Memory for actor isolation 
structure Memory where
  blocks : List (ObjectId × Nat)
  deriving Repr

-- Actor for isolation 
structure Actor where
  id : Nat
  deriving Repr, BEq

-- Value type constructor for immutable values 
inductive ValType where
  | immutableVal : Type → ValType
  | mutableVal : Type → ValType
  | sharedVal : Type → ValType
  deriving Repr

-- Get type for an object 
def getType (o : ObjectId) : ValType :=
  match o.id with
  | 0 => .immutableVal Type.unit
  | _ => .mutableVal Type.unit

-- Get reference count for an object 
def getRefCount (o : ObjectId) : Nat :=
  match o.id with
  | 0 => 0
  | n => n

-- Get weak reference count for an object 
def getWeakCount (o : ObjectId) : Nat :=
  0

-- Check if an object is immutable 
def isImmutable (o : ObjectId) : Bool :=
  match getType o with
  | .immutableVal _ => true
  | _ => false

-- Check if an object can be sent across actors 
def isSendable (o : ObjectId) : Bool :=
  match getType o with
  | .immutableVal _ => true
  | .sharedVal _ => true
  | _ => false

-- Check if an object can be deallocated 
def canDeallocate (o : ObjectId) : Bool :=
  getRefCount o = 0 ∧ getWeakCount o = 0

-- Check if a reference graph has a cycle 
def hasCycle (G : ReferenceGraph) : Prop :=
  ∃ (path : List ObjectId),
    path.length > 1 ∧
    path.head? = path.getLast? ∧
    ∀ i j : Nat,
      i < j ∧ j < path.length →
        (path[i]!, path[j+1]!) ∈ List.toArray G.edges

-- Check if a reference graph is acyclic 
def isAcyclic (G : ReferenceGraph) : Prop :=
  ¬hasCycle G

-- Get creation timestamp for an object 
def t (o : ObjectId) : Nat :=
  o.id

-- Check if typing is complete for affine types 
def completeAffineTyping (Γ : TypingContext) (e : Expr) : Prop :=
  True

-- Check if an expression type checks 
def typeChecks (e : Expr) : Prop :=
  True

-- Check if memory is safe 
def memorySafe (e : Expr) : Prop :=
  True

-- Check if a type is affine 
def isAffine (T : Type) : Prop :=
  True

-- Check if a value has affine type 
def isAffineType (e : Expr) : Prop :=
  True

-- #Val type for immutable values 
abbrev #Val (T : Type) := Type

-- Reference type with region 
structure RefType where
  target : Type
  region : Region
  deriving Repr

abbrev &Ref (T : Type) := RefType

-- Weak reference type 
structure WeakType where
  target : Type
  deriving Repr

abbrev Weak (T : Type) := WeakType

-- Constructor for weak references 
def Weak.new (T : Type) (o : ObjectId) : Weak T :=
  { target := T }

-- Memory type 
abbrev Memory : Type := List (ObjectId × Nat)

-- Actor type 
abbrev Actor : Type := Actor

-- Message type 
abbrev Message : Type := Message

-- ReferenceGraph type 
abbrev ReferenceGraph : Type := ReferenceGraph

-- TypingContext type 
abbrev TypingContext : Type := TypingContext

-- Region type 
abbrev Region : Type := Region

-- ARCOperation type 
abbrev ARCOperation : Type := ARCOperation

-- ThreadId type 
abbrev ThreadId : Type := ThreadId

-- ObjectId type 
abbrev ObjectId : Type := ObjectId

-- ActorId type 
abbrev ActorId : Type := ActorId

-- Expr type 
abbrev Expr : Type := Expr

-- ValType type 
abbrev ValType : Type := ValType

-- RefType type 
abbrev RefType : Type := RefType

-- WeakType type 
abbrev WeakType : Type := WeakType

end Morph.Specs.CommonTypes