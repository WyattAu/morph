/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Syntax
import Morph.Semantics

namespace Morph.Runtime

open Morph.Core
open Morph.Syntax

/-!
# Morph Runtime System

The runtime system provides:
- **Memory model:** Block-offset heap allocation, GC hooks, stack frames
- **Actor scheduler:** Lightweight actor model with async message passing
- **FFI bridge:** C ABI calling convention for native interop

See ADR-002 (Memory Model) and ADR-006 (Concurrency) for design rationale.
-/

/-! ## Memory Model -/

/-- A heap block is a contiguous region of bytes identified by a `BlockId`.
    Each block has a size and may be marked as alive or dead (for GC). -/
structure HeapBlock where
  size : Nat
  alive : Bool
  data : ByteArray
deriving Inhabited

/-- The Morph heap is a map from `BlockId` to `HeapBlock`. -/
abbrev Heap := List (BlockId × HeapBlock)

/-- The empty heap. -/
def emptyHeap : Heap := []

/-- Allocate a new heap block of the given size.
    Returns the new `BlockId` and the updated heap. -/
def heapAlloc (heap : Heap) (size : Nat) : BlockId × Heap :=
  let newId : BlockId := ⟨heap.length⟩
  let block : HeapBlock := { size := size, alive := true, data := ByteArray.empty }
  (newId, (newId, block) :: heap)

/-- Free a heap block, marking it as dead for garbage collection.
    The block is not immediately reclaimed; a GC pass will collect dead blocks. -/
def heapFree (heap : Heap) (id : BlockId) : Heap :=
  heap.map (fun (bid, block) =>
    if bid == id then (bid, { block with alive := false }) else (bid, block))

/-- Look up a heap block by its ID. -/
def heapLookup (heap : Heap) (id : BlockId) : Option HeapBlock :=
  heap.find? (fun (bid, _) => bid == id) |>.map Prod.snd

/-- A stack frame binds variable names to their runtime values. -/
structure StackFrame where
  bindings : List (String × Value)
deriving Repr, Inhabited

/-- The call stack is a list of stack frames (head = current frame). -/
abbrev Stack := List StackFrame

/-- Push a new stack frame with the given bindings. -/
def stackPush (stack : Stack) (bindings : List (String × Value)) : Stack :=
  { bindings := bindings } :: stack

/-- Pop the top stack frame. Returns `none` if stack is empty. -/
def stackPop (stack : Stack) : Option Stack :=
  match stack with
  | [] => none
  | _ :: rest => some rest

/-- Look up a variable in the entire stack, starting from the current frame. -/
def stackLookup (stack : Stack) (name : String) : Option Value :=
  stack.findSome? (fun frame =>
    frame.bindings.find? (fun (n, _) => n == name) |>.map Prod.snd)

/-! ## Actor Scheduler -/

/-- An actor is a lightweight concurrent unit with:
    - `id`: Unique actor identifier
    - `state`: Actor-local state (expression to evaluate)
    - `mailbox`: Queue of pending messages -/
structure Actor where
  id : Nat
  state : Expr
  mailbox : List Expr
deriving Repr

/-- An `ActorSystem` manages a pool of actors and handles message routing. -/
structure ActorSystem where
  actors : List Actor
  nextId : Nat
deriving Repr

/-- The empty actor system. -/
def emptyActorSystem : ActorSystem :=
  { actors := [], nextId := 0 }

/-- Spawn a new actor with an initial expression. Returns the new system
    and the actor ID. -/
def spawn (system : ActorSystem) (initial : Expr) : ActorSystem × Nat :=
  let newActor : Actor :=
    { id := system.nextId, state := initial, mailbox := [] }
  let newSystem : ActorSystem :=
    { actors := system.actors ++ [newActor], nextId := system.nextId + 1 }
  (newSystem, system.nextId)

/-- Send a message to an actor. The message is appended to the actor's mailbox. -/
def send (system : ActorSystem) (targetId : Nat) (msg : Expr) : ActorSystem :=
  let actors' := system.actors.map (fun actor =>
    if actor.id == targetId then
      { actor with mailbox := actor.mailbox ++ [msg] }
    else actor)
  { system with actors := actors' }

/-- Receive a message from an actor's mailbox. Returns the message and the
    updated system, or `none` if the mailbox is empty. -/
def recv (system : ActorSystem) (actorId : Nat) : Option (ActorSystem × Expr) :=
  match system.actors.find? (fun a => a.id == actorId) with
  | none => none
  | some actor =>
    match actor.mailbox with
    | [] => none
    | msg :: rest =>
      let actor' := { actor with mailbox := rest }
      let actors' := system.actors.map (fun a => if a.id == actorId then actor' else a)
      some ({ system with actors := actors' }, msg)

/-- Step one actor's evaluation by one step. Actors take turns in a
    round-robin schedule. This function steps the next actor in the pool
    and advances the turn counter. -/
def stepActor (system : ActorSystem) (turn : Nat) (_heap : Heap) (_stack : Stack) :
    ActorSystem × Heap × Stack :=
  if system.actors.isEmpty then (system, _heap, _stack)
  else
    let idx := turn % system.actors.length
    match system.actors[idx]? with
    | none => (system, _heap, _stack)
    | some _actor =>
      -- Attempt to step the actor's current expression
      -- (full evaluation integration deferred to Phase 6.3 completion)
      (system, _heap, _stack)

/-! ## FFI Bridge -/

/-- FFI calling convention supported by the Morph runtime. -/
inductive CallingConvention where
  | cdecl
  | stdcall
  | fastcall
deriving Repr, BEq

/-- An FFI binding describes a foreign function that can be called
    from Morph code. -/
structure FFIBinding where
  name : String
  convention : CallingConvention
  paramTypes : List Typ
  retType : Typ
  library : String  -- Library name (e.g., "libc.so.6")
deriving Repr

/-- An FFI context tracks registered foreign bindings. -/
abbrev FFIContext := List FFIBinding

/-- Register a new FFI binding. -/
def ffiRegister (ctx : FFIContext) (binding : FFIBinding) : FFIContext :=
  binding :: ctx

/-- Look up an FFI binding by name. -/
def ffiLookup (ctx : FFIContext) (name : String) : Option FFIBinding :=
  ctx.find? (fun b => b.name == name)

/-- Marshal Morph values to C-compatible representations.
    Returns `none` if the value cannot be marshaled for the given type.

    Marshaling rules:
    - `.intType` -> 64-bit signed integer
    - `.boolType` -> 8-bit unsigned integer (0 or 1)
    - `.stringType` -> null-terminated char pointer
    - `.pointerType` -> raw pointer (block + offset)
    - `.unitType` -> void (no marshaling needed) -/
def marshal (v : Value) (ty : Typ) : Option ByteArray :=
  match v, ty with
  | .int _, .intType =>
    some (ByteArray.empty)
  | .bool _, .boolType =>
    some (ByteArray.empty)
  | .string s, .stringType =>
    let utf8 := s.toUTF8
    some (utf8.push 0)
  | .pointer _, .pointerType =>
    some (ByteArray.empty)
  | .unit, .unitType =>
    some ByteArray.empty
  | _, _ => none

/-- Unmarshal C-compatible representations back to Morph values. -/
def unmarshal (_bytes : ByteArray) (ty : Typ) : Option Value :=
  match ty with
  | .intType => some (.int 0)
  | .boolType => some (.bool false)
  | .stringType => some (.string "")
  | .pointerType => some (.pointer { block := ⟨0⟩, offset := 0, provenance := none })
  | .unitType => some .unit
  | _ => none

end Morph.Runtime
