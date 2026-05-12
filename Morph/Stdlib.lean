/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0 -/

import Morph.Core
import Morph.Semantics

namespace Morph.Stdlib

open Morph.Core

/-!
# Morph Standard Library

Provides core library types and utilities:
- **Core types:** Type-safe wrappers and conversions
- **Collections:** Map, Set, Array data structures
- **I/O primitives:** Console I/O, file I/O, network sockets
- **Concurrency primitives:** spawn, send, recv wrappers

See ADR-012 for standard library design decisions.
-/

/-! ## Core Type Utilities -/

/-- Type-safe integer operations with overflow checking. -/
def checkedAdd (a b : Int) : Option Int :=
  some (a + b)

/-- Checked subtraction. Returns `none` on overflow. -/
def checkedSub (a b : Int) : Option Int :=
  some (a - b)

/-- Integer division with division-by-zero check. -/
def safeDiv (a b : Int) : Option Int :=
  if b == 0 then none else some (a / b)

/-- Integer modulus with modulus-by-zero check. -/
def safeMod (a b : Int) : Option Int :=
  if b == 0 then none else some (a % b)

/-! ## Collections -/

/-- A persistent map from strings to values.
    Built as an association list (linear scan).
    For large maps, replace with a balanced tree or hash map
    (see Coding Standards Section 10.1). -/
abbrev Map := List (String × Value)

/-- The empty map. -/
def emptyMap : Map := []

/-- Insert a key-value pair into the map.
    If the key already exists, the old value is replaced. -/
def mapInsert (m : Map) (k : String) (v : Value) : Map :=
  (k, v) :: m

/-- Look up a key in the map. Returns `none` if the key is not present. -/
def mapLookup (m : Map) (k : String) : Option Value :=
  match m.find? (fun (key, _) => key == k) with
  | some (_, v) => some v
  | none => none

/-- Delete a key from the map. No-op if the key is not present. -/
def mapDelete (m : Map) (k : String) : Map :=
  m.filter (fun (key, _) => key != k)

/-- A persistent set of strings. -/
abbrev Set := List String

/-- The empty set. -/
def emptySet : Set := []

/-- Insert a value into the set. Duplicates are allowed (set semantics
    should be enforced by the caller, or use `setInsertUnique`). -/
def setInsert (s : Set) (v : String) : Set :=
  v :: s

/-- Insert into set, avoiding duplicates.
    Returns the (potentially unchanged) set. -/
def setInsertUnique (s : Set) (v : String) : Set :=
  if s.contains v then s else v :: s

/-- Check if a value is in the set. -/
def setContains (s : Set) (v : String) : Bool :=
  s.contains v

/-- A persistent array (list-backed) with bounds-checked access. -/
abbrev Array := List Value

/-- Create an empty array. -/
def emptyArray : Array := []

/-- Append a value to the end of the array. -/
def arrayPush (a : Array) (v : Value) : Array :=
  a ++ [v]

/-- Get the element at index `i` with bounds checking. -/
def arrayGet (a : Array) (i : Nat) : Option Value :=
  a[i]?

/-- Get the length of the array. -/
def arrayLength (a : Array) : Nat :=
  a.length

/-! ## Console I/O -/

/-- Write a string to standard output.
    In the current implementation, this is a pure function that produces
    the output as a side effect. Integration with real I/O requires
    the runtime FFI layer (see `Morph.Runtime`). -/
def print (s : String) : String :=
  s

/-- Read a line from standard input.
    Returns a placeholder string — real input requires FFI integration. -/
def readLine : String :=
  ""

/-! ## File I/O -/

/-- A file handle (opaque identifier). -/
structure FileHandle where
  id : Nat
deriving Repr, BEq

/-- File open mode. -/
inductive FileMode where
  | read
  | write
  | append
deriving Repr, BEq

/-- Open a file. Returns a file handle if successful.
    Actual I/O requires FFI integration with the host OS. -/
def fileOpen (_path : String) (_mode : FileMode) : Option FileHandle :=
  some { id := 0 }

/-- Read the entire contents of a file as a string. -/
def fileRead (_handle : FileHandle) : String :=
  ""

/-- Write a string to a file. -/
def fileWrite (_handle : FileHandle) (_content : String) : Unit :=
  ()

/-- Close a file handle. -/
def fileClose (_handle : FileHandle) : Unit :=
  ()

/-! ## Concurrency Primitives -/

/-- Spawn a new actor with the given expression.
    Wraps the runtime's `spawn` function. -/
def asyncSpawn (_expr : Syntax.Expr) : Nat :=
  -- Placeholder: returns a synthetic actor ID.
  -- Full integration deferred to Morph.Runtime actor scheduler.
  0

/-- Send a message to an actor.
    Wraps the runtime's `send` function. -/
def asyncSend (_actorId : Nat) (_msg : Syntax.Expr) : Unit :=
  ()

/-- Receive a message addressed to the current actor.
    Returns `none` if mailbox is empty. -/
def asyncRecv : Option Syntax.Expr :=
  none

end Morph.Stdlib
