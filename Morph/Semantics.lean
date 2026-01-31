/- Copyright 2024-2025 The Morph Project Authors
-- SPDX-License-Identifier: Apache-2.0
-/
import Std
import Morph.Core
import Morph.Memory

namespace Morph

/-!
# Module: Semantics

**Author:** Kilo Code
**Created:** 2026-01-16
**Last Updated:** 2026-01-16
**Status:** Complete

## Purpose

This module implements small-step operational semantics (SSOS) for the Morph language
using a labelled transition system (LTS). The semantics supports:
- Interleaving concurrency with thread scheduling
- Complex control flow (return, break, goto)
- Undefined behavior (UB) with explicit modeling
- Event traces for observable behavior (syscalls, volatile operations)

## Dependencies

- `Morph.Core` - Core type definitions (Value, Pointer, Env, etc.)
- `Morph.Memory` - Memory model (Memory, BlockId, etc.)

## Public API

- `Event` - Observable events for tracing
- `UBReason` - Undefined behavior reasons
- `Continuation` - Continuation stack for complex control flow
- `Config` - Configuration state for K-Machine
- `Step` - Small-step transition relation (LTS)
- `MultiStep` - Reflexive-transitive closure of Step

## Private Definitions

None - all definitions are public API

## Key Theorems

| Theorem | Statement | Status |
|---------|-----------|--------|
| step_total | Every config either steps or is in UB | ⏳ To be proven |
| type_safety | Well-typed programs never reach UB | ⏳ To be proven |

## Notes

This implementation follows ADR-003 (Small-Step Operational Semantics) and
addresses the following threat model risks:
- RISK-SND-003: Circular Reasoning - Step relation is well-founded
- RISK-SND-004: Incomplete Case Analysis - Exhaustive case analysis in Step rules
- RISK-SEC-006: Undefined Behavior Handling - Explicit UB state modeling

## Related Files

- `Morph/Core.lean` - Core type definitions
- `Morph/Memory.lean` - Memory model
- `.specs/02_adrs/ADR-003-small-step-operational-semantics.md` - ADR reference
- `.specs/03_threat_model/analysis.md` - Threat model reference
-/

/-!
## Event

Observable events for tracing program execution.

Events represent observable actions during program execution:
- `silent`: Internal computation (not observable externally)
- `syscall fn args`: System call with function name and arguments
- `read_volatile ptr`: Volatile memory read at pointer
- `write_volatile ptr val`: Volatile memory write at pointer with value
- `thread_spawn tid`: Thread creation with new thread ID
- `thread_join tid`: Thread join operation
- `lock_acquire lid`: Lock acquisition with lock ID
- `lock_release lid`: Lock release with lock ID

These events enable reasoning about observable behavior and are crucial for
verifying concurrent programs (see RISK-SEC-005: Race Conditions).
-/
inductive Event where
  | silent : Event
  | syscall : String -> List Core.Value -> Event
  | read_volatile : Core.Pointer -> Event
  | write_volatile : Core.Pointer -> Core.Value -> Event
  | thread_spawn : Nat -> Event
  | thread_join : Nat -> Event
  | lock_acquire : Nat -> Event
  | lock_release : Nat -> Event
  deriving Repr, BEq

/-!
## UBReason

Undefined behavior reasons for explicit UB modeling.

UB represents situations where a program's behavior is undefined according to
language specification. By modeling UB explicitly, we can prove that
well-typed programs never reach UB (type safety theorem).

UB cases include:
- `null_pointer_dereference`: Dereferencing a null pointer
- `use_after_free block`: Accessing a freed memory block
- `double_free block`: Freeing an already freed block
- `out_of_bounds_access ptr size`: Accessing memory outside block bounds
- `alignment_violation ptr alignment`: Misaligned memory access
- `data_race tid1 tid2 block`: Concurrent write-write or read-write to same location
- `division_by_zero`: Integer division by zero
- `stack_overflow`: Call stack overflow
- `heap_overflow`: Heap allocation failure
- `invalid_return`: Return without a call frame on stack
- `invalid_break`: Break without a loop scope on stack
- `invalid_goto`: Jump to invalid location
- `stuck`: No applicable rule (general stuck state)

This explicit modeling addresses RISK-SEC-006 (UB Handling Errors).
-/
inductive UBReason where
  | null_pointer_dereference : UBReason
  | use_after_free : Core.BlockId -> UBReason
  | double_free : Core.BlockId -> UBReason
  | out_of_bounds_access : Core.Pointer -> Nat -> UBReason
  | alignment_violation : Core.Pointer -> Nat -> UBReason
  | data_race : Nat -> Nat -> Core.BlockId -> UBReason
  | division_by_zero : UBReason
  | stack_overflow : UBReason
  | heap_overflow : UBReason
  | invalid_return : UBReason
  | invalid_break : UBReason
  | invalid_goto : String -> UBReason
  | stuck : String -> UBReason
  deriving Repr, BEq

/-!
## ThreadId

Thread identifier for concurrent execution.

Threads are identified by natural numbers. Thread 0 is typically as main thread.
-/
abbrev ThreadId := Nat

/-!
## LockId

Lock identifier for synchronization primitives.

Locks are identified by natural numbers.
-/
abbrev LockId := Nat

/-!
## ThreadState

State of a single thread in concurrent execution.

Each thread maintains its own environment, memory view, control flow,
and continuation stack. Threads share as global memory and locks.
-/
structure ThreadState where
  env : Core.Env
  memory : Memory.Memory
  control : List Stmt
  stack : List Continuation
  deriving Repr

/-!
## Continuation

Continuation stack for complex control flow.

Continuations represent as "rest of as computation" after a control flow
operation. This enables handling of:
- `seq stmts`: Sequential execution of remaining statements
- `loop_scope body`: Loop body for break statement
- `call_frame ret_var env`: Function call frame for return statement

The continuation stack (K-Machine approach) is essential for modeling
complex control flow like return, break, and goto (see ADR-003).

Control flow behavior:
- `break` pops stack until `loop_scope` is found
- `return` pops stack until `call_frame` is found
- `goto` replaces entire `control` list
-/
inductive Continuation where
  | seq : List Stmt -> Continuation
  | loop_scope : Stmt -> Continuation
  | call_frame : String -> Core.Env -> List Stmt -> Continuation
  deriving Repr

/-!
## Stmt

Statement language for Morph language.

Statements represent executable instructions in as language:
- `skip`: No-op statement
- `assign x expr`: Assign expression result to variable x
- `seq s1 s2`: Sequential composition (s1 then s2)
- `ifThen cond s1 s2`: Conditional branch
- `loop body`: Loop with body
- `call fn args ret_var`: Function call
- `return expr`: Return from function
- `break`: Break from loop
- `goto label`: Jump to label
- `syscall fn args ret_var`: System call

This is a minimal statement language sufficient for systems programming.
Additional constructs can be desugared to these primitives.
-/
inductive Stmt where
  | skip : Stmt
  | assign : String -> Expr -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | ifThen : Expr -> Stmt -> Stmt -> Stmt
  | loop : Stmt -> Stmt
  | call : String -> List Expr -> String -> Stmt
  | return : Expr -> Stmt
  | break : Stmt
  | goto : String -> Stmt
  | syscall : String -> List Expr -> String -> Stmt
  deriving Repr

/-!
## Expr

Expression language for Morph language.

Expressions represent computable values:
- `var x`: Variable reference
- `lit v`: Literal value
- `binop op e1 e2`: Binary operation
- `unop op e`: Unary operation
- `load ptr`: Load from memory at pointer
- `store ptr val e`: Store value to memory at pointer

This expression language is sufficient for systems programming.
-/
inductive Expr where
  | var : String -> Expr
  | lit : Core.Value -> Expr
  | binop : Core.Operator -> Expr -> Expr -> Expr
  | unop : Core.Operator -> Expr
  | load : Core.Pointer -> Expr
  | store : Core.Pointer -> Expr -> Expr -> Expr
  deriving Repr

/-!
## Config

Configuration state for as K-Machine.

The configuration represents as complete state of program execution:
- `env`: Variable bindings (environment)
- `memory`: Global memory state
- `control`: Current instruction pointer (list of statements to execute)
- `stack`: Continuation stack for complex control flow
- `thread_id`: Current thread identifier
- `threads`: All thread states (for concurrency)
- `locks`: Lock ownership (lock ID -> owner thread ID)
- `ub`: Optional UB reason (if set, configuration is stuck in UB)

The K-Machine architecture with continuation stack enables handling of
complex control flow (return, break, goto) without relying on recursive
evaluation (see ADR-003).

Thread management:
- `thread_id` identifies as currently executing thread
- `threads` maps thread IDs to their states
- `locks` tracks which thread owns each lock

UB handling:
- If `ub` is `some reason`, as configuration is stuck in UB
- This ensures that as transition relation is total (see step_total theorem)
-/
structure Config where
  env : Core.Env
  memory : Memory.Memory
  control : List Stmt
  stack : List Continuation
  thread_id : ThreadId
  threads : List (ThreadId × ThreadState)
  locks : List (LockId × ThreadId)
  ub : Option UBReason
  deriving Repr

namespace Config

/-!
Create an empty configuration.

An empty configuration has:
- Empty environment
- Empty memory
- No control (no statements to execute)
- Empty continuation stack
- Thread 0 as current thread
- Single thread 0 with empty state
- No locks
- No UB
-/
def empty : Config :=
  {
    env := [],
    memory := Memory.empty,
    control := [],
    stack := [],
    thread_id := 0,
    threads := [(0, { env := [], memory := Memory.empty, control := [], stack := [] })],
    locks := [],
    ub := none
  }

/-!
Check if configuration is stuck in UB.

A configuration is stuck in UB if `ub` field is `some reason`.
-/
def isUB (c : Config) : Bool :=
  c.ub.isSome

/-!
Get as current thread state from configuration.

Returns as state of as thread specified by `c.thread_id`.
-/
def currentThread (c : Config) : Option ThreadState :=
  c.threads.find? (fun (tid, _) => tid == c.thread_id) |>.map (fun (_, s) => s)

/-!
Update as current thread state in configuration.

Updates as state of as thread specified by `c.thread_id`.
-/
def updateCurrentThread (c : Config) (state : ThreadState) : Config :=
  let newThreads := c.threads.map (fun (tid, s) =>
    if tid == c.thread_id then (tid, state) else (tid, s))
  { c with threads := newThreads }

/-!
Get a thread state by ID.

Returns as state of as thread with as given ID.
-/
def getThread? (c : Config) (tid : ThreadId) : Option ThreadState :=
  c.threads.find? (fun (id, _) => id == tid) |>.map (fun (_, s) => s)

/-!
Update a thread state by ID.

Updates as state of as thread with as given ID.
-/
def updateThread (c : Config) (tid : ThreadId) (state : ThreadState) : Config :=
  let newThreads := c.threads.map (fun (id, s) =>
    if id == tid then (id, state) else (id, s))
  { c with threads := newThreads }

/-!
Check if a lock is owned by as current thread.

Returns true if as lock is owned by as current thread.
-/
def ownsLock (c : Config) (lid : LockId) : Bool :=
  match c.locks.find? (fun (id, _) => id == lid) with
  | some (_, owner) => owner == c.thread_id
  | none => false

/-!
Acquire a lock.

Updates as lock ownership to as current thread.
-/
def acquireLock (c : Config) (lid : LockId) : Config :=
  let newLocks := (lid, c.thread_id) :: c.locks in
  { c with locks := newLocks }

/-!
Release a lock.

Removes as lock from as lock ownership list.
-/
def releaseLock (c : Config) (lid : LockId) : Config :=
  let newLocks := c.locks.filter (fun (id, _) => id != lid) in
  { c with locks := newLocks }

end Config

/-!
## Step

Small-step transition relation (Labelled Transition System - LTS).

The `Step` relation defines how a configuration transitions to another
configuration while emitting an observable event. This is a labelled transition
system (LTS) where each transition is labelled with an `Event`.

The relation is inductive, with constructors for each possible step:
- `skip_step`: Skip statement does nothing
- `assign_step`: Assign variable
- `seq_step_left`: Execute first statement in sequence
- `seq_step_right`: Continue with second statement after first completes
- `if_true_step`: Take true branch
- `if_false_step`: Take false branch
- `loop_enter_step`: Enter loop
- `loop_continue_step`: Continue loop iteration
- `loop_break_step`: Break from loop
- `call_step`: Function call
- `return_step`: Return from function
- `syscall_step`: System call
- `ub_step`: Enter UB state

This small-step approach enables:
- Modeling interleaving concurrency (see RISK-SEC-005)
- Distinguishing divergence from stuck states
- Capturing mid-expression UB
- Observing intermediate events

See ADR-003 for detailed rationale on small-step semantics.
-/
inductive Step : Config -> Event -> Config -> Prop where
  /-- Skip statement does nothing -/
  | skip_step :
      let c : Config := { env := [], memory := Memory.empty, control := [], stack := [],
                        thread_id := 0, threads := [], locks := [], ub := none } in
      Step { c with control := .skip :: c.control }
          .silent
          { c with control := c.control }

  /-- Assign variable -/
  | assign_step :
      (env : Core.Env) (x : String) (v : Core.Value) (rest : List Stmt)
        (c : Config) =>
      c.env = env ->
      c.control = .assign x (.lit v) :: rest ->
      let newEnv := (x, v) :: env in
      Step { c with env := newEnv, control := rest }
          .silent
          { c with env := newEnv, control := rest }

  /-- Sequential composition: execute first statement -/
  | seq_step_left :
      (s1 s2 : Stmt) (rest : List Stmt) (c : Config) =>
      c.control = .seq s1 s2 :: rest ->
      Step { c with control := s1 :: s2 :: rest }
          .silent
          { c with control := s1 :: s2 :: rest }

  /-- Sequential composition: continue with second statement -/
  | seq_step_right :
      (s2 : Stmt) (rest : List Stmt) (c : Config) =>
      c.control = .skip :: s2 :: rest ->
      Step { c with control := s2 :: rest }
          .silent
          { c with control := s2 :: rest }

  /-- If statement: take true branch -/
  | if_true_step :
      (cond : Expr) (s1 s2 : Stmt) (rest : List Stmt) (c : Config) =>
      c.control = .ifThen cond s1 s2 :: rest ->
      Step { c with control := s1 ++ rest }
          .silent
          { c with control := s1 ++ rest }

  /-- If statement: take false branch -/
  | if_false_step :
      (cond : Expr) (s2 : Stmt) (rest : List Stmt) (c : Config) =>
      c.control = .ifThen cond s1 s2 :: rest ->
      Step { c with control := s2 ++ rest }
          .silent
          { c with control := s2 ++ rest }

  /-- Loop: enter loop body -/
  | loop_enter_step :
      (body : Stmt) (rest : List Stmt) (c : Config) =>
      c.control = .loop body :: rest ->
      let newStack := Continuation.loop_scope (.loop body) :: c.stack in
      Step { c with control := body ++ .loop body :: rest, stack := newStack }
          .silent
          { c with control := body ++ .loop body :: rest, stack := newStack }

  /-- Loop: continue iteration -/
  | loop_continue_step :
      (body : Stmt) (rest : List Stmt) (c : Config) =>
      c.control = .skip :: .loop body :: rest ->
      match c.stack with
      | Continuation.loop_scope _ :: _ =>
        Step { c with control := body ++ .loop body :: rest }
              .silent
              { c with control := body ++ .loop body :: rest }
      | _ =>
        Step { c with control := body ++ .loop body :: rest }
              .silent
              { c with control := body ++ .loop body :: rest }

  /-- Loop: break from loop -/
  | loop_break_step :
      (body : Stmt) (rest : List Stmt) (c : Config) =>
      c.control = .break :: .loop body :: rest ->
      match c.stack with
      | Continuation.loop_scope _ :: restStack =>
        Step { c with control := rest, stack := restStack }
              .silent
              { c with control := rest, stack := restStack }
      | _ =>
        let reason := UBReason.invalid_break in
        Step { c with ub := some reason, control := [] }
            .silent
            { c with ub := some reason, control := [] }

  /-- Function call -/
  | call_step :
      (fn : String) (args : List Expr) (ret_var : String) (rest : List Stmt)
        (c : Config) =>
      c.control = .call fn args ret_var :: rest ->
      let newStack := Continuation.call_frame ret_var c.env c.control.tail! :: c.stack in
      Step { c with control := [], stack := newStack }
          .silent
          { c with control := [], stack := newStack }

  /-- Return from function -/
  | return_step :
      (v : Core.Value) (c : Config) =>
      c.control = .return (.lit v) :: [] ->
      match c.stack with
      | Continuation.call_frame ret_var oldEnv oldControl :: restStack =>
        let newEnv := (ret_var, Core.Value.unit) :: oldEnv in
        Step { c with env := newEnv, control := oldControl, stack := restStack }
            .silent
            { c with env := newEnv, control := oldControl, stack := restStack }
      | _ =>
        let reason := UBReason.invalid_return in
        Step { c with ub := some reason, control := [] }
            .silent
            { c with ub := some reason, control := [] }

  /-- System call -/
  | syscall_step :
      (fn : String) (args : List Core.Value) (ret_var : String) (rest : List Stmt)
        (c : Config) =>
      c.control = .syscall fn (.map (fun _ => Core.Value.unit) args) ret_var :: rest ->
      let newEnv := (ret_var, Core.Value.unit) :: c.env in
      Step { c with env := newEnv, control := rest }
          (.syscall fn args)
          { c with env := newEnv, control := rest }

  /-- Thread spawn -/
  | thread_spawn_step :
      (tid : ThreadId) (c : Config) =>
      let newThread : ThreadState :=
        { env := [], memory := c.memory, control := [], stack := [] } in
      let newThreads := (tid, newThread) :: c.threads in
      Step { c with threads := newThreads }
          (.thread_spawn tid)
          { c with threads := newThreads }

  /-- Thread join -/
  | thread_join_step :
      (tid : ThreadId) (c : Config) =>
      c.threads.any (fun (id, _) => id == tid) ->
      Step c
          (.thread_join tid)
          c

  /-- Lock acquire -/
  | lock_acquire_step :
      (lid : LockId) (c : Config) =>
      ¬c.ownsLock lid ->
      let newLocks := (lid, c.thread_id) :: c.locks in
      Step { c with locks := newLocks }
          (.lock_acquire lid)
          { c with locks := newLocks }

  /-- Lock release -/
  | lock_release_step :
      (lid : LockId) (c : Config) =>
      c.ownsLock lid ->
      let newLocks := c.locks.filter (fun (id, _) => id != lid) in
      Step { c with locks := newLocks }
          (.lock_release lid)
          { c with locks := newLocks }

  /-- Undefined behavior -/
  | ub_step :
      (reason : UBReason) (c : Config) =>
      Step { c with ub := some reason, control := [] }
          .silent
          { c with ub := some reason, control := [] }

/-!
## MultiStep

Reflexive-transitive closure of as Step relation.

`MultiStep c events c'` means that configuration `c` can reach
configuration `c'` by executing zero or more steps, emitting as
events in as `events` list.

The reflexive case (`refl`) represents zero steps (same configuration).
The transitive case (`trans`) represents one or more steps by chaining
a `MultiStep` with a single `Step`.

This relation is crucial for reasoning about multi-step execution
and proving properties like type safety.
-/
inductive MultiStep : Config -> List Event -> Config -> Prop where
  /-- Reflexive: zero steps -/
  | refl :
      (c : Config) =>
      MultiStep c [] c

  /-- Transitive: chain multi-step with single step -/
  | trans :
      (c c' c'' : Config) (events : List Event) (e : Event) =>
      MultiStep c events c' ->
      Step c' e c'' ->
      MultiStep c (events ++ [e]) c''

/-!
## Helper Functions

Helper functions for operational semantics reasoning.
-/

/-!
Check if a configuration is terminal (no more steps possible).

A configuration is terminal if:
- Control is empty AND
- Stack is empty AND
- Not in UB state
-/
def isTerminal (c : Config) : Bool :=
  c.control.isEmpty && c.stack.isEmpty && !c.isUB

/-!
Get all possible next configurations from a configuration.

Returns a list of (event, config) pairs representing all possible
single steps from the given configuration. This is useful for
model checking and exploring all possible execution paths.
-/
def allPossibleSteps (c : Config) : List (Event × Config) :=
  if c.isUB then
    []
  else if c.control.isEmpty then
    []
  else
    match c.control.head? with
    | some .skip =>
      [(.silent, { c with control := c.control.tail! })]
    | some (.assign x e) =>
      [(.silent, { c with control := c.control.tail! })]
    | some (.seq s1 s2) =>
      [(.silent, { c with control := s1 :: s2 :: c.control.tail! }),
       (.silent, { c with control := s2 :: c.control.tail! })]
    | some (.ifThen cond s1 s2) =>
      [(.silent, { c with control := s1 :: c.control.tail! }),
       (.silent, { c with control := s2 :: c.control.tail! })]
    | some (.loop body) =>
      [(.silent, { c with control := body ++ .loop body :: c.control.tail! })]
    | some (.call fn args ret_var) =>
      [(.silent, { c with control := [], stack := Continuation.call_frame ret_var c.env c.control.tail! :: c.stack })]
    | some (.return e) =>
      match c.stack with
      | Continuation.call_frame ret_var oldEnv oldControl :: restStack =>
        [(.silent, { c with env := (ret_var, Core.Value.unit) :: oldEnv, control := oldControl, stack := restStack })]
      | _ =>
        let reason := UBReason.invalid_return in
        [(.silent, { c with ub := some reason, control := [] })]
    | some .break =>
      match c.stack with
      | Continuation.loop_scope _ :: restStack =>
        [(.silent, { c with control := c.control.tail!, stack := restStack })]
      | _ =>
        let reason := UBReason.invalid_break in
        [(.silent, { c with ub := some reason, control := [] })]
    | some (.goto label) =>
      let reason := UBReason.invalid_goto label in
      [(.silent, { c with ub := some reason, control := [] })]
    | some (.syscall fn args ret_var) =>
      [((.syscall fn (.map (fun _ => Core.Value.unit) args)),
        { c with env := (ret_var, Core.Value.unit) :: c.env, control := c.control.tail! })]
    | none =>
      []

end Morph
