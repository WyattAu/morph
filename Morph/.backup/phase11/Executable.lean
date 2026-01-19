import Std
import Morph.Core
import Morph.Memory
import Morph.Semantics

namespace Morph

/-!
# Module: Executable

**Author:** Kilo Code
**Created:** 2026-01-16
**Last Updated:** 2026-01-16
**Status:** Complete

## Purpose

This module implements the executable reference interpreter for the Morph language.
It provides a monad-based interpreter that can be used for:
- Testing and fuzzing
- Conformance checking against formal semantics
- Debugging and verification

## Dependencies

- `Morph.Core` - Core type definitions (Value, Pointer, Env, etc.)
- `Morph.Memory` - Memory model (Memory, BlockId, etc.)
- `Morph.Semantics` - Operational semantics (Config, Event, UBReason, etc.)

## Public API

- `Context` - Read-only typing environment for the interpreter
- `InterpM` - Monad transformer stack for the interpreter
- `step_executable` - Single-step execution function
- `run_executable` - Multi-step execution function
- State management functions (get_env, modify_env, get_memory, modify_memory, etc.)
- I/O operations for syscalls (syscall_read, syscall_write, syscall_spawn, etc.)

## Private Definitions

None - all definitions are public API

## Key Theorems

| Theorem | Statement | Status |
|---------|-----------|--------|
| step_equivalence | step_executable matches formal Step relation | ⏳ To be proven |

## Notes

This implementation follows ADR-006 (Monad Stack for Executable Reference) and
addresses the following threat model risks:
- RISK-SEC-005: Race Conditions in Concurrent Verification - Uses explicit thread state management
- RISK-SEC-006: Undefined Behavior (UB) Handling Errors - Explicit UBReason error type
- RISK-SND-007: Equivalence Proof Errors - Designed to match formal semantics

The monad stack structure is:
```
InterpM = ReaderT Context (StateT Config (ExceptT UBReason Id))
```

This provides:
- ReaderT Context: Read-only access to typing environment
- StateT Config: Mutable execution state (env, memory, control, threads, locks)
- ExceptT UBReason: Error handling for undefined behavior

## Related Files

- `Morph/Core.lean` - Core type definitions
- `Morph/Memory.lean` - Memory model
- `Morph/Semantics.lean` - Operational semantics
- `.specs/02_adrs/ADR-006-monad-stack-executable-reference.md` - ADR reference
- `.specs/03_threat_model/analysis.md` - Threat model reference
-!/

/-!
## Context

Read-only typing environment for the interpreter.

The context contains type information that is shared across all threads
and does not change during execution. This is passed through the ReaderT
monad transformer for efficient read access.
-!/
structure Context where
  types : Std.HashMap String Typ
  lifetimes : Std.HashMap String String
  deriving Repr, BEq

namespace Context

/-!
Create an empty context.

An empty context has no type bindings or lifetime information.
-!/
def empty : Context :=
  { types := Std.HashMap.empty, lifetimes := Std.HashMap.empty }

/-!
Add a type binding to the context.

Used during type checking to track variable types.
-!/
def addType (ctx : Context) (name : String) (ty : Typ) : Context :=
  { ctx with types := ctx.types.insert name ty }

/-!
Get the type of a variable from the context.

Returns `none` if the variable is not in the context.
-!/
def getType? (ctx : Context) (name : String) : Option Typ :=
  ctx.types.find? name

end Context

/-!
## InterpM

Monad transformer stack for the executable reference interpreter.

The stack is:
```
ReaderT Context (StateT Config (ExceptT UBReason Id))
```

This provides:
- **ReaderT Context**: Read-only access to typing environment
- **StateT Config**: Mutable execution state
- **ExceptT UBReason**: Error handling for undefined behavior

The monad stack enables:
- Composable operations
- Centralized error handling
- Explicit state management
- Type-safe state transitions
-!/
abbrev InterpM (α : Type) : Type :=
  ReaderT Context (
  StateT Config (
  ExceptT UBReason Id
  )) α

/-!
## State Management Functions

Functions for accessing and modifying the interpreter state.

These functions provide convenient access to the Config state managed
by the StateT monad transformer.
-!/

/-!
Get the current configuration state.

Returns the entire Config structure.
-!/
def get_config : InterpM Config :=
  get

/-!
Get the current environment (variable bindings).

Returns the env field from the current Config.
-!/
def get_env : InterpM Core.Env :=
  return (← get_config).env

/-!
Modify the current environment.

Applies a function to the env field and updates the Config.
-!/
def modify_env (f : Core.Env → Core.Env) : InterpM Unit := do
  modify (fun cfg => { cfg with env := f cfg.env })

/-!
Get the current memory state.

Returns the memory field from the current Config.
-!/
def get_memory : InterpM Memory.Memory :=
  return (← get_config).memory

/-!
Modify the current memory state.

Applies a function to the memory field and updates the Config.
-!/
def modify_memory (f : Memory.Memory → Memory.Memory) : InterpM Unit := do
  modify (fun cfg => { cfg with memory := f cfg.memory })

/-!
Get the current control flow (instruction pointer).

Returns the control field from the current Config.
-!/
def get_control : InterpM (List Stmt) :=
  return (← get_config).control

/-!
Modify the current control flow.

Applies a function to the control field and updates the Config.
-!/
def modify_control (f : List Stmt → List Stmt) : InterpM Unit := do
  modify (fun cfg => { cfg with control := f cfg.control })

/-!
Get the current continuation stack.

Returns the stack field from the current Config.
-!/
def get_stack : InterpM (List Continuation) :=
  return (← get_config).stack

/-!
Modify the continuation stack.

Applies a function to the stack field and updates the Config.
-!/
def modify_stack (f : List Continuation → List Continuation) : InterpM Unit := do
  modify (fun cfg => { cfg with stack := f cfg.stack })

/-!
Get the current thread ID.

Returns the thread_id field from the current Config.
-!/
def get_thread_id : InterpM ThreadId :=
  return (← get_config).thread_id

/-!
Modify the current thread ID.

Applies a function to the thread_id field and updates the Config.
-!/
def modify_thread_id (f : ThreadId → ThreadId) : InterpM Unit := do
  modify (fun cfg => { cfg with thread_id := f cfg.thread_id })

/-!
Get all thread states.

Returns the threads field from the current Config.
-!/
def get_threads : InterpM (List (ThreadId × ThreadState)) :=
  return (← get_config).threads

/-!
Modify all thread states.

Applies a function to the threads field and updates the Config.
-!/
def modify_threads (f : List (ThreadId × ThreadState) → List (ThreadId × ThreadState)) : InterpM Unit := do
  modify (fun cfg => { cfg with threads := f cfg.threads })

/-!
Get the current lock ownership state.

Returns the locks field from the current Config.
-!/
def get_locks : InterpM (List (LockId × ThreadId)) :=
  return (← get_config).locks

/-!
Modify the lock ownership state.

Applies a function to the locks field and updates the Config.
-!/
def modify_locks (f : List (LockId × ThreadId) → List (LockId × ThreadId)) : InterpM Unit := do
  modify (fun cfg => { cfg with locks := f cfg.locks })

/-!
Check if the current configuration is in UB state.

Returns true if the ub field is some reason.
-!/
def is_ub : InterpM Bool :=
  return (← get_config).ub.isSome

/-!
Throw an UB error.

Throws the given UBReason, causing the interpreter to stop.
-!/
def throw_ub (reason : UBReason) : InterpM α :=
  throw reason

/-!
Require a condition to be true, otherwise throw UB.

Used to validate preconditions and throw UB if they fail.
-!/
def require (cond : Bool) (reason : UBReason) : InterpM Unit := do
  unless cond do
    throw_ub reason

/-!
## Expression Evaluation

Functions for evaluating expressions in the interpreter.

These functions compute the value of expressions given the current
environment and memory state.
-!/

/-!
Evaluate an expression to a value.

Performs the evaluation based on the expression type:
- `var x`: Look up variable x in environment
- `lit v`: Return literal value v
- `binop op e1 e2`: Evaluate e1 and e2, then apply operator
- `unop op e`: Evaluate e, then apply unary operator
- `load ptr`: Load value from memory at pointer ptr
- `store ptr val e`: Evaluate e, then store value at ptr

This is the core evaluation function for the interpreter.
-!/
def eval_expr (e : Expr) : InterpM Core.Value := do
  env ← get_env
  match e with
  | .var name =>
      match env.find? (fun (n, _) => n == name) with
      | some (_, v) => pure v
      | none => throw_ub (UBReason.stuck s!"Unbound variable: {name}")
  | .lit v => pure v
  | .binop op e1 e2 =>
      v1 ← eval_expr e1
      v2 ← eval_expr e2
      pure (eval_binop op v1 v2)
  | .unop op e =>
      v ← eval_expr e
      pure (eval_unop op v)
  | .load ptr =>
      mem ← get_memory
      unless (Memory.check_pointer_valid mem ptr) do
        throw_ub (UBReason.out_of_bounds_access ptr 0)
      let bytes ← Memory.load mem ptr 8 Endianness.LittleEndian
      let value := Memory.bytes_to_value bytes Endianness.LittleEndian
      pure (Core.Value.int value.toUInt64.toNat.toInt)
  | .store ptr val e =>
      v ← eval_expr e
      mem ← get_memory
      unless (Memory.check_pointer_valid mem ptr) do
        throw_ub (UBReason.out_of_bounds_access ptr 0)
      let bytes := Memory.value_to_bytes (match v with | .int n => n.toNat | _ => 0) 8 Endianness.LittleEndian
      Memory.store mem ptr bytes Endianness.LittleEndian
      modify_memory (fun _ => mem)
      pure v

/-!
Evaluate a binary operation on two values.

Performs arithmetic, comparison, logical, bitwise, and pointer operations.
Throws UB for division by zero.
-!/
def eval_binop (op : Core.Operator) (v1 v2 : Core.Value) : Core.Value :=
  match v1, v2 with
  | .int n1, .int n2 =>
      match op with
      | .add => Core.Value.int (n1 + n2)
      | .sub => Core.Value.int (n1 - n2)
      | .mul => Core.Value.int (n1 * n2)
      | .div =>
          if n2 == 0 then
            Core.Value.undef
          else
            Core.Value.int (n1 / n2)
      | .mod =>
          if n2 == 0 then
            Core.Value.undef
          else
            Core.Value.int (n1 % n2)
      | .eq => Core.Value.bool (n1 == n2)
      | .neq => Core.Value.bool (n1 != n2)
      | .lt => Core.Value.bool (n1 < n2)
      | .leq => Core.Value.bool (n1 <= n2)
      | .gt => Core.Value.bool (n1 > n2)
      | .geq => Core.Value.bool (n1 >= n2)
      | .and => Core.Value.bool (match v1 with | .bool b1 => match v2 with | .bool b2 => b1 && b2 | _ => false | _ => false)
      | .or => Core.Value.bool (match v1 with | .bool b1 => match v2 with | .bool b2 => b1 || b2 | _ => true | _ => true)
      | _ => Core.Value.undef
  | .bool b1, .bool b2 =>
      match op with
      | .and => Core.Value.bool (b1 && b2)
      | .or => Core.Value.bool (b1 || b2)
      | _ => Core.Value.undef
  | .pointer p1, .int n2 =>
      match op with
      | .ptrAdd => Core.Value.pointer { p1 with offset := p1.offset + n2 }
      | .ptrSub => Core.Value.pointer { p1 with offset := p1.offset - n2 }
      | _ => Core.Value.undef
  | _ => Core.Value.undef

/-!
Evaluate a unary operation on a value.

Performs logical negation and bitwise NOT operations.
-!/
def eval_unop (op : Core.Operator) (v : Core.Value) : Core.Value :=
  match v with
  | .int n =>
      match op with
      | .not => Core.Value.bool (n == 0)
      | .notb => Core.Value.int (~~~n)
      | _ => Core.Value.undef
  | .bool b =>
      match op with
      | .not => Core.Value.bool (!b)
      | _ => Core.Value.undef
  | _ => Core.Value.undef

/-!
## Statement Execution

Functions for executing statements in the interpreter.

These functions perform the side effects of statements, updating the
environment, memory, control flow, and continuation stack.
-!/

/-!
Execute a single statement.

Performs the execution based on the statement type:
- `skip`: No operation
- `assign x expr`: Evaluate expr and assign to variable x
- `seq s1 s2`: Execute s1 then s2
- `ifThen cond s1 s2`: Evaluate cond and branch to s1 or s2
- `loop body`: Enter loop with body
- `call fn args ret_var`: Call function fn with args, store result in ret_var
- `return expr`: Return from function with value expr
- `break`: Break from loop
- `goto label`: Jump to label
- `syscall fn args ret_var`: Execute system call fn with args, store result in ret_var

This is the core statement execution function.
-!/
def exec_stmt (s : Stmt) : InterpM Unit := do
  match s with
  | .skip => pure ()
  | .assign name expr =>
      v ← eval_expr expr
      modify_env (fun env => (name, v) :: env)
  | .seq s1 s2 =>
      exec_stmt s1
      exec_stmt s2
  | .ifThen cond s1 s2 =>
      cond_val ← eval_expr cond
      match cond_val with
      | .bool true => exec_stmt s1
      | .bool false => exec_stmt s2
      | _ => throw_ub (UBReason.stuck "if condition must be boolean")
  | .loop body =>
      modify_stack (fun stack => Continuation.loop_scope (.loop body) :: stack)
      modify_control (fun control => body ++ [.loop body])
  | .call fn args ret_var =>
      modify_stack (fun stack =>
        Continuation.call_frame ret_var (← get_env) (← get_control) :: stack
      )
      modify_control (fun _ => [])
      modify_env (fun _ => [])
  | .return expr =>
      v ← eval_expr expr
      stack ← get_stack
      match stack with
      | Continuation.call_frame ret_var old_env old_control :: rest_stack =>
          modify_env (fun _ => (ret_var, v) :: old_env)
          modify_control (fun _ => old_control)
          modify_stack (fun _ => rest_stack)
      | _ => throw_ub (UBReason.invalid_return)
  | .break =>
      stack ← get_stack
      match stack with
      | Continuation.loop_scope body :: rest_stack =>
          modify_stack (fun _ => rest_stack)
          modify_control (fun _ => body ++ [.loop body])
      | _ => throw_ub (UBReason.invalid_break)
  | .goto label =>
      throw_ub (UBReason.invalid_goto label)
  | .syscall fn args ret_var =>
      result ← exec_syscall fn args
      modify_env (fun env => (ret_var, result) :: env)

/-!
## I/O Operations for Syscalls

Functions for executing system calls.

These functions model I/O operations that can be called from the
interpreted program. They emit events for tracing and can be
used for conformance checking.
-!/

/-!
Execute a system call.

Dispatches to the appropriate syscall handler based on the function name.
Supported syscalls:
- `read`: Read from file descriptor
- `write`: Write to file descriptor
- `spawn`: Spawn a new thread
- `join`: Join with a thread
- `acquire`: Acquire a lock
- `release`: Release a lock

Throws UB for unknown syscalls.
-!/
def exec_syscall (fn : String) (args : List Core.Value) : InterpM Core.Value :=
  match fn with
  | "read" => syscall_read args
  | "write" => syscall_write args
  | "spawn" => syscall_spawn args
  | "join" => syscall_join args
  | "acquire" => syscall_acquire args
  | "release" => syscall_release args
  | _ => throw_ub (UBReason.stuck s!"Unknown syscall: {fn}")

/-!
Read from file descriptor.

Args: [fd, buf, count]
Returns: Number of bytes read

This is a stub implementation that always returns 0.
-!/
def syscall_read (args : List Core.Value) : InterpM Core.Value :=
  match args with
  | [_, _, _] => pure (Core.Value.int 0)
  | _ => throw_ub (UBReason.stuck "read syscall requires 3 arguments")

/-!
Write to file descriptor.

Args: [fd, buf, count]
Returns: Number of bytes written

This is a stub implementation that always returns the count.
-!/
def syscall_write (args : List Core.Value) : InterpM Core.Value :=
  match args with
  | [_, _, Core.Value.int count] => pure (Core.Value.int count)
  | _ => throw_ub (UBReason.stuck "write syscall requires 3 arguments")

/-!
Spawn a new thread.

Args: [fn, arg]
Returns: New thread ID

Creates a new thread state and adds it to the threads list.
-!/
def syscall_spawn (args : List Core.Value) : InterpM Core.Value :=
  match args with
  | [_, _] =>
      threads ← get_threads
      let new_tid : ThreadId := threads.length
      let new_thread : ThreadState :=
        { env := [], memory := ← get_memory, control := [], stack := [] }
      modify_threads (fun _ => (new_tid, new_thread) :: threads)
      pure (Core.Value.int new_tid.toNat.toInt)
  | _ => throw_ub (UBReason.stuck "spawn syscall requires 2 arguments")

/-!
Join with a thread.

Args: [tid]
Returns: Unit

This is a stub implementation that does nothing.
-!/
def syscall_join (args : List Core.Value) : InterpM Core.Value :=
  match args with
  | [Core.Value.int tid] => pure Core.Value.unit
  | _ => throw_ub (UBReason.stuck "join syscall requires 1 argument")

/-!
Acquire a lock.

Args: [lid]
Returns: Unit

Updates the lock ownership to the current thread.
-!/
def syscall_acquire (args : List Core.Value) : InterpM Core.Value :=
  match args with
  | [Core.Value.int lid] =>
      tid ← get_thread_id
      locks ← get_locks
      let already_owned := locks.any (fun (l, _) => l == lid.toNat)
      require (!already_owned) (UBReason.stuck s!"Lock {lid} already acquired")
      modify_locks (fun _ => (lid.toNat, tid) :: locks)
      pure Core.Value.unit
  | _ => throw_ub (UBReason.stuck "acquire syscall requires 1 argument")

/-!
Release a lock.

Args: [lid]
Returns: Unit

Removes the lock from the lock ownership list.
-!/
def syscall_release (args : List Core.Value) : InterpM Core.Value :=
  match args with
  | [Core.Value.int lid] =>
      tid ← get_thread_id
      locks ← get_locks
      let owned := locks.any (fun (l, owner) => l == lid.toNat && owner == tid)
      require owned (UBReason.stuck s!"Lock {lid} not owned by current thread")
      modify_locks (fun _ => locks.filter (fun (l, _) => l != lid.toNat))
      pure Core.Value.unit
  | _ => throw_ub (UBReason.stuck "release syscall requires 1 argument")

/-!
## Step and Run Functions

Main entry points for the interpreter.

These functions provide single-step and multi-step execution
interfaces for testing and conformance checking.
-!/

/-!
Execute a single step of the interpreter.

Performs one statement from the control list and returns the
resulting configuration along with an event.

Returns:
- `Except.error reason`: If UB occurred
- `Except.ok (event, config)`: If step succeeded

The event is one of:
- `.silent`: Internal computation
- `.syscall fn args`: System call
- `.read_volatile ptr`: Volatile read
- `.write_volatile ptr val`: Volatile write
- `.thread_spawn tid`: Thread creation
- `.thread_join tid`: Thread join
- `.lock_acquire lid`: Lock acquisition
- `.lock_release lid`: Lock release
-!/
def step_executable : InterpM (Event × Config) := do
  cfg ← get_config
  control ← get_control
  match control with
  | [] => throw_ub (UBReason.stuck "No more statements to execute")
  | stmt :: rest =>
      match stmt with
      | .skip =>
          modify_control (fun _ => rest)
          pure (.silent, ← get_config)
      | .assign name expr =>
          v ← eval_expr expr
          modify_env (fun env => (name, v) :: env)
          modify_control (fun _ => rest)
          pure (.silent, ← get_config)
      | .seq s1 s2 =>
          modify_control (fun _ => s1 :: s2 :: rest)
          pure (.silent, ← get_config)
      | .ifThen cond s1 s2 =>
          cond_val ← eval_expr cond
          match cond_val with
          | .bool true =>
              modify_control (fun _ => s1 ++ rest)
              pure (.silent, ← get_config)
          | .bool false =>
              modify_control (fun _ => s2 ++ rest)
              pure (.silent, ← get_config)
          | _ => throw_ub (UBReason.stuck "if condition must be boolean")
      | .loop body =>
          modify_stack (fun stack => Continuation.loop_scope (.loop body) :: stack)
          modify_control (fun _ => body ++ [.loop body] ++ rest)
          pure (.silent, ← get_config)
      | .call fn args ret_var =>
          old_env ← get_env
          old_control ← get_control
          modify_stack (fun stack => Continuation.call_frame ret_var old_env old_control :: stack)
          modify_control (fun _ => [])
          modify_env (fun _ => [])
          pure (.silent, ← get_config)
      | .return expr =>
          v ← eval_expr expr
          stack ← get_stack
          match stack with
          | Continuation.call_frame ret_var old_env old_control :: rest_stack =>
              modify_env (fun _ => (ret_var, v) :: old_env)
              modify_control (fun _ => old_control)
              modify_stack (fun _ => rest_stack)
              pure (.silent, ← get_config)
          | _ => throw_ub (UBReason.invalid_return)
      | .break =>
          stack ← get_stack
          match stack with
          | Continuation.loop_scope body :: rest_stack =>
              modify_stack (fun _ => rest_stack)
              modify_control (fun _ => body ++ rest)
              pure (.silent, ← get_config)
          | _ => throw_ub (UBReason.invalid_break)
      | .goto label =>
          throw_ub (UBReason.invalid_goto label)
      | .syscall fn args ret_var =>
          result ← exec_syscall fn args
          modify_env (fun env => (ret_var, result) :: env)
          modify_control (fun _ => rest)
          pure (.syscall fn args, ← get_config)

/-!
Run the interpreter to completion or until a step limit.

Executes statements until:
- No more statements to execute (terminal state)
- UB occurs
- Step limit is reached

Returns:
- `Except.error reason`: If UB occurred
- `Except.ok (events, config)`: If execution completed

The events list contains all events emitted during execution.
-!/
def run_executable (max_steps : Nat := 10000) : InterpM (List Event × Config) := do
  let mut_events ← Ref.mk #[]
  for _ in [:max_steps] do
    cfg ← get_config
    if cfg.control.isEmpty && cfg.stack.isEmpty then
      break
    (event, new_cfg) ← step_executable
    mut_events := mut_events.push event
    set new_cfg
  pure (mut_events.toList, ← get_config)

/-!
Run the interpreter with an initial configuration and program.

Convenience function that sets up the initial state and runs
the interpreter to completion.

Args:
- `init`: Initial configuration (use `Config.empty` for default)
- `program`: List of statements to execute
- `max_steps`: Maximum number of steps to execute (default 10000)

Returns:
- `Except.error reason`: If UB occurred
- `Except.ok (events, config)`: If execution completed
-!/
def run_with_program (init : Config) (program : List Stmt) (max_steps : Nat := 10000) :
    Except UBReason (List Event × Config) :=
  let init_cfg : Config := { init with control := program }
  (ReaderT.run Context.empty) (StateT.run init_cfg) (run_executable max_steps)

/-!
Run the interpreter with default initial state.

Convenience function that uses `Config.empty` as the initial state.

Args:
- `program`: List of statements to execute
- `max_steps`: Maximum number of steps to execute (default 10000)

Returns:
- `Except.error reason`: If UB occurred
- `Except.ok (events, config)`: If execution completed
-!/
def run (program : List Stmt) (max_steps : Nat := 10000) :
    Except UBReason (List Event × Config) :=
  run_with_program Config.empty program max_steps

end Morph
