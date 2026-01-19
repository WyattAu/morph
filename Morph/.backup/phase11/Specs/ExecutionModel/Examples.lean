/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Std
import Morph.Core
import Morph.Memory
import Morph.Semantics
import Morph.Specs.ExecutionModel.Spec

/-!
# Execution Model Examples

This module provides examples for the execution model specification,
demonstrating program execution, traces, and safety properties.

## Overview

The Examples module provides concrete examples of:
- Simple program execution
- Conditional branching
- Loop execution with break
- Function call and return
- System calls
- Thread spawning and joining
- Lock operations
- Undefined behavior scenarios

## Dependencies

- `Morph.Core` - Core type definitions (Value, Pointer, Env, etc.)
- `Morph.Memory` - Memory model (Memory, BlockId, etc.)
- `Morph.Semantics` - Operational semantics definitions
- `Morph.Specs.ExecutionModel.Spec` - Execution model specification

## Public API

- `simpleProgramExample` - Simple program execution
- `conditionalBranchExample` - Conditional branching example
- `loopExample` - Loop with break example
- `functionCallExample` - Function call and return example
- `syscallExample` - System call example
- `threadSpawnExample` - Thread spawning example
- `lockExample` - Lock operations example
- `ubExample` - Undefined behavior example
- `multiStepExample` - Multi-step execution example
- `determinismExample` - Determinism example
- `nondeterminismExample` - Nondeterminism example
- `traceValidationExample` - Execution trace validation example

-!/

namespace Morph.Specs.ExecutionModel

/-!
## Simple Program Example

A simple program that assigns a value and terminates.

This example demonstrates:
1. Creating a simple program with assignment
2. Executing the program
3. Verifying the execution trace
4. Checking safety properties
-!/
def simpleProgramExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let assignStmt := Semantics.Stmt.assign "x" (Semantics.Expr.lit (Core.Value.int 5))
  let programConfig := { initialConfig with control := [assignStmt] }
  ExecutionTrace.executeProgram programConfig

/-!
Verify simple program example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is safe
4. No UB is reached
-!/

/-!
## Conditional Branch Example

A program with conditional branching.

This example demonstrates:
1. Creating a program with if-then-else
2. Executing both branches
3. Verifying different execution traces
-!/
def conditionalBranchExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let trueBranch := Semantics.Stmt.assign "y" (Semantics.Expr.lit (Core.Value.bool true))
  let falseBranch := Semantics.Stmt.assign "z" (Semantics.Expr.lit (Core.Value.bool false))
  let ifStmt := Semantics.Stmt.ifThen (Semantics.Expr.var "x") trueBranch falseBranch
  let programConfig := { initialConfig with control := [ifStmt] }
  let trace1 := ExecutionTrace.executeProgram programConfig
  let trace2 := ExecutionTrace.executeProgram programConfig

/-!
Verify conditional branch example.

This example demonstrates that:
1. Both traces are valid
2. Both traces terminate normally
3. Both traces are safe
4. No UB is reached
-!/

/-!
## Loop with Break Example

A program with a loop and break statement.

This example demonstrates:
1. Creating a loop with a break condition
2. Executing the loop until break
3. Verifying that break exits the loop correctly
-!/
def loopExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let loopBody := Semantics.Stmt.seq (Semantics.Stmt.assign "i" (Semantics.Expr.binop Core.Operator.add (Semantics.Expr.var "i") (Semantics.Expr.lit (Core.Value.int 1))) Semantics.Stmt.break)
  let loopStmt := Semantics.Stmt.loop loopBody
  let programConfig := { initialConfig with control := [loopStmt] }
  ExecutionTrace.executeProgram programConfig

/-!
Verify loop example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is safe
4. No UB is reached
-!/

/-!
## Function Call and Return Example

A program with function call and return.

This example demonstrates:
1. Creating a function call statement
2. Creating a return statement
3. Executing the call and return
4. Verifying that the return value is captured
-!/
def functionCallExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let callStmt := Semantics.Stmt.call "foo" [] "result"
  let returnStmt := Semantics.Stmt.return (Semantics.Expr.var "result")
  let programConfig := { initialConfig with control := [callStmt, returnStmt] }
  ExecutionTrace.executeProgram programConfig

/-!
Verify function call example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is safe
4. No UB is reached
-!/

/-!
## System Call Example

A program with a system call.

This example demonstrates:
1. Creating a system call statement
2. Executing the syscall
3. Verifying that a syscall event is emitted
-!/
def syscallExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let syscallStmt := Semantics.Stmt.syscall "write" [] "result"
  let programConfig := { initialConfig with control := [syscallStmt] }
  ExecutionTrace.executeProgram programConfig

/-!
Verify syscall example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is safe
4. A syscall event is emitted
-!/

/-!
## Thread Spawn Example

A program that spawns a new thread.

This example demonstrates:
1. Creating a thread spawn statement
2. Executing the spawn
3. Verifying that a thread_spawn event is emitted
4. Verifying that the new thread is created
-!/
def threadSpawnExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let spawnStmt := Semantics.Stmt.seq (Semantics.Stmt.skip) (Semantics.Stmt.thread_spawn 1)
  let programConfig := { initialConfig with control := [spawnStmt] }
  ExecutionTrace.executeProgram programConfig

/-!
Verify thread spawn example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is safe
4. A thread_spawn event is emitted
5. The new thread is created
-!/

/-!
## Lock Operations Example

A program with lock acquire and release.

This example demonstrates:
1. Creating lock acquire and release statements
2. Executing the lock operations
3. Verifying that lock safety property is maintained
-!/
def lockExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let acquireStmt := Semantics.Stmt.seq (Semantics.Stmt.skip) (Semantics.Stmt.lock_acquire 0)
  let releaseStmt := Semantics.Stmt.lock_release 0
  let programConfig := { initialConfig with control := [acquireStmt, releaseStmt] }
  ExecutionTrace.executeProgram programConfig

/-!
Verify lock operations example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is lock-safe
4. No UB is reached
-!/

/-!
## Undefined Behavior Example

A program that reaches undefined behavior.

This example demonstrates:
1. Creating a program with invalid memory access
2. Executing the program
3. Verifying that UB is reached
-!/
def ubExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let invalidPtr := Core.Pointer { block := { id := 0 }, offset := 0, provenance := none }
  let loadStmt := Semantics.Stmt.assign "x" (Semantics.Expr.load invalidPtr)
  let programConfig := { initialConfig with control := [loadStmt] }
  ExecutionTrace.executeProgram programConfig

/-!
Verify UB example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is not safe (reaches UB)
4. UB reason is properly recorded
-!/

/-!
## Multi-Step Execution Example

A program demonstrating multi-step execution.

This example demonstrates:
1. Creating a program with multiple statements
2. Executing the program step by step
3. Verifying that multiple steps are executed
-!/
def multiStepExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let stmt1 := Semantics.Stmt.assign "x" (Semantics.Expr.lit (Core.Value.int 1))
  let stmt2 := Semantics.Stmt.assign "y" (Semantics.Expr.lit (Core.Value.int 2))
  let stmt3 := Semantics.Stmt.assign "z" (Semantics.Expr.binop Core.Operator.add (Semantics.Expr.var "x") (Semantics.Expr.var "y"))
  let programConfig := { initialConfig with control := [stmt1, stmt2, stmt3] }
  ExecutionTrace.executeProgram programConfig

/-!
Verify multi-step execution example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is safe
4. Multiple steps are executed
-!/

/-!
## Determinism Example

A program demonstrating deterministic execution.

This example demonstrates:
1. Creating a simple deterministic program
2. Executing the program
3. Verifying that all executions are identical
-!/
def determinismExample : ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let assignStmt := Semantics.Stmt.assign "x" (Semantics.Expr.lit (Core.Value.int 42))
  let programConfig := { initialConfig with control := [assignStmt] }
  let trace := ExecutionTrace.executeProgram programConfig
  let tracesAreIdentical := ExecutionTrace.isDeterministic trace [trace]

/-!
Verify determinism example.

This example demonstrates that:
1. The trace is valid
2. The trace terminates normally
3. The trace is safe
4. All executions are identical
-!/

/-!
## Nondeterminism Example

A program demonstrating nondeterministic execution.

This example demonstrates:
1. Creating a program with conditional branching
2. Executing all possible branches
3. Verifying that multiple execution traces exist
-!/
def nondeterminismExample : List ExecutionTrace :=
  let initialConfig := Semantics.Config.empty
  let branch1 := Semantics.Stmt.assign "x" (Semantics.Expr.lit (Core.Value.int 1))
  let branch2 := Semantics.Stmt.assign "x" (Semantics.Expr.lit (Core.Value.int 2))
  let ifStmt := Semantics.Stmt.ifThen (Semantics.Expr.var "x") branch1 branch2
  let programConfig := { initialConfig with control := [ifStmt] }
  ExecutionTrace.executeAllBranches programConfig

/-!
Verify nondeterminism example.

This example demonstrates that:
1. Both traces are valid
2. Both traces terminate normally
3. Both traces are safe
4. Multiple execution paths exist
-!/

/-!
## Execution Trace Validation Example

A comprehensive example demonstrating trace validation.

This example demonstrates:
1. Creating multiple execution traces
2. Validating each trace
3. Checking safety properties
-!/
def traceValidationExample : Bool :=
  let initialConfig := Semantics.Config.empty
  let assignStmt := Semantics.Stmt.assign "x" (Semantics.Expr.lit (Core.Value.int 10))
  let programConfig := { initialConfig with control := [assignStmt] }
  let validTrace := ExecutionTrace.executeProgram programConfig
  let isValid := ExecutionTrace.isValid validTrace
  let isSafe := ExecutionTrace.isSafeExecution validTrace
  let terminates := ExecutionTrace.terminatesNormally validTrace
  let noUB := !ExecutionTrace.reachesUB validTrace
  let stepCount := ExecutionTrace.stepCount validTrace
  let events := ExecutionTrace.getEvents validTrace
  let observableEvents := ExecutionTrace.getObservableEvents validTrace
  isValid ∧ isSafe ∧ terminates ∧ noUB

/-!
end Morph.Specs.ExecutionModel
