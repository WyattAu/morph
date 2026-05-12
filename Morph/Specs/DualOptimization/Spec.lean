/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Dual Optimization Specification

Optimization theory for the Morph compiler pipeline.
Defines optimization levels, passes, and result metrics.

## Overview

The Morph compiler supports multiple optimization levels (O0–O3) and composable
optimization passes. Each pass records before/after metrics for verification.

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Optimization levels | `OptimizationLevel` | Done |
| Optimization pass | `OptimizationPass` | Done |
| Optimization result | `OptimizationResult` | Done |

## Known Issues

None.
-/

namespace Morph.Specs.DualOptimization

/-- Optimization level for the compiler -/
inductive OptimizationLevel where
  | O0 : OptimizationLevel
  | O1 : OptimizationLevel
  | O2 : OptimizationLevel
  | O3 : OptimizationLevel
  deriving Repr, BEq, Hashable

/-- Numeric value of an optimization level for comparison -/
def OptimizationLevel.toNat (l : OptimizationLevel) : Nat :=
  match l with
  | .O0 => 0
  | .O1 => 1
  | .O2 => 2
  | .O3 => 3

instance : LT OptimizationLevel where
  lt a b := a.toNat < b.toNat

instance : LE OptimizationLevel where
  le a b := a.toNat <= b.toNat

/-- A single optimization pass with metadata -/
structure OptimizationPass where
  name : String
  level : OptimizationLevel
  enabled : Bool
  deriving Repr, BEq

/-- Metrics snapshot before or after an optimization pass -/
structure Metrics where
  instructionCount : Nat
  memoryBytes : Nat
  callDepth : Nat
  deriving Repr, BEq

/-- Result of applying an optimization pass, with before/after metrics -/
structure OptimizationResult where
  pass : OptimizationPass
  before : Metrics
  after : Metrics
  improved : Bool
  deriving Repr, BEq

/-- Compute whether the after-metrics improve over before-metrics -/
def Metrics.improvesOver (after before : Metrics) : Bool :=
  after.instructionCount <= before.instructionCount &&
  after.memoryBytes <= before.memoryBytes

/-- Build an OptimizationResult, auto-computing the `improved` flag -/
def OptimizationResult.create (pass : OptimizationPass) (before after : Metrics) : OptimizationResult :=
  { pass, before, after, improved := after.improvesOver before }

/-- Check if a pass is enabled at a given level -/
def OptimizationPass.isActiveAt (p : OptimizationPass) (l : OptimizationLevel) : Bool :=
  p.enabled && p.level.toNat <= l.toNat

end Morph.Specs.DualOptimization
