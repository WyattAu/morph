/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.MonadicEffect

/-!
# Monadic Effect Specification

Effect handler semantics for the Morph language.
Defines effect operations, handlers, and effectful computations.

## Overview

This module formalizes algebraic effects and handlers:
- **EffectOp:** Primitive effect operation kinds
- **Effect:** An effect identified by name and operations
- **HandlerAction:** Actions a handler can take
- **Handler:** An effect handler with dispatch function
- **EffectfulComputation:** A computation that may perform effects
- **EffectSet:** Set of effect names a computation may perform
- **HandlerStack:** Stack of installed handlers for effect composition

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Effect operation | `EffectOp` | Done |
| Effect | `Effect` | Done |
| Handler action | `HandlerAction` | Done |
| Handler | `Handler` | Done |
| Effectful computation | `EffectfulComputation` | Done |
| Effect set | `EffectSet` | Done |
| Handler stack | `HandlerStack` | Done |
-/

/-- Primitive effect operation kinds -/
inductive EffectOp where
  | read (name : String) : EffectOp
  | write (name : String) (value : String) : EffectOp
  | ask (name : String) : EffectOp
  | raise (name : String) : EffectOp
  deriving Repr, BEq, Hashable

/-- An effect identified by name and operation signature -/
structure Effect where
  name : String
  ops : List EffectOp
  deriving Repr, BEq

/-- A handler maps effect operations to handler actions -/
inductive HandlerAction where
  | pure (val : String) : HandlerAction
  | resume (val : String) : HandlerAction
  | abort (msg : String) : HandlerAction
  deriving Repr, BEq

/-- An effect handler with a name and a dispatch function -/
structure Handler where
  name : String
  handles : List String
  deriving Repr, BEq

/-- An effectful computation that may perform effects or return a value -/
inductive EffectfulComputation where
  | pure (val : String) : EffectfulComputation
  | perform (op : EffectOp) : EffectfulComputation
  | fail (msg : String) : EffectfulComputation
  | seq (first : EffectfulComputation) (cont : String -> EffectfulComputation) : EffectfulComputation

/-- Set of effect names that a computation may perform -/
abbrev EffectSet := List String

/-- Stack of installed handlers for layered effect handling -/
abbrev HandlerStack := List Handler

/-- Extract the effect name from an operation -/
def EffectOp.effectName : EffectOp -> String
  | .read n => n
  | .write n _ => n
  | .ask n => n
  | .raise n => n

/-- Check if a handler can handle a given effect operation -/
def Handler.canHandle (h : Handler) (op : EffectOp) : Bool :=
  op.effectName ∈ h.handles

/-- Collect all effect names from a computation (shallow, one level) -/
def EffectfulComputation.effectNames : EffectfulComputation -> EffectSet
  | EffectfulComputation.pure _ => []
  | EffectfulComputation.perform op => [op.effectName]
  | EffectfulComputation.fail _ => []
  | EffectfulComputation.seq c _ => c.effectNames

/-- Check if an effect name is in a set -/
def EffectSet.contains (s : EffectSet) (name : String) : Bool :=
  name ∈ s

/-- Push a handler onto the handler stack -/
def HandlerStack.push (stack : HandlerStack) (h : Handler) : HandlerStack :=
  h :: stack

/-- Find the first handler that can handle an effect operation -/
def HandlerStack.findHandler (stack : HandlerStack) (op : EffectOp) : Option Handler :=
  stack.find? (fun h => h.canHandle op)

end Morph.Specs.MonadicEffect
