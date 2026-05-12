/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

namespace Morph.Specs.Maths

/-!
# Mathematical Foundations Specification

Mathematical foundations used throughout the Morph project.
Defines properties of natural numbers, integer operations,
and rational number structures.

## Overview

This module formalizes mathematical structures:
- **NatProperties:** Properties of natural numbers
- **IntOps:** Integer arithmetic operation signatures
- **Rational:** Rational number representation and operations
- **gcd:** Greatest common divisor
- **coprime:** Coprimality check

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Nat properties | `NatProperties` | Done |
| Int operations | `IntOps` | Done |
| Rational | `Rational` | Done |
| GCD | `gcd` | Done |
-/

/-- Properties of natural numbers -/
structure NatProperties where
  zero : Nat := 0
  one : Nat := 1
  deriving Repr

namespace NatProperties

/-- Zero is not equal to any successor -/
def zero_ne_succ (n : Nat) : 0 ≠ Nat.succ n := (Nat.succ_ne_zero n).symm

end NatProperties

/-- Integer arithmetic operation signatures -/
structure IntOps where
  add : Int -> Int -> Int
  sub : Int -> Int -> Int
  mul : Int -> Int -> Int
  div : Int -> Int -> Int
  mod : Int -> Int -> Int
  neg : Int -> Int
  abs : Int -> Nat

namespace IntOps

/-- Default integer operations using built-in arithmetic -/
def default : IntOps :=
  { add := Int.add
    sub := Int.sub
    mul := Int.mul
    div := (· / ·)
    mod := (· % ·)
    neg := Int.neg
    abs := Int.natAbs }

end IntOps

/-- A rational number as a pair of numerator and denominator -/
structure Rational where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving Repr

namespace Rational

/-- Construct a rational number, ensuring positive denominator -/
def create (num : Int) (den : Nat) : Option Rational :=
  if h : 0 < den then some ⟨num, den, h⟩
  else none

/-- The rational number zero -/
def zero : Rational := ⟨0, 1, by decide⟩

/-- The rational number one -/
def one : Rational := ⟨1, 1, by decide⟩

/-- Add two rational numbers -/
def add (p q : Rational) : Rational :=
  let num := p.num * q.den + q.num * p.den
  let den := p.den * q.den
  ⟨num, den, Nat.mul_pos p.den_pos q.den_pos⟩

/-- Multiply two rational numbers -/
def mul (p q : Rational) : Rational :=
  ⟨p.num * q.num, p.den * q.den, Nat.mul_pos p.den_pos q.den_pos⟩

/-- Negate a rational number -/
def neg (p : Rational) : Rational :=
  ⟨-p.num, p.den, p.den_pos⟩

end Rational

/-- Compute the greatest common divisor of two natural numbers -/
partial def gcd (m n : Nat) : Nat :=
  if n = 0 then m
  else gcd n (m % n)

/-- Check if two natural numbers are coprime -/
def coprime (m n : Nat) : Bool :=
  gcd m n = 1

end Morph.Specs.Maths
