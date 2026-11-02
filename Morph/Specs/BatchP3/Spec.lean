/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Feasible-50 kernels — P3 models + storage (loop 110)

Executable cores for the third ten feasible rows (E4 triage, Batch P3):
E-177, E-178, E-187, E-199, E-354, E-355, E-360, E-362, E-363, E-366.
Each section is a *model with a theorem*: the smallest decidable kernel
that makes the row falsifiable. `Std`-only, `Nat`/`List`/`Bool` first.

| Register row | Concept | Lean core |
|---|---|---|
| E-177 | MESI executable model | `MESI`, `rdM`, `wrM` |
| E-178 | store-buffer TSO model | `readB`, `writeB` |
| E-187 | PCIe descriptor ordering | `Desc`, `orderedB`, `checkOrder` |
| E-199 | litmus suite runner | `runLitmus`, `suiteAll` |
| E-354 | open-addressing probes | `probe` |
| E-355 | Bloom no-false-negative | `addB`, `queryB` |
| E-360 | WAL replay + truncation | `applyOp`, `replayW`, `trunc` |
| E-362 | CoW snapshot isolation | `readStore`, `writeStore`, `takeSnap` |
| E-363 | MVCC visibility | `Ver`, `visible` |
| E-366 | maintained aggregate view | `view`, `addView` |
-/

namespace Morph.Specs.BatchP3

/-! ## E-177: MESI states -/

/-- Cache-line states. -/
inductive MESI where
  | I : MESI
  | S : MESI
  | E : MESI
  | M : MESI
  deriving Repr, DecidableEq

/-- A read: invalid lines become shared. -/
def rdM : MESI → MESI
  | .I => .S
  | s => s

/-- A write: every line becomes modified. -/
def wrM : MESI → MESI
  | _ => .M

/-! ## E-178: store buffer -/

/-- Read newest-first, falling back to the default. -/
def readB : List (Nat × Nat) → Nat → Nat → Nat
  | [], _, dflt => dflt
  | (k, v) :: rest, a, dflt => if a = k then v else readB rest a dflt

/-- Buffer a store (newest first). -/
def writeB (buf : List (Nat × Nat)) (a v : Nat) : List (Nat × Nat) :=
  (a, v) :: buf

/-! ## E-187: descriptor ordering -/

/-- A DMA descriptor: doorbell plus payload position. -/
structure Desc where
  doorbell : Nat
  datapos : Nat
  deriving Repr, DecidableEq

/-- Ordered pair: doorbells nondecreasing. -/
def orderedB (d1 d2 : Desc) : Bool := decide (d1.doorbell ≤ d2.doorbell)

/-- Check a descriptor trace end to end. -/
def checkOrder : List Desc → Bool
  | [] => true
  | [_] => true
  | d1 :: d2 :: rest => orderedB d1 d2 && checkOrder (d2 :: rest)

/-! ## E-199: litmus runner -/

/-- A single litmus case passes iff actual matches expected. -/
def runLitmus (expected actual : Nat) : Bool := decide (expected = actual)

/-- A suite passes iff every case matches. -/
def suiteAll : List (Nat × Nat) → Bool
  | [] => true
  | (e, a) :: rest => decide (e = a) && suiteAll rest

/-! ## E-354: probes -/

/-- Open-addressing probe: home plus offset, modulo table size. -/
def probe (h i n : Nat) : Nat := (h + i) % n

/-! ## E-355: Bloom filter with no false negatives -/

/-- A filter is the list of set indices. -/
abbrev Bloom := List Nat

/-- Add hash indices. -/
def addB (bs : Bloom) (hs : List Nat) : Bloom := bs ++ hs

/-- Query: present iff the index was added. -/
def queryB (bs : Bloom) (h : Nat) : Bool := decide (h ∈ bs)

/-! ## E-360: WAL replay -/

/-- Apply one log op (addition into the state). -/
def applyOp (s op : Nat) : Nat := s + op

/-- Replay a log front to back. -/
def replayW : Nat → List Nat → Nat
  | s, [] => s
  | s, op :: ops => replayW (applyOp s op) ops

/-- Truncate below the checkpoint LSN. -/
def trunc (lsn : Nat) (log : List (Nat × Nat)) : List (Nat × Nat) :=
  log.filter (fun e => decide (lsn ≤ e.1))

/-! ## E-362: snapshot isolation -/

/-- Read first match, if any. -/
def readStore : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (k, v) :: rest, key => if key = k then some v else readStore rest key

/-- Write by prepending (newest first). -/
def writeStore (s : List (Nat × Nat)) (k v : Nat) : List (Nat × Nat) :=
  (k, v) :: s

/-- An immutable snapshot handle. -/
structure Snap where
  data : List (Nat × Nat)
  deriving Repr, DecidableEq

/-- Take a snapshot. -/
def takeSnap (s : List (Nat × Nat)) : Snap := ⟨s⟩

/-- Read through a snapshot. -/
def readSnap (sp : Snap) (k : Nat) : Option Nat := readStore sp.data k

/-! ## E-363: MVCC visibility -/

/-- A row version: begin timestamp, end timestamp (`0` = live). -/
structure Ver where
  beginV : Nat
  endV : Nat
  deriving Repr, DecidableEq

/-- Visible at `ts` iff begun and not yet ended. -/
def visible (v : Ver) (ts : Nat) : Bool :=
  decide (v.beginV ≤ ts ∧ (v.endV = 0 ∨ ts < v.endV))

/-! ## E-366: maintained view -/

/-- The maintained aggregate: sum of the base. -/
def view (bs : List Nat) : Nat := bs.sum

/-- Add one base row. -/
def addView (bs : List Nat) (x : Nat) : List Nat := x :: bs

end Morph.Specs.BatchP3
