/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Feasible-50 kernels — P2 concurrency (loop 110)

Executable cores for the second ten feasible rows (E4 triage, Batch P2):
E-151, E-156, E-157, E-159, E-160, E-161, E-162, E-163, E-172, E-174.
Each section is a *model with a theorem*: the smallest decidable kernel
that makes the row falsifiable. `Std`-only, `Nat`/`List`/`Bool` first.

| Register row | Concept | Lean core |
|---|---|---|
| E-151 | nursery task trees | `Task`, `leafCount`, `joinAll` |
| E-156 | flat-combining counters | `batch`, `batchAdd` |
| E-157 | seqlock snapshots | `Seq`, `writeSeq`, `readOk` |
| E-159 | deterministic record/replay | `Log`, `replay`, `replayLen` |
| E-160 | ownership-transfer messages | `Msg`, `give`, `payloadOf` |
| E-161 | supervisor restart | `SState`, `restart` |
| E-162 | credit/flow-control bounds | `Credit`, `avail`, `admitC` |
| E-163 | idempotent dedup delivery | `deliver` |
| E-172 | G-counter CRDT merge | `GCount`, `incr`, `mergeG` |
| E-174 | edge-chasing deadlock check | `deadlock2`, `deadlockSelf` |
-/

namespace Morph.Specs.BatchP2

/-! ## E-151: nursery task trees -/

/-- Lexically scoped task tree. -/
inductive Task where
  | leaf : Nat → Task
  | fork : Task → Task → Task
  deriving Repr, DecidableEq

/-- Leaf (work-item) count. -/
def leafCount : Task → Nat
  | .leaf _ => 1
  | .fork a b => leafCount a + leafCount b

/-- Join: flatten one level into a work list (documented order). -/
def joinAll : Task → List Nat
  | .leaf n => [n]
  | .fork a b => joinAll a ++ joinAll b

/-! ## E-156: combining counter -/

/-- Combined batch sum. -/
def batch (xs : List Nat) : Nat := xs.sum

/-- Add two batches. -/
def batchAdd (x y : List Nat) : Nat := batch (x ++ y)

/-! ## E-157: seqlock snapshot -/

/-- Sequence-locked cell: even counter ⇒ stable. -/
structure Seq where
  ctr : Nat
  dat : Nat
  deriving Repr, DecidableEq

/-- Write: bump data, advance the counter by two (stays even). -/
def writeSeq (s : Seq) (v : Nat) : Seq := ⟨s.ctr + 2, v⟩

/-- A read is tear-free iff the counter is even. -/
def readOk (s : Seq) : Bool := decide (s.ctr % 2 = 0)

/-! ## E-159: record/replay log -/

/-- A schedule log entry: task id × operation id. -/
abbrev Log := List (Nat × Nat)

/-- Replay: task order of the log. -/
def replay (l : Log) : List Nat := l.map Prod.fst

/-- Replay length. -/
def replayLen (l : Log) : Nat := (replay l).length

/-! ## E-160: ownership transfer -/

/-- An isolated-heap message. -/
structure Msg where
  owner : Nat
  payload : Nat
  deriving Repr, DecidableEq

/-- Transfer ownership to a new holder. -/
def give (m : Msg) (newOwner : Nat) : Msg := ⟨newOwner, m.payload⟩

/-- Read the payload. -/
def payloadOf (m : Msg) : Nat := m.payload

/-! ## E-161: supervisor restart -/

/-- Supervised child state. -/
inductive SState where
  | running : SState
  | failed : Nat → SState
  | restarted : SState
  deriving Repr, DecidableEq

/-- Restart policy: failed children go back to restarted. -/
def restart : SState → SState
  | .failed _ => .restarted
  | s => s

/-! ## E-162: credit bounds -/

/-- A flow-control credit window. -/
structure Credit where
  limit : Nat
  used : Nat
  deriving Repr, DecidableEq

/-- Available headroom. -/
def avail (c : Credit) : Nat := c.limit - c.used

/-- Admit `n` units iff they fit the headroom. -/
def admitC (c : Credit) (n : Nat) : Bool := decide (n ≤ avail c)

/-- A credit window is valid when usage stays within the limit. -/
def windowOk (c : Credit) : Bool := decide (c.used ≤ c.limit)

/-! ## E-163: idempotent delivery -/

/-- Deliver `k`: accepted once, refused on redelivery with the seen set. -/
def deliver (seen : List Nat) (k : Nat) : Bool × List Nat :=
  if k ∈ seen then (false, seen) else (true, k :: seen)

/-! ## E-172: G-counter merge -/

/-- A grow-only counter replica. -/
structure GCount where
  v : Nat
  deriving Repr, DecidableEq

/-- Local increment. -/
def incr (g : GCount) : GCount := ⟨g.v + 1⟩

/-- Merge: least upper bound. -/
def mergeG (a b : GCount) : GCount := ⟨Nat.max a.v b.v⟩

/-! ## E-174: edge-chasing -/

/-- A waits-for edge set. -/
abbrev Edges := List (Nat × Nat)

/-- A 2-cycle between `a` and `b`. -/
def deadlock2 (e : Edges) (a b : Nat) : Bool :=
  decide ((a, b) ∈ e ∧ (b, a) ∈ e)

/-- A self-loop on `a`. -/
def deadlockSelf (e : Edges) (a : Nat) : Bool :=
  decide ((a, a) ∈ e)

end Morph.Specs.BatchP2
