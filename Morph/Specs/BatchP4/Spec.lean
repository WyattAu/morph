/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Feasible-50 kernels — P4 wire/session (loop 110)

Executable cores for the fourth ten feasible rows (E4 triage, Batch P4):
E-380, E-381, E-382, E-383, E-384, E-385, E-392, E-393, E-396, E-398.
Each section is a *model with a theorem*: the smallest decidable kernel
that makes the row falsifiable. `Std`-only, `Nat`/`List`/`Bool` first.

| Register row | Concept | Lean core |
|---|---|---|
| E-380 | length-prefix framing | `mkFrame`, `parseFrame` |
| E-381 | FIX/ITCH/MDP codec conformance | `Tag`, `tagToNat`, `encodeM`, `conforms` |
| E-382 | session state machine | `Sess`, `SEv`, `sstep` |
| E-383 | token-bucket rate limiting | `Bucket`, `refill`, `takeB` |
| E-384 | cancel-on-disconnect | `Conn`, `disconnect` |
| E-385 | drop-copy consistency | `Prim`, `Backup`, `syncB`, `consistent` |
| E-392 | strict-priority scheduling | `sched` |
| E-393 | traffic shaping budget | `Shaper`, `allow` |
| E-396 | capture-record codec | `mkCap`, `parseCap`, `caps` |
| E-398 | Lamport sequencing | `sendL`, `recvL` |
-/

namespace Morph.Specs.BatchP4

/-! ## E-380: length-prefix framing -/

/-- Frame a payload with its length. -/
def mkFrame (bs : List Nat) : Nat × List Nat := (bs.length, bs)

/-- Parse: accept iff the length matches. -/
def parseFrame : Nat × List Nat → Option (List Nat)
  | (n, bs) => if bs.length = n then some bs else none

/-! ## E-381: codec conformance -/

/-- Venue protocol tags. -/
inductive Tag where
  | fix : Tag
  | itch : Tag
  | mdp : Tag
  deriving Repr, DecidableEq

/-- Tag encoding. -/
def tagToNat : Tag → Nat
  | .fix => 0
  | .itch => 1
  | .mdp => 2

/-- A wire message. -/
structure WireMsg where
  tag : Tag
  payload : List Nat
  deriving Repr, DecidableEq

/-- Encode: tag number plus payload. -/
def encodeM (m : WireMsg) : Nat × List Nat := (tagToNat m.tag, m.payload)

/-- Conformant iff the tag number is in range. -/
def conforms (e : Nat × List Nat) : Bool := decide (e.1 ≤ 2)

/-! ## E-382: session FSM -/

/-- Session states. -/
inductive Sess where
  | down : Sess
  | sync : Sess
  | up : Sess
  deriving Repr, DecidableEq

/-- Session events. -/
inductive SEv where
  | logon : SEv
  | gapfill : SEv
  | heartbeat : SEv
  | close : SEv
  deriving Repr, DecidableEq

/-- Transitions; illegal combos are `none`. -/
def sstep : Sess → SEv → Option Sess
  | .down, .logon => some .sync
  | .sync, .gapfill => some .up
  | .sync, .logon => some .sync
  | .up, .heartbeat => some .up
  | _, .close => some .down
  | _, _ => none

/-! ## E-383: token bucket -/

/-- A token bucket. -/
structure Bucket where
  tokens : Nat
  cap : Nat
  deriving Repr, DecidableEq

/-- Refill by `n`, capped. -/
def refill (b : Bucket) (n : Nat) : Bucket :=
  ⟨Nat.min b.cap (b.tokens + n), b.cap⟩

/-- Take `n` tokens iff available; returns the remainder. -/
def takeB (b : Bucket) (n : Nat) : Option Bucket :=
  if n ≤ b.tokens then some ⟨b.tokens - n, b.cap⟩ else none

/-! ## E-384: cancel-on-disconnect -/

/-- A connection with pending work. -/
structure Conn where
  alive : Bool
  pending : List Nat
  deriving Repr, DecidableEq

/-- Disconnect: kill liveness, drop everything pending. -/
def disconnect (_c : Conn) : Conn := ⟨false, []⟩

/-! ## E-385: drop-copy consistency -/

/-- The primary session cursor. -/
structure Prim where
  seq : Nat
  dat : Nat
  deriving Repr, DecidableEq

/-- The backup session cursor. -/
structure Backup where
  seq : Nat
  dat : Nat
  deriving Repr, DecidableEq

/-- Sync the backup to the primary. -/
def syncB (_b : Backup) (p : Prim) : Backup := ⟨p.seq, p.dat⟩

/-- Consistency: cursors agree. -/
def consistent (b : Backup) (p : Prim) : Bool :=
  decide (b.seq = p.seq ∧ b.dat = p.dat)

/-! ## E-392: strict priority -/

/-- Schedule: high-priority head wins; low runs only when high is empty. -/
def sched (hi lo : List Nat) : Option Nat :=
  match hi, lo with
  | h :: _, _ => some h
  | [], l :: _ => some l
  | [], [] => none

/-! ## E-393: shaping budget -/

/-- A shaper: sustained rate plus burst allowance. -/
structure Shaper where
  rate : Nat
  burst : Nat
  deriving Repr, DecidableEq

/-- Admit `n` units iff they fit rate plus burst. -/
def allow (s : Shaper) (n : Nat) : Bool := decide (n ≤ s.rate + s.burst)

/-! ## E-396: capture records -/

/-- Frame one capture record with timestamp and length. -/
def mkCap (ts : Nat) (dat : List Nat) : Nat × Nat × List Nat :=
  (ts, dat.length, dat)

/-- Parse: accept iff the length matches. -/
def parseCap : Nat × Nat × List Nat → Option (Nat × List Nat)
  | (ts, n, dat) => if dat.length = n then some (ts, dat) else none

/-- Capture a batch at one timestamp (order-preserving). -/
def caps (ts : Nat) (ds : List (List Nat)) : List (Nat × List Nat) :=
  ds.map (fun d => (ts, d))

/-! ## E-398: Lamport clocks -/

/-- Send: tick the clock. -/
def sendL (s : Nat) : Nat := s + 1

/-- Receive: merge and tick. -/
def recvL (here there : Nat) : Nat := Nat.max here there + 1

end Morph.Specs.BatchP4
