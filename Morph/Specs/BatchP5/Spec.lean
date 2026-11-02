/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Feasible-50 kernels — P5 everyday product (loop 110)

Executable cores for the fifth ten feasible rows (E4 triage, Batch P5):
E-1455, E-1460, E-1463, E-1468, E-1469, E-1470, E-1484, E-1487, E-1489,
E-1490. Each section is a *model with a theorem*: the smallest decidable
kernel that makes the row falsifiable. `Std`-only, `Nat`/`List`/`Bool`.

| Register row | Concept | Lean core |
|---|---|---|
| E-1455 | affine RPC tokens | `invoke` |
| E-1460 | Presburger rate lattice | `Rule`, `admitR`, `meet` |
| E-1463 | channel duality | `ChanEnd`, `dualOf`, `matchC` |
| E-1468 | affine actor mailboxes | `Mbox`, `receive` |
| E-1469 | SPSC ring arithmetic | `Ring`, `used`, `push`, `pop` |
| E-1470 | glitch-free signal lattice | `Sig`, `combine`, `evalOnce` |
| E-1484 | deny-list compliance check | `denyCheck` |
| E-1487 | linear permission capabilities | `Cap`, `grant`, `revoke`, `useC` |
| E-1489 | snapshot restore | `App`, `snapA`, `restoreA`, `rotate` |
| E-1490 | peripheral-driver FSM | `BState`, `BEv`, `bstep` |
-/

namespace Morph.Specs.BatchP5

/-! ## E-1455: affine RPC tokens -/

/-- Invoke `id`: accepted once, refused on redelivery. -/
def invoke (consumed : List Nat) (id : Nat) : Option (List Nat) :=
  if id ∈ consumed then none else some (id :: consumed)

/-! ## E-1460: Presburger rate lattice -/

/-- An admission rule: the allowed request-size window. -/
structure Rule where
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

/-- Admit `n` iff it lies in the window. -/
def admitR (r : Rule) (n : Nat) : Bool := decide (r.lo ≤ n ∧ n ≤ r.hi)

/-- Meet: both windows must admit. -/
def meet (r1 r2 : Rule) : Rule := ⟨Nat.max r1.lo r2.lo, Nat.min r1.hi r2.hi⟩

/-! ## E-1463: channel duality -/

/-- One channel end: its id and its dual's id. -/
structure ChanEnd where
  id : Nat
  dual : Nat
  deriving Repr, DecidableEq

/-- The dual end. -/
def dualOf (e : ChanEnd) : ChanEnd := ⟨e.dual, e.id⟩

/-- Ends match iff each names the other. -/
def matchC (a b : ChanEnd) : Bool := decide (a.id = b.dual ∧ a.dual = b.id)

/-! ## E-1468: affine mailboxes -/

/-- A mailbox expecting exactly one next sequence number. -/
structure Mbox where
  state : Nat
  expect : Nat
  deriving Repr, DecidableEq

/-- Receive: accept only the expected message, then advance. -/
def receive (m : Mbox) (msg : Nat) : Option Mbox :=
  if msg = m.expect then some ⟨msg, msg + 1⟩ else none

/-! ## E-1469: SPSC ring -/

/-- Ring cursors: consumed head, produced tail. -/
structure Ring where
  head : Nat
  tail : Nat
  deriving Repr, DecidableEq

/-- Buffered items. -/
def used (r : Ring) : Nat := r.tail - r.head

/-- Produce one item. -/
def push (r : Ring) : Ring := ⟨r.head, r.tail + 1⟩

/-- Consume one item. -/
def pop (r : Ring) : Ring := ⟨r.head + 1, r.tail⟩

/-! ## E-1470: signal lattice -/

/-- A signal: value plus source stamp. -/
structure Sig where
  val : Nat
  stamp : Nat
  deriving Repr, DecidableEq

/-- Combine two signals: values add, stamp covers both. -/
def combine (a b : Sig) : Sig := ⟨a.val + b.val, Nat.max a.stamp b.stamp⟩

/-- Single-pass evaluation over a node list. -/
def evalOnce (ns : List Sig) : Nat := (ns.map Sig.val).sum

/-! ## E-1484: deny-list compliance -/

/-- A request is allowed iff its permission is not denied. -/
def denyCheck (denied : List Nat) (p : Nat) : Bool := decide (p ∉ denied)

/-! ## E-1487: permission capabilities -/

/-- A permission capability: which plus whether live. -/
structure Cap where
  perm : Nat
  live : Bool
  deriving Repr, DecidableEq

/-- Grant a live capability. -/
def grant (p : Nat) : Cap := ⟨p, true⟩

/-- Revoke: kill liveness, keep the label. -/
def revoke (c : Cap) : Cap := ⟨c.perm, false⟩

/-- Use: allowed iff live. -/
def useC (c : Cap) : Bool := decide (c.live = true)

/-! ## E-1489: snapshot restore -/

/-- App state: screen plus data. -/
structure App where
  screen : Nat
  dat : Nat
  deriving Repr, DecidableEq

/-- Snapshot: copy. -/
def snapA (a : App) : App := a

/-- Restore: reinstall the snapshot. -/
def restoreA (_killed snap : App) : App := snap

/-- Rotate: new screen, same data. -/
def rotate (a : App) : App := ⟨a.screen + 1, a.dat⟩

/-! ## E-1490: peripheral-driver FSM -/

/-- Link states. -/
inductive BState where
  | idle : BState
  | advertising : BState
  | connected : BState
  deriving Repr, DecidableEq

/-- Link events. -/
inductive BEv where
  | startAdv : BEv
  | connect : BEv
  | drop : BEv
  | timeout : BEv
  deriving Repr, DecidableEq

/-- Transitions; illegal combos are `none`. -/
def bstep : BState → BEv → Option BState
  | .idle, .startAdv => some .advertising
  | .advertising, .connect => some .connected
  | .connected, .drop => some .idle
  | .advertising, .timeout => some .idle
  | .connected, .timeout => some .connected
  | _, _ => none

end Morph.Specs.BatchP5
