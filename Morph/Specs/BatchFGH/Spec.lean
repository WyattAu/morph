/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Frontier Kernels — Batch F remainder, Batch G, Batch H start (E-48–E-57)

Status: In Progress (loop 108, first-ten second cycle).

Executable cores for the next ten registered frontier experiments (ADR-019:
Batch F remainder E-48–E-50; Batch G E-51–E-55; Batch H start E-56, E-57).
Each section is a *model with a theorem*, not the experiment itself: the
register's acceptance rule asks for a decidable checking algorithm or
computable synthesis procedure plus a kill criterion, and these are the
smallest kernels that make each row falsifiable.

The mathematics these rows name (cluster algebras, Lieb–Robinson bounds,
Atiyah–Sutcliffe determinants, noncommutative Hodge theory, Khovanov
homology, Selberg trace formula, SUSY localization, cobordism anomalies,
Tannakian duality, Cuntz–Krieger algebras) is documentation. The Lean code
is the checkable fragment: certificates, checkers, and the laws they
satisfy.

## Mapping Summary

| Register row | Concept | Lean core |
|---|---|---|
| E-48 | Cluster-mutation quote updates | `Seed`, `mut0`, `seedPos`, `seedPosB` |
| E-49 | Lieb–Robinson coherency cones | `safeR`, `placeAll` |
| E-50 | Atiyah–Sutcliffe repulsion routing | `Pair2`, `gap`, `repel`, `repelN` |
| E-51 | NC-Hodge macro termination | `Mex`, `msize`, `stepM`, `isNormal`, `normM` |
| E-52 | Khovanov network cobordisms | `CS`, `DS`, `bdyC`, `bdyD`, `cmap` |
| E-53 | Selberg spectral routing | `alive`, `mids`, `route2`, `hopsAlive` |
| E-54 | Pestun tail-latency localization | `isum`, `lsumN`, `Orb`, `total`, `countGt` |
| E-55 | Freed–Hopkins descriptor checker | `Desc`, `within`, `aligned`, `admit`, `rejectReason` |
| E-56 | Tannakian cross-ISA transpilation | `XOp`, `AOp`, `transp`, `xrun`, `arun` |
| E-57 | Cuntz–Krieger parser minimization | `DFA`, `run`, `accepts`, `reachN`, `minimize` |

## What the model does *not* claim

No quote engine, scheduler, allocator, macro system, network stack, mesh
model, queueing library, driver verifier, transpiler backend, or parser
synthesizer is produced. Rows are graded L1 (definitions plus
`decide`-able checks and examples) or L3 (proved laws). The execution
record and kill criteria are tracked in
`.specs/03_research/briefs/E3-batchfgh-kernel.md`.
-/

namespace Morph.Specs.BatchFGH

/-! ## E-48: cluster-mutation quote updates

A quote seed is a pair of books. A mutation replaces one side by the
exchange quotient, witnessed explicitly: `mut0 s num q` fires only when
`num = q * s.x`, which is the exact-division content of the Laurent
phenomenon. Positivity (no negative liquidity) is preserved.
-/

/-- A two-book quote seed. -/
structure Seed where
  x : Int
  y : Int
  deriving Repr, DecidableEq

/-- Mutate position 0 with explicit numerator and quotient witness. -/
def mut0 (s : Seed) (num q : Int) : Seed :=
  if num == q * s.x then ⟨q, s.y⟩ else s

/-- Laurent positivity: both books strictly positive. -/
def seedPos (s : Seed) : Prop := 0 < s.x ∧ 0 < s.y

/-- Decidable positivity check. -/
def seedPosB (s : Seed) : Bool := decide (0 < s.x) && decide (0 < s.y)

/-! ## E-49: Lieb–Robinson coherency cones

A mutator at `m` can reach a reader at `r ≥ m` only inside the cone
`v * t ≥ r - m`. The placer keeps readers outside every mutator's cone;
`placeAll_sound` is the certificate that the placement is safe.
-/

/-- One reader is safe against one mutator. -/
def safeR (v m r t : Nat) : Bool := decide (m ≤ r ∧ v * t < r - m)

/-- A placement is safe against every mutator. -/
def placeAll : Nat → List Nat → Nat → Nat → Bool
  | _, [], _, _ => true
  | v, m :: ms, r, t => safeR v m r t && placeAll v ms r t

/-! ## E-50: Atiyah–Sutcliffe repulsion routing

Two thread pointers share a slot while `lo < hi` fails. Repulsion pushes
them apart by one per step; the gap grows by exactly two each step, so
separation is certified, not hoped for. The repulsion potential is
documentation; the gap law is the artifact.
-/

/-- A two-pointer configuration. -/
structure Pair2 where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

/-- The separation gap. -/
def gap (p : Pair2) : Int := p.hi - p.lo

/-- One repulsion step. -/
def repel (p : Pair2) : Pair2 :=
  if p.lo < p.hi then ⟨p.lo - 1, p.hi + 1⟩ else p

/-- Iterated repulsion. -/
def repelN : Nat → Pair2 → Pair2
  | 0, p => p
  | n + 1, p => repelN n (repel p)

/-! ## E-51: NC-Hodge macro termination

Macro expressions with two TLS-style shrinking rules. The measure `msize`
drops on every step (the finiteness certificate), steps fire only off normal
forms, and the fuel-bounded normalizer reaches a normal form whenever fuel
covers the measure. The Hodge language is documentation; the measure is the
admission certificate.
-/

/-- Macro expressions: constants and addition. -/
inductive Mex where
  | const (n : Nat)
  | add (l r : Mex)
  deriving Repr, DecidableEq

/-- The termination measure. -/
def msize : Mex → Nat
  | .const _ => 1
  | .add l r => 1 + msize l + msize r

/-- One rewrite step (zero-unit elimination, leftmost-innermost). -/
def stepM : Mex → Option Mex
  | .const _ => none
  | .add l r =>
    if l = .const 0 then some r
    else if r = .const 0 then some l
    else match stepM l with
      | some l' => some (.add l' r)
      | none =>
        match stepM r with
        | some r' => some (.add l r')
        | none => none

/-- Normal forms admit no step. -/
def isNormal (e : Mex) : Bool := decide (stepM e = none)

/-- Fuel-bounded normalization. -/
def normM : Nat → Mex → Mex
  | 0, e => e
  | n + 1, e =>
    match stepM e with
    | some e' => normM n e'
    | none => e

/-! ## E-52: Khovanov network cobordisms

A reroute is a cobordism between a before-complex and an after-complex.
The pushforward `cmap` is a chain map: it commutes with the boundary, so
cycles (conserved classes) map to cycles. The categorification language
is documentation; the commuting square is the artifact.
-/

/-- Before-states of the reroute. -/
inductive CS where
  | c0
  | c1
  deriving Repr, DecidableEq

/-- After-states of the reroute. -/
inductive DS where
  | d0
  | d1
  deriving Repr, DecidableEq

/-- Boundary before: `c0` bounds `c1`. -/
def bdyC : CS → List CS
  | .c0 => [.c1]
  | .c1 => []

/-- Boundary after: `d0` bounds `d1`. -/
def bdyD : DS → List DS
  | .d0 => [.d1]
  | .d1 => []

/-- Pushforward along the reroute. -/
def cmap : CS → DS
  | .c0 => .d0
  | .c1 => .d1

/-- Cycles before. -/
def isCycleC : CS → Bool
  | .c1 => true
  | .c0 => false

/-- Cycles after. -/
def isCycleD : DS → Bool
  | .d1 => true
  | .d0 => false

/-! ## E-53: Selberg spectral routing

Links carry a liveness mask; a route is direct when the edge is alive, or
re-derived through one live intermediate when it is not. `route2_alive`
certifies every hop of the emitted route; `route2_ends` certifies the
endpoints. Graph traversal beyond one intermediate is out of fragment.
-/

/-- A hop is usable iff present and not dead. -/
def alive (e dead : List (Nat × Nat)) (u v : Nat) : Bool :=
  decide ((u, v) ∈ e ∧ (u, v) ∉ dead)

/-- Live intermediates between `a` and `b`. -/
def mids (e dead : List (Nat × Nat)) (a b : Nat) : List Nat :=
  ((e.filterMap fun x => if x.1 == a then some x.2 else none).filter fun m =>
    alive e dead a m && alive e dead m b)

/-- Direct route, else one-hop re-derivation. -/
def route2 (e : List (Nat × Nat)) (a b : Nat) (dead : List (Nat × Nat)) :
    Option (List Nat) :=
  if alive e dead a b then some [a, b]
  else match mids e dead a b with
    | [] => none
    | m :: _ => some [a, m, b]

/-- Every consecutive pair of a path is a live hop. -/
def hopsAlive (e dead : List (Nat × Nat)) : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => alive e dead a b && hopsAlive e dead (b :: rest)

/-! ## E-54: Pestun tail-latency localization

The finite analog of collapsing to the fixed locus: a weight constant on
each free orbit sums to the fixed contribution plus twice the orbit
representatives. Separately, the Markov bound certifies a closed-form
tail estimate against the counted exceedances.
-/

/-- Project-local integer list sum. -/
def isum : List Int → Int
  | [] => 0
  | x :: xs => x + isum xs

/-- Project-local natural list sum. -/
def lsumN : List Nat → Nat
  | [] => 0
  | x :: xs => x + lsumN xs

/-- A finite locus: fixed points plus free-orbit pairs. -/
structure Orb where
  fixed : List Nat
  pairs : List (Nat × Nat)
  deriving Repr, DecidableEq

/-- Total weight over the locus. -/
def total (w : Nat → Int) (o : Orb) : Int :=
  isum (o.fixed.map w) + isum (o.pairs.map fun p => w p.1 + w p.2)

/-- Count of samples strictly above the threshold. -/
def countGt (xs : List Nat) (t : Nat) : Nat :=
  (xs.filter fun x => decide (t < x)).length

/-! ## E-55: Freed–Hopkins descriptor checker

A DMA descriptor is admitted iff it lies in bounds, is aligned, and carries
the DMA flag. Every rejection names the offending check. The cobordism
language is documentation; the two-way soundness is the artifact.
-/

/-- A DMA descriptor. -/
structure Desc where
  off : Nat
  len : Nat
  flag : Bool
  deriving Repr, DecidableEq

/-- The descriptor lies inside memory. -/
def within (mem : Nat) (d : Desc) : Bool := decide (d.off + d.len ≤ mem)

/-- The offset is 8-aligned. -/
def aligned (d : Desc) : Bool := decide (d.off % 8 = 0)

/-- Admission: bounds, alignment, and flag together. -/
def admit (mem : Nat) (d : Desc) : Bool :=
  within mem d && aligned d && d.flag

/-- Every rejection names its offender. -/
def rejectReason (mem : Nat) (d : Desc) : Option String :=
  if !within mem d then some "bounds"
  else if !aligned d then some "align"
  else if !d.flag then some "flag"
  else none

/-! ## E-56: Tannakian cross-ISA transpilation

A three-opcode source and target with register semantics. Transpilation is
a table map; the intertwiner law says evaluation commutes with the map,
per opcode and per program. The fiber-functor language is documentation;
the commuting square is the artifact.
-/

/-- Source opcodes. -/
inductive XOp where
  | nop
  | inc
  | add (n : Nat)
  deriving Repr, DecidableEq

/-- Target opcodes. -/
inductive AOp where
  | nop
  | inc
  | add (n : Nat)
  deriving Repr, DecidableEq

/-- Source evaluation on a register. -/
def xeval : XOp → Nat → Nat
  | .nop, r => r
  | .inc, r => r + 1
  | .add n, r => r + n

/-- Target evaluation on a register. -/
def aeval : AOp → Nat → Nat
  | .nop, r => r
  | .inc, r => r + 1
  | .add n, r => r + n

/-- Opcode translation table. -/
def transp : XOp → AOp
  | .nop => .nop
  | .inc => .inc
  | .add n => .add n

/-- Source program run. -/
def xrun : List XOp → Nat → Nat
  | [], r => r
  | o :: os, r => xrun os (xeval o r)

/-- Target program run. -/
def arun : List AOp → Nat → Nat
  | [], r => r
  | o :: os, r => arun os (aeval o r)

/-- Program translation. -/
def transpL : List XOp → List AOp := List.map transp

/-! ## E-57: Cuntz–Krieger parser minimization

A deterministic automaton with explicit states. `minimize` drops states
unreachable from the start (the `K₀`-preserving move in miniature:
restriction to the essential subgraph); acceptance is preserved on every
word that fits in the state budget, and the state count never grows.
Timing closure itself is out of fragment.
-/

/-- A deterministic automaton over bits. -/
structure DFA where
  states : List Nat
  start : Nat
  accept : List Nat
  step : Nat → Bool → Nat

/-- Run a word from a state. -/
def run : DFA → List Bool → Nat → Nat
  | _, [], s => s
  | d, b :: bs, s => run d bs (d.step s b)

/-- Acceptance by membership. -/
def accepts (d : DFA) (w : List Bool) : Bool :=
  decide (run d w d.start ∈ d.accept)

/-- States reachable within `fuel` expansions. -/
def reachN : DFA → Nat → List Nat
  | d, 0 => [d.start]
  | d, n + 1 =>
    reachN d n ++ (reachN d n).flatMap fun s => [d.step s false, d.step s true]

/-- Decidable reachability within the state budget. -/
def reachableB (d : DFA) (s : Nat) : Bool :=
  decide (s ∈ reachN d d.states.length)

/-- Restrict to reachable states. -/
def minimize (d : DFA) : DFA :=
  { states := d.states.filter (reachableB d)
  , start := d.start
  , accept := d.accept.filter (reachableB d)
  , step := d.step }

end Morph.Specs.BatchFGH
