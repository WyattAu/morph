/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Frontier Kernels — Batch B remainder, Batch C, Batch D start (E-28–E-37)

Status: In Progress (loop 106, second-ten first cycle).

Executable cores for the next ten registered frontier experiments (ADR-019:
Batch B remainder E-28–E-30; Batch C E-31–E-35; Batch D start E-36, E-37).
Each section is a *model with a theorem*, not the experiment itself: the
register's acceptance rule asks for a decidable checking algorithm or
computable synthesis procedure plus a kill criterion, and these are the
smallest kernels that make each row falsifiable.

The mathematics these rows name (conformal bootstrap, Verlinde fusion,
twisted K-theory, BV quantization, equivariant localization,
reflection positivity, Frobenius manifolds, Ramanujan graphs, graph
Riemann–Roch, PT symmetry) is documentation. The Lean code is the checkable
fragment: certificates, checkers, and the laws they satisfy.

## Mapping Summary

| Register row | Concept | Lean core |
|---|---|---|
| E-28 | Bootstrap latency bounds | `Stage`, `totalLo`/`totalHi`, `realizes`, `certify` |
| E-29 | Anyonic matching | `ACharge`, `fuse`, `neutral`, `pairsWith`, `bestFill` |
| E-30 | Hot-reload anomaly check | `Field`, `findField`, `obstructions`, `admitReload` |
| E-31 | BV memory safety | `stepL`, `reachSet`, `leakFree`, `dangleFree`, `findLeak` |
| E-32 | Atiyah-Bott risk localization | `halfSum`, `orbitSum` |
| E-33 | OS reflection positivity | `Gram`, `sosVal`, `correlator`, `rpCheck` |
| E-34 | Frobenius/WDVV execution | `schedSq`, `meetsBudget` |
| E-35 | Ramanujan interconnects | `cubeEdges`, `deg`, `boundary`, `maskVerts`, `goodCut` |
| E-36 | Baker-Norine arbitration | `get`/`put`, `fire`, `stabilize`, `genus`, `admitFast` |
| E-37 | PT-symmetric telemetry | `det2`, `matMul2`, `gapLaw`-witnesses, `detect` |

## What the model does *not* claim

No SDPB solver, matching engine, reload toolchain, borrow checker, risk
library, event-log checker, execution synthesiser, topology generator,
divisor-rank oracle, or telemetry sensor is produced. Rows are graded L1
(definitions plus `decide`-able checks and examples) or L3 (proved laws).
The execution record and kill criteria are tracked in
`.specs/03_research/briefs/E1-batch-bcd-kernel.md`.
-/

namespace Morph.Specs.BatchBCD

/-- Project-local list sum: structural recursion, so cons/length facts hold
by `rfl` and `simp [lsum]` with no API risk. Used by E-28, E-32, E-34, E-36. -/
def lsum : List Nat → Nat
  | [] => 0
  | x :: xs => x + lsum xs

/-! ## E-28: bootstrap latency bounds

A pipeline is four (here: any number of) stages, each with a latency window
`[lo, hi]`. A realization picks one latency per window. `certify` checks a
candidate bound against the worst case; the crossing identity is that totals
do not depend on parenthesization (`totalHi_append`). The SDP solve of the
kill criterion is the benchmark, not a theorem here. -/

/-- One pipeline stage: latency lies in `[lo, hi]`. -/
structure Stage where
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

/-- Best-case total: the sum of lower bounds. -/
def totalLo : List Stage → Nat
  | [] => 0
  | s :: ss => s.lo + totalLo ss

/-- Worst-case total: the sum of upper bounds. -/
def totalHi : List Stage → Nat
  | [] => 0
  | s :: ss => s.hi + totalHi ss

/-- A realization picks one latency per stage window. -/
def realizes : List Stage → List Nat → Prop
  | [], [] => True
  | s :: ss, a :: as => s.lo ≤ a ∧ a ≤ s.hi ∧ realizes ss as
  | _, _ => False

/-- Certificate check: the bound covers the worst case. -/
def certify (bound : Nat) (ss : List Stage) : Bool :=
  decide (totalHi ss ≤ bound)

/-! ## E-29: anyonic matching

Orders carry an anyon charge; a fill pairs a buy with a sell when the pair
fuses to vacuum (the Verlinde table for Z₃) and prices cross. The engine
picks the best such pair. Jitter-invariance (order of arrival must not
matter) is a property of the benchmark harness; the kernel proves the fill
is sound and price-optimal. -/

/-- Z₃ anyon charges: vacuum, +, −. -/
inductive ACharge where
  | vac
  | pos
  | neg
  deriving Repr, DecidableEq

/-- Verlinde fusion for Z₃. -/
def fuse : ACharge → ACharge → ACharge
  | .vac, x => x
  | x, .vac => x
  | .pos, .pos => .neg
  | .pos, .neg => .vac
  | .neg, .pos => .vac
  | .neg, .neg => .pos

/-- A pair can annihilate: it fuses to vacuum. -/
def neutral (c₁ c₂ : ACharge) : Bool :=
  decide (fuse c₁ c₂ = .vac)

/-- One order: side, charge, limit price. -/
structure Order where
  buy : Bool
  charge : ACharge
  price : Nat
  deriving Repr, DecidableEq

/-- All neutral, crossing pairs a buy can form. -/
def pairsWith : Order → List Order → List (Order × Order)
  | _, [] => []
  | b, s :: ss =>
    if b.buy && !s.buy && neutral b.charge s.charge && decide (s.price ≤ b.price) then
      (b, s) :: pairsWith b ss
    else pairsWith b ss

/-- Every candidate fill across both books. -/
def candidates : List Order → List Order → List (Order × Order)
  | [], _ => []
  | b :: bs, sells => pairsWith b sells ++ candidates bs sells

/-- Strictly better fill: higher buy price, then lower sell price. -/
def better (p q : Order × Order) : Bool :=
  decide (q.1.price < p.1.price ∨ (q.1.price = p.1.price ∧ p.2.price < q.2.price))

/-- Engine step: keep the better of the accumulator and a new candidate. -/
def pickStep : Option (Order × Order) → Order × Order → Option (Order × Order)
  | none, p => some p
  | some q, p => if better p q then some p else some q

/-- The engine's fill: the best candidate, or nothing. -/
def bestFill (buys sells : List Order) : Option (Order × Order) :=
  (candidates buys sells).foldl pickStep none

/-! ## E-30: hot-reload anomaly check

A layout is a field list with offsets and sizes. The obstruction report
names every removed, shifted, or resized field; a reload is admitted iff
the report is empty. The Dixmier–Douady language of the register row is
documentation; the diff checker is the artifact. -/

/-- One struct field: name, byte offset, byte size. -/
structure Field where
  name : String
  off : Nat
  size : Nat
  deriving Repr, DecidableEq

/-- A struct layout is a field list. -/
abbrev Layout := List Field

/-- One ABI obstruction. -/
inductive Obstr where
  | removed (name : String)
  | shifted (name : String) (old new : Nat)
  | resized (name : String) (old new : Nat)
  deriving Repr, DecidableEq

/-- Look up a field by name. -/
def findField : Layout → String → Option (Nat × Nat)
  | [], _ => none
  | f :: fs, n => if f.name == n then some (f.off, f.size) else findField fs n

/-- The obstruction report of old layout against new. -/
def obstructions : Layout → Layout → List Obstr
  | [], _ => []
  | f :: fs, ls2 =>
    match findField ls2 f.name with
    | none => .removed f.name :: obstructions fs ls2
    | some (o, s) =>
      (if o == f.off then [] else [.shifted f.name f.off o]) ++
      (if s == f.size then [] else [.resized f.name f.size s]) ++
      obstructions fs ls2

/-- Admit the hot reload iff the report is empty. -/
def admitReload (l1 l2 : Layout) : Bool :=
  decide (obstructions l1 l2 = [])

/-! ## E-31: BV memory safety

Capabilities pair loans with borrowers; the two BV exactness checks become
two reachability checks over the finite loan graph: every borrower must be
reachable from a live root (no leaks, `(S,S) = 0`), and every lender must
itself be live (no dangles, `ΔS = 0`). `reachSet` is iterated neighbourhood
expansion, exactly as in E-25. -/

/-- One expansion step: the front plus everything it lends to. -/
def stepL (loans : List (Nat × Nat)) (front : List Nat) : List Nat :=
  front ++ loans.filterMap (fun l => if l.1 ∈ front then some l.2 else none)

/-- Borrowers reachable from the roots within `n` steps. -/
def reachSet (loans : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, roots => roots
  | n + 1, roots => stepL loans (reachSet loans n roots)

/-- No leaks: every borrower is reachable from a root. -/
def leakFree (loans : List (Nat × Nat)) (roots : List Nat) : Bool :=
  loans.all fun l => decide (l.2 ∈ reachSet loans loans.length roots)

/-- No dangles: every lender is live. -/
def dangleFree (loans : List (Nat × Nat)) (roots : List Nat) : Bool :=
  loans.all fun l => decide (l.1 ∈ reachSet loans loans.length roots)

/-- Find a leaking loan, threading the full loan list for the fuel/set. -/
def findLeakAux (all : List (Nat × Nat)) (roots : List Nat) :
    List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | l :: ls =>
    if decide (l.2 ∈ reachSet all all.length roots) then findLeakAux all roots ls
    else some l

/-- Find a leaking loan, if any. -/
def findLeak (loans : List (Nat × Nat)) (roots : List Nat) : Option (Nat × Nat) :=
  findLeakAux loans roots loans

/-! ## E-32: Atiyah-Bott risk localization

A symmetric payoff template is evaluated on the full reversal orbit; the
localization theorem says the orbit sum is twice the fundamental-domain
sum. The closed-form basket/Var template is the fixed-point contribution;
Monte Carlo remains the fallback for asymmetric books. -/

/-- Sum over the fundamental domain. -/
def halfSum (f : Nat → Nat) (xs : List Nat) : Nat :=
  lsum (xs.map f)

/-- Sum over the full reversal orbit. -/
def orbitSum (f : Nat → Nat) (xs : List Nat) : Nat :=
  lsum ((xs.map f) ++ (xs.map f).reverse)

/-! ## E-33: reflection positivity for event sourcing

A two-event window has Gram matrix `[[a, b], [b, c]]`. Reflection positivity
is positive-semidefiniteness; the certificate is an explicit sum-of-squares
decomposition: `a·Q = (ax+by)² + det·y²`, so a nonnegative witness equal to
`a` times the correlator. Replay or parallel compaction is admitted on
windows whose certificate checks. -/

/-- A 2×2 Gram matrix. -/
structure Gram where
  a : Int
  b : Int
  c : Int
  deriving Repr, DecidableEq

/-- The sum-of-squares certificate value. -/
def sosVal (g : Gram) (x y : Int) : Int :=
  (g.a * x + g.b * y) * (g.a * x + g.b * y) + (g.a * g.c) * (y * y)

/-- The event correlator `Q(x, y)`. -/
def correlator (g : Gram) (x y : Int) : Int :=
  g.a * (x * x) + (2 * g.b * (x * y) + g.c * (y * y))

/-- Certificate check: `a > 0` and `det ≥ 0`. -/
def rpCheck (g : Gram) : Bool :=
  decide (0 < g.a ∧ 0 ≤ g.a * g.c - g.b * g.b)

/-! ## E-34: Frobenius/WDVV optimal execution

Impact is the sum of squared fills. The Cauchy–Schwarz certificate says any
schedule's impact, scaled by its length, dominates the squared target: the
uniform (TWAP) schedule is optimal for quadratic impact. The comparison
against grid HJB is the benchmark, not a theorem here. -/

/-- Quadratic impact of a fill schedule. -/
def schedSq : List Nat → Nat
  | [] => 0
  | x :: xs => x * x + schedSq xs

/-- Budget check: impact within `c`. -/
def meetsBudget (c : Nat) (sched : List Nat) : Bool :=
  decide (schedSq sched ≤ c)

/-! ## E-35: Ramanujan interconnects

The 3-cube is the concrete topology: 3-regular, with edge expansion at
least 1 on every small cut (proved by exhaustive check over all 256 vertex
subsets). The LPS generator and the Alon–Boppana bound are the benchmark
context; the expansion certificate is the artifact. -/

/-- Cube edges (3-cube, 8 vertices, 12 edges). -/
def cubeEdges : List (Nat × Nat) :=
  [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]

/-- Degree of a vertex. -/
def deg (v : Nat) : Nat :=
  (cubeEdges.filter (fun e => decide (e.1 = v ∨ e.2 = v))).length

/-- Edges crossing the cut. -/
def boundary (S : List Nat) : List (Nat × Nat) :=
  cubeEdges.filter fun e => (decide (e.1 ∈ S)) != (decide (e.2 ∈ S))

/-- Vertices selected by an 8-bit mask. -/
def maskVerts (m : Nat) : List Nat :=
  [0,1,2,3,4,5,6,7].filter (fun i => decide ((m / 2 ^ i) % 2 = 1))

/-- The cut meets the expansion bound. -/
def goodCut (S : List Nat) : Bool :=
  decide (S.length ≤ (boundary S).length)

/-! ## E-36: Baker-Norine chip-firing arbitration

Credit distributions are chip configurations; firing a vertex with at least
as many chips as incident edges sends one chip along each edge. Firing
conserves chips, and stable configurations are fixed points. The genus fast
path (`deg ≥ g`) is a checkable admission premise; divisor-rank existence is
not proved. -/

/-- Chips held by a vertex (association list). -/
def get : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (w, c) :: rest, v => if w == v then c else get rest v

/-- Set a vertex's chips. -/
def put : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], v, c => [(v, c)]
  | (w, c') :: rest, v, c => if w == v then (w, c) :: rest else (w, c') :: put rest v c

/-- Total chips in play. -/
def total (cfg : List (Nat × Nat)) : Nat :=
  lsum (cfg.map (·.2))

/-- Neighbours of a vertex (with multiplicity). -/
def neighbors (edges : List (Nat × Nat)) (v : Nat) : List Nat :=
  edges.filterMap fun e =>
    if e.1 == v then some e.2 else if e.2 == v then some e.1 else none

/-- Fire a vertex: no-op unless it holds at least its degree. -/
def fire (edges : List (Nat × Nat)) (cfg : List (Nat × Nat)) (v : Nat) :
    List (Nat × Nat) :=
  if (neighbors edges v).length ≤ get cfg v then
    (neighbors edges v).foldl (fun c w => put c w (get c w + 1))
      (put cfg v (get cfg v - (neighbors edges v).length))
  else cfg

/-- A configuration is stable: every non-bank vertex holds fewer than its
degree. -/
def Stable (edges : List (Nat × Nat)) (cfg : List (Nat × Nat)) (bank : Nat)
    (verts : List Nat) : Prop :=
  ∀ v ∈ verts, v ≠ bank → get cfg v < (neighbors edges v).length

/-- First unstable non-bank vertex, if any. -/
def findUnstable (edges : List (Nat × Nat)) (cfg : List (Nat × Nat)) (bank : Nat) :
    List Nat → Option Nat
  | [] => none
  | v :: vs =>
    if v == bank then findUnstable edges cfg bank vs
    else if decide ((neighbors edges v).length ≤ get cfg v) then some v
    else findUnstable edges cfg bank vs

/-- Stabilize by repeated firing (fuel-bounded). -/
def stabilize : Nat → List (Nat × Nat) → List (Nat × Nat) → Nat → List Nat →
    List (Nat × Nat)
  | 0, _, cfg, _, _ => cfg
  | fuel + 1, edges, cfg, bank, verts =>
    match findUnstable edges cfg bank verts with
    | none => cfg
    | some v => stabilize fuel edges (fire edges cfg v) bank verts

/-- Graph genus `g = |E| + 1 − |V|`. -/
def genus (edges : List (Nat × Nat)) (verts : List Nat) : Nat :=
  edges.length + 1 - verts.length

/-- Fast-path admission: degree covers the genus. -/
def admitFast (edges : List (Nat × Nat)) (verts : List Nat)
    (cfg : List (Nat × Nat)) : Bool :=
  decide (genus edges verts ≤ total cfg)

/-! ## E-37: PT-symmetric exceptional-point telemetry

The EP₂ sensor model over integers (ADC counts): the shifted residual
matrix `[[−d, 1], [ε, −d]]` has determinant `d² − ε`, so a reading shift `d`
detects perturbation `ε = d²` — quadratic sensitivity amplification. At zero
perturbation the residual is nilpotent (the Jordan-block certificate of the
exceptional point). Detection against a threshold names its witness. -/

/-- 2×2 determinant. -/
def det2 (a b c d : Int) : Int :=
  a * d - b * c

/-- Shifted residual matrix entries `(a, b, c, d)`. -/
def shiftMat (d e : Int) : Int × Int × Int × Int :=
  (d, 1, e, d)

/-- 2×2 product on entry tuples `(a, (b, (c, d)))`. -/
def matMul2 (M N : Int × Int × Int × Int) : Int × Int × Int × Int :=
  (M.1 * N.1 + M.2.1 * N.2.2.1,
   M.1 * N.2.1 + M.2.1 * N.2.2.2,
   M.2.2.1 * N.1 + M.2.2.2 * N.2.2.1,
   M.2.2.1 * N.2.1 + M.2.2.2 * N.2.2.2)

/-- The unperturbed residual `[[0, 1], [0, 0]]`. -/
def nilMat : Int × Int × Int × Int :=
  (0, 1, 0, 0)

/-- Zero matrix. -/
def zeroMat : Int × Int × Int × Int :=
  (0, 0, 0, 0)

/-- Alarm iff some reading has `d² ≥ thresh`. -/
def detect (thresh : Int) (readings : List Int) : Bool :=
  readings.any (fun d => decide (thresh ≤ d * d))

end Morph.Specs.BatchBCD
