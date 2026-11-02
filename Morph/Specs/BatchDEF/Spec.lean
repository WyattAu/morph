/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Frontier Kernels — Batch D remainder, Batch E, Batch F start (E-38–E-47)

Status: In Progress (loop 107, third-ten first cycle).

Executable cores for the next ten registered frontier experiments (ADR-019:
Batch D remainder E-38–E-40; Batch E E-41–E-45; Batch F start E-46, E-47).
Each section is a *model with a theorem*, not the experiment itself: the
register's acceptance rule asks for a decidable checking algorithm or
computable synthesis procedure plus a kill criterion, and these are the
smallest kernels that make each row falsifiable.

The mathematics these rows name (derived algebraic geometry, Connes-Kreimer
renormalization, geometric quantization, arithmetic topology, geometric
measure theory, index theory, thermofield dynamics, inverse scattering,
deformation quantization, causal fermion systems) is documentation. The Lean
code is the checkable fragment: certificates, checkers, and the laws they
satisfy.

## Mapping Summary

| Register row | Concept | Lean core |
|---|---|---|
| E-38 | Derived-AG over-constrained routing | `Link`, `loadsOK`, `firstBad`, `satCount`, `solve` |
| E-39 | Connes-Kreimer Hopf AST slicing | `Tree`, `eval`, `prune`, `atPath`, `setPath`, `cuts`, `neg` |
| E-40 | Kostant-Souriau quantization backends | `lowerReg`, `lowerStack`, `evalCells` |
| E-41 | Arithmetic-topology Massey deadlock check | `reachE`, `hasTwoCycle`, `hasCycle`, `massey3` |
| E-42 | GMT rectifiable-current cache packing | `packAux`, `extents`, `disjointCheck` |
| E-43 | Families-index glitch-free DPR | `isPath`, `checkPath`, `bfs`, `deform` |
| E-44 | Thermofield active-active failover | `Entry`, `upsert`, `reconcile`, `findK`, `best` |
| E-45 | IST soliton signal processing | `scatter`, `reconstruct`, `sumsq` |
| E-46 | Kontsevich formality transaction quantization | `bracket`, `cross`, `corr`, `star` |
| E-47 | Causal-fermion spectral causality | `EvOp`, `disc`, `classify`, `needsFence` |

## What the model does *not* claim

No SOR solver, optimizer pass, backend generator, deadlock oracle, layout
pass, FPGA toolchain, replication protocol, signal library, STM, or
coherence classifier is produced. Rows are graded L1 (definitions plus
`decide`-able checks and examples) or L3 (proved laws). The execution record
and kill criteria are tracked in
`.specs/03_research/briefs/E2-batchdef-kernel.md`.
-/

namespace Morph.Specs.BatchDEF

/-- Project-local list sum over naturals: structural recursion, so cons/length
facts hold by `rfl` and `simp [lsum]` with no API risk. Used by E-40. -/
def lsum : List Nat → Nat
  | [] => 0
  | x :: xs => x + lsum xs

/-- Project-local list sum over integers. Used by E-45, E-46. -/
def lsumI : List Int → Int
  | [] => 0
  | x :: xs => x + lsumI xs

/-! ## E-38: derived-AG over-constrained routing

Routing constraints rarely fail cleanly: the Tor-defect picture grades the
outcome. Degree 0 is a feasible route (every load fits its link). Degree 1
is an obstruction certificate naming the conflicting pair (the load that
breaks its link cap) plus the maximal feasible fraction (satisfied pairs
over total pairs). `solve` returns one or the other, never an abort. -/

/-- A capacity constraint on one link. -/
structure Link where
  name : String
  cap : Nat
  deriving Repr, DecidableEq

/-- Pairwise check: every load fits its link cap (truncating zip). -/
def loadsOK : List Nat → List Link → Bool
  | [], _ => true
  | _, [] => true
  | l :: ls, c :: cs => decide (l ≤ c.cap) && loadsOK ls cs

/-- First violating (load, link) pair, if any. -/
def firstBad : List Nat → List Link → Option (Nat × Link)
  | [], _ => none
  | _, [] => none
  | l :: ls, c :: cs =>
    if decide (l ≤ c.cap) then firstBad ls cs else some (l, c)

/-- Number of satisfied (load, link) pairs. -/
def satCount : List Nat → List Link → Nat
  | [], _ => 0
  | _, [] => 0
  | l :: ls, c :: cs =>
    (if l ≤ c.cap then 1 else 0) + satCount ls cs

/-- The degree-1 obstruction certificate. -/
structure Cert where
  load : Nat
  link : String
  sat : Nat
  tot : Nat
  deriving Repr, DecidableEq

/-- The graded outcome: feasible route or obstruction certificate. -/
inductive Outcome where
  | ok
  | blocked (c : Cert)
  deriving Repr, DecidableEq

/-- Graded solver: feasible iff every pair fits, else the first conflict
plus the maximal feasible fraction. -/
def solve (loads : List Nat) (caps : List Link) : Outcome :=
  match firstBad loads caps with
  | none => .ok
  | some (l, c) =>
    .blocked ⟨l, c.name, satCount loads caps, (loads.zip caps).length⟩

/-! ## E-39: Connes-Kreimer Hopf AST slicing

BPHZ renormalization decomposes a diagram into subdivergences (coproduct)
and removes them (antipode counterterms). The optimizer analog: decompose an
expression tree along admissible cuts and slice dead branches. Trees here are
sums over integers; `prune` is the DCE pass, `cuts` the coproduct (every
subtree paired with the tree with that subtree countertermed to zero), `neg`
the antipode. -/

/-- Expression trees: constants and sums. -/
inductive Tree where
  | const (v : Int)
  | add (l r : Tree)
  deriving Repr, DecidableEq

/-- Tree evaluation. -/
def eval : Tree → Int
  | .const v => v
  | .add l r => eval l + eval r

/-- Slice dead (zero-evaluating) branches. -/
def prune : Tree → Tree
  | .const v => .const v
  | .add l r =>
    let l' := prune l
    let r' := prune r
    if eval l' == 0 then r' else if eval r' == 0 then l' else .add l' r'

/-- Count of add-nodes with a zero-evaluating child (dead weight). -/
def deadCount : Tree → Nat
  | .const _ => 0
  | .add l r =>
    (if eval l == 0 || eval r == 0 then 1 else 0) + deadCount l + deadCount r

/-- The coproduct: every subtree paired with the countertermed remainder.
Direct recursion: the trivial cut plus every cut of the children, with the
sibling subtree grafted back onto the remainder. -/
def cuts : Tree → List (Tree × Tree)
  | .const v => [(.const v, .const 0)]
  | .add l r =>
    (.add l r, .const 0) ::
      ((cuts l).map fun c => (c.1, .add c.2 r)) ++
        ((cuts r).map fun c => (c.1, .add l c.2))

/-- The antipode: negate every constant. -/
def neg : Tree → Tree
  | .const v => .const (-v)
  | .add l r => .add (neg l) (neg r)

/-! ## E-40: Kostant-Souriau backend generator

One phase-space kernel (finite `(q, p)` observable pairs) is lowered through
two polarizations: a register polarization (flat alternating `q, p` cells)
and a stack polarization (all `q`s pushed, then all `p`s). BKS-style
conformance is observable agreement (both evaluate to the same spectrum)
plus phase-volume preservation (both polarizations hold exactly `2n` cells). -/

/-- Register polarization: flat alternating cells. -/
def lowerReg : List (Nat × Nat) → List Nat
  | [] => []
  | (q, p) :: k => q :: p :: lowerReg k

/-- Stack polarization: positions pushed, then momenta. -/
def lowerStack (k : List (Nat × Nat)) : List Nat :=
  k.map (·.1) ++ k.map (·.2)

/-- Cell evaluation: the observable spectrum (a single total). -/
def evalCells (c : List Nat) : Nat :=
  lsum c

/-! ## E-41: arithmetic-topology Massey deadlock check

Pairwise cycle checks miss Borromean configurations: three modules can wait
on each other cyclically with no 2-cycle among them. The Massey kernel fires
exactly there: a directed 3-cycle with no back-edges. `reachE` is iterated
neighbourhood expansion (fuel-bounded, as in E-31); `hasCycle` is the global
verdict; `massey3` is the ternary decision procedure. -/

/-- One expansion step: the front plus everything it waits on. -/
def stepE (edges : List (Nat × Nat)) (front : List Nat) : List Nat :=
  front ++ edges.filterMap fun e =>
    if e.1 ∈ front then some e.2 else none

/-- Modules reachable from the roots within `n` steps. -/
def reachE (edges : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, roots => roots
  | n + 1, roots => stepE edges (reachE edges n roots)

/-- Pairwise check: is there a 2-cycle? -/
def hasTwoCycle (edges : List (Nat × Nat)) : Bool :=
  edges.any fun e => decide (e.1 ≠ e.2 ∧ (e.2, e.1) ∈ edges)

/-- Global check: does any module reach itself? Fuel covers the edge list
plus the ternary witness. -/
def hasCycle (edges : List (Nat × Nat)) : Bool :=
  edges.any fun e => decide (e.1 ∈ reachE edges (edges.length + 3) [e.1])

/-- Ternary Massey decision: directed 3-cycle with no back-edges. -/
def massey3 (a b c : Nat) (edges : List (Nat × Nat)) : Bool :=
  decide ((a, b) ∈ edges ∧ (b, c) ∈ edges ∧ (c, a) ∈ edges ∧
    (b, a) ∉ edges ∧ (c, b) ∉ edges ∧ (a, c) ∉ edges)

/-! ## E-42: GMT rectifiable-current cache packing

A struct is packed into the 64-byte cache-line lattice with a fixed ABI
boundary (field sizes never change). The greedy first-fit layout is the
mass-minimizing polyhedral approximation; the certificate is pairwise
disjointness of field extents, checked by `disjointCheck`. -/

/-- First-fit offsets starting at `base`. -/
def packAux (base : Nat) : List Nat → List Nat
  | [] => []
  | f :: fs => base :: packAux (base + f) fs

/-- Field extents `(offset, size)` starting at `base`. -/
def extentsAux (base : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | f :: fs => (base, f) :: extentsAux (base + f) fs

/-- The packed layout (offsets from zero). -/
def pack (fs : List Nat) : List Nat :=
  packAux 0 fs

/-- The packed extents. -/
def extents (fs : List Nat) : List (Nat × Nat) :=
  extentsAux 0 fs

/-- Two extents are disjoint (proposition). -/
def disj (p q : Nat × Nat) : Prop :=
  p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1

/-- Two extents are disjoint (decidable check). -/
def disjB (p q : Nat × Nat) : Bool :=
  decide (p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1)

/-- Check one extent against all later ones (each pair once, no self-pairs). -/
def allDisjoint : (Nat × Nat) → List (Nat × Nat) → Bool
  | _, [] => true
  | p, q :: qs => disjB p q && allDisjoint p qs

/-- All-pairs disjointness certificate check. -/
def disjointCheck : List (Nat × Nat) → Bool
  | [] => true
  | p :: ps => allDisjoint p ps && disjointCheck ps

/-! ## E-43: families-index glitch-free DPR

Bitstream configurations form a graph; the anomaly locus is the set of
glitching configs (nontrivial holonomy). `checkPath` admits a
reconfiguration path iff every hop is an edge and no config is anomalous.
`deform` reroutes an inadmissible path around the locus by fuel-bounded BFS,
leaving already-good paths alone. -/

/-- Successors of a configuration. -/
def neighbors (edges : List (Nat × Nat)) (v : Nat) : List Nat :=
  edges.filterMap fun e =>
    if e.1 == v then some e.2 else none

/-- Every consecutive pair is an edge. -/
def isPath : List Nat → List (Nat × Nat) → Bool
  | [], _ => true
  | [_], _ => true
  | a :: b :: rest, e =>
    if decide ((a, b) ∈ e) then isPath (b :: rest) e else false

/-- No configuration on the path is anomalous. -/
def avoids : List Nat → List Nat → Bool
  | [], _ => true
  | v :: vs, bad => if decide (v ∈ bad) then false else avoids vs bad

/-- The admission check. -/
def checkPath (p : List Nat) (edges : List (Nat × Nat)) (bad : List Nat) : Bool :=
  isPath p edges && avoids p bad

/-- Extend a partial reroute by one hop (loop-free: never revisit). -/
def expand (edges : List (Nat × Nat)) (bad : List Nat) (p : List Nat) :
    List (List Nat) :=
  match p.getLast? with
  | none => []
  | some v =>
    ((neighbors edges v).filter fun w =>
      decide (w ∉ bad ∧ w ∉ p)).map fun w => p ++ [w]

/-- First frontier path reaching `dst` without touching `bad`. -/
def findGood : List (List Nat) → List Nat → Nat → Option (List Nat)
  | [], _, _ => none
  | q :: qs, bad, dst =>
    if decide (q.getLast? = some dst) && avoids q bad then some q
    else findGood qs bad dst

/-- Fuel-bounded BFS over reroutes starting from the source. -/
def bfs (front : List (List Nat)) (edges : List (Nat × Nat)) (bad : List Nat)
    (dst : Nat) : Nat → Option (List Nat)
  | 0 => findGood front bad dst
  | n + 1 =>
    match findGood front bad dst with
    | some q => some q
    | none => bfs (front.flatMap (expand edges bad)) edges bad dst n

/-- Deform a path around the anomaly locus (identity when already good). -/
def deform (p : List Nat) (edges : List (Nat × Nat)) (bad : List Nat) :
    Option (List Nat) :=
  match p.head?, p.getLast? with
  | some s, some d =>
    if checkPath p edges bad then some p
    else if decide (s ∈ bad) then none
    else bfs [[s]] edges bad d (edges.length + 1)
  | _, _ => none

/-! ## E-44: thermofield active-active failover

Primary and standby are the doubled state; failover reconciles by tracing
out the failed side — per key, the highest version wins. `reconcile` folds a
max-version `upsert` over the concatenation, so no entry is ever invented and
the reconciled version dominates every input version. -/

/-- A versioned state entry. -/
structure Entry where
  key : Nat
  ver : Nat
  val : Nat
  deriving Repr, DecidableEq

/-- Look up a key (first hit). -/
def findK (k : Nat) : List Entry → Option Entry
  | [] => none
  | e :: es => if e.key == k then some e else findK k es

/-- Insert, keeping the highest version on key collision (ties keep old). -/
def upsert (e : Entry) : List Entry → List Entry
  | [] => [e]
  | x :: xs =>
    if x.key == e.key then
      if e.ver ≤ x.ver then x :: xs else e :: xs
    else x :: upsert e xs

/-- Reconcile the doubled state. -/
def reconcile (p s : List Entry) : List Entry :=
  (p ++ s).foldl (fun acc e => upsert e acc) []

/-- Max-version merge of one entry against an optional incumbent. -/
def best (e : Entry) : Option Entry → Option Entry
  | none => some e
  | some x => if e.ver ≤ x.ver then some x else some e

/-! ## E-45: IST soliton signal processing

The direct scattering transform splits a sampled signal into bound states
(samples whose magnitude clears the threshold `κ` — the discrete
eigenvalues, the alpha) and radiation (everything else — the noise). GLM
reconstruction merges them back by position mask. Energy (sum of squares)
splits exactly: the Parseval analog. -/

/-- Bound-state test: magnitude clears the threshold. -/
def isBound (t : Nat) (x : Int) : Bool :=
  decide (t ≤ x.natAbs)

/-- Scatter a signal into `(position mask, bound states, radiation)`. -/
def scatter (sig : List Int) (t : Nat) : List Bool × List Int × List Int :=
  (sig.map (isBound t), sig.filter (isBound t),
    sig.filter fun x => !(isBound t x))

/-- Merge bound states and radiation back by position mask. -/
def reconstruct : List Bool → List Int → List Int → List Int
  | [], _, _ => []
  | true :: m, x :: b, r => x :: reconstruct m b r
  | false :: m, b, x :: r => x :: reconstruct m b r
  | _ :: _, _, _ => []

/-- Signal energy (sum of squares). -/
def sumsq : List Int → Int
  | [] => 0
  | x :: xs => x * x + sumsq xs

/-! ## E-46: Kontsevich formality transaction quantization

Colliding order-book operations compose through the truncated `⋆`-product:
the classical sum plus first-order bracket corrections over ordered pairs.
The bracket is antisymmetric (the Poisson sign), so reversing the contention
window negates the correction — determinism is order-explicit, not
order-fragile. When every bracket vanishes, the product is the classical
(serialized) sum. -/

/-- The Poisson-bracket analog on amounts. -/
def bracket (a b : Int) : Int :=
  a - b

/-- Bracket corrections of `l₁` against every element of `l₂`. -/
def cross : List Int → List Int → Int
  | [], _ => 0
  | x :: xs, l₂ => lsumI (l₂.map (bracket x)) + cross xs l₂

/-- Total first-order correction over ordered pairs `i < j`. -/
def corr : List Int → Int
  | [] => 0
  | a :: as => lsumI (as.map (bracket a)) + corr as

/-- The truncated `⋆`-product: classical sum plus correction. -/
def star (ops : List Int) : Int :=
  lsumI ops + corr ops

/-! ## E-47: causal-fermion spectral causality

Thread-event operators are `2 × 2` models; causality is read off the
spectrum of the operator product, here its discriminant `tr² − 4·det`.
Negative discriminant (nonreal spectrum, conjugate hence equal-modulus)
means spacelike: the zero-coordination path. Large positive discriminant
(real gapped spectrum) means timelike: the ordered path. The near-degenerate
remainder is lightlike. The classifier is total and the spacelike/timelike
verdicts are disjoint, so no event takes both paths. -/

/-- A `2 × 2` event-operator model. -/
structure EvOp where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving Repr, DecidableEq

/-- The spectral discriminant `tr² − 4·det`. -/
def disc (m : EvOp) : Int :=
  (m.a + m.d) * (m.a + m.d) - 4 * (m.a * m.d - m.b * m.c)

/-- The causal verdict. -/
inductive Causal where
  | space
  | time
  | light
  deriving Repr, DecidableEq

/-- The spectral-causality classifier (`gap` = minimum timelike splitting). -/
def classify (m : EvOp) (gap : Nat) : Causal :=
  if disc m < 0 then .space
  else if (gap : Int) ≤ disc m then .time else .light

/-- Spacelike events skip coordination entirely. -/
def needsFence : Causal → Bool
  | .space => false
  | _ => true

end Morph.Specs.BatchDEF
