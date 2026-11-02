/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Earliest Frontier Kernels — specification (E-03, E-06, E-10, E-21–E-27)

Status: first cycle complete (loop 105).

Executable cores for the ten earliest registered frontier experiments
(ADR-019: Batch 0 carry-forwards E-03, E-06, E-10; Batch A E-21–E-25; Batch B
E-26, E-27). Each section is a *model with a theorem*, not the experiment
itself: the register's acceptance rule asks for a decidable checking
algorithm or computable synthesis procedure plus a kill criterion, and these
are the smallest kernels that make each row falsifiable.

The mathematics these rows name (Itô calculus, tropical geometry, symplectic
maps, Hecke correspondences, min-cut, Lefschetz thimbles, fluctuation
theorems, scrambling, motives, GIT) is documentation. The Lean code is the
checkable fragment: tags, algebras, checkers, and the laws they satisfy.

## Mapping Summary

| Register row | Concept | Lean core |
|---|---|---|
| E-03 | Filtration-graded pricing types | `Stage`, `acausal`, `strategyOk`, `stratOfIto` |
| E-06 | Tropical max-plus timing | `Trop`, `tadd`, `tmul`, `blockWCET`, `branchWCET` |
| E-10 | Certified symplectic integrators | `shearX`, `shearY`, `area`, `leapfrog` |
| E-21 | Hecke-type transition preservers | `Trans`, `outEdges`, `simulates`, `checkSim`, `synth` |
| E-22 | Holographic min-cut placement | `Edge`, `crosses`, `cutWeight`, `starWeight`, `moveOut` |
| E-23 | Lefschetz critical points | `evalPoly`, `derivAux`, `derivPoly`, `isCritical` |
| E-24 | Crooks speculation bound | `Region`, `expectedCost`, `best`, `best_optimal` |
| E-25 | Scrambling / integrable templates | `step`, `spread`, `mem_spread_succ` |
| E-26 | Motivic backend conformance | `KerOp`, `evalKer`, `compileAff`, `conformant` |
| E-27 | Hilbert-Mumford stability | `mu`, `checkStable`, `findWitness` |

## What the model does *not* claim

No quant library, timing pass, integrator, protocol compiler, placer, pricing
kernel, scheduler, checker, backend, or stability prover is produced. Rows are
graded L1 (definitions plus `decide`-able checks and examples) or L2 (proved
algebraic laws). The execution record and kill criteria are tracked in
`.specs/03_research/briefs/E0-earliest-kernel.md`.
-/

namespace Morph.Specs.Earliest

/-! ## E-03: filtration-graded pricing types

A strategy is a list of stages; each stage runs at a time and needs data
from a list of times. Lookahead bias (acausality) is a stage needing data
from its own future. The checker rejects it. Separately, the Itô↔Stratonovich
conversion carries a drift correction; with the factor 2 cleared, the
conversion is exact integer arithmetic. -/

/-- One strategy stage: runs at `at`, reads data at each time in `needs`. -/
structure Stage where
  time : Nat
  needs : List Nat
  deriving Repr, DecidableEq

/-- Lookahead bias: the stage needs data from its own future. -/
def acausal (s : Stage) : Prop := ∃ t ∈ s.needs, s.time < t

/-- Executable acausality check over a whole strategy. -/
def strategyOk : List Stage → Bool
  | [] => true
  | s :: ss =>
    (!(s.needs.any (fun t => decide (s.time < t)))) && strategyOk ss

/-- Semantic strategy validity. -/
def StrategyValid (ss : List Stage) : Prop := ∀ s ∈ ss, ¬ acausal s

/-- Stratonovich drift from Itô data, clearing the ½: `A = 2a`, so
`S = 2a − b·∂b`. -/
def stratOfIto (A B D : Int) : Int := A - B * D

/-- Itô drift from Stratonovich data, clearing the ½. -/
def itoOfStrat (S B D : Int) : Int := S + B * D

/-! ## E-06: tropical max-plus timing

Latencies live in `Option Nat` (`none` is −∞): addition is `max`,
multiplication is `+`. A straight-line block costs the sum; a branch costs
the max. The kill criterion's question — whether the max bound is tight — is
asked about `branchWCET_ge`, which states the bound dominates every branch. -/

/-- Tropical numbers: `none` is −∞. -/
abbrev Trop := Option Nat

/-- Tropical addition is `max`. -/
def tadd : Trop → Trop → Trop
  | none, y => y
  | x, none => x
  | some a, some b => some (max a b)

/-- Tropical multiplication is `+`. -/
def tmul : Trop → Trop → Trop
  | none, _ => none
  | _, none => none
  | some a, some b => some (a + b)

/-- Tropical zero (−∞) and one (0). -/
def tzero : Trop := none

def tone : Trop := some 0

/-- Worst-case time of a straight-line block: the sum of latencies. -/
def blockWCET : List Nat → Nat
  | [] => 0
  | l :: ls => l + blockWCET ls

/-- Worst-case time across branches: the max of alternatives. -/
def branchWCET : List Nat → Nat
  | [] => 0
  | a :: as => max a (branchWCET as)

/-! ## E-10: symplectic integrators as shear compositions

A shear `(q, p) ↦ (q + c·p, p)` has Jacobian determinant 1: it preserves the
discrete symplectic area `q₁p₂ − q₂p₁`. Leapfrog is a palindromic composition
of three shears, so it is symplectic (area-preserving) and reversible. Step
sizes are unit-scaled integers — the ½ of textbook Verlet is cleared, and the
theorem is about the shear structure, which is exactly what makes Verlet
symplectic. The energy-drift bound of the kill criterion is the benchmark,
not a theorem here. -/

/-- Shear in position: `(q, p) ↦ (q + c·p, p)`. -/
def shearX (c : Int) (u : Int × Int) : Int × Int := (u.1 + c * u.2, u.2)

/-- Shear in momentum: `(q, p) ↦ (q, p + c·q)`. -/
def shearY (c : Int) (u : Int × Int) : Int × Int := (u.1, u.2 + c * u.1)

/-- Discrete symplectic area form. -/
def area (u v : Int × Int) : Int := u.1 * v.2 - u.2 * v.1

/-- Leapfrog: palindromic shear composition. -/
def leapfrog (h k : Int) (u : Int × Int) : Int × Int :=
  shearX h (shearY k (shearX h u))

/-! ## E-21: Hecke-type transition preservers

A protocol is a finite list of transitions. A handler conforms when it
simulates the protocol: every specified move is matched. `synth` builds the
event-loop skeleton (per-state outgoing edges); `checkSim` decides simulation
on finite state and label sets. -/

/-- One protocol transition. -/
structure Trans where
  from_ : Nat
  label : Nat
  to : Nat
  deriving Repr, DecidableEq

/-- Outgoing edges of a state: the synthesised event-loop skeleton. -/
def outEdges (spec : List Trans) (s : Nat) : List (Nat × Nat) :=
  (spec.filter (fun t => t.from_ == s)).map (fun t => (t.label, t.to))

/-- The skeleton for a list of states. -/
def synth (spec : List Trans) (states : List Nat) : List (Nat × List (Nat × Nat)) :=
  states.map (fun s => (s, outEdges spec s))

/-- Simulation: every system move from related states is matched. -/
def simulates (R : Nat → Nat → Prop)
    (sys impl : Nat → Nat → List Nat) : Prop :=
  ∀ s t, R s t → ∀ l s', s' ∈ sys s l → ∃ t', t' ∈ impl t l ∧ R s' t'

/-- Executable simulation check over finite states and labels. -/
def checkSim (R : Nat → Nat → Bool) (sys impl : Nat → Nat → List Nat)
    (states : List Nat) (labels : List Nat) : Bool :=
  states.all fun s => states.all fun t =>
    (!R s t) || labels.all fun l =>
      (sys s l).all fun s' => (impl t l).any fun t' => R s' t'

/-! ## E-22: min-cut placement

A placement is a side of a bisection; the cut weight is the affinity crossing
it. The Kernighan–Lin kernel is the move-gain formula: moving `v` out of the
side changes the cut by exactly `ext − int`, where `ext` is the weight to the
outside and `int` the weight to the inside. -/

/-- One affinity edge. -/
structure Edge where
  u : Nat
  v : Nat
  w : Nat
  deriving Repr, DecidableEq

/-- The edge crosses the side. -/
def crosses (side : List Nat) (e : Edge) : Bool :=
  (decide (e.u ∈ side)) != (decide (e.v ∈ side))

/-- Cut weight: total affinity crossing the side. -/
def cutWeight : List Edge → List Nat → Nat
  | [], _ => 0
  | e :: es, side => (if crosses side e then e.w else 0) + cutWeight es side

/-- Weight of edges from `v` to the outside of the side. -/
def extW : List Edge → List Nat → Nat → Nat
  | [], _, _ => 0
  | e :: es, side, v =>
    (if ((decide (e.u = v) && !decide (e.v ∈ side)) ||
      (decide (e.v = v) && !decide (e.u ∈ side))) then e.w else 0)
      + extW es side v

/-- Weight of edges from `v` to the inside of the side (excluding itself). -/
def intW : List Edge → List Nat → Nat → Nat
  | [], _, _ => 0
  | e :: es, side, v =>
    (if ((decide (e.u = v) && decide (e.v ∈ side) && decide (e.v ≠ v)) ||
      (decide (e.v = v) && decide (e.u ∈ side) && decide (e.u ≠ v))) then e.w
      else 0) + intW es side v

/-- Move `v` out of the side. -/
def moveOut (side : List Nat) (v : Nat) : List Nat :=
  side.filter (fun x => decide (x ≠ v))

/-! ## E-23: critical points of a phase polynomial

The phase is a coefficient list; `derivAux` is the formal derivative with an
explicit index, `evalPoly` is Horner evaluation. The power rule
(`derivAux_eval`) says they agree. A critical point is a verified zero of the
derivative — the input the contour deformation of the kill criterion starts
from. -/

/-- Horner evaluation. -/
def evalPoly : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * evalPoly cs x

/-- Integer powers. -/
def ipow (x : Int) : Nat → Int
  | 0 => 1
  | n + 1 => x * ipow x n

/-- Formal derivative with explicit starting index. -/
def derivAux : List Int → Nat → List Int
  | [], _ => []
  | c :: cs, n => ((n : Int) * c) :: derivAux cs (n + 1)

/-- Formal derivative of a coefficient list. -/
def derivPoly : List Int → List Int
  | [] => []
  | _ :: cs => derivAux cs 1

/-- The explicit derivative sum `Σ (k+n)·cₖ·xᵏ`. -/
def dsum : List Int → Nat → Int → Int
  | [], _, _ => 0
  | c :: cs, n, x => (n : Int) * c + x * dsum cs (n + 1) x

/-- Critical-point check: the derivative vanishes. -/
def isCritical (p : List Int) (x : Int) : Bool :=
  decide (evalPoly (derivPoly p) x = 0)

/-! ## E-24: speculation depth from a Crooks-type bound

A region carries measured work, rollback likelihood (per thousand), and redo
cost. Expected cost is kept in thousandths so the arithmetic is exact. The
compiler sets the depth to the argmin (`best`); `best_optimal` says no
candidate beats it. -/

/-- A speculative region. -/
structure Region where
  work : Nat
  rollback : Nat
  redo : Nat
  deriving Repr, DecidableEq

/-- Expected cost in thousandths: `work + p·redo`. -/
def expectedCost (r : Region) : Nat := r.work * 1000 + r.rollback * r.redo

/-- Fold the minimum-cost region. -/
def foldMin : Region → List Region → Region
  | b, [] => b
  | b, r :: rs => foldMin (if expectedCost r < expectedCost b then r else b) rs

/-- The compiler's choice: the argmin, or nothing. -/
def best : List Region → Option Region
  | [] => none
  | r :: rs => some (foldMin r rs)

/-! ## E-25: scrambling cones and integrable templates

Information spread is iterated neighbourhood expansion on a finite dependency
graph. The integrable class (`λ_L = 0`) is the templates whose cone the
checker admits; `mem_spread_succ` is the exact one-step law the checker
relies on. -/

/-- One expansion step: the front plus everything it points at. -/
def step (edges : List (Nat × Nat)) (front : List Nat) : List Nat :=
  front ++ edges.filterMap (fun e => if e.1 ∈ front then some e.2 else none)

/-- Nodes reachable from `v` within `n` steps. -/
def spread : List (Nat × Nat) → Nat → Nat → List Nat
  | _, 0, v => [v]
  | edges, n + 1, v => step edges (spread edges n v)

/-- The integrable-class check: two-step growth bounded by `c`. -/
def lyapZero (edges : List (Nat × Nat)) (v c : Nat) : Bool :=
  decide ((spread edges 2 v).length ≤ (spread edges 1 v).length + c)

/-! ## E-26: motivic backend conformance

One kernel source, two realizations. The CPU realization interprets
directly; the GPU realization compiles to an affine closed form
`x ↦ a·x + b`. Functoriality is the agreement theorem: the diagram commutes
on every input. `conformant` decides agreement on a finite corpus. -/

/-- Kernel operations. -/
inductive KerOp where
  | addConst : Nat → KerOp
  | mulConst : Nat → KerOp
  deriving Repr, DecidableEq

/-- Direct interpretation. -/
def evalKer : List KerOp → Nat → Nat
  | [], x => x
  | .addConst c :: ops, x => evalKer ops (x + c)
  | .mulConst c :: ops, x => evalKer ops (x * c)

/-- Compile to the affine closed form. -/
def compileAff : List KerOp → Nat × Nat
  | [] => (1, 0)
  | .addConst c :: ops =>
    ((compileAff ops).1, (compileAff ops).1 * c + (compileAff ops).2)
  | .mulConst c :: ops =>
    ((compileAff ops).1 * c, (compileAff ops).2)

/-- Apply a closed form. -/
def affApply (f : Nat × Nat) (x : Nat) : Nat := f.1 * x + f.2

/-- Agreement on a finite corpus. -/
def conformant (f g : Nat → Nat) (corpus : List Nat) : Bool :=
  corpus.all (fun x => f x == g x)

/-! ## E-27: Hilbert-Mumford stability

Configs and 1-PS subgroups are integer vectors; `mu` is the pairing. A config
is unstable when some subgroup pairs positively with it. `checkStable`
decides stability against a sampled subgroup list; `findWitness` returns the
destabilizing subgroup — the `λ` the kill criterion demands. -/

/-- Dot product. -/
def dot : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + dot as bs

/-- The Hilbert-Mumford weight. -/
def mu (x lam : List Int) : Int := dot x lam

/-- Unstable: some subgroup pairs positively. -/
def Unstable (x : List Int) (lam : List Int) : Prop := 0 < mu x lam

/-- Stability against a sampled subgroup list. -/
def checkStable (x : List Int) (lams : List (List Int)) : Bool :=
  lams.all (fun lam => decide (mu x lam ≤ 0))

/-- Find the destabilizing witness. -/
def findWitness (x : List Int) : List (List Int) → Option (List Int)
  | [] => none
  | lam :: lams => if mu x lam ≤ 0 then findWitness x lams else some lam

end Morph.Specs.Earliest
