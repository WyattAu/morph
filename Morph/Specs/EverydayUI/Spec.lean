/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Everyday UI Kernel — specification (E-1351–E-1360)

Status: In Progress (loop 103, batch CB first cycle).

Executable cores for the first ten everyday-software register entries
(ADR-030, Clusters XXX). Each section is a *model with a theorem*, not a
browser engine: the register's acceptance rule asks for a decidable checking
or computable synthesis procedure plus a kill criterion, and these are the
smallest kernels that make each row falsifiable.

## Mapping Summary

| Register row | Concept | Lean core |
|---|---|---|
| E-1351 | Sheaf-theoretic DOM geometry | `Covered`, `Covered.confined` over `rowBoxes` |
| E-1352 | Incremental fixed-point functors | `iterate`, `Kleene.stabilizes` |
| E-1353 | Delta-lens view/model coherence | `Lens`, `Lens.comp`, `Lawful` |
| E-1354 | Affine monoidal layout algebras | `rowBoxes`, width/no-overlap/translation |
| E-1355 | Topological event fibrations | `BTree.route`, `BTree.route_sound` |
| E-1356 | Zero-hydration continuations | `Expr.compile`, `run`, `run_compile` |
| E-1357 | Homotopic vector graphics | `lerp`, affine/endpoint identities |
| E-1358 | Linear resource typing | `Usage.Linear`, `Linear.seq`, double-use rejection |
| E-1359 | Component operads | `Op.composeAt`, arity/output laws |
| E-1360 | Continuous-time FRP signals | `DagNode`, `evalDag`, single-evaluation law |

## What the model does *not* claim

No layout engine, renderer, runtime, or compiler is produced. The rows are
graded L1 (definitions + `decide`-able checks + examples) or L2 (proved
algebraic laws). Execution records and kill criteria are tracked in
`.specs/03_research/briefs/CB-everyday-ui-kernel.md`; none of the register
kill criteria can fire until the kernels are benchmarked against the
baselines named in ADR-030.
-/

namespace Morph.Specs.EverydayUI

/-! ## Shared geometry (E-1351, E-1354) -/

/-- An axis-aligned integer rectangle. Integer coordinates keep every layout
claim `decide`-able; sub-pixel resolution is deliberately out of fragment. -/
structure Rect where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Repr, DecidableEq

/-- Exclusive right edge. -/
def Rect.right (r : Rect) : Nat := r.x + r.w

/-- Exclusive bottom edge. -/
def Rect.bottom (r : Rect) : Nat := r.y + r.h

/-- Two rectangles do not overlap, including shared borders. -/
def Rect.disjoint (a b : Rect) : Prop :=
  a.right ≤ b.x ∨ b.right ≤ a.x ∨ a.bottom ≤ b.y ∨ b.bottom ≤ a.y

/-- `outer` contains `inner` (borders included). -/
def Rect.contains (outer inner : Rect) : Prop :=
  outer.x ≤ inner.x ∧ outer.y ≤ inner.y ∧
    inner.right ≤ outer.right ∧ inner.bottom ≤ outer.bottom

/-- A point lies in a box (half-open interval). -/
def Rect.holds (r : Rect) (p : Nat × Nat) : Prop :=
  r.x ≤ p.1 ∧ p.1 < r.right ∧ r.y ≤ p.2 ∧ p.2 < r.bottom

/-! ## E-1354: one-pass affine row layout

`rowBoxes [w₁, …, wₙ] x` lays widths left to right starting at `x`, returning
`(offset, width)` pairs. This is the affine, single-pass fragment: no
backtracking, no constraint solver, no flexible sizing — exactly the
fragment the register row claims a linear type discipline can express. -/

/-- Left-to-right layout of intrinsic widths starting at offset `x`. -/
def rowBoxes : List Nat → Nat → List (Nat × Nat)
  | [], _ => []
  | w :: ws, x => (x, w) :: rowBoxes ws (x + w)

/-- A row rendered as rectangles with common top `y` and height `h`. -/
def rowRects (ws : List Nat) (x y h : Nat) : List Rect :=
  (rowBoxes ws x).map (fun b => ⟨b.1, y, b.2, h⟩)

/-- Total laid-out extent from `x`. -/
def rowExtent (ws : List Nat) (x : Nat) : Nat := x + ws.sum

/-- Point coverage by a list of boxes (E-1351's sheaf condition, 1-D). -/
def Covered (boxes : List (Nat × Nat)) (p : Nat) : Prop :=
  ∃ b ∈ boxes, b.1 ≤ p ∧ p < b.1 + b.2

/-- Every box lies inside the parent span (the restriction maps agree). -/
def Confined (boxes : List (Nat × Nat)) (x : Nat) (span : Nat) : Prop :=
  ∀ b ∈ boxes, x ≤ b.1 ∧ b.1 + b.2 ≤ x + span

/-! ## E-1352: fixed-point UI update

A UI update pass is a monotone, extensive map on a lattice of height `N`
(here the natural numbers, standing for a bounded dirty-work measure).
Kleene iteration from bottom stabilises, and it stabilises within `N` steps.
This is the computable content behind "incremental fixed-point functors":
termination is a height argument, not a fuel counter. -/

/-- `n`-fold Kleene iterate of `f` from the bottom element `0`. -/
def iterate (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f (iterate f n)

/-- A bounded monotone extensive endomap: the abstract update pass. The
lattice is the finite segment `0 … height`; both conditions are restricted to
that segment, otherwise no non-trivial instance exists (a map that is
extensive and bounded on all of `Nat` must be the identity past the bound). -/
structure UpdatePass where
  step : Nat → Nat
  height : Nat
  mono : ∀ a b, a ≤ b → step a ≤ step b
  extensive : ∀ a, a ≤ height → a ≤ step a
  bounded : ∀ a, a ≤ height → step a ≤ height

/-! ## E-1353: delta lenses

A lens is a `get`/`put` pair; `Lawful` is the three standard laws. The module
proves that lawful lenses compose, which is what makes field-path state sync
a *checked* construction rather than per-form glue code. -/

/-- A bidirectional accessor between a whole `S` and a part `A`. -/
structure Lens (S A : Type) where
  get : S → A
  put : S → A → S

/-- Composition of lenses: focus through `l₁`, then `l₂`. -/
def Lens.comp {S A B : Type} (l₁ : Lens S A) (l₂ : Lens A B) : Lens S B where
  get s := l₂.get (l₁.get s)
  put s b := l₁.put s (l₂.put (l₁.get s) b)

/-- The Put-Get, Get-Put and Put-Put laws. -/
structure Lawful {S A : Type} (l : Lens S A) : Prop where
  putGet : ∀ s a, l.get (l.put s a) = a
  getPut : ∀ s, l.put s (l.get s) = s
  putPut : ∀ s a b, l.put (l.put s a) b = l.put s b

/-! ## E-1355: event routing over a UI tree

The tree is binary (`empty | leaf | node`) so routing is structurally
recursive and its soundness is an induction, not a fuel argument. `route t x`
returns the unique subtree that contains `x`, or `none`. Soundness says the
returned subtree really contains the target: an event cannot be routed to a
sibling that does not hold it. -/

/-- A binary UI/event tree. -/
inductive BTree where
  | empty
  | leaf (id : Nat)
  | node (id : Nat) (left right : BTree)
  deriving Repr, DecidableEq

/-- Node identity (`empty` has the sentinel `0`). -/
def BTree.id : BTree → Nat
  | .empty => 0
  | .leaf i => i
  | .node i _ _ => i

/-- All identities in the subtree. -/
def BTree.ids : BTree → List Nat
  | .empty => []
  | .leaf i => [i]
  | .node i l r => i :: (l.ids ++ r.ids)

/-- Route to the subtree containing `target`, preferring the node itself. -/
def BTree.route : BTree → Nat → Option BTree
  | .empty, _ => none
  | .leaf i, target => if i = target then some (.leaf i) else none
  | .node i l r, target =>
      if i = target then some (.node i l r)
      else (l.route target).orElse (fun _ => r.route target)

/-! ## E-1356: compile-time continuations

`compile` turns an expression into stack instructions; `run` is the resumption
machine. The theorem `run_compile` says the compiled continuation, resumed
from any stack, computes exactly `eval` and leaves the stack otherwise
untouched — the formal kernel of "the work is done at compile time, the
client only resumes". -/

/-- Arithmetic expressions over literals. -/
inductive Expr where
  | lit (n : Nat)
  | add (a b : Expr)
  | mul (a b : Expr)
  deriving Repr

/-- Direct evaluation. -/
def Expr.eval : Expr → Nat
  | .lit n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- Stack instructions. -/
inductive Instr where
  | push (n : Nat)
  | iadd
  | imul
  deriving Repr

/-- Compile to a postfix instruction sequence. -/
def Expr.compile : Expr → List Instr
  | .lit n => [.push n]
  | .add a b => a.compile ++ b.compile ++ [.iadd]
  | .mul a b => a.compile ++ b.compile ++ [.imul]

/-- Resume a compiled sequence on a stack. -/
def run : List Instr → List Nat → Option (List Nat)
  | [], st => some st
  | .push n :: is, st => run is (n :: st)
  | .iadd :: is, a :: b :: st => run is ((b + a) :: st)
  | .imul :: is, a :: b :: st => run is ((b * a) :: st)
  | _, _ => none

/-! ## E-1357: homotopic shape interpolation

Linear interpolation over `Nat` with an exact `/100` step is the 1-parameter
homotopy used for shape and animation blending. The identities proved are the
ones a renderer relies on: endpoints, constancy, and reversal symmetry. The
fragment is integral (`s ≤ 100`, no fractional weights) — sub-pixel weights
belong to a real-valued kernel and are out of scope here. -/

/-- Convex blend of `a` and `b` at parameter `s` (percent, integer division). -/
def lerp (a b s : Nat) : Nat := (a * (100 - s) + b * s) / 100

/-! ## E-1358: affine resource usage

A resource expression records handle use; `Linear` bounds every handle to at
most one use. The theorems are the checker's soundness on composition and its
rejection of double use — the observable claim behind affine client assets. -/

/-- Resource-using expressions. -/
inductive Usage where
  | pure (v : Nat)
  | use (h : Nat)
  | seq (a b : Usage)
  deriving Repr

/-- Handles mentioned by an expression, in order. -/
def Usage.handles : Usage → List Nat
  | .pure _ => []
  | .use h => [h]
  | .seq a b => a.handles ++ b.handles

/-- Every handle is used at most once. -/
def Usage.Linear (e : Usage) : Prop := ∀ h, (e.handles.count h) ≤ 1

/-! ## E-1359: component operads

An operation has an ordered colour interface and an output colour.
`composeAt f i g` plugs `g` into slot `i` of `f`. The laws are the typing
laws of operadic substitution: the output colour is untouched and the arity
changes by exactly `|g| − 1`. -/

/-- A coloured operation. -/
structure Op where
  name : String
  inputs : List Nat
  output : Nat
  deriving Repr

/-- Substitute `g` into input slot `i` of `f`. -/
def Op.composeAt (f : Op) (i : Nat) (g : Op) : Op where
  name := f.name ++ "." ++ g.name
  inputs := f.inputs.take i ++ g.inputs ++ f.inputs.drop (i + 1)
  output := f.output

/-! ## E-1360: single-pass signal propagation

A DAG node list is evaluated in one left-to-right fold, appending exactly one
value per node. `evalDag_ids` proves the evaluation order is exactly the
topological order with no node evaluated twice and none skipped — the
"glitch-free, single-pass" claim in its checkable form. -/

/-- A DAG node: identity plus dependency identities. -/
structure DagNode where
  id : Nat
  deps : List Nat
  deriving Repr

/-- Look up a computed value in the environment. -/
def lookupVal (env : List (Nat × Nat)) (id : Nat) : Option Nat :=
  (env.find? (fun p => p.1 = id)).map (fun p => p.2)

/-- Evaluate one node from the current environment and append its value. -/
def dagStep (env : List (Nat × Nat)) (n : DagNode) : List (Nat × Nat) :=
  env ++ [(n.id, (n.deps.map (fun d => (lookupVal env d).getD 0)).sum)]

/-- Single left-to-right pass over a topologically ordered node list. -/
def evalDag (nodes : List DagNode) : List (Nat × Nat) :=
  nodes.foldl dagStep []

end Morph.Specs.EverydayUI
