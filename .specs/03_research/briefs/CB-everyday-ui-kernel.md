# Experiment Brief — Batch CB, first cycle (E-1351–E-1360)

**Status:** first cycle complete (loop 103, 2026-10-31).
**Register rows:** ADR-030, batch CB (Clusters XXX: UI, web runtimes,
reactive engines).
**Artifact:** `Morph/Specs/EverydayUI/{Spec,Lemmas,Examples}.lean`,
`Morph/Tests/EverydayUI.lean`.
**Grade now:** model L3 (no `sorry`, no axiom, warning-free build) for the
formal kernel; **claim L1** for the register row, because no baseline was
benchmarked. The two grades are deliberately separate — see §5.

---

## 1. What was built, and what was not

The ten rows are engines/systems claims ("sheaf-theoretic DOM geometry
replaces CSS reflow"). Building those is out of scope for one cycle and would
be dishonest to claim. What was built is the *computable core* each row needs
to be falsifiable, in the register's own terms (ADR-019 §1: a decidable
checking algorithm or computable synthesis procedure, plus a kill criterion):

| Row | Kernel built | Key result |
|---|---|---|
| E-1351 | `Covered`, `Confined`, `rowBoxes_covered` | every point of a row's span is covered by a child box, and every box is confined to the parent span |
| E-1352 | `iterate`, `UpdatePass` | extensive bounded passes stabilise within `height` steps (Kleene, no fuel counter) |
| E-1353 | `Lens`, `Lens.comp`, `Lawful` | lawful lenses compose (Put-Get, Get-Put, Put-Put preserved) |
| E-1354 | `rowBoxes`, `rowRects` | widths preserved, no overlap, translation invariance, rendered rectangles pairwise disjoint |
| E-1355 | `BTree.route` | routing lands only in a subtree that contains the target |
| E-1356 | `Expr.compile`, `run` | compiled continuations resume to `eval`, leaving the rest of the stack intact |
| E-1357 | `lerp` | endpoints, constancy, reversal symmetry of the blend |
| E-1358 | `Usage`, `Usage.Linear` | linearity projects through `seq`, single uses accepted, double use rejected |
| E-1359 | `Op.composeAt` | operadic substitution preserves the output colour and changes arity by `|g| − 1` |
| E-1360 | `evalDag` | one value emitted per node, in topological order, none twice |

Not built: a layout engine, a renderer, a reconciler, a runtime, a compiler,
a GPU path, an event system, a resource checker, an operad library, a
signal engine. No browser or JavaScript code was written. Every row remains
an experiment whose *external* claim is untested.

## 2. Research basis (per row)

- **E-1351.** Sheaves on a poset: a section is a compatible family, and
  compatibility is exactly the restriction-map condition. Standard sources:
  Mac Lane–Moerdijk, *Sheaves in Geometry and Logic*; Curry, *Sheaves,
  Cosheaves and Applications* (2014) for the computational reading. The
  layout reading is the classical one: CSS 2.1 §9–10 defines the box model
  and the containing-block relation, which is a poset; reflow is the repair
  of an inconsistent section. The 1-D row is the smallest poset with a
  non-trivial gluing condition, so coverage + confinement is the kernel.
- **E-1352.** Kleene iteration and the Cousot–Cousot fixpoint framework
  (POPL 1979): an increasing chain in a finite-height lattice stabilises, and
  the height bounds the number of steps. The UI reading is incremental
  rendering (React Fiber's interruptible reconciliation as the engineering
  baseline). The kernel is the height argument, not a scheduler.
- **E-1353.** Foster, Greenwald, Moore, Pierce, Schmitt, "Combinators for
  Bidirectional Tree Transformations" (TOPLAS 2007) — the three lens laws and
  composition. The kernel is composition, because field-path state sync is
  built by composing accessors; if composition did not preserve the laws,
  every composed path would need its own proof.
- **E-1354.** Affine/linear typing (Walker, "Substructural Type Systems",
  2005) applied to layout: each box is consumed once, so layout is a single
  pass with no backtracking. The engineering baseline it targets is
  constraint layout (Cassowary, Badros et al. 2001) and flex/grid solving.
  The kernel states what the affine fragment buys: widths preserved, boxes
  disjoint, translation invariant.
- **E-1355.** Event propagation in the DOM (WHATWG DOM standard: capture,
  target, bubble) is a tree walk; the fiber-bundle metaphor contributes the
  idea of routing along a base. The falsifiable part is soundness: the
  routed subtree contains the target. That is what `BTree.route_sound`
  proves, and it is the property a misrouting bug violates.
- **E-1356.** Delimited continuations (Danvy–Filinski, LFP 1990) and the
  CEK/SECD machine tradition (Felleisen–Friedman 1986). The kernel is the
  standard compiler-correctness theorem for a stack machine; it is the
  formal content of "serialize the continuation and resume it", which is
  what zero-hydration claims. Hydration itself (framework behaviour) is the
  untested baseline.
- **E-1357.** Homotopy/linear interpolation; resolution-independent curve
  rendering (Loop–Blinn, SIGGRAPH 2005) as the graphics context. The
  integral `/100` fragment is deliberate: exact integer weights keep the
  identities decidable. Sub-pixel weights need a real-valued kernel, which
  is out of fragment and recorded as such.
- **E-1358.** Affine/linear types again, and Rust's ownership discipline as
  the engineering baseline (Weiss et al., "Oxide: The Essence of Rust",
  2019). The kernel's job is to reject double use; the validation caught
  that the naive composition rule is *false* (two linear fragments can share
  a handle), which is exactly the bug an affine client-asset checker must
  not have.
- **E-1359.** Coloured operads (May 1972; Leinster, *Higher Operads, Higher
  Categories*, 2004). Component composition is operadic substitution:
  plugging a component into a slot. The typing laws (output colour fixed,
  arity changes by `|g| − 1`) are the checkable part; prop-drilling is the
  engineering baseline.
- **E-1360.** Functional reactive programming (Elliott–Hudak, ICFP 1997) and
  differential dataflow (McSherry et al., CIDR 2013) as the incremental
  baseline. The kernel's theorem is the single-evaluation/ordering property:
  one value per node, in listed order. Glitch freedom in the full sense
  (no intermediate inconsistent observation) is not proved and is listed as
  the next iteration's target.

## 3. Design decisions

1. **One module family, ten sections.** ADR-019 allows a brief to cover a
   coherent row family; the three-file pattern (ADR-004) forbids extra files
   per domain. `EverydayUI` holds all ten cores, with a mapping table in the
   `Spec.lean` docstring. Rows are separable into their own modules later
   without changing definitions.
2. **Integer geometry.** `Rect` is `Nat`-valued. This keeps every layout
   claim decidable and every theorem elementary; it excludes sub-pixel
   effects by construction, which is stated rather than hidden.
3. **Binary event tree.** The tree is `empty | leaf | node l r` so routing
   is structurally recursive. A list-of-children tree would need a fuel or
   well-founded argument for the same theorem; the binary encoding is a
   faithful model of a DOM-ish tree and keeps the soundness proof an
   induction.
4. **Continuations as a stack machine.** No `Cont` monad: the compiled
   instruction list *is* the continuation, and `run_append` is its
   composition law. This is closer to what a runtime resumes.
5. **Bounded pass model.** `UpdatePass` restricts extensivity and
   boundedness to `0 … height`. The first draft stated them globally on
   `Nat`, which is **unsatisfiable** (`a ≤ f a ≤ N` for `a > N`); the
   validation stage caught the vacuity and the model was corrected. The
   stabilisation proof does not actually need monotonicity, and the lemma
   says so; `mono` stays as a modelling constraint.
6. **Scaled interpolation.** `lerp` divides by 100; the identity set is
   chosen so the division is exact. No real-number library was introduced.

## 4. Implementation map and proof burden

| File | Lines | Content |
|---|---|---|
| `Morph/Specs/EverydayUI/Spec.lean` | 303 | 10 cores, mapping table, scope statement |
| `Morph/Specs/EverydayUI/Lemmas.lean` | 440 | 37 theorems, no `sorry`, no axioms |
| `Morph/Specs/EverydayUI/Examples.lean` | 191 | 40+ concrete instances, incl. law witnesses |
| `Morph/Tests/EverydayUI.lean` | 178 | 30+ independent checks, incl. negative cases |

Proof burden: 37 theorems over ~300 lines of definitions (ratio ≈ 1.2 proof
lines per definition line, excluding comments). All proofs are manual
`induction`/`simp`/`omega`; no SMT, no automation beyond core tactics. No
core file (`Morph.HIR`, `Morph.MIR`, `Morph.Semantics`) was touched, per the
register's trusted-core rule.

Build record (warm cache, this machine):

- `lake build Morph.Specs.EverydayUI.Lemmas` — 3.0–7.2 s.
- `lake build Morph.Tests.EverydayUI` — 1.5–3.9 s (incremental).
- `lake build Morph Morph.Tests` — 412 jobs, success, 0 warnings, 0 `sorry`
  in the new files.

## 5. Validation log — what the cycle caught

The cycle is only worth its cost if it found defects. It found four:

1. **Vacuous fixpoint model (E-1352).** Global `a ≤ f a` + `f a ≤ N` on
   `Nat` is inconsistent, so the theorem was true but empty. Fixed by
   restricting both hypotheses to the finite segment and adding
   `iterate_bounded`; the example pass (`cappedPass`) is now a real witness.
2. **False composition law (E-1358).** "Sequences of linear fragments are
   linear" is false: `use x; use x` is a counterexample. Replaced with the
   correct projection theorem plus an explicit rejection theorem; the gap
   (the disjointness side-condition) is recorded in §7.
3. **Undecidable test propositions.** `Rect.disjoint`, `contains` and
   `BTree` equality had no `Decidable` instances, so `decide`-based checks
   failed; `BTree` gained `DecidableEq` and the geometry checks unfold
   before deciding. Recorded because it is a usability datum for the
   "decidable core" claim.
4. **Wrong coverage witness (E-1351 test).** The first translated-row test
   named the wrong box (a witness that was false), which the build rejected.
   The theorem was right; the test was wrong — evidence that the tests are
   independent of the statements.

## 6. Row status against the ADR-030 kill criteria

None of the external kill criteria can fire yet: they name baselines (browser
box model, React reconciler, Flutter/Skia, Node event loop, Ghidra, OPA, …)
that no harness in this repository exercises. Status per row:

| Row | Model grade | Claim grade | Kill criterion status |
|---|---|---|---|
| E-1351 | L3 | L1 | untested — needs a layout corpus + reflow counter |
| E-1352 | L3 | L1 | untested — needs a reconciler patch-count benchmark |
| E-1353 | L3 | L1 | untested — needs law-test generation over real form schemas |
| E-1354 | L3 | L1 | untested — needs the project's own UI corpus in the affine fragment |
| E-1355 | L3 | L1 | untested — needs dispatch-latency + listener-leak measurement |
| E-1356 | L3 | L1 | untested — needs TTI/bytes on identical pages |
| E-1357 | L3 | L1 | untested — needs quality/frame-time vs a CPU rasteriser |
| E-1358 | L3 | L1 | kernel-level rejection works; annotation-burden claim untested |
| E-1359 | L3 | L1 | untested — needs a real component API corpus |
| E-1360 | L3 | L1 | untested — needs frame-drop measurement under load |

No row is cut. No row is promoted to "supported" either: a proved kernel is
not a measured replacement.

## 7. Next iteration (repeat)

1. **E-1358:** complete the composition law with the disjointness
   side-condition (`Linear (seq a b) ↔ Linear a ∧ Linear b ∧ handles a ∩
   handles b = ∅`), which needs `count = 0 ↔ ¬ mem` plumbing.
2. **E-1351:** lift coverage from 1-D rows to 2-D grids and prove gluing
   uniqueness (two sections agreeing on a cover agree on the union).
3. **E-1360:** add the glitch-freedom theorem (every node observes only
   final dependency values), which needs a topological-order predicate
   over `DagNode` dependencies.
4. **E-1354:** add min/max sizing and either prove no-overlap survives or
   exhibit the counterexample — that is the boundary of the affine fragment.
5. **Execution record:** build a data-only harness (JSON layout trees) and a
   Node/Chromium comparison for E-1351/E-1354, so the claim grade can move
   off L1. This is the first point at which a kill criterion becomes
   testable.
