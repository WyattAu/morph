# Proof crates: estate-style modularization for Stage C proofs

Mirrors the `WyattAu` estate layout (L0 leaves with no inter-leaf deps,
L1 composition over leaves only, shared gate checklist) without inventing
new concepts. Each leaf keeps the `Morph/Specs/*/` triple shape:
spec-statement header docs (= value prop), lemmas (= implementation),
examples/goldens (= tests).

## Why

`Morph/HIRToMIRBranch.lean` is one 23k-line monolith. Its own `/-!` section
markers already draw the leaf boundaries, but everything lives in one
module, so every change rebuilds everything and reuse means copy-paste.
The estate rule is: leaves compose, never depend upward; an L1 module
imports leaves only.

## Leaf map (L0 — import `Core`/`Total` only, never each other or Branch)

| Leaf module | Source section in Branch | Contents | Reusers |
|---|---|---|---|
| `Proofs.Branch.Merge` | §741 (C2c groundwork) ✅ EXTRACTED | `mergeIds`, `rhoLookup_some_of_mem`, `mergeIds_mem_lookup`, `mkMergePhis`, `mkMergePhis_le`, `mkMergePhis_growth_fresh`, `boundIds` | Phase B switch, top-level C3 rework |
| `Proofs.Branch.Fragments` | §§72–468 + Phase A | `ArmStmts`, `BindArmStmts`, `LoopStmts`, `ArmNoBreak`, inclusion, `straightStmts_to_branch` | all workers |
| `Proofs.Branch.Fuel` | §505 (§4.4) + §22729 | budget, `blockBound`, monotonicity, closed-program fuel bound | C3 workers |
| `Proofs.Branch.Fresh` | §§1165, 1880 | growth, uniqueness, freshness preservation | merge, loop headers |
| `Proofs.Branch.LoopAlloc` | §596 (C7a) + §917 | `assignedIds`, `dedupIds`, `LoopInfo`, `carryCopies`, `mkCarried` + growth proofs, `mkHeaderPhis` | loop lowering + workers |
| `Proofs.Branch.Spine` | §§14127, 14219 | oracle while cases, loop-carried membership, spine-P, trampoline/header lemmas | loop workers |
| `Proofs.Branch.BodyWorker` | §20310 | closed bodies run to the oracle's value | `whileLoop_correct` |

## Composition (L1 — import leaves only, never Branch)

| Module | Contents |
|---|---|
| `Proofs.Branch.Workers` | `arm_total`, `arm_broke`, `arm_continued`, `loopBody_run`, C3 worker helpers (§2822) |
| `Proofs.Branch.Loop` | `whileLoop_correct` + header re-read (§23016), nested-arm phi predecessor (§22974) |
| `Proofs.Branch.TopLevel` | lowered CFG runs (§22912), `runHIRStmts_arm_lookup` family ((binding-free arm facts stay until 2b/2c resolves) |

## Import DAG

```
HIRToMIRCore / HIRToMIRTotal
  └─ Merge, Fragments, Fuel, Fresh, LoopAlloc, Spine, BodyWorker   (L0, no lateral imports)
       └─ Workers, Loop, TopLevel                                  (L1, leaves only)
            └─ HIRToMIRBranch (re-exports + statement grammars until fully split)
```

Layer check (estate rule, manual until CI): no L0 module imports another
L0 module or any L1 module; no L1 module imports `HIRToMIRBranch`.

## Gate checklist per leaf (estate gates translated)

- `sorry`-free: `grep -rn "sorry" Morph/ --include="*.lean"` empty (⇔ `cargo-vet` clean).
- Zero-warning build: `lake build <Module>` prints no warnings (⇔ `clippy -D warnings`).
- Documented public theorems: every `def`/`theorem` carries a `/--` doc (⇔ `deny(missing_docs)`).
- Statement stability: lemma *statements* used by L1 are versioned through
  fragment inclusions; changing a statement without a matching inclusion
  update fails the L1 build (⇔ `cargo-semver-checks`).
- Green main: each extraction commits with the monolith importing the leaf
  back, so the tree never goes red between cuts (⇔ estate "never break main").

## Extraction order (smallest green cuts first)

1. ✅ `Merge` — self-contained, list-based, zero worker deps (§741 + `boundIds`).
   Phase B consumes it: the lowering's join keys on `mergeIds`, and every
   C3 if-case discharges `[]` via `arm_rho` + `mergeIds_self`.
2. ✅ `Fragments` — grammars + Phase A inclusion (gates every worker's hypotheses).
3. ✅ `Fuel` — block budget, fully pure (0 lowering cites). `Fresh` stays in
   Branch: its theorems cite the lowering/execution (105 cites), so it is L1
   material, not an L0 leaf — reclassify when the lowering itself moves.
4. ✅ `LoopAlloc` — `mkCarried`/`mkHeaderPhis` moved with growth proofs (0
   lowering cites); the `mkCarried_*` worker lemmas stay (they reason about
   lowering call sites).
5. `Spine` → `BodyWorker` → `Workers` → `Loop` — the proof core, last (deep
   lowering interdeps; extract only with the lowering).
