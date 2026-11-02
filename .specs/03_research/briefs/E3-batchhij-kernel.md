# E3 — BatchHIJ Kernel Brief (E-58–E-67, loop 109)

## 1. Research basis (one line per row)

- **E-58.** Sato Grassmannian / KP hierarchy (Sato 1981; Krichever data;
  Hirota bilinear equations). Kernel keeps the falsifiable fragment: a FIFO
  controller whose drain is an integrable-flow update with conserved Lax-like
  accounting (`stepBuf buf burst drain = buf + burst - drain`), admitted iff
  the τ-zero check (`dropFree`) holds. The τ-function itself is
  documentation; the drop-free certificate is the artifact.
- **E-59.** Conley index + barcodes (Conley 1978; Edelsbrunner–Harer
  persistence). Kernel keeps the gate: quoting-parameter updates are blocked
  iff they cross a tracked barcode wall on the half-open path
  (`between`/`crosses`). Continuation theory is documentation; the
  cross/none two-way certificate is the artifact.
- **E-60.** Fargues–Fontaine curve + Harder–Narasimhan slopes (Fargues–Fontaine
  2018; `μ(E) = deg/rank`). Kernel keeps the sign check over commuting
  integers: `hnFlag` flags positive degree, `flagAll` folds it over the
  settlement graph. The curve is documentation; soundness + completeness of
  the flag is the artifact.
- **E-61.** Hitchin integrable system (Hitchin 1987; spectral curve
  `S = {det(λI − Φ) = 0}`, flow linearized on `Jac(S)`). Kernel keeps the
  decoupled model: independent 1-D linear flows (`flow1`), mapped per asset
  (`liquidate`), with per-asset sold amounts (`drained`) that add back
  exactly. Slippage quality is the untested claim.
- **E-62.** Kempf–Ness + symplectic reduction (`X//G ≅ μ⁻¹(0)/K`; gradient
  flow on `‖μ‖²`). Kernel keeps the discrete descent: ordered load pairs,
  gap potential, one-unit migration that preserves total load and shrinks the
  gap by exactly 2 while live, and stops at gap ≤ 1. Oscillation on real
  traces is the untested risk.
- **E-63.** ADHM equations (`[B₁,B₂] + IJ = 0` plus the real equation).
  Kernel keeps the commuting-scalar fragment where the commutator vanishes
  provably (`adhmErr = i * j` by `Int.mul_comm`), so admission is exactly the
  vanishing product, with a tolerant variant for the ≤3-cycle model. The
  systolic timing claim is untested.
- **E-64.** Berkovich analytification (`P¹_Berk`; Fatou equicontinuity vs
  Julia chaos). Kernel keeps the threshold guard: expansion below `T` stays,
  at/above `T` prunes, with a count bounded by trace length and zero on
  all-quiet traces. Flush-rate wins are the untested claim.
- **E-65.** SLE / Cardy crossing (`∂ₜgₜ = 2/(gₜ − ξₜ)`; `κ = 6` crossing via
  `₂F₁`). Kernel keeps only the shaper's accounting: halves add back, each
  slice fits, and splitting never increases the linear `a² + b²` impact
  model. The fractal-boundary impact claim is explicitly out of fragment.
- **E-66.** Hörmander wave-front sets (`WF(u) ⊂ T*X ∖ {0}`; disjointness
  `WF(u) ∩ −WF(v) = ∅` licenses elision). Kernel keeps discrete direction
  sets with a two-way disjointness certificate; `elideFence` is exactly that
  test. Hammer-test soundness is the untested claim.
- **E-67.** Bridgeland stability + Kontsevich–Soibelman wall-crossing
  (`φ = arg Z/π`; DT jump `ΔΩ` at `arg Z(γ₁) = arg Z(γ₂)`). Kernel keeps the
  chamber-exit guard: charge `Z = depth − inv`, anchor iff the update leaves
  the positive chamber, held inventory modeled exactly. Replay behavior is
  the untested claim.

## 2. Design decisions

1. **Nat-first arithmetic.** Seven of ten cores are `Nat`-valued (E-58, E-59,
   E-61, E-62, E-64, E-65, parts of E-66/67); E-60/E-63 drop to `Int` only
   where signs are the claim. Keeps every law `omega`-decidable.
2. **Half-open walls (E-59).** `between l l' w = (l < w ∧ w ≤ l')` models the
   direction a relaxation travels; the crossing test is an `||`-fold with a
   two-way certificate (`crosses_sound` / `crosses_none`).
3. **Explicit commutator (E-63).** `adhmErr` writes the commutator out
   rather than assuming scalars commute; the vanishing is a proved lemma,
   not an axiom.
4. **No `ring` anywhere.** The one nonlinear identity (E-65 split impact) is
   proved from `Nat.add_mul` / `Nat.mul_add` distribution facts plus `omega`;
   the ADHM commutator goes through `Int.mul_comm` + `omega`. No Mathlib
   dependency beyond `Std`.
5. **Three-file pattern (ADR-004).** `BatchHIJ` holds all ten cores with a
   mapping table in `Spec.lean`; rows separate later without definition
   changes.

## 3. Implementation map and proof burden

| File | Lines | Content |
|---|---|---|
| `Morph/Specs/BatchHIJ/Spec.lean` | 243 | 10 cores, mapping table, scope statement |
| `Morph/Specs/BatchHIJ/Lemmas.lean` | 339 | 36 theorems, no `sorry`, no axioms |
| `Morph/Specs/BatchHIJ/Examples.lean` | 177 | 40+ concrete instances incl. law witnesses |
| `Morph/Tests/BatchHIJ.lean` | 159 | 30+ independent checks incl. negative cases |

Proof burden: 36 theorems over ~120 lines of definitions (≈ 2.8 proof lines
per definition line incl. comments). All proofs are manual
induction/`simp`/`omega`; no SMT, no automation beyond core tactics. No core
file was touched, per the register's trusted-core rule.

Build record (this machine):

- `lake build Morph.Specs.BatchHIJ.Spec` — ~5 s.
- `lake build Morph.Specs.BatchHIJ.Examples Morph.Tests.BatchHIJ` — 5 jobs,
  success, 0 warnings, 0 `sorry` in the new files.

## 4. Validation log — what the cycle caught

1. **Anonymous-constructor inference (E-60).** Bare `⟨-1, 2⟩` list literals
   do not elaborate against `List Bundle` in `Examples`/`Tests`; fixed with
   explicit `([⟨-1, 2⟩, ⟨4, 1⟩] : List Bundle)` annotations. Usability datum
   for the "decidable core" claim.
2. **Missing `Bool.or_eq_false` lemma.** The E-59 `crosses_none` proof first
   assumed a `Bool.or_eq_false` rewrite that does not exist in this
   toolchain; replaced with `cases` on the `between` test plus `simp`.
   Recorded so the next cycle does not repeat it.
3. **`simp only [knGap]` opacity.** `simp only` with the gap definition did
   not expose the subtraction to `omega` in `stepKN_gap2`/`stepKN_stable`;
   fixed with an explicit `knGap p = p.hi - p.lo := rfl` fact. Same class of
   issue as the FGH `seedPos` unfold datum.
4. **Nonlinear `ring` unavailable.** Both nonlinear goals (ADHM commutator,
   split-impact expansion) were rewritten to use distribution lemmas +
   `omega` instead of `ring`, keeping the module on `Std` only.
5. **Negative tests are real.** Every row has a refused/quiet/off-path case
   (`dropFree` over-drain, off-path walls, negative books, nonzero ADHM
   product, pruned branches, shared covectors, stable books) so a vacuous
   pass cannot hide.

## 5. Row status against the kill criteria

None of the external kill criteria can fire yet: they name baselines (burst
traces, crash-shock replay, CIP routers, Almgren–Chriss, load traces,
FPGA-model certification, speculation traces, TWAP/VWAP replay, hammer
tests, flash-crash replay) that no harness in this repository exercises.
Status per row:

| Row | Model grade | Claim grade | Kill criterion status |
|---|---|---|---|
| E-58 | L3 | L1 | untested — needs burst traces vs M/M/1 sizing |
| E-59 | L3 | L1 | untested — needs crash-shock replay vs Lyapunov gate |
| E-60 | L3 | L1 | untested — needs settlement P&L vs CIP router |
| E-61 | L3 | L1 | untested — needs slippage vs multi-asset Almgren–Chriss |
| E-62 | L3 | L1 | untested — needs migration bandwidth vs work-stealing |
| E-63 | L3 | L1 | untested — needs FPGA-model certify latency vs leg-checker |
| E-64 | L3 | L1 | untested — needs flush rate vs depth-limit speculation |
| E-65 | L3 | L1 | untested — needs impact vs TWAP/VWAP on replay |
| E-66 | L3 | L1 | untested — needs hammer tests vs happens-before oracle |
| E-67 | L3 | L1 | untested — needs flash-crash replay vs volatility gate |

No row is cut. No row is promoted to "supported" either: a proved kernel is
not a measured replacement.

## 6. Next iteration (repeat)

1. **E-62:** oscillation test on synthetic load traces (does the gap-2
   descent chatter at equilibrium under asymmetric arrivals?).
2. **E-65:** state the fractal-boundary claim as a property of a real
   impact model or drop it from the row scope.
3. **E-59/E-67:** shared wall-crossing harness — one replay format for
   barcode walls and chamber exits over the same volatility traces.
4. **E-63:** real-equation half (`[B₁,B₁†] + [B₂,B₂†] + II† − J†J = 0`) in
   the commuting model, then the noncommuting-matrix move.
5. **Execution record:** data-only harnesses (burst schedules, book-state
   traces, settlement graphs) so the claim grades can move off L1 — the
   first point at which a kill criterion becomes testable.
