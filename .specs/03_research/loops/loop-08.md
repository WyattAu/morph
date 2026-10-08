# Loop 08 — 2026-09-19

Whole-repo sweep. Construction loop: MIR stage-1 continuation (store-aware
execution + CFG walker). Research fetches deferred to Loop 9.

## Sources consulted

None this loop (construction-focused; Oxide/Pony carry to Loop 9).

## Adjudications

### MIR stage-1 continuation: **DELIVERED (this loop's construction)**

`Morph/MIR.lean` extended:

- `FullEnv` — value registers + the typed `Store` threaded together.
- `evalInstrFull` — store-aware execution: `load`/`store`/`alloc`/`free`
  interact with the typed store; pure instructions delegate to the same
  `evalBinOp`/`evalUnOp` as before.
- `execInstrsFull`/`execBlockFuel`/`execBlockById`/`execFunc` — CFG walker
  with fuel: `goto`/`branch`/`return_` handled; `switch` and `call`/`phi`
  deferred to stage 2.

### P6 — EffectSet deletion: **DONE (Loop 5, confirmed this loop)**

No references remain; the frozen `MonadicEffect` spec is separate.

### Stage-2 borrow-judgment design: **queued, Oxide-shaped**

Per Loop 6's refinement: stage 2's correctness theorem should be stated as a
typing judgment with progress/preservation lemmas (Oxide architecture), not as
raw dataflow. The MIR CFG is the input; the judgment tracks loans and
provenances. This is the critical-path design item for ADR-012 (closures) and
ADR-013 (branch-merge operator).

## Proof changes made this loop

1. `Morph/MIR.lean` extended with store-aware execution (above).

## Open questions carried to Loop 9

1. **`lowering_correct` proof** — blocked on the write-avoidance simp-tactic
   engineering documented in loop-07.md's notes.
2. Owed fetches: Oxide full text, Pony paper.
3. Stage-2 borrow-judgment design (Oxide-shaped ADR-013 successor).
4. `switch`/`call`/`phi` execution (stage 2).
