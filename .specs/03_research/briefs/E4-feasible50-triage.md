# E4 — Feasible-50 Triage (all 1,250 registered rows scored, loop 110)

## Method

All rows from ADR-019 (E-03–E-100) through ADR-031 (E-1451–E-1550) were
listed (`/tmp/allE.txt`, 1,250 `| E-` rows) and scored on one axis:
**can this become a small decidable Lean kernel provable with `Std`-only
tactics (`simp`/`omega`/`decide`) over `Nat`/`Int`/`List`/`Bool`, shaped as
a checker/certificate/accounting law?** Rows needing real numbers,
physics, hardware fab, or full-system baselines scored infeasible *for
kernel-proving* (they stay tracked-open; they are not cut).

Already-proved rows (E-03, E-06, E-10, E-21–E-67, E-1351–E-1360) are
excluded from the 50. The survivors below are the 50 cheapest-to-prove
rows that also sit closest to the core (verification, types, concurrency,
storage, wire/session, everyday-product surface).

## The 50 (5 proof batches of 10)

### Batch P1 — verification + type core (E-104 … E-149)
| Row | Kernel shape |
|---|---|
| E-104 | peephole pre/post equivalence validator with fallback log |
| E-113 | `decide`-check vs interpreter-oracle differential harness |
| E-116 | Kildall backward-fixpoint liveness on a straight-line fragment |
| E-120 | borrow-checker completeness on loop-free MIR (acceptance predicate) |
| E-123 | monotone-framework engine (lattice + transfer + join laws) |
| E-124 | interval/octagon domain ops with widening convergence |
| E-137 | order-lifecycle typestate FSM (placed→acked→filled) |
| E-141 | phantom brand discipline for venue/session identity |
| E-148 | or-pattern exhaustiveness with GADT refinement |
| E-149 | row-polymorphic risk-record composition |

### Batch P2 — concurrency primitives (E-151 … E-174)
| Row | Kernel shape |
|---|---|
| E-151 | nursery task-tree (no-orphan by construction) |
| E-156 | flat-combining counter with collapse accounting |
| E-157 | seqlock snapshot with tearing-freedom predicate |
| E-159 | deterministic record/replay scheduler log |
| E-160 | ownership-transfer message passing (copy-cost ledger) |
| E-161 | supervisor restart/escalation FSM |
| E-162 | credit/flow-control buffer-bound proofs |
| E-163 | idempotent-handler + dedup-window delivery |
| E-172 | op-based CRDT book merge convergence |
| E-174 | edge-chasing deadlock detector on cluster sim |

### Batch P3 — models + storage kernels (E-177 … E-366)
| Row | Kernel shape |
|---|---|
| E-177 | executable MESI + litmus-outcome checker |
| E-178 | store-buffer/LSB TSO/PSO model with fence-sufficiency |
| E-187 | PCIe descriptor/doorbell ordering checker |
| E-199 | memory-consistency litmus suite (pass/fail corpus) |
| E-354 | open-addressing hash-table probe accounting |
| E-355 | Bloom-filter FPR sizing certificate |
| E-360 | WAL truncation/replay correctness |
| E-362 | CoW snapshot-isolation predicate |
| E-363 | MVCC visibility rules |
| E-366 | materialized-view incremental-maintenance audit |

### Batch P4 — wire/session kernels (E-380 … E-398)
| Row | Kernel shape |
|---|---|
| E-380 | length-prefix framing codec with fuzz corpus |
| E-381 | FIX/ITCH/MDP codec conformance suite |
| E-382 | logon/heartbeat/gap-fill session FSM |
| E-383 | token-bucket rate limiter |
| E-384 | cancel-on-disconnect liveness |
| E-385 | drop-copy backup-session consistency |
| E-392 | strict/WFQ priority-queue bounds |
| E-393 | venue rate-limit traffic shaping |
| E-396 | pcap-determinism replay audit |
| E-398 | clock-sync-free sequencing audit |

### Batch P5 — everyday-product kernels (E-1455 … E-1490)
| Row | Kernel shape |
|---|---|
| E-1455 | affine RPC token (single-execution linearity) |
| E-1460 | Presburger rate-limit lattice admission |
| E-1463 | linear channel duality checker (`A ⊗ A^⊥ → I`) |
| E-1468 | affine actor-mailbox state sequence |
| E-1469 | SPSC ring index arithmetic (modular, cache-line) |
| E-1470 | coinductive signal lattice (glitch-free propagation) |
| E-1484 | app-store policy rule checker on rejection corpus |
| E-1487 | linear permission-capability gating |
| E-1489 | snapshot/restore lifecycle (rotation/kill) |
| E-1490 | BLE/NFC protocol-FSM to user-space driver |

## Proof plan (same cadence that worked for FGH/HIJ)

Per batch: `Morph/Specs/BatchP{n}/Spec.lean` → `Lemmas.lean` (target
~35 theorems, `Std`-only, no `sorry`) → `Examples.lean` →
`Morph/Tests/BatchP{n}.lean` → `lake build` clean → brief + ADR-019
execution record (§24–§28). Five cycles, then stop frontier work and
return to the core per the user's directive.

## Core-continuation gate (agreed)

After P5, no new frontier batches. Next work is core progression:
soundness/preservation gaps, lowering/borrow-check stages, driver and
test-suite hardening — informed by whichever P1–P5 kernels actually
deserve wiring into `HIR`/`MIR` (prime candidates: E-104, E-116, E-123,
E-137, E-148, E-159, E-162, E-178, E-383, E-1463).
