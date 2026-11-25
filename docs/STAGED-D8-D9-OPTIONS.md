# S4 decision memo: D-8 (`stepActor` interface) and D-9 (memory authority)

S4 deliverable (`docs/YEAR1-SPRINTS.md`), drafted early: S3's D-7 work
closed out ahead of the sprint clock, and both items need a dated
maintainer call with a deadline of end of S4 (operating rule 2). Past
that deadline, work proceeds on the stated provisional defaults
recorded as provisional ADRs.

The facts below are read off the tree, not proposed: `stepActor`'s
signature and body (`Morph/Runtime.lean`), the D3 sketch (target
shapes in `docs/STAGED-SCOPE.md` §4, open questions in §7), and the
spec side (`Morph/Specs/ActorDeadlock`, `ConcurrencyProcessAlgebra`).

## D-8: what `stepActor`'s interface is

Current state, verbatim from the tree:

- Signature threads state:
  `stepActor (system) (turn) (_heap) (_stack) : ActorSystem × Heap × Stack`.
- Body ignores it: returns `(system, _heap, _stack)` unchanged, with
  evaluation integration explicitly deferred.
- Actors hold surface expressions (`Actor.state : Expr`); stepping one
  for real means evaluating an `Expr`, which needs the evaluator plus
  heap and stack.
- No stuck outcome: the return type cannot say "this system is stuck",
  which the §4 `actors_progress` shape presumes (`= (.stuck, _) → ∃ witness`).

### Reading A — state-threading step (recommended)

Keep the signature the code already anticipates; grow the body into
real evaluation and add a stuck outcome. D3 is then the preservation
proof the scope doc sketches: `stepActor` preserves per-actor
progress plus the chosen global invariant, stated over the
`ActorStmts` fragment predicate (drafted S16).

Why A:

- The signature already threads state — the code anticipates this
  reading; B would narrow a signature that exists.
- The §4 target shape is a preservation-with-witness statement; it
  needs state in the step to quantify over.
- The spec side (`ActorDeadlock.Steps`) is a stateful step relation
  with `progress_invariant` and `ranked_not_deadlocked` already
  proved. Bridging a state-free scheduler to it would need an extra
  layer translating scheduler moves into spec steps; A meets the spec
  at its own level.
- C8's lesson (prove at one level): evaluation inside the step keeps
  one level where progress means something.

Cost of A: the stuck outcome must be added (return type grows), and
evaluation needs its divergence story (fuel is the established idiom
— `runHIRStmts 256` in the C8 evidence). That is real work, but it is
work D3 needs under any reading that keeps "step safety" meaning
anything.

### Reading B — state-free step, evaluation elsewhere

Narrow `stepActor` to pure scheduling (round-robin pick, message
route); the caller threads heap/stack through the evaluator. D3 then
stops being a step-safety statement and becomes scheduler
correctness (no message loss, turn advance, lookup agreement).

Why not B:

- The safety content evaporates: per-actor progress would live in the
  evaluator, which has no fragment predicate and no S16 drafting slot.
- It drifts into the explicitly excluded zone (`docs/STAGED-SCOPE.md`
  §6: no scheduler fairness beyond what is stated).
- The `ActorStmts` predicate — the BranchStmts-precedent instrument
  the whole D-track is built around — would have nothing to range over.

### Needed under either reading

- A stuck/divergence outcome in the return type (fuel + stuck, or an
  explicit outcome triple). The current type cannot state progress.
- The `ActorStmts` fragment predicate (S16) and the global invariant
  choice (mailbox boundedness vs crash containment — still open in
  §7; this memo does not pre-decide it).

**Provisional default (rule 2):** Reading A, with the stuck outcome
added at D3-drafting time (S16), if unanswered past end of S4.

## D-9: which memory model is authoritative

Landscape, per `docs/STAGED-D1-INVENTORY.md`: `Memory.lean` is the
executable model (0 theorems, imported by nothing);
`Specs/MemoryModel` holds 34 theorems over a disconnected model;
`Borrows.lean` has `borrow_preservation` proved.

- **Supersede** (recommended, and already the roadmap register's
  default): `Memory.lean` authoritative, spec model as
  requirements-only. Rationale: the 34 theorems touch neither
  executable model, so a bridge would relate models that disagree by
  design — a relation pair whose agreement lemma restates the
  disagreement. Supersede costs a rewrite of the spec side's
  authority, not a refactor of anything proved.
- **Bridge:** a `RelMemorySpec` pair plus agreement, C8-style. Honest
  only if the spec model is meant to keep independent authority; no
  consumer of it exists in the tree.

**Provisional default (rule 2):** supersede, as the roadmap register
already records, if unanswered past end of S4.

## Decision block

- D-8: Reading A (state-threading step) vs Reading B (state-free step).
- D-9: confirm supersede (default) vs order a bridge.
- Dated: S4. Deadline: end of S4. Past it, the provisional defaults
  above proceed as provisional ADRs; a wrong default costs a
  refactor, a stalled chain costs the quarter.
- Out of scope for this memo: the global invariant choice (S16
  input), the stuck-outcome shape (S16 drafting), D5's quantifier
  level (§7 Q4, Y2 work).
