# D3 reading prep — what the tree says before S16 drafts (S9 quiet-days, reading only)

Per `docs/YEAR1-SPRINTS.md` S9: *"D3 reading prep (the `stepActor`
interface, the D3 sketch, the actor specs) fills the quiet days after the
invites go out — reading only, no drafting."* This file is the reading
output: measured facts with pointers, plus the named S16 inputs. **No
fragment predicate, no invariant choice, no proof** is drafted here — those
are S16 and §7 maintainer calls.

## 1. `stepActor` today (facts)

`Morph/Runtime.lean` (actor section):

- Signature: `stepActor (system : ActorSystem) (turn : Nat) (_heap : Heap)
  (_stack : Stack) : ActorSystem × Heap × Stack` — **state is already
  threaded** (underscore-named, so unused today).
- Body: empty-actor-pool short-circuit; otherwise `idx := turn %
  actors.length`, `actors[idx]?` lookup, then returns
  `(system, _heap, _stack)` unchanged — evaluation integration is
  explicitly deferred in a body comment.
- Supporting operations on `ActorSystem`: `spawn` (appends, returns new
  id), `send` (appends to the target's mailbox via `actors.map`), `recv`
  (`find?` + mailbox pop, `none` on empty mailbox or missing actor).
- `Actor.state : Expr` — actors hold **surface expressions**, so real
  stepping means running the evaluator (`Morph.Executable` /
  `Morph.Interp`), which needs fuel (the established divergence idiom,
  e.g. `runHIRStmts 256` in the C8 evidence).
- **No stuck outcome**: the return type is a product; it cannot say "this
  system is stuck", which the D3 target shape presumes.

## 2. Interface decision status (D-8)

`docs/STAGED-D8-D9-OPTIONS.md` set the provisional default under rule 2:
**Reading A — state-threading step** (grow the body into real evaluation,
add the stuck outcome at S16), rejecting Reading B (state-free scheduling)
for the reasons in the memo §D-8. The S4 deadline has passed; the default
is now recorded as **ADR-033** (provisional, maintainer-revisable). S16
drafts against Reading A unless a maintainer call lands first.

## 3. Memory authority status (D-9)

Supersede is the provisional default and is now recorded (ADR-033):
`Memory.lean` is authoritative; `Specs/MemoryModel`'s 34 theorems are
requirements-only (no bridge obligation). Consequence for D3: any
heap-touching statement in the actor step ranges over `Memory.lean`
models, not the spec model.

## 4. The D3 target shape (`docs/STAGED-SCOPE.md` §4)

```lean
theorem actors_progress :
  WFActors sys → stepActor sys turn heap stack = (.stuck, _) →
  ∃ witness, DeadlockWitness sys witness
```

Names are placeholders (the scope doc says so); the load-bearing facts:

- It is a **preservation-with-witness** statement: a well-formed system
  never gets stuck without a witness. The `.stuck` outcome does not exist
  yet (§1) — S16's first drafting act is the return-type growth.
- It needs `WFActors` — not yet defined anywhere; the closest proved
  notions live in the spec side (§5 below).
- `DeadlockWitness` is likewise a placeholder; the D4 row requires
  **executable counterexamples** (a stuck-system witness the evaluator can
  produce, mirroring the C8 refusal pins).

## 5. Spec-side inventory (what exists, measured)

| Module | Provides | Relation to D3/D4 |
|---|---|---|
| `Specs/ActorDeadlock` | `Sys`/`Actor` with `waitOn`, `Ask`/`Live`/`Closed`/`WF`/`Ranked`; `chain_*`, `chain_rank_lt`/`ge`, `ranked_implies_progress`, `ranked_not_deadlocked`, preservation of `Live`/`Closed`/`WF` under `Ask` | The stateful step + progress/dyad notions D3's invariant can cite; `WF`/`Ranked` are the closest ancestors of `WFActors` |
| `Specs/ConcurrencyProcessAlgebra` | 41 theorems | Message-passing model; D4's process-side requirements |
| `Specs/LayeredConcurrency` | 25 theorems | Layered send/receive model; D4 requirements |
| `Morph/Runtime.lean` | The executable actors (0 theorems over the file, per `docs/STAGED-D1-INVENTORY.md`) | The model D3 must prove over |

D4's bridge shape (per `STAGED-SCOPE.md` D4 row): the `ActorDeadlock` +
process-algebra specs bridged to `Runtime.lean` — two proved-apart
artifacts that must first agree, the same lesson D1/D2 recorded.

## 6. S16 inputs (named here, drafted there)

1. **Stuck-outcome shape** — grow `stepActor`'s return type (fuel + stuck,
   or an explicit outcome triple); ADR-033 defers the shape.
2. **`ActorStmts` fragment predicate** — the `BranchStmts` precedent:
   new constructors beside the old ones, never widening an existing
   grammar (so existing proofs stay untouched between drafting and proof).
3. **`WFActors`** — the global invariant choice is §7-open (mailbox
   boundedness vs crash containment); the memo explicitly does not
   pre-decide it. `ActorDeadlock`'s `WF`/`Ranked` are the reading
   candidates.
4. **Fuel idiom** — actor steps run expression evaluation, so the
   `ActorStmts` interpreter needs the fuel discipline every other
   interpreter in the tree uses.

## 7. Reading-only conclusions (no drafting happened here)

- The D-8/D-9 provisional defaults (ADR-033) unblock D3/D4 drafting; the
  §7 questions that remain maintainer calls are the global invariant and
  the progress-statement style (the §4 sketch already leans
  witness-style, matching the roadmap's executable-counterexample
  requirement).
- The largest S16 unknown is the `ActorStmts` grammar: `Actor.state :
  Expr` means the fragment lives at the surface-expression level, where
  `Morph.Interp` (statement execution, loop 74) and `Morph.Executable`
  (expression evaluation) already run — the fragment predicate decides
  which of those levels (or both) an actor step ranges over. That choice
  is recorded as S16's, not made here.
