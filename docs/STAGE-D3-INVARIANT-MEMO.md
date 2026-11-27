# S4-style decision memo: the D3 global invariant (§7 open question)

> Decision ask for the maintainers, drafted at S9's quiet-days (2026-11-26,
> alongside the audit window). Operating rule 2 applies: a dated call with a
> deadline; on silence past the deadline, the recommended default proceeds as
> a provisional ADR (the D-8/D-9 precedent, ADR-033).

## The question

`docs/STAGED-SCOPE.md` §7: what global invariant does D3 (actor step safety)
preserve? The candidates named there: **mailbox boundedness**, **crash
containment**, or a bridge to `ActorDeadlock`'s proved `WF`/`Ranked`
notions. Nothing can be written until one is chosen — the D3 statement's
second conjunct is whatever this memo picks.

## Measured facts (read off the tree, 2026-11-26)

- `stepActor` is now the Reading-A step (ADR-033): round-robin, fuel-bounded
  evaluation of the scheduled actor's state expression, with a `.stuck`
  outcome (`Morph/Runtime.lean`).
- **Containment is proved**: a stuck step returns the input system verbatim
  — `stepActor_stuck_system_unchanged` in `Morph/ActorProgress.lean`. Under
  Reading A this was definitional; the proof just records it.
- Per-actor progress is proved at the statement level:
  `actors_progress` (same file) — a stuck step is always witnessed by the
  scheduled actor and its failing evaluation, **unconditionally** (no
  well-formedness hypothesis needed at this strength).
- The fragment predicate `ActorStmts` does not exist yet — it is the
  remaining S16 work, and both non-containment options depend on it.
- `Specs/ActorDeadlock` already proves `ranked_implies_progress` and
  `ranked_not_deadlocked` over its own `Sys` — a different actor model
  (`waitOn`/`Ask`/`Live`), reachable from `Runtime.lean` only through a
  relation bridge (the D4 shape, not D3's invariant).

## Options

### A. Crash containment as the D3 invariant (recommended)

D3 = "`stepActor` preserves per-actor progress and containment": the
containment conjunct is **already proved** (measured fact above); the
progress conjunct is `actors_progress` over the `ActorStmts` fragment once
that predicate lands. No mailbox bounds, no global send-budget argument.

Cost: none now. Limitation, stated honestly: containment says a failing
actor harms nothing; it does not say mailboxes stay finite.

### B. Mailbox boundedness as an additional invariant

"`ActorStmts`-fragment programs cannot grow any mailbox beyond a bound
computed from the program." Stronger claim; needs the fragment predicate to
bound send-statements per step plus a global sends-per-step argument.

Cost: the fragment predicate is prerequisite either way, so the extra work
is the budget arithmetic — bounded, but real. This is D4-adjacent (bounded
mailboxes are what a deadlock argument wants to consume).

### C. Ranked/WF bridge to `ActorDeadlock` as D3's invariant

Relate `Runtime.ActorSystem` to `ActorDeadlock.Sys` and lift
`ranked_not_deadlocked`. Rejected for D3: that is precisely D4's bridge
(the scope doc assigns it there), and making it D3's invariant would
front-load D4's hardest obligation before the fragment exists.

## Recommendation

**A** for D3's statement, with **B** queued as an additional D4-adjacent
theorem after the fragment lands, and **C** staying where the scope doc
already put it (D4). Rationale: A is the only option whose expensive part
(containment) is already banked, and it keeps D3's claim exactly as strong
as the current model supports — the pipeline's one-directional discipline
(`agreeBoth`, ADR-032's verified-lowering boundary) has consistently
preferred claims the tree can carry today.

## Decision block

- **DECIDED 2026-11-27 (explicit, ahead of deadline): A — crash
  containment.** Recorded as **ADR-034** (provisional, revisable): D3's
  invariant is crash containment (`stepActor_stuck_system_unchanged`,
  proved) + witnessed progress (`actors_progress`, proved) — both against
  the Reading-A executable step, unconditional at this strength.
- B (mailbox boundedness) is queued as a D4-adjacent theorem after the
  `ActorStmts` fragment lands; its rigorous form needs the fragment's
  send/recv discipline (an undrafted design). C (ranked/WF bridge) stays
  in D4.
- The S16 remainder is unchanged: the `ActorStmts` fragment predicate,
  with `actors_progress` restated over it if the fragment's well-
  formedness strengthens the statement.
