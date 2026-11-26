# Year 1 sprints (2026-12 → 2027-11)

> Companion to `docs/FIVE-YEAR-ROADMAP.md` Year 1. Twenty-six two-week
> sprints, S1–S26. Every sprint ends the same way: tree pushed, pipeline
> read, `spec-status.md` regenerated (deterministic since the `LC_ALL=C`
> fix), `check-gates.sh` green. A sprint is done when its exit criteria
> hold on the pushed tree, not on a local build.
>
> Dependencies: D-7/D-8/D-9 are maintainer decisions (`FIVE-YEAR-ROADMAP.md`
> decision register). Anything marked *(maintainer call)* blocks on an
> answer, not on effort — its sprint produces the options memo if the
> answer hasn't landed.

## Q1 — Observe CI, settle the interfaces (S1–S6)

### S1 — First green pipeline (wks 1–2)

- If the fortnight holds a `Morph/**` change, read the push pipeline;
  if not, hand-trigger (`gh workflow run Lean\ Build --ref main`,
  likewise Specification Validation) instead of manufacturing churn.
  The sort-fix verification predicts green.
- Confirm a Pages deploy from a live run; close G-1/G-2 in
  `HARD-GATES.md` against observed evidence, not predictions.
- Resolve the untracked `.reports/regression/snapshot-*.json` strays:
  commit the Era-1 baseline set, ignore the rest.
- **Exit:** Lean Build green on a pushed tree; G-1/G-2 closed with run
  links; `git status` shows no strays.

### S2 — C8 ABI options memo (wks 3–4)

- Read out the refusal: `Morph/Tests/ClifCall.lean` pins + the C8 row's
  recorded analysis. Write the options (encode with stated ABI vs keep
  refusing) with the cost of each: hypotheses the encoder would need,
  tests it would add, what stays pinned either way.
- **Exit:** memo circulated; *(maintainer call D-7 dated; deadline:
  end of S3; unanswered ⇒ default, refusal stands, provisional ADR)*.

### S3 — D-7 lands, C8 moves (wks 5–6)

- If D-7 decides encode: spec the encoder statement (fragment predicate
  + agreement shape, Stage-C discipline: MIR produced `w` ⇒ CLIF
  produced `w`), following the relations→agreement→composition pattern.
- If D-7 decides refuse — or is unanswered past the S3 deadline, in
  which case the default (refusal stands) proceeds as a provisional
  ADR: publish the rationale beside the pins and close
  the item; C8 is a leaf, D-work is unaffected either way.
- **Exit:** C8 encoder spec'd or refusal published; no open "ABI?" thread.

### S4 — D-8 and D-9 (wks 7–8)

- D-8: read `stepActor` (`Morph/Runtime.lean:135` — heap/stack currently
  threaded through unchanged) and the D3 sketch; memo the two interface
  readings (state-threading step vs state-free step + stepping
  elsewhere), with what each makes D3 state.
- D-9: read the 34 `Specs/MemoryModel` theorems against `Memory.lean`'s
  35 definitions; memo bridge-vs-supersede with the cost of each (a
  D2-style relation pair vs a rewrite of the spec side's authority).
- **Exit:** both memos circulated; *(maintainer calls dated; deadline:
  end of S4; unanswered ⇒ provisional defaults — supersede for D-9, the
  S4 memo's stated reading for D-8 — recorded as provisional ADRs)*.

### S5 — `HeapSafe` as a definition (wks 9–10)

- Draft the D1 fragment predicate over `Memory.lean` blocks
  (allocated ⇒ in-bounds, freed ⇒ unreadable, no use-after-free) and
  circulate for attack per `STAGED-SCOPE.md` §5 — a predicate needs no
  theorems to be stated, but it needs reviewers before proofs begin.
- Set up the D1 pin pattern in `Morph/Tests/Memory.lean`: success case
  plus a refusal/divergence case, mirroring the C8 pins.
- **Exit:** `HeapSafe` defined and attacked in review; pins in place.

### S6 — D1 preservation (wks 11–12)

- Prove `HeapSafe` preserved by `writeBlock`/`readBlock`/`freeBlock`
  (shape: `heapWrite_safe` in `STAGED-SCOPE.md` §4). No evaluator
  involved — pure model work.
- **Exit:** D1 preservation proved, 0 sorry, gates green; Q1 decisions
  (D-7/D-8/D-9) all dated, answered or explicitly carried with owners.

## Q2 — Agreement, audit, 0.1.0 (S7–S12)

### S7 — Borrow–heap relation (wks 13–14)

- Build the D2 bridge: `heapOf` projection (or an explicit
  `RelBorrowHeap` relation) from `Borrows.lean` provenances to
  `Memory.lean` heaps. Depends on D1 + D-9's verdict on what a heap is
  (or its provisional default — rule 2, no waiting past S4).
- **Exit:** relation stated; projection total on the fragment or its
  partiality characterized with pins.

### S8 — `wfBorrow_heapSafe` (wks 15–16)

- Prove `WFBorrow` implies `HeapSafe` — the Stage-C-style agreement
  lemma, building on the already-proved `borrow_preservation`. This is
  the cheapest real Stage-D theorem and the load-bearing lemma for D5.
- **Exit:** agreement proved; D2 closed; D5 unblocked.

### S9 — Audit invites (wks 17–18)

- Cut the snapshot (`scripts/regression-snapshot.sh`), refresh
  `docs/AUDIT-PACKET-0.1.md`, send invites per
  `docs/AUDIT-INVITES-0.1.md` (G-3 opens, 3-week review clock starts).
- No proof work that the audit could contest starts this sprint. D3
  reading prep (the `stepActor` interface, the D3 sketch, the actor
  specs) fills the quiet days after the invites go out — reading only,
  no drafting.
- **Exit:** invites sent with packet + snapshot + timeline.

### S10–S11 — Review window (wks 19–22)

- Answer reviewers; triage each finding the day it lands: spec
  contradiction, named future work, or accepted-baseline waiver with
  rationale. Nothing evaporates.
- No D3 drafting these sprints — the review window is reactive work
  and will crowd it out. Reading notes only; drafting lives in S16
  deliberately.
- **Exit:** review closes (overrun ⇒ rule 5); every finding triaged with
  an owner.

### S12 — Tag 0.1.0 (wks 23–24)

- Run the G-7 checklist in order: snapshot, `git tag 0.1.0`, push tag,
  CI/Pages green on the tag, re-stamp `SPECIFICATION_INDEX.md` +
  `site/docs/specs.html` to measured values (or mark historical),
  announce.
- If the review overruns: the tag waits (rule 5) — remediation absorbs
  the slip first, tag moves at most 2 sprints, then tags with known
  findings documented as errata.
- **Exit:** tag cut, deploy observed, announcement out; Era-1 exit
  criteria checked (CI per push; 0/0/0; `--hir` end-to-end; 0.1
  released; one audit published).

## Q3 — Remediation + actor safety (S13–S18)

### S13–S15 — Audit remediation (wks 25–30)

- Work the triaged findings in priority order; each fix lands with its
  contradiction entry updated or its waiver rationale recorded.
- Toolchain-churn duty rides along (Lean/mathlib bumps against
  `lake build`; cache keys in `lean-build.yml` if the manifest moved).
- **Exit:** all P0 findings closed; remainder re-planned with dates, not
  dropped.

### S16 — D3 fragment predicate (wks 31–32)

- State the actor fragment predicate (the `ActorStmts` analogue of
  `BranchStmts`: new constructors beside the old ones, never widening)
  plus the per-actor progress statement behind the D-8 interface
  (drafting deferred here from S10–S11 deliberately).
- **Exit:** predicate + progress statement circulated for attack.

> **Pulled forward 2026-11-26** (maintainer "proceed all" at S9): the
> Reading-A `stepActor` landed in `Morph/Runtime.lean` (fuel + `.stuck`
> outcome, ADR-033), and `Morph/ActorProgress.lean` defines `WFActors`,
> `DeadlockWitness`, and the proved `actors_progress` — exit met, minus the
> D3 global invariant (still §7-open). Remaining S16 work: the invariant
> choice and its preservation pins.

### S17–S18 — `stepActor` invariant (wks 33–36)

- Prove the step preserves the per-actor invariant and the chosen global
  property (mailbox boundedness / crash containment per §7's answer).
  Depends on D-8 (interface settled S4) — if D-8 slipped, this block
  becomes interface work, not invariant work.
- **Exit:** D3 proved; D4 unblocked.

## Q4 — Deadlock-freedom, D5 start, exit check (S19–S26)

### S19 — Witness shapes (wks 37–38)

- State `WFActors` and the witness-style progress theorem
  (`actors_progress` shape in `STAGED-SCOPE.md` §4): a stuck system
  comes with a `DeadlockWitness` the evaluator can produce. Refusal
  cases get pins first, proofs second (C8 discipline).
- **Exit:** shapes stated; witness producer sketched against
  `Runtime.lean`'s `spawn`/`send`/`recv`.

### S20–S21 — D4 proofs (wks 39–42)

- Prove channel safety + deadlock-freedom over `ActorSystem`, bridging
  the `ActorDeadlock` + `ConcurrencyProcessAlgebra` specs to
  `Runtime.lean` (needs D3's step invariant). Executable
  counterexample: a stuck-system witness the evaluator produces.
- **Exit:** D4 proved with witnesses; Stage D's concurrency half closed.

### S22–S23 — D5 start (wks 43–46)

- State attacker-observable equivalence over the evaluator and begin
  taint noninterference + OCap (needs D2 — if D2 slipped, this block
  becomes D2-completion, and D5 moves to Y2 H1 per the roadmap's
  miss rule).
- **Exit:** equivalence stated; noninterference proved for the
  straight-line fragment at minimum, or D5 formally re-planned.

### S24 — Proof health (wks 47–48)

- Mathlib/Lean bump if due; measure the core proof-check budget (target:
  <30 min laptop check, the Year 3 gate, early); retire dead tactics;
  re-run the full corpus (`morph test` 13/13, `check.sh` 22/22).
- **Exit:** budgets measured and recorded; no red anywhere.

### S25 — Scoreboard + annual review prep (wks 49–50)

- Recount everything (theorems, modules, coverage, links, runs; method locked: `scripts/regression-snapshot.sh` all-in counting, test pins included);
  quarterly score the `FIVE-YEAR-ROADMAP.md` table; draft the annual
  review ADR (confirm or revise, never drift).
- **Exit:** scoreboard current; review ADR drafted.

### S26 — Buffer + Era-1 exit rehearsal (wks 51–52)

- Overflow for whatever slipped; then rehearse the exit check end to
  end on a clean tree: CI per push, 0/0/0, `--hir` end-to-end, 0.1
  released, audit published, D1–D4 proved.
- **Exit:** Year 1 exit criteria met or missed-with-plan (misses slip
  to Y2 H2 with owners; theorem scope untouched).

## Sprint operating rules

1. **Push per sprint, read every pipeline.** CI reads the tree on push
   only when a watched path changes (`Morph/**` for lean-build;
   `spec/**`, `docs/conventions/**`, `scripts/spec_tools/**` for
   spec-validation) — a sprint with no watched-path change
   hand-triggers its read (`workflow_dispatch` is enabled on both
   workflows) instead of manufacturing churn. Nightly (06:00 UTC)
   covers the rest.
2. **Decisions are dated, not awaited — and they have deadlines.** D-7
   answers by end of S3, D-8/D-9 by end of S4. Past the deadline, work
   proceeds on a stated provisional default recorded as a provisional
   ADR (D-7 default: refusal stands; D-9 default: supersede —
   executable `Memory.lean` authoritative, spec model as requirements
   only, per the roadmap register; D-8 default: the reading the S4
   memo recommends). A wrong provisional default
   costs a refactor; a stalled chain costs the quarter.
3. **Predicates before proofs, pins before theorems.** Every D-item
   lands its fragment predicate, its corpus/pin pair (success +
   refusal), and only then its preservation/agreement proof.
4. **Findings never evaporate.** Audit findings, pilot bugs (Y2+), and
   reviewer attacks each resolve to exactly one of: contradiction entry,
   named future work with a sprint number, or accepted-baseline waiver
   with rationale.
5. **The tag waits for the review.** If the audit review overruns, the
   S12 tag slips rather than ships blind: the remediation block absorbs
   the slip first, the tag moves at most 2 sprints, and past that it
   tags with known findings documented as errata. Schedule slips;
   honesty about the release does not.
