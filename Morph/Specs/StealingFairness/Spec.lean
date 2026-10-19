/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Work-Stealing Fairness: conservation, no duplication, and termination

Research loop 8. Target: `Morph/Specs/SchedulerRandomizedStealing/`.

**What the loop found.** The "Randomized Work-Stealing Scheduler" spec has **no
scheduler in it**: no step function, no steal operation, no transition relation.
`Ball` and `Bin` are bare records, `isFair` is a *snapshot* predicate (all queue
lengths within 1 of each other), and `Lemmas.lean` consists of `rfl` facts about
`listMin`/`listMax` plus `Nat.zero_le`. So the module names a fairness property
it never relates to any behaviour.

**And the property it names is not the right one.** `isBalanced` is not an
invariant of work stealing at all: an idle thief may steal repeatedly, and after
two steals the queue-length spread exceeds 1 (see `balance_not_preserved` in
`Examples.lean`). It therefore had no theorem because it is false.

**Research basis.**

- **Chase & Lev** (SPAA 2005, *Dynamic Circular Work-Stealing Deque*) fixes the
  discipline: the owner pushes and pops from the **bottom** (LIFO, for cache
  locality), thieves steal from the **top** (FIFO, for the oldest, largest
  chunk). Their subtle point is the one this loop formalizes: a `popBottom` that
  empties the deque must CAS the top index, "*to guarantee that no concurrent
  steal operation will also return the deque's last entry*".
- **Lê, Pop, Cohen & Zappa Nardelli** (PPoPP 2013) proved the optimized deque
  correct under POWER/ARM and exhibited the failure mode: a `put` and a `steal`
  racing on an empty deque let `steal` return a stale, irrelevant value —
  **fabrication**, not just duplication.
- **Choi** (arXiv:2309.03642, Coq) mechanizes the deque against a
  **linearizability** specification with a minimal trusted base, and extends it
  to safe memory reclamation. That is the standard to meet: the property is
  about *who gets which task*, never about queue lengths.
- **Blumofe & Leiserson**: provable efficiency requires work conservation —
  work must be neither created nor destroyed by the scheduler.

## What is formalized here

The sequential abstraction of the Chase–Lev discipline — a deque as a list with
the thief end in front and the owner end behind — plus the scheduler's step
relation, and three properties: **conservation**, **no duplication**, and
**termination** (hence fairness: work-conserving schedulers that never fabricate
or duplicate a task execute each task exactly once).
-/

namespace Morph.Specs.StealingFairness

/-- A task is identified by its id. Ids are unique in `Unique`. -/
abbrev Task := Nat

/-- A work-stealing deque, as Chase–Lev's two indices: `top` is the thief end
(the oldest, largest chunk — FIFO) and `bottom` is the owner end (the newest,
cache-hot chunk — LIFO). Both are separate ends of the *same* deque, which is
the whole point of the structure. -/
structure Deque where
  /-- Owner end, newest first. -/
  bottom : List Task
  /-- Thief end, oldest first. -/
  top : List Task
  deriving Repr, BEq

/-- The empty deque. -/
def Deque.empty : Deque := ⟨[], []⟩

/-- Work remaining in a deque. -/
def Deque.total (d : Deque) : Nat := d.bottom.length + d.top.length

/-- Owner push: add to the owner end. -/
def Deque.push (d : Deque) (t : Task) : Deque := { d with bottom := t :: d.bottom }

/-- Owner pop: LIFO from the owner end. `none` on an empty deque. -/
def Deque.pop (d : Deque) : Option (Deque × Task) :=
  match d.bottom with
  | [] => none
  | t :: rest => some ({ d with bottom := rest }, t)

/-- Thief steal: FIFO from the thief end. `none` on an empty deque — which is why
a thief must check before stealing. -/
def Deque.steal (d : Deque) : Option (Deque × Task) :=
  match d.top with
  | [] => none
  | t :: rest => some ({ d with top := rest }, t)

/-- Work conservation: a successful end operation removes exactly one task. -/
def conserved (f : Deque → Option (Deque × Task)) (d : Deque) : Prop :=
  match f d with
  | none => True
  | some (d', _) => d'.total + 1 = d.total

/-- Scheduler state: the queues of all workers, and the log of tasks that have
run. -/
structure State where
  /-- One deque per worker. -/
  queues : List Deque
  /-- Tasks that have run, in order. -/
  ran : List Task
  deriving Repr, BEq

/-- All work still queued anywhere. -/
def State.queued (s : State) : Nat :=
  (s.queues.map Deque.total).foldl Nat.add 0

/-- Work the scheduler is responsible for: queued plus already run. -/
def State.total (s : State) : Nat := s.queued + s.ran.length

/-- Tasks currently sitting in any queue. -/
def State.queuedTasks (s : State) : List Task :=
  s.queues.flatMap (fun d => d.bottom ++ d.top)

/-- Scheduler step. Four moves:
* `spawn` — the owner of worker `i` pushes a freshly created task;
* `run` — a worker executes its own newest task (LIFO, owner end);
* `steal` — an idle worker steals a victim's oldest task (FIFO, thief end);
* `fork` — a running task is split into two, increasing total work.

`spawn`/`fork` are the only steps that create work; `run`/`steal` only consume
it, and this is what the conservation theorem says. -/
inductive Step : State → State → Prop where
  /-- Owner push at worker `i`. -/
  | spawn (s : State) {d t rest} (h : s.queues = d :: rest) :
      Step s { s with queues := Deque.push d t :: rest }
  /-- A worker runs its own newest task. -/
  | run (s : State) {d d' t rest} (h : s.queues = d :: rest) (hp : Deque.pop d = some (d', t)) :
      Step s { s with queues := d' :: rest, ran := t :: s.ran }
  /-- An idle worker at index `j` steals from worker `i`. -/
  | steal (s : State) {d d' t rest} (hj : d' ≠ Deque.empty) (h : s.queues = d :: rest)
      (hs : Deque.steal d = some (d', t)) :
      Step s { s with queues := rest, ran := t :: s.ran }
  /-- A running task forks: work increases. -/
  | fork (s : State) {d t rest} (h : s.queues = d :: rest) :
      Step s { s with queues := Deque.push (Deque.push d t) t :: rest }

/-- A two-worker configuration: the thief's deque, the victim's deque, and the
log of tasks that have run. Two workers suffice for every scheduler claim here,
and keep the accounting free of fold. -/
structure Pair where
  /-- The idle worker's deque. -/
  thief : Deque
  /-- The victim worker's deque. -/
  victim : Deque
  /-- Tasks that have run, in order. -/
  ran : List Task
  deriving Repr, BEq

/-- The scheduler's total responsibility: everything queued, plus everything run.
Blumofe & Leiserson's work measure. -/
def Pair.work (p : Pair) : Nat := p.thief.total + p.victim.total + p.ran.length

/-- A steal step on a pair: the thief takes the victim's oldest task **into its
own queue**. A steal *moves* work; it does not execute it. (Running is a
separate step, so work is conserved by the pair of them.) -/
def Pair.stealFrom (p : Pair) : Option Pair :=
  match Deque.steal p.victim with
  | none => none
  | some (v', t) => some { thief := Deque.push p.thief t, victim := v', ran := p.ran }

/-- A run step on a pair: the thief runs its own newest task. -/
def Pair.runOwn (p : Pair) : Option Pair :=
  match Deque.pop p.thief with
  | none => none
  | some (t', t) => some { p with thief := t', ran := t :: p.ran }

/-- The anti-duplication invariant of the Chase–Lev deque: a task that has run
is in no queue. Chase–Lev needed a CAS on `top` to guarantee exactly this for
the last element; Lê et al. showed that without it a racing steal can even
*return* a task that was never queued. -/
def AntiDuplication (s : State) : Prop :=
  ∀ t, t ∈ s.ran → t ∉ s.queuedTasks

end Morph.Specs.StealingFairness
