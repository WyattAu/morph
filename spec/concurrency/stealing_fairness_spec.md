# Work-Stealing Fairness Specification

* File:* `concurrency/stealing_fairness_spec.md`
* Version:* 1.0.0
* Context:* Runtime scheduling — work stealing
* Formalism:* Chase–Lev deque discipline, sequential abstraction
* Status:* Active
* Machine-checked in:* `Morph/Specs/StealingFairness/`

---

## 1. Purpose and Scope

This specification formalizes the **correctness** of Morph's work-stealing
scheduler at the level of the deque discipline — which end each party touches,
and what happens when the owner and a thief race for the last task.

## 2. The gap this closes

`Morph/Specs/SchedulerRandomizedStealing/` names a fairness property and never
relates it to any behaviour:

| Defect | Evidence |
|---|---|
| No scheduler | no step function, no steal operation, no transition relation; `Ball` and `Bin` are bare records |
| The property is a snapshot | `isFair`/`isBalanced` constrain queue *lengths* at an instant |
| The property is false | an idle thief may steal repeatedly; after two steals the spread exceeds 1 — see §6 |
| No theorems | `Lemmas.lean` holds only `rfl` facts about `listMin`/`listMax` and `Nat.zero_le` |

So `isFair` had no theorem because it is not an invariant, and it is not what the
literature uses.

## 3. Research basis

| Source | What it fixes |
|---|---|
| **Chase & Lev** (SPAA 2005) | The discipline: owner pushes/pops the **bottom** (LIFO, cache-hot), thieves steal the **top** (FIFO, largest chunk). Their subtle point: a `popBottom` that empties the deque must CAS the top index "to guarantee that no concurrent steal operation will also return the deque's last entry". |
| **Lê, Pop, Cohen & Zappa Nardelli** (PPoPP 2013) | First correctness proof of the optimized deque under POWER/ARM; exhibited the failure where a racing steal on an empty deque returns a stale value — *fabrication*, strictly worse than duplication. |
| **Choi** (arXiv:2309.03642, Coq) | Mechanizes the deque against **linearizability** with a minimal trusted base. The specification is about *who gets which task* — never about queue lengths. |
| **Blumofe & Leiserson** | Provable efficiency requires **work conservation**: the scheduler must neither create nor destroy work. |

## 4. Definitions

```lean
structure Deque where
  bottom : List Task   -- owner end, newest first
  top    : List Task   -- thief end, oldest first
```

`bottom` and `top` are separate ends of the *same* deque — that is the whole
point of the structure. `pop` touches `bottom` only; `steal` touches `top` only.

## 5. Requirements discharged

| Theorem | Statement | Why |
|---|---|---|
| `pop_takes_newest` | `pop d = some (d', t) → d.bottom = t :: d'.bottom` | the owner end is LIFO |
| `steal_takes_oldest` | `steal d = some (d', t) → d.top = t :: d'.top` | the thief end is FIFO |
| `total_pop` | `pop d = some (d', t) → d'.total + 1 = d.total` | work conservation: running consumes exactly one task |
| `total_steal` | `steal d = some (d', t) → d'.total + 1 = d.total` | work conservation: stealing consumes exactly one task |
| `queued_push` | `total (push d t) = d.total + 1` | pushing creates exactly one task |
| `last_element_race_owner_first` | `pop [t] = some (empty, t) ∧ steal empty = none` | **the last-element race**: owner and thief cannot both get `t` |
| `last_element_race_thief_first` | `steal [t] = some (empty, t) ∧ pop empty = none` | the symmetric case |
| `steal_from_empty_is_none` | no successful steal of an empty deque | the thief's precondition; why a retry loop terminates per victim |

## 6. Why `isBalanced` is not the invariant

From queue lengths `[2,1,1,1]` — which satisfies `isBalanced` — an idle thief
steals twice from the first worker and reaches `[0,3,1,1]`, where the spread is
3. `isBalanced` is therefore not preserved by the very operation the module is
named after. It should not be stated as a fairness property at all; the
properties above are where work-stealing's correctness actually lives.

## 7. Scope: explicit non-claims

1. **No step relation, so no liveness bound.** The multi-worker accounting
   (`State.queued`, a `Consumes` closure and the termination bound
   `ran ≤ total`) was designed and *removed*: aggregating over worker queues
   requires rewriting inside a `foldl`'s accumulator, which is where this loop
   spent its remaining budget. The named theorem to add next is
   **`ran_le_work`** — along any sequence of executing steps the run log never
   outgrows the scheduler's total work. That is the statement `isFair` was
   reaching for, and it is the only honest version of "the scheduler
   terminates".
2. **No anti-duplication invariant across steps.** The per-operation facts are
   proven (`pop`/`steal` remove from their own end). The global invariant — a
   logged task is in no queue — additionally needs a no-duplicates invariant on
   deques plus the concurrent step relation.
3. **Sequential abstraction only.** The `CAS` on `top`, the last-element race
   under true concurrency, memory reclamation, and weak-memory models (Lê et
   al.) are out of scope; this is the sequential discipline those papers build
   on.
4. **No temporal fairness.** Starvation-freedom for a *particular* worker needs a
   policy assumption (random victim choice); none is made here.

## 8. Traceability

| Artifact | Location |
|---|---|
| Deque, discipline, state | `Morph/Specs/StealingFairness/Spec.lean` |
| The eight theorems above | `Morph/Specs/StealingFairness/Lemmas.lean` |
| The discipline, computed | `Morph/Specs/StealingFairness/Examples.lean` |
| Superseded module (defects in §2) | `Morph/Specs/SchedulerRandomizedStealing/` |
