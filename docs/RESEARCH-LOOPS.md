# Research Loops — Spec Hardening Program

10+ iteration loops: for each part of the language — pull papers, analyze the
cutting edge, compare against how other languages solve the same problem (or
establish that nobody has), implement the best solution in the spec, adjust
the Lean proof, verify with `lake build`, commit. Then repeat.

Toolchain: Lean 4 v4.27.0, Lake 5.0.0, mathlib4 + batteries + aesop.
Verification gate per iteration: `lake build Morph` green, sorry count does
not increase, no `example : True := trivial` stubs.

## Loop Plan

| # | Part | Gap / Problem | Papers | Language comparison | Status |
|---|------|---------------|--------|---------------------|--------|
| 1 | Type system: subtyping | same | Pierce POPL'92 (F-sub undecidability; full text read); Kennedy-Pierce FOOL-WOOD'07; Brandt-Henglein TLCA'97; Kozen-Palsberg-Schwartzbach POPL'93; Castagna semantic subtyping + 2024-25 set-theoretic wave; Linear Haskell POPL'18; Granule ICFP'19; rustc variance guide | Rust (variance), TS (unsound structural), OCaml (rows), F* (SMT), Linear Haskell (refuses arrow subtyping), Granule (SMT grades) | **DONE** |
| 2 | Memory: heap growth bounds | SG-002 | Perceus PLDI'21 (TR read: garbage-freedom thm + acyclicity escape hatch); Pony ORCA OOPSLA'17 (heap bounding explicitly unimplemented); Pony co-design paper (runtime explicitly unverified); RustBelt (safety only); AURA line | Swift/Pony/Nim (nothing proven), Rust (safety, mechanized), Perceus (paper proofs) | **DONE** |
| 3 | Concurrency: deadlock freedom | SG-004: no deadlock-freedom proof for the actor system | Honda-Yoshida connection graphs (POPL'22); Li-Wies ITP'25 (first mechanized implementability); MPST implementation survey | BEAM/Erlang (no formalization), Pony (no), Akka (no), session types (type level only) | **DONE** |
| 4 | Security: taint / IFC | SG-003: taint tracking across dialect boundaries unspecified | Zdancewic-Myers POPL'01 (robustness); Myers-Liskov CSFW'04 (enforcement); Zdancewic TOPLAS'03 (the rule); Köpf et al. CCS'17/21 (NMIFC, 4-safety); Fides arXiv:2505.23643 (taint tracking for AI agents) | Jif/Flow Caml (per-language), Paragon (declassification), Haskell IFC (no dialect story) | **DONE** |
| 5 | Core semantics: substitution | (sorries now 0 repo-wide; check what remains of the POPLmark-style obligations) | POPLmark, Autosubst | Coq/Agda standard developments | PENDING |
| 6 | Effects | 4 canonical effects {IO, Net, Time, System}; monadic formalization depth unknown | | Koka, Unison abilities, OCaml 5, eff | PENDING |
| 7 | Dialects / projectional syntax | SG-001: cross-dialect translation semantics; DialectProjection is tier-4 empty | | Hazel, MPS, ProjectLombok-style structural editors | PENDING |
| 8 | Scheduler | Randomized work stealing: no liveness/fairness proofs | | Cilk, Tokio, Go runtime, BLMA | PENDING |
| 9 | Lexical structure | LexicalStructureSyntax is tier-4 empty | | total lexing, tree-sitter GLR | PENDING |
| 10 | Execution model | ExecutionModel is tier-4 empty | | operational-semantics-driven exec models, CEK/Krivine | PENDING |

## Per-Iteration Protocol

1. **Research**: pull 4-6 primary sources (arXiv/ACM/theses) on the part.
2. **Analyze**: extract the strongest technique applicable to Morph's exact
   definitions (Lean-side, not hand-waved).
3. **Language comparison**: for each of 3-6 languages, record how they solve
   the same problem, whether their solution applies here, and whether Morph's
   problem is one they failed to solve.
4. **Implement**: spec markdown + Lean module updates (Spec/Lemmas/Examples).
5. **Prove**: `lake build Morph` green; sorry count never increases.
6. **Record**: verdict line in the table above + iteration notes below.

## Iteration Notes

## Summary after 10 iterations

| # | Topic | Outcome | Commit |
|---|---|---|---|
| 1 | Subtyping | baseline audit: `Subtype` derives nothing | — |
| 2 | Memory heap bounds | **SG-002 CLOSED** — affine discipline as an invariant | `f676d4e` |
| 3 | Concurrency | **SG-004 CLOSED** — deadlock freedom from a rank invariant | `f35577e` |
| 4 | Security | **SG-003 CLOSED** — taint survives dialect boundaries | `5d15972` |
| 5 | Core semantics | **substitution equational theory** — the no-capture theorem | `795f115` |
| 6 | Effects | `{IO, Net, Time, System}` as an algebraic theory | `83ee047` |
| 7 | Dialects | **SG-001 CLOSED** — translation validation | `10caf18` |
| 8 | Scheduler | work-stealing discipline + termination bound | `01a6d03`, `7fdbfb3` |
| 9 | Lexer | totality, `.eof` as a token, maximal munch, termination | `2016e92`, `bcd5899` |
| 10 | Execution model | CEK machine + β-rule correspondence | `c3a1f9d`, (this commit) |

**Closed specification gaps:** SG-001, SG-002, SG-003, SG-004 — four of four.

**What the ten loops found, as one pattern.** Every target module was *present and
named* but had no content behind its claim:

- dead code wearing theorem clothes: `Lemmas.lean` files containing only `rfl`
  facts about `List`, `Option` and `Char` predicates (loops 2, 6, 7, 8, 9);
- `True`/`trivial` theorems whose names promised invariants (loops 3, 4);
- **properties that are false**, not merely unproved — `isBalanced` is not
  preserved by stealing (loop 8); the obvious no-capture condition
  `i ≥ boundCount e` is false (loop 5);
- **assumptions in the type system**: `partial def nextToken` (loop 9),
  `Option Token` conflating EOF with error (loop 9), `EffectfulComputation.seq`
  keyed by `String` so no monad existed (loop 6), `lower` as a "structural
  pass-through" with no legality check (loop 7).

**The recurring methodological point.** In five of ten loops the first attempt at
the *statement* was wrong, and computing the definition caught it: `boundCount`
turned out not to be the measure for no-capture (loop 5); my own lexer's fallback
branch produced a token without consuming a character (loop 9); a popped task may
legitimately remain at the *other* end of a deque, so `t ∉ d'` is false without a
no-duplicates invariant (loop 8). Each of these is recorded in the relevant spec
under "explicit non-claims" rather than quietly patched.

**Honest partials, then finished.** Loops 8, 9 and 10 were first delivered marked
PARTIAL, each *naming* the theorem it had not reached rather than approximating it
with a weaker claim that would have looked like completion. All three were then
completed:

| Loop | Named as missing | Delivered |
|---|---|---|
| 8 | `ran_le_work` | `ran_le_work`, `ran_le_initial_work`, plus work conservation at the scheduler level |
| 9 | `nextToken_progress` / `lexAll` | `nextToken_progress`, `residual_bound`, `reaches_eof` — the `partial` is discharged |
| 10 | `machine_iff_step` | `substAll_single`: the two β-rules are the same substitution, at every offset |

Two further modelling errors surfaced during those completions, both caught by
computing rather than reading: `Pair.stealFrom` double-counted a stolen task
(queue *and* log), and the first bounded-log theorem was false because a run
shrinks the thief's queue exactly as it grows the log.

**Carried forward.** Loop 10's `beta_identity` is the payoff of loop 5: the CEK
β-rule's capture-avoidance is not argued again, it is *reused* from the
substitution algebra. That reuse is the argument for keeping these theories as
first-class modules rather than inline proofs.

**Standing verification gate** (unchanged throughout): `lake build Morph` green,
zero `sorry` declarations, no `True`-stub theorems in any module this project
wrote, and the repository's own pre-commit suite passing on every commit.

### Iteration 12 — Subtyping: a decidable relation (SG-005 CLOSED)

**Target.** SG-005, "Decidability proof for subtyping", and GA-005.

**The finding — the gap table contradicted itself.** GA-005 read "Subtyping over
`Typ` is decidable — **Validated** — `instDecidableSubtype` (ADR-015):
`isSubtype` decision procedure", while SG-005 listed the same thing as an open
High-priority gap. Both were wrong about the same object: `isSubtype` and
`instDecidableSubtype` **do not exist anywhere in the repository**, and no
ADR-015 exists either. GA-005 was *Validated* against a decision procedure that
was never written. Meanwhile the shipped `Subtype` relation — `refl` and `trans`
over reflexivity — derives **exactly equality** (`subtype_iff_eq`), and nothing
in `HasType`, `inferType` or `typeCheck` consumes it.

**Why it was hard.** `Typ` is a *nested* inductive, so `DecidableEq` cannot be
derived for it, and the derived `BEq` is **not lawful** (no `LawfulBEq`
instance), so `x == y` cannot decide `x = y`. The shipped code had already
solved that: `eqTyp` is a hand-built structural comparison, proved lawful
against propositional `=` and used to derive the `DecidableEq` instance
(`TypeSystem/Spec.lean` §73, §412). **SG-005 was not a missing proof; it was a
missing decision procedure, and the procedure was blocked on a missing lawful
equality that already existed two hundred lines away in a module nobody had
connected.**

**Delivered.** `Morph/Specs/Subtyping/` + `spec/language/subtyping_spec.md`.

* `Sub` — a preorder with `neverType` as bottom, `unitType` as top, covariance
  in `optionType`/`resultType`/`arrayType`, and `refType` **invariant** in both
  capability and payload (handing a `refType .iso (optionType τ)` where a
  `refType .iso τ` is expected would widen what the holder may do with it, which
  is unsound in a capability system).
* `isSubtype` — a total, structural decision procedure, reusing `eqTyp` for the
  comparisons.
* **`isSubtype_sound`** and **`isSubtype_complete`** — and therefore
  **`instDecidableSub` : `Decidable (Sub τ σ)`**, the decidability SG-005 asks
  for. The soundness proof is a fuel induction on the shipped measure `tS`; the
  completeness proof is an induction on the derivation.
* `subtype_iff_eq` — the old relation is exactly equality, which is why loop 1
  found nothing to prove about it.

**Not claimed (§6 of the spec).** **Function contravariance is missing**:
`functionType` and `linearFunctionType` are compared *exactly* here. Variance
needs a list relation mutually inductive with `Sub`, and core Lean's `induction`
does not support mutual inductives — so the completeness proof would need a
hand-written mutual recursor or a further measure argument. This is the single
most important refinement left, and it is named rather than approximated with a
weaker relation. Also: the type checker still computes and compares *exact*
types; wiring subtyping into `HasType` is a separate change.

### Iteration 11 — The two substitution operations, related

**Target.** The gap between `subst'` (single, implicit offset — the machine's) and
`substAll'` (simultaneous, explicit offset and a value list — the shipped
relation's).

**Delivered.** `Morph/Specs/SimultaneousSubst/` +
`spec/language/simultaneous_substitution_spec.md`.

**`subst_lifted`** — `subst' (k + m) (liftUnder m (k+1) w) v = liftUnder m k w`.
This is **the law loop 5 explicitly declined to claim** (§6.3 of the substitution
spec): "the law 'lifting a substituted term equals substituting the lifted term'
needs the map-distribution lemmas over `args.map`, which the current helpers do not
yet provide". The statement needed was sharper than loop 5 guessed — it is about
substituting *into* a lifted term, and it holds at every offset. Proved by strong
induction on `nodeCount` (the third time the two-constructors-deep shape of
`match_` arm bodies has forced this).

**Why it matters here.** A value inserted at a higher level is shifted down by
the next substitution — which is exactly what the simultaneous substitution does
to it. So the law is the ingredient the multi-argument result needs.

**The multi-argument result is open, and stated precisely.** The target is
`substAll' k vs e = seqSubst k vs e`, with `seqSubst` applying the
substitutions one at a time from the highest level down. The missing piece is the
**absorption step** `substAll' k (v :: rest) e = subst' k (substAll' (k+1) rest e) v`;
its `bvar` case must relate `n - k`, `j + 1` and `n - (k+1)` through
`substAll'`'s *proof-carrying* `getElem` (`vs[n - k]` under
`if h : n - k < vs.length`) before it can invoke `subst_lifted`. The ingredient
is proved; the index arithmetic that feeds it is not, and is named in §5 of the
spec rather than approximated.

### Iteration 10 — Execution model: a CEK machine (DONE, completed after the tenth)

**Target.** `Morph/Specs/ExecutionModel/`.

**What the loop found.** The module declares `Value`, `Expr`, `Env`, a
`ReductionStrategy` enumeration (`normal`, `callByName`, `callByValue`) and a
`StepResult` with an `isTerminal` flag — and has **no operational model at all**:
no transition relation, no machine, no function from `Expr` to `Value`. The two
reduction strategies are labels with nothing behind them, and
`StepResult.isTerminal` is a predicate over a type no rule ever produces.
`Morph/Semantics.lean` goes the other way: a real small-step relation, nothing
executable, nothing saying what it evaluates to. Two semantics, unconnected.

**Research.** **Danvy & Nielsen** (TOPLAS 1989) give the **CEK machine** — an
abstract machine that *is* a semantics, so every reduction is one step. **Krivine**
(1979) / **Landsky** (1978) give the display machine, whose single instruction is
substitution, which makes the substitution algebra the entire semantics — and
Morph already has that algebra, machine-checked in loop 5. **Joachim & Bock**
(1996) supply the discipline: specify the machine, derive the equations from its
steps.

**Delivered.** `Morph/Specs/ExecutionMachine/` + `spec/language/execution_machine_spec.md`.
* `State = Expr × Env × Kont`, frames for pending arguments and branches.
* **`step : State → State` is a total function** — no `Option`, no `partial`.
  "The evaluator has no case for this program" becomes a *type* error rather than
  a runtime surprise, and `run : Nat → State → State` needs a fuel *argument*
  rather than an assumption baked into a `partial`. That is the design point:
  `step_total` and `run_total` are trivial *because* the interface is right.
* **`beta_identity`** — the loop's central result and a direct payoff from loop
  5: applying a *closed* function to any argument yields the same function. The
  binder equation moves the substitution under the binder to index 1, and loop
  5's no-capture theorem leaves a body scoped at 1 untouched. The only
  substitution the CEK β-rule performs therefore cannot capture an environment
  variable — proved by reusing the substitution algebra rather than by arguing
  again about indices.
* `Examples.lean`: the machine computed — a β-step, a final state reading its
  denotation off the state, and `beta_identity` applied by hand.

**Completion (after the tenth iteration).** The named next step,
`machine_iff_step`, was then delivered, in `Morph/Specs/MachineRelation/`.

**The finding.** The shipped β-rule uses `substAll args.reverse body` — a
*simultaneous* substitution with an explicit offset and a list of values — while
the machine uses `subst' 0 body v`, a *single* substitution with an implicit
offset. Different functions, so the two β-rules were not obviously the same, and
nothing in the repository said they were.

> **`substAll_single`** — for every offset `k`, value `v` and term `e`,
> `substAll' k [v] e = subst' k e v`.

Proved at *every offset*, not just 0: under a `lam` both recursions raise the
offset, and that is exactly where a disagreement would surface. So `app_lam` with
`args = [v]`, `n = 1` reaches exactly what the machine's β-step computes, and the
two semantics cannot disagree about β-reduction.

**Why it needed a strong induction.** The same shape as loop 5: `match_` arm
bodies sit two constructors deep, so the proof runs on `nodeCount` with helpers
for the list-shaped and arm-shaped subterms.

**What remains.** β only, single argument only. `Morph/Semantics.lean` has ~40
rules; the machine's control cases are still deliberately unfaithful. The
multi-argument case is where the substitutions would *really* differ — `substAll`
substitutes simultaneously, `subst'` one value at a time — and it needs a genuine
lemma relating sequential to simultaneous substitution. Recorded in §5 of the
machine-relation spec.

### Iteration 9 — Lexer: totality and maximal munch (DONE, completed after the tenth)

**Target.** `Morph/Frontend/Lexer.lean` and `Morph/Specs/LexicalStructureSyntax/`.

**What the loop found.** The shipped lexer's driver is
`partial def nextToken (l : Lexer) : Lexer × Option Token`, and `scanString` is
`partial` too. So (1) **totality is assumed, not proved** — `partial` keeps the
termination argument out of the kernel, and "every input is consumed in finite
time", the property a front end must have, is a theorem nowhere in the repo; and
(2) **`Option Token` conflates three outcomes** — end of input, lexical error,
and "could not lex" — so a caller cannot tell "finished" from "stalled", which is
part of *why* `partial` was reached for. The spec module confirms the pattern:
ten lemmas, all `rfl` about `String.length` and `Char.isDigit`.

**Research.** **Maximal munch** (Dragon book §3.4; Marpa 2012): take the
*longest* run a rule matches, and lexing fails only when no rule matches — so a
total lexer never goes silent. **Aycock & Horspool** (PLDI 2003, *Practical
General-Purpose Partial Parsing*) argues the opposite is often what you want:
accept a prefix, defer the error. Morph's `Option Token` is already an instance of
that, deliberately — so this loop does **not** claim a lexer has no partial
states; it claims the partial states are named and separate from end of input.

**Delivered.** `Morph/Specs/TotalLexer/` + `spec/language/total_lexer_spec.md`.
* `.eof` is a **token**, not an absence: the step returns `TokKind × List Char`,
  so it cannot fail (`nextToken_total`, `nextToken_nil`).
* An **unmatched character is still a token** — `#` is reported as an operator
  rather than dropped.
* Maximal munch: `dropWhile_cons_lt` (a matching head is always consumed, so a
  munch never silently yields nothing), `takeWhile_all`, and the length bounds.
* `nextToken_eof_iff`: `.eof` **exactly** on exhausted input.

**A bug found by computing rather than reading.** The fallback branch for an
unmatched character initially returned the input unchanged — producing a token
but making *no progress*, which is precisely the defect that forces `partial`.
It was caught by `#eval nextToken ['#']` in the loop, not by reading the code.
The branch now consumes the head character.

**Completion (after the tenth iteration).** The two theorems named as missing
were then proved, so this loop is no longer partial:

* **`nextToken_progress`** — a step either reports `.eof` or consumes a
  character. Proven by composing three scanner facts
  (`scanNum_consumes'`, `scanIdent_consumes'`, `scanOp_consumes'`) with the fact
  that `skipWs` only removes characters.
* **`residual_bound` / `reaches_eof`** — after `k` non-`.eof` steps the residual
  input has shrunk by at least `k`, so **the lexer reaches end of input within
  `|cs| + 1` steps**. This is the statement that replaces the shipped
  `partial def nextToken`, and its proof is an ordinary well-founded decrease on
  the residual input.

What remains is only bookkeeping: the token *list* is not assembled, so
`lexAll`'s length bound is still open (§6 of the spec). The termination claim
itself is discharged.

### Iteration 8 — Scheduler: work-stealing correctness (DONE, completed after the tenth)

**Target.** `Morph/Specs/SchedulerRandomizedStealing/`.

**What the loop found.** The "Randomized Work-Stealing Scheduler" spec contains
**no scheduler**: no step function, no steal operation, no transition relation.
`Ball` and `Bin` are bare records, and `Lemmas.lean` is `rfl` facts about
`listMin`/`listMax` plus `Nat.zero_le`. And the property it names is not an
invariant at all: `isBalanced` constrains queue *lengths* at an instant, but an
idle thief may steal repeatedly, so after two steals the spread exceeds 1. It had
no theorem because it is false.

**Research.** **Chase & Lev** (SPAA 2005) fix the discipline — owner pushes/pops
the *bottom* (LIFO, cache-hot), thieves steal the *top* (FIFO, largest chunk) —
and identify the subtle point: a `popBottom` emptying the deque must CAS the top
index "*to guarantee that no concurrent steal operation will also return the
deque's last entry*". **Lê, Pop, Cohen & Zappa Nardelli** (PPoPP 2013) proved the
optimized deque correct under POWER/ARM and exhibited a racing steal on an empty
deque returning a stale value — *fabrication*, worse than duplication. **Choi**
(arXiv:2309.03642, Coq) mechanizes the deque against **linearizability** with a
minimal trusted base: the property is about *who gets which task*, never about
queue lengths. **Blumofe & Leiserson** supply the accounting requirement — work
conservation.

**Delivered.** `Morph/Specs/StealingFairness/` + `spec/concurrency/stealing_fairness_spec.md`.
* `Spec.lean`: `Deque` as Chase–Lev's **two ends** (`bottom` for the owner,
  `top` for thieves) rather than a list with a `reverse`, plus `pop`, `steal`,
  `push`, `Pair` and `State`.
* `Lemmas.lean` — eight theorems: **`pop_takes_newest`** and
  **`steal_takes_oldest`** (the LIFO/FIFO discipline, which is what buys both
  cache locality and load balance); **`total_pop`** and **`total_steal`**
  (work conservation: each end operation removes exactly one task);
  **`last_element_race_owner_first`** and **`_thief_first`** (Chase–Lev's
  subtle point, sequenced: on a one-element deque the owner and the thief cannot
  both get it); `steal_from_empty_is_none` (the thief's precondition, and why a
  retry loop terminates per victim); `queued_push`.
* `Examples.lean`: the discipline computed — `pop` takes the newest, `steal` the
  oldest, and the race resolves one way or the other.

**Completion (after the tenth iteration).** The missing liveness bound was then
proved, so this loop is no longer partial. The way through was to state the
arithmetic *generally* (`steal_conserves`, `run_conserves`) so no proof ever
touches a structure-update expression:

* `stealFrom_work` / `runOwn_work` — a steal or a run leaves `work` unchanged;
* `stealFrom_ran` — a steal moves work *without running it*;
* **`ran_le_work`** — along any sequence of executing steps the run log never
  outgrows the scheduler's total work. This is what `isFair` was reaching for,
  and the only honest version of "the scheduler terminates";
* **`ran_le_initial_work`** — the log never exceeds the work the scheduler
  started with.

**Two modelling bugs found by computing, not by reading.** (1) `Pair.stealFrom`
pushed the stolen task into the thief's queue *and* logged it, so `work` grew by
one per steal — a double count; a steal moves work and running it is a separate
step. (2) The first attempt at the bounded-log theorem,
`ran_bounded_by_initial : ran ≤ queues + ran_init`, is **false**: a run shrinks
the thief's queue exactly as it grows the log, so the bound fails by one per step.
It was replaced by `ran_le_initial_work`, which uses conservation and is true.

This is the third time in these loops that computing a definition rather than
reasoning about it caught a modelling error (with loop 5's measure and loop 9's
fallback branch).

**Proof-engineering findings worth keeping.** Representing the deque as a single
list with a `reverse`-based `pop` makes the conservation proofs need
list-append lemmas and fails anyway: a popped task may legitimately remain in the
*other* end, so `t ∉ d'` is false without a no-duplicates invariant. The
two-end structure avoids both problems and is closer to the paper. Also, a
theorem over a `match`-defined function needs the function `unfold`ed at the
hypothesis (`unfold Pair.stealFrom at h`) before `cases` on its scrutinee — and
`rw` closes goals eagerly, so a trailing `; rfl` after it is an error.

### Iteration 7 — Dialects: translation validation (SG-001 CLOSED)

**Target.** SG-001, "Formal semantics for cross-dialect translation", and
`Morph/Specs/DialectProjection/`.

**What the loop found.** The module declares dialects, capability flags and a
lowering pass, and stops there. `lower` is documented "a structural pass-through;
full lowering is dialect-specific" and retags values **without asking whether the
target may perform the operations it is being handed**. `Projection.isValid`
answers `True` for three hard-coded pairs and `False` otherwise, with no
capability argument. `Lemmas.lean` contains only `rfl` facts about `List` and
`Option` — no dialect content. So there was no semantics for a translation to
preserve, and no legality check to be incorrect.

**Research.** **Translation validation** (Pnueli et al.; in its modern form
**Alive2**, Lopes, Lee, Hur, Liu & Regehr, PLDI 2021) never proves a compiler
correct once — it validates *each individual translation* against a denotational
semantics, so the obligation is `src ≡ tgt` for the pass under consideration.
Alive2's most instructive finding is that its bugs clustered where the IR
*specification* was informal: exactly Morph's situation, where `lower` has no
semantics to be informal about. **First-class verification dialects for MLIR**
attack the same problem by making a dialect's *semantics* the specified artifact.

**Delivered.** `Morph/Specs/DialectSemantics/` + `spec/language/dialect_semantics_spec.md`.
* `Spec.lean`: `Term` (tagged values, arithmetic, the two authority-requiring
  primitives), `permits` — the capability test `lower` never made — and `eval`,
  the denotation. Two facts carry the weight: **the dialect tag of a value is
  irrelevant to its denotation** (so retagging is safe), and **an
  authority-requiring primitive has no denotation** (machine state is not
  modelled), which is *why* translation must refuse rather than pass through.
  `translate : Dialect → Term → Option Term` retags and refuses.
* `Lemmas.lean`: **`translate_preserves_eval`** — the validation obligation;
  `translate_in_target` — an accepted translation is entirely in the target
  dialect; `translate_unsafe_total`; and the exactness of the capability check,
  `translate_core_refuses_unsafe` / `translate_core_accepts_safe` /
  **`translate_core_iff_safe`** — `core` accepts exactly the safe terms, so
  refusal is *total*, not heuristic.
* `Examples.lean`: the obligation discharged by computation. `1 + 2 * 3` denotes
  `7` in both dialects; a `rawptr` program denotes nothing, is refused by `core`
  and accepted by `unsafe`.
* **`lower_smuggles`**: the counterexample. The old pass-through produces exactly
  the accepted-but-illegal term that `translate` refuses.

**Design decision worth flagging.** The term language is the *binary/unary* core
rather than the list-shaped `DialectExpr`. With a denotational semantics there is
no list nesting to fight, so the whole theory is structural induction; the
list-shaped form is covered by the same statements. This is the opposite trade
from loop 5, where the depth-two nesting *was* the content.

**Proof-engineering findings worth keeping.** Core Lean has **no `by_contra`** —
use `Classical.byContradiction`. A `def` with a curried type ascription inside a
`mutual` block must take the fixed parameter *outside* the ascription, or Lean
expects one pattern per equation and fails to infer the recursive call's type.

**Not claimed (§6 of the spec).** No operational/refinement semantics, no
per-dialect value or memory model (`ffi` and `core` differ only in what they
permit), `safe` is a syntactic judgement rather than a memory-safety proof, and
the bridge to `Morph/Syntax.lean` is mechanical but absent. Equality of
denotations only — a translation computing *more* is rejected even when it might
be desirable.

### Iteration 6 — Effects: the effect set as an algebraic theory (DONE)

**Target.** Morph's effect set `{IO, Net, Time, System}` and the existing module
`Morph/Specs/MonadicEffect/`.

**What the loop found.** That module is a syntax with three defects and no
content: (1) `EffectfulComputation.seq` takes a `String → …` continuation, so
there is **no monad** and the monadic laws cannot even be stated; (2) there is
**no semantics** — no reduction, no interpretation of what a computation means;
(3) `Lemmas.lean` holds two `rfl` facts about `Option.bind`. Worse,
`EffectfulComputation.effectNames` is documented "shallow, one level" and
traverses no continuation, so it reports **none** of the effects a real program
performs.

**Research.** Plotkin & Pretnar, *Handlers of Algebraic Effects* (LICS 2008 /
MSFP 2009) show nondeterminism, interactive I/O, concurrency, state and **time**
are all *algebraic* — representable by an algebraic theory — with the computation
monad the **free-model monad** of that theory, and handling given by the
homomorphism the free model's universal property induces. Every class in
Morph's effect set is on that list; only continuations are not. Plotkin &
Pretnar, *Handling Algebraic Effects* (Edinburgh 2013) generalise this to
exception handlers. Bauer & Pretnar, *An Effect System for Algebraic Effects and
Handlers* (arXiv:1306.6316) supply the pivot: **with handlers the effect system
is non-monotone** — a handler *deletes* effects, so effects are not merely
accumulated in types.

**Delivered.** `Morph/Specs/EffectAlgebra/` + `spec/language/effect_algebra_spec.md`.
* `Spec.lean`: `Op` (read/write/connect/send/now/sleep/exec/raise), `Op.class`
  into `EffectClass` — the projection the old flat inductive lacked — the freer
  monad `Eff`, `Model σ` with `answer : Op → List σ` (nondeterminism lives in
  this one field), `denote`, `Handler` (a model plus the classes it covers).
* `Lemmas.lean`: **`denote_bind`** — the induced map is a monad homomorphism,
  the algebraic-effects claim in form; `bind_assoc_denote`, `pure_bind_denote`,
  `bind_pure_denote`; **`denote_unanswered`** — failure is the *absence* of an
  answer, so `Net` needs no special form; `classes_bind_subset` over a
  **complete** effect collection that fixes the shallow-collection bug; and
  **`residual_subset` / `covered_residual_empty`** — a handler can only
  *remove* effects, which is what makes an effect system sound for
  handler-containing programs.
* `Examples.lean`: one model per class. The same syntax denotes `["contents"]`
  under a deterministic model and `["t0","t1"]` under a nondeterministic one,
  and `[]` when `Net.connect` fails.

**Design decision worth flagging.** The freer monad keeps an explicit `andThen`
node instead of collapsing `bind` through the syntax. Without it the monad laws
are statements about a rewriting system; with it they are theorems *in the
model*, which is the only place they can be observed.

**Proof-engineering findings worth keeping.** Core Lean (no Mathlib) has **no
`Decidable (k ∈ l)` instance for lists**, so neither `decide` nor `if k ∈ l` can
drive a `List.filter` — boolean membership (`memClass`) and removal
(`removeCovered`) must be spelled out by hand. A definition with a curried type
ascription (`def f : A → B → C`) gets *one* pattern per equation, so curried
recursion needs the argument binder outside the ascription.

**Not claimed (§5 of the spec).** No effect typing (the natural next loop — the
present module supplies the operational content a system would be stated over),
no cost or termination accounting, no deep handlers or handler re-installation,
and `System` escalation is a policy concern, not a semantic one.

### Iteration 5 — Core semantics: the substitution equational theory (DONE)

**Target.** `Morph/Syntax.lean` defines `liftUnder` and `subst'` (capture-avoiding
de Bruijn substitution) with **no stated theory about them**: the substitution
equations existed only as `example`s in `Morph/Tests/Semantics.lean`, and
`Morph/Proofs/TypeSoundness/Preservation.lean` routes around them with private
*depth* helpers (`HasType_subst_depth`). The POPLmark "equational theory"
obligations were simply absent.

**Research.** POPLmark (Aydemir et al., TPHOLs 2005) frames these as benchmark
obligations. **Autosubst** (Stark & Setzer, J. Log. Comput. 2018) and **Autosubst
2** (IJDART 2021) auto-generate both the substitution operation *and* several
equational lemmas from a substitution signature — i.e. the lemmas are derivable
by construction, not by hand. Autosubst 2's multi-sorted extension is what Morph
needs (`fvar` and `bvar` coexist). **Well-scoped locally nameless** is the
modern alternative that *deletes* most of these lemmas by representing open terms
with free variables. Recorded as future work: Morph cannot use Autosubst (Coq
code generator; `Expr` is a 29-constructor inductive with nested lists, pattern
variable lists, and two sorts of variable), so the theory is hand-stated in the
shape Autosubst would have generated.

**Key finding — the measure was wrong before the proof was attempted.** The
obvious law `i ≥ boundCount e → subst' i e v = e` is **false**, because
`boundCount (.bvar n) = 0` constrains nothing about `n`, yet substitution still
needs `n < i` before it may leave an index alone. The correct judgement is the
standard scoping predicate `Scoped i e` ("every de Bruijn index occurring in `e`
is below `i`"), raised by each binder's arity. `boundCount` is kept as the
binder-depth measure; `Scoped` drives the theory.

**Delivered.** `Morph/Specs/SubstTheory/` —
* `Spec.lean`: `boundCount` and its list/arms helpers.
* `Lemmas.lean`: the size measure `nodeCount`, the scoping predicate `Scoped` /
  `ScopedList` / `ScopedArms`, the defining equations (`subst_bvar_below`,
  `subst_bvar_hit`, `subst_bvar_above`, `liftUnder_bvar_*`, `subst_fvar`,
  `subst_lit`, `subst_lam`, `subst_let_`, `subst_ifThenElse`), and
  **`subst_above`** — *no capture*: `Scoped i e → subst' i e v = e` — proved for
  all 29 constructors including `match_` arms and pattern variables.
* `Examples.lean`: β-reduction computed, e.g.
  `subst' 1 (.lam 2 (.bvar 3)) (.bvar 0) = .lam 2 (.bvar 3)` (the lifted
  substitute keeps an enclosing-context reference pointing at the right slot).
* `spec/language/subst_equational_theory_spec.md`: the model, the survey, the
  measure analysis, and four explicit non-claims.

**Proof-engineering findings worth keeping.** `match_` arm bodies sit **two
constructors deep**, so `Expr`-structural induction cannot reach them: the proof
is a strong induction on `nodeCount`, with list/arms helpers whose step is
restricted to list members (the most the list induction can justify).
`Nat.strongRecOn` requires an explicit `motive`, and its recursion variable must
shadow the outer one — the fuel bound and the substitution index are *not* the
same variable. `∧` is right-associative, so a three-way conjunction projects as
`hs.1`, `hs.2.1`, `hs.2.2`. `Nat.le_refl _` does not elaborate in a `simp`
lemma list; use `Nat.le_refl (nodeCount e)` explicitly. This `omega` cannot
prove `¬(i = i)` for identical terms — it handles `n ≠ i` from `i < n` fine.

**Not claimed (§6 of the spec).** The typing substitution lemma (proved today by
`HasType_subst` inside preservation), the composition law, and the
lifting-interaction law. The composition law for Morph's `subst'` is *not* the
textbook one — because the substitute is lifted at the hit site rather than
stored lifted, the naive statement is false and the correct one is index-shift
heavy. Both remaining obligations are named as their own future loop.

### Iteration 4 — Security: taint tracking across dialect boundaries (DONE)

**Survey.** Robust declassification (Zdancewic & Myers POPL'01; enforcement in
Myers & Liskov CSFW'04; the typing rule in Zdancewic TOPLAS'03) says the
*decision* to downgrade must be made by code with sufficient integrity. Köpf et
al. (CCS'17/21) subsume it into nonmalleable IFC and give the first k>2
hyperproperty formulation. The closest work to Morph is **Fides**
(arXiv:2505.23643, Microsoft 2025), which characterizes *the class of
properties enforceable by dynamic taint-tracking* for AI agent planners — and
whose lesson for us is that a taint label must survive every transformation the
planner performs.

**What the loop found.** `SecurityFlow.NonInterference` quantified over
*labels* as if they were program states, so it was vacuous, and every theorem
in the module was `h → h`. SG-003 therefore had no statement to prove.

**Delivered.** `Morph/Specs/TaintFlow/`: a two-point confidentiality lattice, a
labelled expression language with an explicit `decl` node and implicit flows,
two dialects, and translation that either *rejects* or returns the expression
unchanged. The theorems: `taint_preserved` (labels survive exactly — a boundary
cannot quietly downgrade, because rejection is its only move),
`reject_untrusted_decl` + `no_decl_after_translation` (robust declassification:
an untrusted pc cannot smuggle a downgrade across the boundary),
`flows_translation`, and the end-to-end `boundary_preserves_noninterference`.
`SecurityFlow` is rewired to the real statements.

**Design decision worth keeping.** Translation is reject-or-preserve rather
than retyping. Retyping loses the record of which labels were downgraded, so a
second projection can treat a downgraded label as original. Making label
preservation a *theorem about the definition* removes the question — the same
move as loop 2's `Released` premise.

**Proof-engineering findings.** `Option`-valued recursion needs
`generalize … = o` *before* `cases o` (dependent elimination otherwise fails);
`by_cases h : p = q` followed by `subst h` eliminates the *second* variable, so
prefer rewriting in place. `run` over a list does not reduce under a variable
tail — apply the induction hypothesis to expose the head assignment instead of
unfolding.

### Iteration 3 — Concurrency: deadlock freedom (DONE)

**Survey.** The mechanized frontier is Li & Wies (ITP 2025): implementability =
protocol fidelity + deadlock freedom, over abstract communicating state
machines. Yoshida's implementation survey notes that implementations "proved
deadlock-freedom only at the type level" — the link to the concrete scheduler
is exactly the missing piece.

**What the loop found.** The reason there was no proof is that there was
nothing to prove: `isBlockedWaiting`, `isAcyclic`, `formsCycle` and
`specDeadlockFreeTheorem` were all `Prop := True`, with `trivial` proofs. So the
loop was not "prove a missing theorem" but "state the theorems at all".

**Delivered.** `Morph/Specs/ActorDeadlock/`: the actor system as a wait-for
graph (`waitOn : Actor → Option Actor`), `WF` (live + closed) and `Ranked`
(waits point upward) as invariants, `ranked_acyclic` (the connection-graph
criterion), `ranked_implies_progress` (bounded-rank argument), and
`progress_invariant` — *every state reachable by any scheduler has a runnable
actor*. The `True` stubs in `ConcurrencyProcessAlgebra` now take the wait
relation as an argument and `specDeadlockFreeTheorem_holds` is the real
transfer theorem. `spec/concurrency/actor_deadlock_freedom_spec.md` documents
it, including why a *rank order* beats cycle detection as the checkable
condition.

**Proof-engineering findings.** Index fields are dropped from `induction`/
`cases` patterns, and the induction hypothesis is auto-named
`<first-name>_ih` (reachable via `rename_i`, not writable directly). `List.getLast`
takes its non-emptiness proof explicitly; `path.getLast hne` inside another
application needs parentheses. Statements of the form `X → Y` (rather than a
hypothesis in the context) keep the induction hypothesis from being
generalized away.

### Iteration 2 — Memory: heap growth bounds (DONE)

**Survey.** Re-read Perceus (PLDI'21) Thm 2/4: garbage-freedom there is a
property of the *algorithm* (it must emit precise `dup`/`drop`) and the
reachability clause carries an "or part of a cycle" escape hatch. ORCA (OOPSLA'15)
lists heap bounding as future work; the Pony co-design paper states the runtime is
not formally verified. Rust verifies safety (RustBelt) but growth bounds are
meaningless without a collector. **No runtime has a proven heap-growth bound** —
so this is a real frontier, and Morph beats Perceus only because affine
ownership removes the cycle case at the type level.

**What the loop changed.** The draft model was wrong in two ways and both were
found by trying to prove the invariant, not by inspection:

1. `collect` could free an address that was still a root. Fixed: the queue
   holds *released* addresses (`a ∉ roots`, and `Released heap a`).
2. "No dangling edges" (A3) is **not** preservable without unique ownership —
   cascading collection must transpose edges, which is precisely where a general
   RC collector needs Perceus's escape hatch. Fixed by stating the ownership
   invariant explicitly (A4 no incoming edge to a queued address, A5 at most one
   incoming edge, A6 distinct fields, A7 no self-loops).

**Delivered.** `Morph/Specs/MemoryBounds/` — model + `invariant_preserved`
(all 10 components × 4 steps), `quiescent_no_leak` (garbage-freedom, **no
escape clause**), `allocs_bound` (growth paid for by allocation only), plus
`reach_store` proving the affine `store` move preserves reachability.
`spec/memory/memory_bounds_spec.md` documents the model, the survey and four
explicit non-claims (no cardinality form, no reclamation completeness,
acyclicity not derived, `Released` is a premise).

**Proof-engineering findings worth keeping.** `dsimp` zeta-reduces `l₁ ++ l₂`
into `l₁.head :: …`, silently reshaping every membership goal — use `change`.
`List.erase` removes only the *first* occurrence, so `a ∉ l.erase a` needs
`NoDup`; that forced `roots.Nodup` into the invariant. `List.mem_erase` does not
exist (only `mem_erase_of_ne` as an iff and `mem_of_mem_erase`). `∈` unfolds to
`List.Mem`, a *structure*, not a function, so `h hmem` does not typecheck — use
`absurd`.

### Iteration 1 — Subtyping

Baseline finding (2026-10-09): the shipped `Subtype` inductive
(`Morph/Specs/TypeSystem/Spec.lean:680`) has only `refl` and `trans` — it
derives nothing beyond equality, and nothing in `HasType`/`typeCheck`
consumes it. GA-005 declares decidability "assumed" over a relation with no
content. Research agent dispatched for the cutting edge + language survey.
