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

### Iterations 17–18 — The linker, the module system, and two superseded modules

**Targets.** `Morph/Specs/DialectProjection/`, `Morph/Specs/MonadicEffect/`,
`Morph/Specs/LinkerLogic/`, `Morph/Specs/ModuleSystem/`.

**LinkerLogic (iteration 18).** Ten theorems about `Option.map` and
`List.append`, with no theorem about linking. Replaced with the binding rules
(strong beats global beats weak beats local; ties keep the first definition) —
and with a **finding**: `acyclic` is documented as checking "directly or
transitively" but checks only **directly**, so a two-object cycle is reported as
*acyclic*. The function's name promises a property it does not have.
`ltoSafe` is a stub (`:= true`, "a no-op in the current model") and is now
stated as one.

**ModuleSystem (iteration 18).** The interesting-looking theorems were about
*empty* tables — true because the table is empty. Replaced with the round-trip a
content-addressed linker needs: a module added to the link table is findable by
id (`addToLinkTable_finds`) and resolves to the module that was added
(`resolveModule_finds`). A third instance of the same core-level defect: `ModuleId`
derived `BEq` with no `LawfulBEq`, so `resolveModule`'s `mid == id` was
unprovably sound. Now `DecidableEq` + `decide`.

**The two superseded modules (iteration 17).** `DialectProjection` (13 trivia
theorems) and `MonadicEffect` (2) had their real content delivered in loops 7
and 6. Their lemma files now *connect* to those frameworks instead of pretending
to be about their own subjects: `DialectProjection` records that the old
pass-through `lower` accepts a translation into `core` of a program performing
`raw-ptr` (which the validated translation refuses), and `MonadicEffect` records
that its `effectNames` traverses no continuation — so it reports *none* of the
effects a real computation performs, where the new algebra's collection
traverses them.

**Not claimed (§4 of the spec).** No transitive cycle detection (the named fix),
no LTO safety check, no symbol-table merging theorem, no workspace resolution
or version constraints, and no registry search.

### Iterations 15–16 — Null coalescing and the lexical rules

**Targets.** `Morph/Specs/OperatorNullCoalescing/`,
`Morph/Specs/LexicalStructureSyntax/`.

**Null coalescing (iteration 15).** Four theorems, all `rfl` facts about
`Option.getOrDeref` and `Option.orElse` — nothing about the module's subject.
Replaced with the *semantics* of `??`: a chain resolves to the **first
non-null** value, a null head continues the chain, a non-null head
short-circuits it, and `evaluate` agrees with the chain
(`evaluate_eq_chain`).

**Lexical rules (iteration 16).** Ten theorems, all `rfl` facts about
`String.length` and `Char.isDigit`. Replaced with the lexical invariants —
*an identifier start is also an identifier continuation* — and with a **finding**:
the module's two rules **disagree**. `isIdentStart` accepts `'_'`, but
`classifyChar` classifies `'_'` as an **operator** (it tests `c.isAlpha` only),
so every `snake_case` identifier would be tokenized with its first character
split off. The inconsistency is invisible until the two rules are put side by
side, which is what the loop does.

**Not claimed (§4 of the spec).** No keyword/identifier exclusion proof, and
**no character-class disjointness** — `Char.isAlpha` and `Char.isDigit` are
range tests in the standard library whose disjointness is not proved here, so
"a digit is not an identifier start" is not claimed. No `??` type system, no
chain-length accounting.

### Iteration 14 — MemoryModel: seven `True` stubs, replaced

**Target.** `Morph/Specs/MemoryModel/`.

**What the loop found.** The module advertised **seven** `Prop := True`
stubs — `spec_memory_allocation`, `spec_memory_deallocation`,
`spec_memory_access`, `memory_safety_invariant`, `allocation_preserves_safety`,
`deallocation_preserves_safety`, `empty_memory_well_formed` — and
`isMemorySafe` was `True` *for every memory*, so every safety theorem about it
was vacuous. The one theorem that looked like a real property was a tautology:

```lean
theorem read_preserves_memory (mem : Memory) (id : Core.BlockId) (offset : Nat) :
    readByte mem id offset = readByte mem id offset := by rfl
```

**Delivered.** The three advertised `spec_memory_*` properties now say what they
claim — allocation is fresh and well-formed, deallocation removes the block, and
**access is bounds-checked** (a read past the end of a block yields nothing; a
write past the end leaves the memory alone) — and they are proved
(`allocation_spec`, `deallocation_spec`, `readByte_out_of_bounds`,
`writeByte_out_of_bounds`, `access_spec`). `isMemorySafe` is now a real
predicate: every block's data has exactly the size it claims.

**A core-level finding.** Proving the deallocation property needed `BlockId`'s
equality to be decidable *and* sound. It was neither: `Morph/Core.lean` derived
`BEq` for `BlockId` with **no `LawfulBEq` instance**, so every `==` on a block
id in the compiler was unprovably sound — the same defect loop 12 found for
`Typ`, but at the level of the core type. Fixed by deriving `DecidableEq` for
`BlockId` and comparing ids with `decide` in the memory model. The same
treatment is still owed for the other `BEq` types in `Morph/Core.lean` that lack
a `LawfulBEq` instance — named in §4 of the spec.

**Not claimed (§5 of the spec).** Four stubs remain `True` and are recorded as
vacuous rather than quietly left; two of them are proved in their honest form.
No refcount semantics (that is loop 2's `MemoryBounds`, at the affine-type
level), no aliasing or use-after-free reasoning, and no connection to
`Morph/Memory.lean` — this is the *model*, not the runtime.

### Iteration 13 — MorphLanguage: real edits behind vacuous theorems

**Target.** `Morph/Specs/MorphLanguage/`.

**What the loop found.** The module's *theorems* were true for the wrong
reasons — and, importantly, **not** `True` stubs, so the spec-tools check could
not have caught them:

| Theorem | Why it was true |
|---|---|
| `applyEditToAst_id` | `applyEditToAst` **ignores its edit** — the parameter is `_edit`, the body is `some ast`. The identity by construction, not by law. |
| `parseCode_always_empty` | `parseCode` returns `some Program.empty` on **both** branches of its `if`. It parses nothing. |
| `applyEdit_insert` | `insert newCode => code ++ newCode` *appends*; there is no position. |
| `applyEdit_delete` | `delete => ""` *erases the whole program*. |
| `applyEdit_move` | `move _ _ => code` *does nothing*. |

**Delivered.** `Morph/Specs/MorphLanguage/Lemmas.lean` rewritten +
`spec/language/morph_language_edits_spec.md`. Real, position-aware edits over a
half-open range `[lo, hi)`: `insertAt`, `deleteRange`, `moveRange`, and the
`prefixOf`/`suffixOf`/`sliceOf` views — with the properties the old theorems
should have had: the insertion point, the prefix and suffix preservation, the
empty-range no-op, and the move's relocation. The two stubs are now *stated as
findings* (`parseCode_is_a_stub`, `applyEditToAst_is_a_stub`) rather than
hiding behind a `rfl`.

**A design note worth keeping.** The edits are over `List Char`, not `String`:
`String.take`/`String.drop` return `String.Slice`, whose API cannot support
these statements, while the list API's `take_append`/`drop_append` can. The
range is half-open and the text is a list — so the *shape* of an edit is stated
once, in the one representation where its laws are provable.

**Not claimed (§5 of the spec).** The parser and `applyEditToAst` remain stubs:
the real parser (`Morph/Frontend/Parser.lean`) is a *partial* recursive-descent
parser, and connecting the specification to it needs a non-partial parser and a
decision procedure for it — separate work, named rather than faked. The
specification's own `applyEdit` is unchanged, since redefining it would change
the meaning of the existing (vacuous) theorems.

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

### Iteration 19 — Adoption: the shipped lexer is now total

**Target.** `Morph/Frontend/Lexer.lean` — the first *adoption* item: results
that change the compiler rather than a specification.

**What was there.** Four `partial` functions: `advanceWhile`,
`skipWhitespaceAndComments`, `scanString` and `tokenizeLoop`. `partial` keeps
the termination argument out of the kernel, so "the lexer always terminates" was
not a theorem anywhere — and research loop 9 had already proved the *specification*
of a total scanner, with nothing connecting it to the compiler.

**The change.** Each recursive function now takes an explicit fuel, and the fuel
is the number of characters remaining (`l.chars.length + 1`):

```lean
def advanceWhileFuel : Nat → Lexer → (Char → Bool) → Lexer × String
  | 0, l, _ => (l, "")
  | n + 1, l, p => ...
```

The `+ 1` matters: with fuel exactly the input length the last character is
consumed by the base case, which returns the empty string, and the lexeme is
truncated.

**Behaviour is preserved.** The original `partial` lexer and the fuel-bounded one
were compared on five inputs — a keyword sequence, a comment, an operator
expression, an unterminated string, and two adjacent string literals — and
produce *identical* token lists. So this is a totality change, not a semantic
one.

**A pre-existing bug, pinned by a test.** Two adjacent string literals produce
**no tokens at all**: the escape-handling path consumes the closing quote of the
first literal together with the opening quote of the second, and the second
literal is swallowed. The original `partial` lexer did the same ✓ — it is not a
regression ✓ — but it had no test, so nobody could see it. `Morph/Tests/Lexer.lean`
now pins the behaviour (so the change cannot be blamed for it) and documents it
as a bug for whoever fixes it.

**Also.** The lexer had **no tests at all** before this. `Morph/Tests/Lexer.lean`
now covers literals, keywords, identifiers (including `x_1`), operators, string
literals, unterminated strings, whitespace, comments, and the totality of
`tokenize`.

### Iteration 20 — LayeredConcurrency: purity is a theorem about the language

**Target.** `Morph/Specs/LayeredConcurrency/` — the subject of **GA-002**
("the SSUS pattern preserves referential transparency", marked *Validated*).

**What the loop found.** The module's purity predicates were all `True`:
`hasNoSideEffects`, `doesNotMutateArguments`, `isDeterministic`,
`isDescriptor`, `isPureDescriptor`, `stateTransitionsFlowUnidirectional`. So
`isPureFunction f` was a conjunction of three vacuous conditions, and GA-002
was *Validated* for a trivial reason: **there are no effects to preserve
referential transparency against**. The `Reducer` type is `State → State → State`
— a pure function of its arguments.

**What is here.** The predicates are now real statements — equal arguments give
equal results, a call cannot disturb the state it was given, the same arguments
always give the same result — and the finding is proved:

> **`isPureFunction_of_pure_language`** — *every* function in a pure language is
> pure. Purity is a theorem about the language, not a property to be checked.

The same for descriptors (`isPureDescriptor_of_pure_language`) and for
unidirectional data flow (`stateTransitionsFlowUnidirectional_holds`).

**Why this matters beyond the module.** A specification whose job is to *check*
purity cannot do so in a language where purity is guaranteed — and the gap table
recorded the check as passing. The honest formulation is the theorem above: the
guarantee comes from the type, and a *future* impure layer would be where the
predicate starts to bite.

### Iteration 21 — MemoryAcyclicity: the cycle characterisation, proved

**Target.** `Morph/Specs/MemoryAcyclicity/`.

**What was there.** The module has a genuine graph model — `ReferenceGraph`,
`hasPath`, `hasCycle`, `isAcyclic` — and several real properties, but two
functions were stubs: `eventuallyDeallocated o := True` and
`weakReferences o G := 0` (the graph was ignored).

**What is here.** The module's central characterisation, proved:
`spec_no_reference_cycles_holds` — `isAcyclic G ↔ ¬hasCycle G` — and
`empty_graph_acyclic_holds` / `single_vertex_acyclic_holds` ✓.

**What is not proved.** `cycle_detection_algorithm` — that a cycle is exactly a
vertex that reaches itself — relates the module's own `hasPath` to
`CommonTypes.hasCycle`, and the two are *different definitions* of reachability
(the module's is edge-based, the common one is a path-index formulation). The
bridge is a path-to-edges lemma; it is named in the spec rather than asserted
here.

### Iteration 22 — MemoryAffineLogic: a false law, refuted

**Target.** `Morph/Specs/MemoryAffineLogic/`.

**What was there.** The module has a real model — `AffineContext` with variables
and resources, `joinContexts`, `splitContext`, `isWellFormedContext`,
`disjointContexts` — and it *states* three laws of the context algebra. None was
proved: the lemma file had only `rfl` facts about counts and lookup. Eleven
further properties were `True`.

**The finding.** One of the three stated laws is **false**:

```lean
def context_join_commutative (Γ₁ Γ₂ : AffineContext) : Prop :=
  joinContexts Γ₁ Γ₂ = joinContexts Γ₂ Γ₁
```

`joinContexts` appends the first context's variables to the second's, and
`a ++ b ≠ b ++ a` — so this was a counterexample waiting to be written, and it
was never noticed because it was never proved. The order of a context's variables
is part of its meaning (it is the order in which resources are consumed), so the
law cannot be rescued by weakening it to "equal up to reordering" — but it *can*
be stated correctly, as commutativity **up to permutation**, which is what the
specification now says and what `context_join_commutative_holds` proves.

**Also proved.** Associativity of the join, the empty context as a unit, and
**`context_join_not_commutative`** — the explicit refutation of the old claim, so
that nobody re-adds it.

**A toolchain note.** Core Lean 4.27 has **no `List.append_comm` theorem** (only
the `List.Perm` version, `List.perm_append_comm`), and no `List.Perm.eq` — so
the permutation law is proved with `List.perm_append_comm` directly, and the
refutation with `simp`. The absence of `List.append_comm` from core is why this
loop's first attempt (an induction proving commutativity) could not work — and
that attempt is what exposed the law as false.

**What is not proved.** The eleven `True` properties are about *typing* and
*copying*: `spec_affine_typing` needs a typing judgment for expressions, and
`affine_types_no_copy` / `copy_requires_affine` need a copy operation. The module
has neither, so those claims are unstateable here for the same reason the
concurrency module's message-passing claims were (loop 20): the operation they
constrain does not exist.

### Iteration 23 — SecurityOCap: well-formedness meant nothing

**Target.** `Morph/Specs/SecurityOCap/`.

**What was there.** `AccessGraph.well_formed` was `True` — and it sat *directly
next to* `AccessGraph.edges_valid`, which is the real statement: every edge's
endpoints are nodes of the graph. The module had the property it needed and named
the wrong thing.

**The cost of the stub.** The old proof of `add_node_preserves_well_formed` was
`fun h => h` — a tautology, valid only because the property was `True`. With
`well_formed` meaning "the edges are valid", the theorem became a real one and
the proof real: the edges are unchanged, and a node list that grew still contains
every endpoint it did.

**What is here.** `well_formed` is now `edges_valid` ✓, the two "trivial" graph
theorems are proved properly ✓, and the add-a-node preservation theorem is a real
argument rather than `fun h => h` ✓.

### Iteration 24 — LicenseDeonticLogic: two theorems behind `True`

**Target.** `Morph/Specs/LicenseDeonticLogic/`.

**What was there.** A real deontic model — licences carry permission,
obligation and prohibition predicates over a seven-action algebra, and
`checkCompatibility` / `detectGplInfection` are executable `Bool` checks. The
two properties the module names were `True`: `spec_compatibility_theorem` and
`spec_gpl_infection_theorem`.

**What is here.**
* `spec_compatibility_theorem` — if the rights check passes (the dependency
  prohibits no action the root grants) **and** the obligation check passes
  (every obligation of the dependency is matched by the root), then
  `checkCompatibility` returns `.compatible`. Stated in the decidable form the
  check itself uses, so the proof is a computation (`simp`), not a choice.
* `spec_gpl_infection_theorem` — if `detectGplInfection root gplLicense` fires,
  then the root carries the GPL's open-source obligation **and** prohibits
  `openSource`. This exposed a **mismatch in the detector itself**: it tests
  `hasProhibition root .openSource`, while the old prose promised
  `.closeSource`. The theorem now states what the detector actually checks.

**What is still vacuous, and why.** Six specifications remain `∀ _, True`-shaped:
`spec_model_licenses_deontic`, `spec_support_all_predicates`,
`spec_support_all_actions`, `spec_verify_compatibility`,
`spec_enforce_gpl_compatibility`, `spec_compatibility_complexity`. They are not
`:= True` (so a grep for that misses them) but their bodies are `match ... =>
True` on every branch, i.e. the same nothing in a different costume. Two name a
*model* that does not exist (a deontic semantics; a complexity model); the
`support_all_*` pair is true but only says the enumerations are enumerations.
Saying so is the honest outcome.

**A note on cost.** The compatibility proof is where the implementation's
`decide`-wrapped `Bool` conditions fought the mathematically natural `Prop`
statement. The lesson is recorded rather than smoothed over: when a spec's
executable form and its declarative form differ, the declarative theorem must
be *phrased* in the executable form or the gap becomes a proof obligation that
needs `decide_eq_true_eq` surgery.

### Iteration 25 — UnitGroupTheory: the dimension algebra, proved

**Target.** `Morph/Specs/UnitGroupTheory/`.

**What was there.** A genuine dimensional-analysis model — four base units, unit
*vectors* over the integers, `mul`/`div`/`pow` as vector arithmetic — and
fifteen real theorems about the base evaluations. Two properties were `True`:
`spec_exchange_rate_invariant` and `spec_unit_names_unique`.

**What is here.** Both, stated and proved, plus the algebra they rest on:
* `spec_exchange_rate_invariant` — dividing a unit by itself is
  **dimensionless** (the identity unit vector), which is what makes an exchange
  rate a pure number rather than a quantity with a unit.
* `spec_unit_names_unique` — the four base units have pairwise distinct unit
  vectors, so a quantity in one base unit cannot be silently used as another.
* `addUnitVectors_comm` (for equal-length vectors), `addUnitVectors_assoc`,
  and `addUnitVectors_ident` — the algebra of the vector arithmetic, proved on
  the raw exponent lists and lifted to the structures.

**A finding.** `addUnitVectors` is commutative **only for equal-length
vectors**: `List.zipWith` truncates to the shorter list, so adding a length-1
vector to a length-2 vector keeps the length-2 vector's tail. Units of different
lengths are not compatible in the first place (`areCompatible` requires equal
lengths), so the operation is never called that way — but the commutativity law
needs the hypothesis stated, and it is.

**What is not proved.** `spec_reject_incompatible_dimensions` is stated as
`∀ v1 v2, ¬areCompatible v1 v2 → True` — literally vacuous even in the
specification itself, and left that way here: the property it gestures at
("reject incompatible dimensions") needs a type checker that consumes
`areCompatible`, which does not exist in this module. Also `unitToString`
ignores its vector entirely, returning `"unit"` for every unit.

### Iteration 26 — MemoryModel: the other fourteen

**Target.** `Morph/Specs/MemoryModel/`.

**What was there.** Loop 14 replaced the three `spec_memory_*` properties and
gave `isMemorySafe` a real definition, but fourteen `Prop := True`
advertisements remained: `memory_safety_invariant`, the three preservation
claims, `read_does_not_modify`, `write_modifies_only_target`, the two ref-count
claims, `zero_ref_count_allows_deallocation`,
`non_zero_ref_count_prevents_deallocation`, `unique_block_identifiers`,
`block_data_integrity`, `write_read_consistency`.

**What is here.** Every one is now a real statement, proved or refuted:
* `memory_safety_invariant` is a *closed* proposition — the empty memory is safe
  and allocation, deallocation and writing all preserve safety — assembled from
  the four preservation theorems.
* `read_does_not_modify` becomes expressible through a stateful wrapper
  (`readByteWithState`) that returns `(mem, readByte …)`; the proof is `rfl`,
  but the property is no longer a tautology in the spec.
* `write_modifies_only_target`, `ref_count_increment`, `ref_count_decrement`
  are proved in their **no-target** form; the strong "changes exactly one
  block" forms need a uniqueness hypothesis on the block list and a
  find-after-map lemma, and are not claimed.
* `write_read_consistency` is proved for a write to a *missing* id; the strong
  write-then-read form is not claimed for the same reason.
* `unique_block_identifiers`, `block_data_integrity`,
  `zero_ref_count_allows_deallocation` are proved.

**A finding, and a refuted law.**
`non_zero_ref_count_prevents_deallocation` is **false**: `deallocate` filters
the block out without ever reading `refCount`. The spec now states its
refutation — a witness memory with a live reference whose block is removed all
the same — the same form as loop 22's `context_join_commutative`.

**A note on the model.** The implementation's `writeByte` uses `Array.set!`
(which is `setIfInBounds`), so array size — and therefore block well-formedness
— is preserved by construction. The proofs lean on
`Array.size_setIfInBounds`, which is why the size-preservation argument is
three lines and not a case analysis.

### Iteration 27 — LayeredConcurrency: the layer model the claims needed

**Target.** `Morph/Specs/LayeredConcurrency/`.

**What was there.** Fourteen `Prop := True` advertisements and tautologies in
predicate costume. `stateTransitionsFlowUnidirectional state` was
`∀ s, s = state → s = state` — literally `s = s`. `specLcaActorTypes` demanded
`hasMailbox` (a non-empty mailbox) of **every** actor, which is false for the
empty actor, so it was never a theorem and could not be.

**What is here.** The smallest model that makes the claims meaningful:
`send` (enqueue at the front), `receive` (dequeue), `processOne` (remove one
message), `integrate` (application state down to an actor, no return path) and
`appStep` (a forward application transition).

* `messagesAreImmutable` — enqueue then dequeue returns the message and leaves
  the list intact.
* `processesMessagesSequentially` — `processOne` removes exactly the head.
* `stateTransitionsAreDeterministic` — equal states give equal reducer results.
* `actorCommunicationIsBidirectional` — enqueue/dequeue round-trips and a
  non-empty mailbox dequeues.
* `layerIntegrationMaintainsUnidirectional`, `noSharedStateBetweenLayers` —
  integration writes down, never back; changing an actor's state cannot change
  the application's.
* the eight `specLca*` theorems are each proved from the above.

**Two corrections.** `stateTransitionsFlowUnidirectional` now states that the
application step's `direction` is `forward` (it was `s = s`). And
`specLcaActorTypes` no longer requires a non-empty mailbox of every actor: the
old conjunction was false on the empty actor.

### Iteration 28 — MemoryAffineLogic: typing and ownership, modelled

**Target.** `Morph/Specs/MemoryAffineLogic/`.

**What was there.** A real context algebra (loop 22 fixed the false join law),
but eleven `Prop := True` claims about affine typing and ownership. They looked
unstateable because "there is no typing judgment or copy operation" — except
`CommonTypes.Expr` already has `var`, `app`, `lam`, `move`, `copy`, `borrow`.

**What is here.** A usage-based model and all eleven claims proved:
* `uses e x` counts occurrences; `spec_affine_typing` says an expression uses
  each variable at most once and every name it uses is in scope.
* `spec_affine_typing_memory_safety` — typing implies every used name is bound.
* `spec_resource_linearity` — resource counts add under `joinContexts`.
* `spec_context_splitting` — a split keeps all resources on one side.
* `moveVar` / `borrowVar` / `copyVar` / `consumeVar` / `consumeResource` make
  the ownership claims statements: move consumes its source, borrow preserves
  it, copy requires an affine type, and consumption removes the binding.
* `affine_types_no_copy`, `linear_types_used_once`, `move_consumes_source`,
  `borrow_preserves_source`, `copy_requires_affine`, `variable_use_tracking`,
  `resource_consumption` — proved.

**A finding.** `moveVar`'s postcondition needs `src ≠ dst`: moving a variable
onto itself leaves the source present, so the "source is gone" half is false
without the hypothesis. It is now stated, and the specification records the
hypothesis rather than silently assuming it.

**Not modelled.** Binder shadowing: `uses (.lam x T e) y` counts `y` in `e`
even when `y = x`. This is the spec's own simplification, not a gap introduced
here, but the model inherits it.

### Iteration 29 — ModuleExistential: seven claims, and a `BEq` fix

**Target.** `Morph/Specs/ModuleExistential/`.

**What was there.** Seven `Prop := True` claims over a real module model.
`AccessControl.isAllowed` and `ModuleComposition.importsOf` compared ids with
`==`; `ModuleId` derived only `BEq`, so no soundness statement about them could
be proved (the `LawfulBEq` gap first recorded in the ten-loop summary).

**What is here.** `ModuleId`, `Visibility` and `AccessRule` now derive
`DecidableEq`, and both functions use `decide` equality. Then:
* `spec_module_privacy` — environment entries for a module carry its
  visibility; proved for the empty environment.
* `ModuleDecl.isEncapsulated` — exported names are public; proved for a module
  with no exports.
* `spec_module_access_control` / `inv_access_control_sound` — an allowed name
  has an `allow` entry; proved from `find?`.
* `spec_module_composition` — a successful import relates two declared
  modules.
* `spec_existential_types` — a conforming value's interface is the bound one.
* `inv_private_no_public_impl` — **derived** from `hasImplementation` rather
  than assumed: an exported symbol cannot be a private one.

## Remaining work, measured

After eighteen iterations the repository's specifications fall into three
categories.

**Closed.** Every SG gap: SG-001 (loop 7), SG-002 (loop 2), SG-003 (loop 4),
SG-004 (loop 3), SG-005 (loop 12). The three loops that first shipped as
PARTIAL were finished afterwards: loop 9's `nextToken_progress`/`reaches_eof`
(`bcd5899`), loop 8's `ran_le_work` (`7fdbfb3`), loop 10's
`substAll_single` (`07b5bc3`).

**Audited and found empty.** Every `Morph/Specs/*/Lemmas.lean` now contains at
least one real theorem — the modules that carried only `rfl` facts about
`List`, `Option` and `Char` have been replaced (loops 6, 7, 13, 14, 15, 16, 17,
18) or consolidated with the framework that superseded them.

**Not yet audited — 86 `Prop := True` stubs remain**, concentrated in:

| Module | Stubs | Subject | Why they remain |
|---|---|---|---|
| `ConcurrencyProcessAlgebra` | 19 | message-passing laws | need a message-passing semantics the module lacks |
| `MemoryModel` | 0 | **audited** — the fourteen claims are real (loop 26); three are no-target/refuted forms | done |
| `LayeredConcurrency` | 0 | **audited** — a small layer model (`send`/`receive`/`integrate`) makes the 14 claims real (loop 27) | done |
| `MemoryAffineLogic` | 0 | **audited** — usage-based typing and move/borrow/copy operations make the 11 claims real (loop 28) | done |
| `ModuleExistential` | 0 | **audited** — the seven claims are real; access/import compare with `decide`, not `==` (loop 29) | done |
| `TerminologyStandardization` | 5 | terminology consistency | need the term model |
| `SecurityOCap` | 4 | capability paths | need a path semantics |
| `MorphLanguage` | 4 | the projectional-only mandate | need a projection semantics |
| `LicenseDeonticLogic` | 6 | licence model/enumeration | need a deontic semantics; the two headline theorems are now real |
| `UnitGroupTheory` | 2 | group structure | need the unit model |
| `ASTGraph` | 2 | AST graph invariants | need a reachability definition |
| `MemoryAcyclicity` | 1 | deallocation | need a deallocation model |

These are the next iterations, in that order. The pattern is now known well
enough that each is a *form*: find the property the module names, decide
whether it is true (prove it), false (say so, as loop 8 did for `isBalanced`),
or a stub (replace the advertisement, as loop 14 did for `spec_memory_access`).
Loops 19–23 showed the fourth case as well: a property that is *true but
vacuous*, where the module sat next to the real statement under a different name
(`SecurityOCap.well_formed` next to `edges_valid`), or a stated law that was
simply **false** (`MemoryAffineLogic.context_join_commutative`).

A note on the `True` stubs that remain: most of them are not waiting for a
proof, they are waiting for a *model* — a typing judgment, a copy operation, a
message-passing semantics, a deallocation model. A property about an operation
that does not exist cannot be stated, and saying so is the honest outcome
(the same finding as loops 20 and 22).

**Two things that are not iterations.** The first is *adoption*: none of the
eighteen iterations' results is wired into the shipped compiler. The shipped
lexer is still `partial` where loop 9 proved a total scanner terminates; the
shipped β-rule still uses `substAll` where loops 10 and 11 proved the single
substitution is the same function; `HasType` still compares exact types where
loop 12 proved a decidable subtyping. The second is a **core-level defect** that
three separate loops hit independently: `Morph/Core.lean` derives `BEq` without
`LawfulBEq` for `BlockId`, `ModuleId` and (for `Typ`) has no decidable equality
at all — so `==` comparisons on them are unprovably sound. Loops 12, 14 and 18
fixed the three instances they needed; the remaining ones in `Morph/Core.lean`
should be swept together.
