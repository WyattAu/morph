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
