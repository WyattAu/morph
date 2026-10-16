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
| 4 | Security: taint / IFC | SG-003: taint tracking across dialect boundaries unspecified | | Jif, Flow Caml, Paragon, robust declassification | PENDING |
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
