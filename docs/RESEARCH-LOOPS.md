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
| 2 | Memory: heap growth bounds | same | Perceus PLDI'21 (TR read: garbage-freedom thm + acyclicity escape hatch); Pony ORCA OOPSLA'17 (heap bounding explicitly unimplemented); MAC OOPSLA'13; LFPL/AARA line; RustBelt (safety only) | Swift/Pony/Nim (nothing proven), Rust (safety, mechanized), Perceus (paper proofs) | **MODEL+PROOFS 90%** |
| 3 | Concurrency: deadlock freedom | SG-004: no deadlock-freedom proof for the actor system | | Erlang/BEAM, Pony, Akka, multiparty session types | PENDING |
| 4 | Security: taint / IFC | SG-003: taint tracking across dialect boundaries unspecified | | Jif, Flow Caml, Paragon, robust declassification | PENDING |
| 5 | Core semantics: substitution | 6 sorries in `Proofs/TypeSoundness/Preservation.lean` (subst lemmas) | POPLmark, Autosubst | Coq/Agda standard developments | PENDING |
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

### Iteration 1 — Subtyping (in progress)

Baseline finding (2026-10-09): the shipped `Subtype` inductive
(`Morph/Specs/TypeSystem/Spec.lean:680`) has only `refl` and `trans` — it
derives nothing beyond equality, and nothing in `HasType`/`typeCheck`
consumes it. GA-005 declares decidability "assumed" over a relation with no
content. Research agent dispatched for the cutting edge + language survey.
