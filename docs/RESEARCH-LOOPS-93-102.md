# Research Loops 93–102 — Spec Research Pass (papers → analysis → spec → Lean)

Session protocol (every loop):

1. **Research** — pull the current literature (papers, language docs, release
   notes) on one language-design area; identify the strongest known solution.
2. **Analyze** — compare it to Morph's current spec position: is Morph solving
   a problem others solved better, a problem nobody solved, or re-solving a
   solved problem worse? Decide: adopt / adapt / reject, with reasons.
3. **Spec** — implement the decision in the affected `spec/` documents.
4. **Lean** — adjust the machine-checked theory (`Morph/Specs/...`) to match:
   new lemmas for what we adopt, refutations for what the spec overstated.
5. **Verify** — `lake build Morph` 0 warnings/0 errors, spec lint clean on
   touched files, `scripts/regression-snapshot.sh` no regressions.
6. **Log** — this file, per-loop entry with the sources used.

Plan (target areas, chosen to cover every major spec layer):

| Loop | Area | Research targets | Spec files | Lean module |
|------|------|------------------|-----------|-------------|
| 93 | Effects & handlers | Koka effect rows, Unison abilities, OCaml 5 handlers, Plotkin–Pretnar algebraic effects | `type/effect_system_spec.md`, `language/effect_algebra_spec.md` | EffectAlgebra |
| 94 | Memory: affine + ARC | Koka Perceus (FPRC), Pony ORCA, Swift sendability, cycle collection | `memory/*` | ArcAffineIntegration |
| 95 | Error handling | Rust `?`/Try, Zig error unions, Gleam result, exceptions-as-effects | `language/morph_language_spec.md` §15 | MorphLanguage |
| 96 | Subtyping | MLsub algebraic subtyping, Simple-sub, set-theoretic types | `language/subtyping_spec.md` | Subtyping |
| 97 | Modules | 1ML, Dreyer modules, ML functors vs existentials | `language/module_system_spec.md` | ModuleSystem |
| 98 | Concurrency | Structured concurrency (Trio), Erlang/OTP supervision, Pony causal messaging | `concurrency/*` | LayeredConcurrency |
| 99 | Substitution/closures | Autosubst (Schönfinkel–de Bruijn parallel subst), locally nameless | `language/simultaneous_substitution_spec.md` | SimultaneousSubst |
| 100 | Syntax/projectional editing | Hazel typed holes, Unison hashing, Intentional post-mortems; GA-003 | `language/dialect_projection_spec.md` | DialectProjection |
| 101 | Inference/unification | Paterson–Wegman, algorithm W completeness, OutsideIn(X) | `type/type_unification_spec.md` | TypeSystem |
| 102 | Determinism/execution | Deterministic parallelism (LVars), confluence of the core semantics | `concurrency/execution_model_spec.md` | ExecutionModel |

Baseline at session start: commit `30ac08e` (prior-session loops 84–92
checkpoint), Lean v4.27.0, build 402 jobs 0 warnings, 1508 real theorems,
58 spec modules, 0 sorries.

---

## Loop 93 — Effect system: rows, the pure row, and handler elimination (DONE)

**Research** (papers pulled and analyzed):
- Leijen, *Algebraic Effects for Functional Programming* (MSR-TR-2016, Koka):
  effects as polymorphic **rows** of operations, handlers as the elimination
  form, effect sets carried in the arrow with subset instantiation.
- Unison *abilities* docs: same convergence — pure code has the empty
  ability request; request handling closes the row.
- Bauer & Pretnar, *An Effect System for Algebraic Effects and Handlers*
  (arXiv:1306.6316): with handlers the system is **non-monotone** — handling
  deletes covered classes. Already cited (loop 6) by the Lean module but
  absent from the type-system spec.
- Plotkin & Pretnar (LICS 2008): handlers = models of the algebraic theory.

**Analysis.** Morph's closed 4-class world is a defensible restriction — a
4-atom row system, not an unsolved problem — but the spec contradicted both
itself and its own Lean theory:
1. §2.3 claimed a power-set lattice yet set ⊥ = IO and asserted
   $E \sqcup \text{IO} = E$ — false in a power set once ∅ exists.
2. §4.4.1 gave literals effect IO, making *every* expression effectful: the
   Pure capability was unreachable, and §6's own correctness proof used
   literals as the zero-effect base case (self-contradiction, and a stale
   "Pure-as-effect" the C-003 resolution had supposedly removed).
3. No handler/elimination rule existed — every rule was monotone union, so
   the spec and `EffectAlgebra` (which proves residuals shrink) diverged.

Koka/Unison/OCaml 5 verdict: adopt ∅-bottom rows, pure literals, and the
non-monotone handler rule; keep the closed class set (deliberate simplicity
for green-thread mapping — documented as such).

**Spec** (`spec/type/effect_system_spec.md` → v2.1.0):
- Effects are **rows**: subsets of 𝒞 = {io, net, time, system}; the four
  named effects are canonical rows; ∅ = the pure row (Pure stays a
  capability, C-003 stands); chain ∅ ⊑ IO ⊑ Net ⊑ Time ⊑ System.
- Lattice identities fixed ($E \sqcup \emptyset = E$; the old IO-identity
  restricted to named rows with the ∅ counterexample stated).
- New §2.4.4 + typing rule §4.3.7: handler elimination,
  $E \mapsto E \setminus \text{covered}(h)$, grounded in the Lean facts.
- §4.4.1: literals infer ∅ (old rule documented as the v2.1.0 fix).
- `Pure(T)` sugar = `Effect(T, ∅)`; change log entry added. File lint ✔.

**Lean** (`Morph/Specs/EffectAlgebra/`): the spec's §2.3 chain claims are now
machine-checked — `classRank`/`classLE` (refl/trans/antisym, io min, system
max), `namedRow`, `mem_namedRow_iff` (row membership ≡ class order),
`namedRow_inj` (distinct classes have distinct rows), 4 example pins.
Build 404 jobs, 0 warnings/errors; snapshot ✔ no regressions —
total theorems **1508 → 1539** (+31), Lean modules 217 → 219.

---

## Loop 94 — Memory: strong-heap acyclicity by construction, and the weak escape (DONE)

**Research** (papers pulled and analyzed):
- Reinking, Xie, de Moura & Leijen, *Perceus: garbage free reference counting
  with reuse* (PLDI 2021): precise RC is garbage free only for **cycle-free**
  programs — the hypothesis is in the abstract but never discharged; drop
  specialization + reuse analysis (FBIP) noted as future adoptables.
- Swift ARC practice: no cycle collector, `weak`/`unowned` are the programmer
  discipline; LLVM "peer-pressure" collector exists but is not semantic.
- Bacon & Rajan, *Concurrent Cycle Collection in Reference Counted Systems*
  (2001): trial-deletion — the backstop Python actually ships.
- McBride, *FP²: Fully In-Place Functional Programming* (ICFP 2023): the
  FIP discipline — candidate for a later loop as a function annotation.

**Analysis.** Morph's own scope-limit §5.3.3 recorded "acyclicity is not
derived; a cycle `a → b → a` still satisfies A5" — a real gap shared with
every industrial RC system. The literature's answers are (a) assume
cycle-freedom (Perceus), (b) leave it to the programmer (Swift), or (c) ship a
trial-deletion collector (Python). Morph can do better *provably*: functional
construction (the only kind affine moves permit without sharing) is
young-into-old — a fresh object captures only existing objects — and under
that discipline the strong heap cannot cycle. Adopt: make the discipline a
named, compile-time-enforced invariant; keep `Weak<T>` as the escape; prove
the escape unblocks collection. Reject: no new runtime machinery, no FBIP
annotation yet (logged for a later loop).

**Spec**:
- `spec/memory/memory_model_spec.md` → v3.4.0: new §2.6.7 states the
  young-into-old construction discipline and the acyclicity consequence;
  adds MMS-INV-034; identifies Perceus's implicit cycle-freedom hypothesis;
  reduces runtime cycle collection to the trial-deletion premise.
- `spec/memory/memory_bounds_spec.md` → v1.1.0: scope-limit §5.3.3 narrowed
  (acyclicity derived *for disciplined executions*, still not for arbitrary
  ones — the model's `store` can build a 2-cycle and that is now stated);
  §5.3.2 gains the `weak_cut_released` note; traceability row added.
  Both files lint ✔.

**Lean** (`Morph/Specs/MemoryBounds/Spec.lean`): `Strong`, `Referenced`,
`StrongPath` (young-into-old paths), `StrongPath_lt` (paths strictly descend),
`strong_acyclic` (no strong path returns to its origin),
`referenced_not_released` (why `Released` is exactly "no strong in-refs"),
`weak_cut_released` (weakening the sole strong in-reference — fields `Nodup`,
which is required: `erase` drops only the first occurrence — restores
`Released`). Proof notes: index-varying induction needed explicit `@cons`
naming; core Lean has no general `not_mem_erase`, only `Nodup.not_mem_erase`.
Snapshot ✔ no regressions — total theorems **1539 → 1543**.

---

## Loop 95 — Error handling: errors as the `raise` operation (DONE)

**Research** (sources pulled and analyzed):
- matklad, *The Second Great Error Model Convergence* (Dec 2025): the
  Go/Rust/Swift/Zig consensus — fallibility marked at the call side, a
  separate panic path, results as first-class values; "midpoint" error-set
  inference (Zig) poorly served; sum types win exhaustiveness.
- Leroy, *The practice of effects: from exceptions to effect handlers*
  (Collège de France 2023–24): exceptions = the algebraic theory with one
  operation `raise` and no equations; `try` = the induced handler.
- JAPL, *Failures Are Normal and Typed* (2025): the dual model — domain
  errors as `Result` + `Fail` effect; process failures as crash + supervision
  — with the explicit comparison table row "effect tracking for errors:
  Rust ✗".
- *Value-Based Errors Improve Software Reliability* (Revista PPC 14.8,
  2025): empirical sentiment study — value-based error handling positive,
  exception-based negative despite dominance.

**Analysis.** Morph's §15 was a conventional Rust-shaped error story
(`Result`, `From` conversion, panics) **disconnected from its own effect
algebra** — the one thing that would differentiate it. The `raise` operation
already existed in `EffectAlgebra` (loop 6, classed under `net` as
partiality) but no spec text connected errors to it, and the 2025 convergence
(Errors-as-effects + dual model) is exactly Morph's architecture. Adopt: the
exception laws (abort/recover) as normative semantics; the handler
elimination rule (loop 93's §4.3.7) as the meaning of `try`; the dual error
model (domain vs process failures) as normative. Reject: Zig-style inferred
error sets (requires closed-world cross-function inference — against Morph's
explicit rows).

**Spec**:
- `spec/language/morph_language_spec.md` → v2.1.0: new §15.2.4 states the
  `raise` operational reading, the abort/recover laws with their
  machine-checked names, `try` = handler elimination, and makes the dual
  error model normative (domain errors never cross handlers as panics;
  panics never become `Result` values).
- `spec/language/effect_algebra_spec.md` → v1.1.0: new §7 "The exception
  laws" — the algebraic statement (after Leroy) with the Lean anchors.
  Both lint ✔.

**Lean** (`Morph/Specs/EffectAlgebra/`): `raise_aborts` (an unanswered
`raise` kills the continuation — instance of `denote_unanswered`) and
`raise_recovers` (answering `raise` with `r` resumes at `k r`), each pinned
by an example. Snapshot ✔ no regressions — total theorems **1543 → 1545**.

---

## Loop 96 — Subtyping: transitivity proved, position recorded (DONE)

**Research** (papers pulled and analyzed):
- Dolan, *Algebraic Subtyping* (thesis) / MLsub (POPL 2017): biunification,
  polar types, union/intersection in a distributive lattice, compact
  principal types with subtyping — the strongest inference story.
- Parreaux, *The Simple Essence of Algebraic Subtyping* (ICFP 2020):
  Simple-sub — constraint-based, <500 lines, agrees with MLsub on 10⁶
  generated programs; several MLsub implementation bugs found by that
  comparison. Three schools named: syntactic, semantic, algebraic.
- Castagna et al. (semantic subtyping; Laurent, *Implementing Set-Theoretic
  Types*): subtyping as set inclusion; decidable at EXPTIME-class cost,
  needs regular coinductive types + DNF.
- Brandt & Henglein (TLCA 1997): coinductive closure's finite fragment = the
  derivability relation → a finite derivation system must prove
  transitivity explicitly.

**Analysis.** Morph's `Sub` is the syntactic structural school, decidable,
sound, complete (loop 12), with contravariant functions (loop 61) and deep
variance (loop 70) — but §3's "preorder" claim had no transitivity theorem.
That was the gap: any subsumption chain (τ ≤ σ ≤ υ) was unwarranted.
Non-adoptions recorded with reasons (spec §10): no union/intersection types
(decision cost, no consumer in runtime/ABI), no equirecursive types (affine
discipline keeps data acyclic — §2.6.7), no polar separation (conflicts with
`refType` invariance — the capability system's price), principal-types-
with-subtyping deferred to loop 101 with Simple-sub as the reference
algorithm. Verdict: morph is *not* re-solving a solved problem — it took a
different, cheaper point in the design space and the spec now says so
explicitly.

**Spec** (`spec/language/subtyping_spec.md` → v1.1.0): §9 the transitivity
table + proof-shape notes for future loops (joint recursor; substituted
targets need `_` in inversion hypotheses); §10 the three-school comparison
and the four non-adoptions; §11 change log. Lint ✔.

**Lean** (`Morph/Specs/Subtyping/Lemmas.lean`): `sub_trans_core` (mutual
recursion via the joint recursor with trans-shaped motives — plain
`induction` is unavailable for the mutual family), `Sub_trans`,
`SubList_refl`/`SubFields_refl` (structural), `sub_tuple_inv`/
`sub_struct_inv` (inversions), `SubList_trans`/`SubFields_trans` (by
inversion over `Sub_trans`), `SubX_trans` (lifts through the loop-61
extension; corner cases: an exact-`Sub` target can only be `refl` or `unit`).
Snapshot ✔ no regressions — total theorems **1545 → 1553** (+8).

---

## Loop 97 — Modules: sealing semantics and abstraction safety (DONE)

**Research** (papers pulled and analyzed):
- Rossberg, *1ML — Core and Modules United* (JFP 2018): sealing (`:>`) as the
  abstraction mechanism; opaque vs transparent ascription; translucency via
  singleton types; applicative vs generative functors — sealing inside a
  functor body makes it generative.
- Dreyer, *Understanding and Evolving the ML Module System*: abstraction as
  relational parametricity; generativity as a proof technique.

**Analysis.** Morph's `ExistentialType`/`ExistentialValue` *named*
existentials but had no semantics: no packing, no sealing, no abstraction
theorem — the spec promised encapsulation guarantees nothing could check.
Against 1ML's design space: adopt sealing + generativity (provable at
Morph's model level); reject applicative functors (linker-keyed modules are
generative by nature; applicative semantics needs type-level functor
application the type system deliberately lacks) and translucent singleton
signatures (no singleton types, per the subtyping spec §10 decision).
Full relational parametricity recorded as future work (needs a client
language model).

**Spec** (`spec/module_existential_spec.md` → v1.1.0): new §7 — the
Package/WellSealed/seal model table, abstraction safety, generativity, and
the two non-adoptions with reasons. Lint ✔.

**Lean** (`Morph/Specs/ModuleExistential/Spec.lean`): `Package`,
`Package.WellSealed`, `sealPackage` (Bool-guarded), `resolveClient`,
`resolveSealed_private` (a private name of a sealed package is unresolvable —
the name-level abstraction theorem), `resolveSealed_exported` (declared
types resolve to exactly their interface spelling, under key-Nodup),
`seal_idempotent`, `SealedType` + `sealed_generative` (sealed identity =
(sealing site, type); `M1.map int ≠ M2.map int` pinned by example).
Support lemmas `lookup_none_of_not_mem_fst`/`lookup_eq_some_of_mem` written
by hand — core Lean has no `List.lookup` membership lemmas.
Snapshot ✔ no regressions — total theorems **1553 → 1557** (+4).

---

## Loop 98 — Concurrency: supervision and crash containment (DONE)

**Research** (sources pulled):
- OTP 29 supervisor docs: `one_for_one` default strategy — only the crashed
  child restarts; restart intensity limits; inbox not preserved across crash.
- Trio `_run.py` + Smith's notes: nursery `__aexit__` blocks until all child
  tasks exit; "nurseries ensure the absence of orphaned tasks"; parallel
  cancellation requires the bundle, not a loop.
- Pony isolation (prior loop knowledge, cited for the containment framing).

**Analysis.** Loop 95 made the dual error model normative — process failures
crash the actor, supervision restarts it — but no spec section and no Lean
module contained a supervision model. The three canonical systems agree on
exactly the properties worth pinning: crash containment (OTP one-for-one /
Pony isolation), restart-with-fresh-state, and scope-join draining (Trio).
Adopt all three; model the drain premise as checked (like `Released`),
matching OTP's practice. Reject: one-for-all/rest-for-one strategies (sibling
termination is policy, not mechanism — a `restartOne` composition; recorded
as such), crash-message redelivery (sender's concern, as in OTP).

**Spec** (`spec/architecture/layered_concurrency_spec.md` → v1.1.0): new
section "Supervision and Crash Containment" with the research basis, the
concept/property table, the two checked-premise non-claims, and LC-INV-035.
Lint ✔.

**Lean** (`Morph/Specs/LayeredConcurrency/Spec.lean`): `ProcessTable`
(function table, MemoryBounds-Heap style), `crashOne`/`restartOne`,
`Nursery`/`allDrained`/`join`; theorems `crash_contained`,
`restart_fresh`, `restart_contained`, `join_drained`. `ActorId` gained
`DecidableEq` (needed for id comparison; additive). Snapshot ✔ no
regressions — total theorems **1557 → 1561** (+4).

## Release-track entries (not part of the 93–102 research plan)

Roadmap follow-ups after Sprint 10, done in one pass at maintainer
request ("all of the above"): docs site + versioned spec index, audit
invite drafts, Era-2 backend scoping with the exit-gate override noted.

### R1 — docs site + versioned spec index for 0.1 (DONE)

- `site/index.html`: hero stats corrected to the snapshot ground truth
  (402 jobs / 1508 theorems / 836 tests / 96% — the page still showed
  328/550/735/93%); Preservation badge Partial→Proven (0 sorries repo-wide,
  verified by grep); new 0.1.0 release section linking CHANGELOG,
  STABILITY, and the audit packet.
- `SPECIFICATION_INDEX.md`: stamped to 0.1.0 (170 spec modules, 1,094 spec
  theorems) with the claims-not-results warning pointing at
  `SPEC_CONTRADICTIONS.md`.
- `site/docs/specs.html`: 0.1.0 version note pointing at the versioned index.
- HTML sanity-checked with `html.parser`; no spec-lint surface touched.

### R2 — audit invite drafts (DONE, UNSENT)

- `docs/AUDIT-INVITES-0.1.md`: reviewer profile (2–3, PL/verification),
  materials list (packet + tag + snapshot), invite-message template,
  4-week timeline, findings template. Names blank for the maintainer.
- Sprint 9's hard gate is still open: invites must be sent by a human.

### R3 — Era 2 backend scoping (DONE, gate override on record)

- `docs/ERA2-BACKEND-SCOPE.md`: grounded in what exists (HIRLower agree ✅,
  ADR-011 stage-1 lowering, MIR SSA/CFG + `execMain`); six gaps to a
  verified compiler (`compile_correct`, backend-choice ADR with
  proof-interface-simplicity criterion, load-bearing ABI lemmas with #11
  resolved first, `morph build`/`morph test`); post-audit staging A–D;
  two open questions routed to the auditors.
- Explicit: no Era-2 implementation lands until the audit publishes.
