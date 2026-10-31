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
