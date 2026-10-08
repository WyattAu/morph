# Loop 07 — 2026-09-19 (in progress at session end)

Whole-repo sweep. Construction loop: ROADMAP 1.9 stage 1 (lowering) —
definitions delivered; the correctness theorem designed but not yet proven.
Research fetches deferred again (Loop 8).

## Sources consulted

None fetched this loop (construction-focused; the owed Oxide/Pony full texts
carry to Loop 8).

## Delivered

### `Morph/Lowering.lean` — stage-1 definitions (compiling)

- `IsPureArith` fragment predicate (int literals, `+`/`-`/`*`, `let`).
- `lowerIn (paramMap) (supply) (e) : Option (ValId × List Instr × Nat)` —
  de Bruijn indices resolve through `paramMap`; `let` binds by *lookup shift*
  (`pm' n = if n = 0 then va else pm (n-1)`), so no substitution is performed
  during lowering.
- `lower (e) : Option Func` — closed expressions → a single-block,
  single-return function; unbound indices lower to `ValId 0`, which no
  instruction writes (supplies start at 1), so ill-scoped programs evaluate to
  `none` on both sides of the eventual correctness statement.
- `execInstrs`/`execMain` — structural (list-recursive) execution; **no fuel
  needed** for single-block programs.
- `exprVal`/`bvVal` coercions (Option Expr → Option Value) — the agreement
  currency between the interpreter (Expr-valued) and the MIR (Value-valued).

### The `evalFuel` design (the loop's key research finding)

`Executable.eval` is a `partial def` — **no equation lemmas, no definitional
unfolding** (verified by probe). Any correctness theorem stated against `eval`
is unprovable as-is. The unblock: `evalFuel : Nat → Context → Expr → Option
Expr`, a fuel-bounded total clone mirroring `eval` constructor-for-constructor
(for-loops re-enter the loop expression with an incremented literal bound;
`app` re-enters after β-substitution — both at decreased fuel, so `evalFuel`
is structurally recursive on fuel and *has* equation lemmas).

The pipeline's correctness chain therefore anchors to `evalFuel`, with fuel
exhaustion as the documented divergence point (fuel = expression depth for the
lowered fragment; tests can compare `evalFuel` vs `eval` differentially).

## The correctness theorem — fully designed, not yet proven

```lean
theorem lowerIn_correct (pm : Nat → ValId) (s : Nat)
    (hpos : 1 ≤ s) (hpm : ∀ n, pm n < s)
    (e : Expr) (ctx : Context) (env : Env)
    (hagree : ∀ n, exprVal (ctx.getBv? n) = env (pm n))
    (v : ValId) (is : List Instr) (s' : Nat)
    (hl : lowerIn pm s e = some (v, is, s')) :
    ∃ env', execInstrs env is = some env'
      ∧ exprVal (evalFuel (s' + 1) ctx e) = env' v
      ∧ (∀ n, exprVal (ctx.getBv? n) = env' (pm n))
```

Design points settled (the hard thinking is done):

1. **Strong agreement** (`exprVal (ctx.getBv? n) = env (pm n)`) makes unbound
   bvars stuck on *both* sides — no closedness hypothesis needed; open terms
   come free.
2. **The `let` trick** (lookup-shift `pm'`) makes the b-IH apply at
   `ctx.pushBv (…)` with `pm'`; the case splits on `n = 0` / `n = m+1` close
   by the a-IH's result and agreement respectively.
3. **Write-avoidance**: sub-derivations write only ids `≥` their own supply,
   so `pm`-ids (`< s`) are never clobbered — this is what preserves agreement
   across the instruction sequence. Needs `evalInstr_write` (per-instruction
   env-stability outside the written id) and `execInstrs_agree` (induction).
4. **Fuel bookkeeping**: a-IH provides fuel `s1+1` for `a`; the goal needs
   `s'+1` for the whole expression (`s' ≥ s1`), bridged by an
   `evalFuel_mono`-style lemma: `evalFuel k ctx e = some r → k ≤ f → evalFuel
   f ctx e = some r` — provable by induction on `k` with per-constructor
   `simp [evalFuel, ih, …]` mirroring.
5. `evalInstr_write` is *only* needed for the three constructors `lowerIn`
   emits (`const`/`copy`/`binop`); the other 13 are `none`-stubs (trivial).
   A draft got ~90% of the way (all four real cases structured; final `simp`
   incantations for the `Env.update` if-resolution unresolved).

## Proof changes made this loop

1. `Morph/Lowering.lean` (definitions, compiling, in the build).
2. `Morph/Tests/MIR.lean` untouched this loop; HT-37-style acceptance tests
   land with the theorem.

## Proof-engineering notes (Loop 7 session, for the continuation)

Tactics discovered during drafting (all verified in probes):

- `Executable.eval` has no equation lemmas; `evalFuel` (plain structural def)
  does. All correspondence theorems must target `evalFuel`.
- `Env.update`'s `rw [Env.update]` fails ("failed to rewrite using equation
  theorems") when the goal's `Env` is the abbrev — unfolding works with
  `simp only [Env.update]` in some shapes and fails in others; the reliable
  route is `cases hb : (dst == d)` + `rw [hb] at h; simp at h` for the
  failure direction and `rw [Env.update, if_neg (…)]` for the success
  direction **after** proving `(dst == d) = false` via:
  ```lean
  have h2 : (!(dst == d)) = true := hskip      -- defeq unfold of disjointWrites
  cases hb : (dst == d)
  · rw [hb] at h2; simp at h2                  -- closes
  · rfl
  ```
- Beq-symmetry: `Nat.beq_symm` does not exist; `Nat.beq_eq` exists but its
  rewrite is `Nat.beq a b = true`-shaped (fails on `= false`). The closing
  form that works: `revert h; cases a <;> cases b <;> simp` with residual
  `· exact fun hh' hp => hh' hp.symm`.
- `List.mem_nil` does not exist as a simp lemma; `List.mem_cons` does.
- Lowering's `evalInstr` coverage: only const/copy/unop/binop execute; the
  other 13 instructions are `none`-stubs, so `evalInstr_write` needs 4 real
  cases + 13 trivial (`simp [evalInstr] at h`).

## Open questions carried to Loop 8

1. Finish `lowerIn_correct`: `evalInstr_write` (4 real cases, final simp
   forms), `execInstrs_agree`, `evalFuel_mono`, then the induction. All
   mechanical with the design above; estimate one focused session.
2. Owed fetches: Oxide full text (abstract verified Loop 6), Pony paper
   (P4 refinement), Perceus done.
3. Then: stage-1 continuation — `if` (branch CFG, Loop 8's execFuel-CFG
   executor), memory instructions (store-aware oracle), ADR-012 (closures).
