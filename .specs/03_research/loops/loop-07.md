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


## Resolution (post-program, 2026-10-09)

The two mechanical blockers identified below are now **proven** in
`Morph/LoweringLemmas.lean`:

- `Env.update_same` / `Env.update_ne` — update touches exactly its destination.
- `writtenReg` + `evalInstr_write` — an instruction writes exactly the
  register it names and leaves every other register untouched when it
  succeeds (the `Env.update` equation-lemma problem that stalled earlier
  attempts is avoided by rewriting the *conclusion* via
  `Env.update_ne` after inverting `h`, not by rewriting `Env.update`).
- `evalBinOp_align` / `evalUnOp_align` — the MIR oracle is definitionally
  the surface `evalBinop`/`evalUnop` on `.lit`-wrapped operands.

What remains for `lowerIn_correct` is only the strong-agreement relation
coupling the interpreter `Context` to the MIR `Env` through `let_`/`bvar`
(including the monotonicity step and the `evalFuel` monotone-success
bridge). That part is still open — the blocker is no longer tactic
mechanics but the invariant design itself.


## Progress on `lowerIn_correct` (post-program, 2026-10-12)

### What was resolved

`advances_pure` — the extended-supply invariant — is **proven**
(`Morph/LoweringLemmas.lean`):

    advances_pure : ∀ a, IsPureArith a → paramMap → supply →
      (∀ n, paramMap n < supply) →
      match lowerIn paramMap supply a with
      | none => True
      | some (v, is, s) => supply ≤ s ∧ v < s ∧ ∀ k, paramMap k < s

Two enabling discoveries:

1. **Induct on `IsPureArith`, not `lowerIn.induct`.** `Expr` is a *nested*
   inductive, so `induction e` is rejected, and `lowerIn.induct` (the
   equation compiler's principle for `lowerIn`) has a **10-case** shape —
   one case per `toBinOp` / `lowerIn a` / `lowerIn b` combination plus a
   no-constructor case — which is impractical to apply by hand. `IsPureArith`
   is a *non-nested* inductive with exactly three constructors (`lit`,
   `binop`, `let_`) that correspond one-to-one with the three forms
   `lowerIn` lowers. Applying `IsPureArith.rec` with an explicit motive
   works:

       IsPureArith.rec (motive := fun a _ => paramMap → supply → (∀ n, …) → …)
         (fun n … => …)          -- lit
         (fun bop a b hop … iha ihb … => …)  -- binop
         (fun a b … iha ihb … => …)         -- let_
         hpa

   Note `induction hpa with` in tactic mode does *not* work when the goal
   does not syntactically mention `hpa` — it produces "no cases to select".
   Term-mode `IsPureArith.rec` is the reliable route.

2. **Tuple destructuring.** `lowerIn` returns `Option (ValId × List Instr ×
   Nat)`. Neither `cases … with | some (a, b, c)` nor `⟨a, b, c⟩` works in
   `cases` pattern position (right-nested triples). Use
   `rcases val with ⟨va, rest⟩; rcases rest with ⟨ia, s1⟩`.

### A modelling fix this required

`IsPureArith.binop` now binds `bop` with the equation `toBinOp op = some
bop`. Without it, `IsPureArith` admits operators (comparisons, division)
that `lowerIn` rejects while the interpreter's richer `evalBinop` *does*
evaluate them — making the "lowering fails ⟹ interpreter stuck" direction
unprovable. Membership in `IsPureArith` now guarantees translatability.
(`toBinOp` moved above `IsPureArith`.)

### What remains

`lowerIn_correct` itself. The `lit` case is done. The remaining obstacle is
a *fuel* side-lemma —

    evalStuck : lowerIn … = none → 0 < fuel → exprVal (evalFuel fuel ctx a) = none

needed for the "lowering is stuck" branches. The difficulty is that
`evalFuel` is fuel-bounded, so the binop's sub-evaluations run at `fuel - 1`
while the top-level runs at `fuel`; threading the `0 < fuel` hypothesis
through the `cases fuel` split needs care (`by omega` fails because the
hypothesis is about the *outer* fuel, not the split component).

Two options, both untried:
- state `evalStuck` for `Nat.succ fuel` and add an explicit weakening
  lemma (`stuck at k+1 ⟹ stuck at k`, which needs `evalFuel` monotonicity),
  or
- make `lowerIn_correct` require exactly the fuel each sub-call needs by
  generalizing over `fuel` in the motive and re-instantiating.

All machinery the theorem needs is proven and in the repository
(`evalInstr_write`, `execInstrs_preserves_below`, `Agrees`, `agrees_bvar`,
`advances_pure`, `evalBinOp_align`).


## `evalStuck` proven; the last two steps (2026-10-12, later)

`evalStuck` is **proven** (`f071702`) — lowering rejection mirrors
interpreter stuckness, for *any* fuel. The key was to state it with **no fuel
bound**: the binop/let cases evaluate subexpressions at one less fuel unit, and
a hypothesis about the outer fuel says nothing useful about the split
component. The `let_` case instantiates `b`'s stuckness at the *pushed*
context `ctx.pushBv v1`.

### Remaining for `lowerIn_correct` — two steps, both well-understood

1. **`lowerIn_writes_above`** — `lowerIn paramMap supply a = some (v, is, s)
   → WritesAbove supply is`. Same shape as `advances_pure` (induct on
   `IsPureArith`, 3 cases); needs the `∀ n, paramMap n < supply` hypothesis to
   invoke `advances_pure` for the extended-supply bound. Tactic note:
   `WritesAbove` is a match-defined def, so `⟨h₁, h₂⟩`/`constructor` do not
   apply — unfold with `simp only [WritesAbove, List.append]` first.

2. **The binop/let `some/some` cases** — given `WritesAbove`, the agreement
   propagation is:
   `hagA' : Agrees paramMap ctx envA` via `execInstrs_preserves_below ia env
   envA supply _ hIA n (hpm n)`, then `ihb paramMap s1 ctx envA hagA' _`,
   then execute `ia ++ ib ++ [binop s2 …]` from `env` (rewrite by `hIA` and
   `hIB`) and show `env' s2 = evalBinOp bop …` agrees with the surface
   `evalBinop` (via `evalBinOp_align`).

The fuel handling for the `some/some` cases works because both sub-IHs are at
the *same* outer fuel; only the `none` branches needed `evalStuck`.

Everything these two steps need is already proven and in-tree:
`evalInstr_write`, `execInstrs_preserves_below`, `WritesAbove(.anti_mono)`,
`Agrees`, `agrees_bvar`, `advances_pure`, `evalStuck`, `evalBinOp_align`.
