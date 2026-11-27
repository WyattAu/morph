# Build-first ledger (directive: `docs/BUILD-FIRST-DIRECTIVE.md`)

> State of the build-first program. Re-read first after restart/compaction.
> Verify claims against the tree before acting — the dev tree flaps.

## Landed

| Item | Status | Evidence |
|---|---|---|
| Boolean corpus bug (morph-clif i8 returns) | ✅ fixed, pushed `585a5f6` | `native.sh` 14/14, `check.sh` 22/22 |
| Build-first directive recorded | ✅ pushed `4ec6fbe` | `docs/BUILD-FIRST-DIRECTIVE.md`; HARD-GATES G-3 re-stamped (deferred, review at first launch) |
| Stage D groundwork | ✅ pushed `f4da26f`/`eba1d95`/`b072a8d` | ADR-033; `Morph/ActorProgress.lean` (`actors_progress`, containment); `docs/STAGE-D3-INVARIANT-MEMO.md` (A/B/C decision ask, deadline 2026-12-18) |
| Call-fragment extraction (`toCallProg`) + Driver call stage | ✅ compiles, tree green, **NOT committed** | `Morph/HIRFunc.lean` (`toCallProg`), `Morph/Driver.lean` (buildClif call stage → `Morph.Codegen.emitProg`) |

## Landed: callee return-type inference + multi-function emission (7608fd9)

`lowerFunc`/`lowerCallProg` compute declared return types from the body
(`inferBody`: marshal-table typing over the MIR instructions — `const`
via `Morph.Clif.valueTyp`, `binop`/`unop` carry their own `τ`, `copy`
propagates, `call` resolves through the callee table, everything else
refuses; identity functions are untypable and refuse, documented per the
D-4 contract). `lowerFunc_inv` exposes `τ` + the inference equation;
`Correct.lean`'s consumers (name lemma, destructure at :1465,
`lowerCallProg_correct`'s program shape) updated; evidence pins use
`.intType` returns. The call fragment now lowers to a multi-function
`MIR.Program` that emits whole via `Morph.Codegen.emitProg` (D-7 option C
slice D2): preamble + main + callees + `call` instructions.

**Still open (the next loop):** the Rust `morph-clif` driver compiles
single-function modules only — the emitted multi-function artifact has a
duplicate `%main` signature-declaration line (the D-7 preamble declares
every function including the entry — the reader treats sig-only lines as
imports, so import+definition of `%main` reads as a redefinition) and a
missing declaration for callees whose parameter types are `.unitType`
placeholders (the marshal filter drops their sig). The driver side needs:
multi-function compilation, `main` exported as `morph_main`, callees as
local linkages; the Lean side needs: param-typed signatures for callees
(the param types come from call sites — `inferBody` over the caller with
the callee table gives the actuals' types), entry excluded from the
preamble. Plus a calls corpus case (`native.sh` → 15/15).

**Discovered blocker (the real next loop).** `lowerFunc`/`lowerCallProg`
hardcode `.unitType` return types, and a proper fix is a small **MIR-side
type inference**, not a tail edit:

- `Morph.Clif.bodyResultTyp` computes over **CLIF** instructions; the
  lowering produces **MIR** instructions (`const`/`binop`/`unop`/`copy`) —
  different types, no direct reuse (first attempted, reverted).
- Required: `bodyTypeOf : List (ValId × Typ) → List Instr → Reg → Option Typ`
  over MIR instructions — `const` via `Morph.Clif.valueTyp` (the marshal
  table), `binop`/`unop` carry their own `τ`, `copy` propagates, other
  instructions refuse. Return type = the final register's type; also needed
  for the synthetic `main`.
- **Param types** are the harder half: `fn x -> x` (identity) is untypable
  from the body — param types must come from **use sites** (operator-required
  operand types) or from call sites (all sites must agree). Identity
  functions stay refused in v1; document it.
- Then the proof churn: `Morph/Proofs/Call/Correct.lean` (2,350 lines) cases
  on `lowerCallProg`'s output — the `.unitType` literals become computed
  `τ`s. Then `morph-clif` multi-function support, then the corpus case.

Interim behavior: call programs build to the call lowering and are refused
at emission with the sharpened message — honest, not silent.

## Landed: CLIF function parameters + the multi-function driver (2ebebf1..51e044d)

The item-1 loop landed in three slices, all differential-tested:

- **2ebebf1** — the model: `Morph.Clif.Func` gains `params : List (Reg × Typ)`;
  `blockEncode` threads a params argument into the emitted header
  (`blockEncode_params`: the header declares exactly the caller's list);
  `emitFunc` passes the lowered MIR function's params through;
  `toksFunc`/`parseFunc`/`parseParamPairs` round-trip them (proved);
  `blockEncode_return` generalized over the params argument, `clif_correct`
  recovers `params = []` via `blockEncode_params`.
- **1c08d48** — the dialect: artifacts render in the form
  `cranelift-reader` 0.137 actually parses (checked empirically against the
  reader): headers name parameter *types* (`(i64, i64)`), the entry block
  binds value registers (`block0(v1: i64, v2: i64):`), call-bearing bodies
  carry per-function `sig0 = (…) -> …` / `fn0 = %callee sig0` declarations
  and the call line uses the numeric form (`call fn0(v0, v1)`).
  `abiName` strips HIRLower's internal `free:` prefix at the rendering
  boundary only — MIR keeps the raw name, so the Correct.lean call-fragment
  proofs are untouched.
- **51e044d** — the driver: `morph-clif` filters the ABI documentation lines
  (the reader's grammar has no decl-only form), rewrites symbolic fn
  references to the relocatable user-name encoding (`fn0 = u0:<FuncId>
  sig0` — testcase targets panic in cranelift-module's relocation path;
  FuncId == file position over definitions only), declares everything
  before defining anything (`%main` exports as `morph_main`; callees stay
  `Linkage::Local`), and refuses a parameter-taking `%main` (the runner
  calls it with none).

Result: `tests/codegen/native.sh` → **15/15** (new `calls_add.hum`:
`let add = fn a b -> a + b; let r = add 2 3; r`), `tests/codegen/check.sh`
→ **23/23** rejection goldens hold, Morph + Morph.Tests green, 0 sorry.

Known sharp edges (follow-ups, none blocking):

- `u0:<FuncId>` encodes declaration order; the driver derives it from file
  positions. A future artifact that lets callees reference each other keeps
  working (same mapping) but multi-level call chains are still refused by
  the fragment (`callee bodies call-free`).
- The ld warnings (`DT_TEXTREL in a PIE`) are cosmetic for the current
  runner shape; a `-no-pie` link or `Linkage::Export` on callees would
  silence them if they ever matter.
- Identity functions (`fn x -> x`) still refuse (typed surface parameters
  would lift it); the v1 int-actuals contract stands.

## Also open

- D3 invariant decision: `docs/STAGE-D3-INVARIANT-MEMO.md` (A/B/C, deadline
  2026-12-18; default A on silence — ADR-033 mechanism). **Decided A
  2026-11-27, recorded as ADR-034; the `ActorStmts` fragment + progress
  restatement is the next proof work.**
- Audit invites: deferred by directive; draft send-ready for first launch.
- Stale worktree `/tmp/opencode/bl2` was pruned 2026-11-26; re-check if it
  reappears (tmpfs).
