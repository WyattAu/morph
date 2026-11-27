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

## Also open

- D3 invariant decision: `docs/STAGE-D3-INVARIANT-MEMO.md` (A/B/C, deadline
  2026-12-18; default A on silence — ADR-033 mechanism).
- Audit invites: deferred by directive; draft send-ready for first launch.
- Stale worktree `/tmp/opencode/bl2` was pruned 2026-11-26; re-check if it
  reappears (tmpfs).
