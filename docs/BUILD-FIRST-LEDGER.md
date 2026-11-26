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

## In flight: multi-function call artifacts (directive item 1)

State: `toCallProg` extracts top-level `fn` declarations into the function
table and the rest into `main`; `lowerCallProg` lowers to a multi-function
`MIR.Program`; `emitProg` refuses it because **`lowerFunc`/`lowerCallProg`
hardcode `.unitType` return types** (the D-7 slot gate `clifTyOfTyp
unitType = none` then refuses the call instruction itself).

Next steps, in order:

1. `lowerFunc`: compute the body's result type via `Morph.Clif.bodyResultTyp
   is v` (in `Morph/ClifTarget.lean:742`; HIRFunc must add
   `import Morph.ClifTarget` — no cycle) and set `retType := τ`, refusing
   unslotted bodies (`none`). Same for the synthetic `main` in
   `lowerCallProg` (`bodyResultTyp is v` over the pre-prologue `is`).
2. **Proof churn expected**: `Morph/Proofs/Call/Correct.lean` (2,350 lines)
   cases on `lowerCallProg`'s output shape — the `.unitType` literals in its
   construction will become `τ`. Iterate: `lake build Morph.HIRFunc`, then
   `Morph.Proofs.Call`, fixing `simp only [lowerCallProg] at h` sites.
3. `morph build` a call program; inspect the emitted CLIF (multi-function +
   preamble + call instructions); confirm `cranelift-reader` accepts it
   (preamble format: `docs/ClifEmit.lean` §Signature-declaration preamble,
   `sigSuffix`/`retSuffix`).
4. `morph-clif`: multi-function support — compile every function, declare
   callees `Linkage::Local`, export the module's `main` as `morph_main`;
   runner dispatch on main's return kind (i64/i8 — done).
5. Corpus: add a call case to `tests/codegen/corpus/` + `manifest.tsv`;
   `native.sh` → 15/15.

## Also open

- D3 invariant decision: `docs/STAGE-D3-INVARIANT-MEMO.md` (A/B/C, deadline
  2026-12-18; default A on silence — ADR-033 mechanism).
- Audit invites: deferred by directive; draft send-ready for first launch.
- Stale worktree `/tmp/opencode/bl2` was pruned 2026-11-26; re-check if it
  reappears (tmpfs).
