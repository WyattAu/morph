/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.HIREval

/-!
# HIR application, unfolded (Stage C item C8, HIR-side groundwork)

Loop 186. The future C8c generalization must relate two different
binding mechanisms: HIR `evalHIR` evaluates a call body under
`binds ++ env` (first-match list), while MIR `execInstrsCall` binds the
same actuals to registers through `bindCallArgs`. This module pins the
HIR side of that bridge, with no MIR or lowering dependency, so it lands
while the encoder work is still in flight:

- `appBinds` names the actual-argument binding `evalHIR` builds, once, so
  the lowering and the future agreement lemma cite one constant.
- `evalHIR_app_unfold`: applying a `lam` found in the environment is
  exactly evaluating its body under the built binding — the equation C8c
  will rewrite with.
- `appBinds_mem`: every successful index pair lands in the binding, so a
  later "nothing dropped" argument starts from membership, not from
  `filterMap` internals.
-/

namespace Morph.Proofs.Call

open Morph.HIR Morph.Core Morph.Frontend.HIREval

/-- The actual-argument binding `evalHIR` builds for `.app`: `params[j]`
gets `argv[n - 1 - j]` (innermost-first, mirroring the surface
`substAll`-reverse convention), dropping indices that fail on either
side. Copied verbatim from `evalHIR`'s `.app` arm (with `n` inlined), so
`hbridge` below closes by `rfl`. -/
def appBinds (params : List HIR.Id) (argv : List HIR.Expr) : HEnv :=
  (List.range params.length).filterMap fun j =>
    match params[j]?, argv[params.length - 1 - j]? with
    | some p, some v => some (p, v)
    | _, _ => none

/-- Applying a `lam` from the environment evaluates its body under the
built binding. Hypotheses mirror the arm: the function position holds a
`lam`, every argument evaluates, arity matches, and the binding kept all
`n` pairs (otherwise the arm returns `none` and there is nothing to
relate). -/
theorem evalHIR_app_unfold {fuel : Nat} {env : HEnv} {fid : HIR.Id}
    {args : List HIR.Expr} {params : List HIR.Id} {body : HIR.Expr}
    {argv : List HIR.Expr} {binds : HEnv}
    (hfn : lookupHEnv env fid = some (.lam params body))
    (hargs : args.mapM (evalHIR fuel env) = some argv)
    (harity : args.length = params.length)
    (hbinds : binds = appBinds params argv)
    (hblen : binds.length = params.length) :
    evalHIR (fuel + 1) env (.app fid args) =
      evalHIR fuel (binds ++ env) body := by
  have h1 : ¬ args.length ≠ params.length := by simp [harity]
  have h2 : ¬ binds.length ≠ params.length := by simp [hblen]
  simp only [evalHIR, hfn, hargs, Bind.bind, Option.bind, h1]
  -- The arm body is now explicit; fold the inlined binding construction
  -- back to `appBinds` by definitional unfolding (`show` is up to defeq,
  -- so the compiled match shape does not matter), then rewrite with the
  -- pinned binding and discharge the length test.
  show (if (appBinds params argv).length ≠ params.length then none
      else evalHIR fuel (appBinds params argv ++ env) body) =
    evalHIR fuel (binds ++ env) body
  rw [← hbinds, if_neg h2]

/-- Every successful index pair lands in the binding. -/
theorem appBinds_mem {params : List HIR.Id} {argv : List HIR.Expr}
    {j : Nat} {p : HIR.Id} {v : HIR.Expr}
    (hp : params[j]? = some p)
    (hv : argv[params.length - 1 - j]? = some v) :
    (p, v) ∈ appBinds params argv := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hp
  unfold appBinds
  rw [List.mem_filterMap]
  exact ⟨j, List.mem_range.mpr hlt, by simp [hp, hv]⟩

end Morph.Proofs.Call
