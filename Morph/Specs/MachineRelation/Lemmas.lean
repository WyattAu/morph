/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MachineRelation.Spec

/-!
# The shipped β-rule at one argument

Research loop 47. The ledger's last adoption note read: *the shipped β-rule
still uses `substAll` where loops 10 and 11 proved the single-argument case is
the same function.* This module closes that note, and records why the shipped
rule should **not** be rewritten.

**Why the rule stays simultaneous.** `Step.app_lam` fires for an application of
`n` arguments at once:

```lean
| app_lam : ∀ σ n body args,
    args.length = n →
    Step σ (.app (.lam n body) args) σ (substAll args.reverse body)
```

It has to: `substAll` is simultaneous substitution, and replacing it by a
sequential fold of `subst` would be *wrong* (later substitutions shift the free
indices of earlier ones — the reason `substAll` exists at all). There is no
single-argument branch to specialise; `n = 1` is a *use* of the rule, not a
different rule.

**What was missing** is the bridge at that use. `substAll_single` (loop 10)
proves the two substitutions agree; this module lifts it to the step relation,
so the shipped semantics and the CEK machine's β-step are visibly the same
transition at `n = 1`:

- `substAll_singleton` — `substAll [v] body = subst body v`;
- `Step.app_lam_one` — the shipped step at one argument lands on `subst body v`;
- `Step.app_lam_of_length_one` — the same with the arity named.

This is the honest closure: an equation plus a step lemma, not a refactor that
would make the simultaneous rule unable to handle `n > 1`.
-/

namespace Morph.Specs.MachineRelation

open Morph.Syntax Morph.Semantics

/-- **The shipped simultaneous substitution at one value is the machine's
single substitution.** -/
theorem substAll_singleton (body v : Expr) :
    substAll [v] body = subst body v := by
  simpa [subst] using substAll_single 0 v body

/-- **The shipped β-rule at one argument.** Applying `lam 1 body` to `[v]`
steps to `subst body v` — exactly the CEK machine's β-step. -/
theorem Step.app_lam_one {σ : Store} {body v : Expr} :
    Step σ (.app (.lam 1 body) [v]) σ (subst body v) := by
  have h := Step.app_lam σ 1 body [v] rfl
  simpa [substAll_singleton] using h

/-- The same step when the arity is a variable known to be one. -/
theorem Step.app_lam_of_length_one {σ : Store} {n : Nat} {body v : Expr}
    (hn : n = 1) :
    Step σ (.app (.lam n body) [v]) σ (subst body v) := by
  subst hn
  exact Step.app_lam_one

end Morph.Specs.MachineRelation
