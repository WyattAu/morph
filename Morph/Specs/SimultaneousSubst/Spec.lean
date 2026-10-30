/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Semantics
import Morph.Specs.SubstTheory.Lemmas

/-!
# Simultaneous and sequential substitution are the same function

Research loop 11 (the continuation of loop 10).

`Morph/Semantics.lean`'s β-rule uses `substAll` — a *simultaneous* substitution
that takes a list of values — while the CEK machine uses `subst'`, a *single*
substitution. Loop 10 proved they agree for **one** argument. This module
discharges the two things that were left:

1. **the lifting law loop 5 declined to claim** (§6.3 of
   `spec/language/subst_equational_theory_spec.md`): what happens when a
   substituted-in term is itself lifted. It is needed here, and it has a clean
   form.
2. **the multi-argument case**: `substAll` with *n* values equals *n* sequential
   `subst'` applications, taken from the highest level down.

The second is the one that matters: it is what makes the shipped relation and
the machine agree on a genuine multi-parameter application, rather than only on
the degenerate one-argument case.
-/

namespace Morph.Specs.SimultaneousSubst

open Morph.Syntax Morph.Specs.SubstTheory

/-! ### The lifting law

`subst' k e v` inserts `v` at index `k`. If every index of `e` is strictly above
`k`, nothing is hit and every index simply shifts down by one. Written in the
offset form the two recursions actually use:

> **`subst_lifted`** — `subst' (k + m) (liftUnder m (k+1) w) v = liftUnder m k w`

The indices below `m` are untouched (they are below the substitution point
`k + m`), and the indices at or above `m` are lifted by `k+1` and then shifted
down by one — net `k`, which is what `liftUnder m k` does.

The proof is a strong induction on `nodeCount`, because `match_` arm bodies sit
two constructors deep — the same shape as loops 5 and 10. -/

private theorem subst_lifted_list (k m : Nat) (es : List Expr) (v : Expr)
    (step : ∀ e ∈ es, ∀ (k m : Nat) (v : Expr),
      subst' (k + m) (liftUnder m (k + 1) e) v = liftUnder m k e) :
    (es.map (liftUnder m (k + 1))).map (subst' (k + m) · v) = es.map (liftUnder m k) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons]
      rw [step e (List.mem_cons_self) k m v, ih (fun e' he' => step e' (List.mem_cons_of_mem _ he'))]

private theorem subst_lifted_arms (k m : Nat) (arms : List (Pattern × Expr)) (v : Expr)
    (step : ∀ (pat : Pattern) (body : Expr), (pat, body) ∈ arms → ∀ (k m : Nat) (v : Expr),
      subst' (k + m) (liftUnder m (k + 1) body) v = liftUnder m k body) :
    substArms (k + m) v (liftUnderArms m (k + 1) arms) = liftUnderArms m k arms := by
  induction arms with
  | nil => simp [substArms, liftUnderArms]
  | cons hd rest ih =>
      rcases hd with ⟨pat, body⟩
      simp only [liftUnderArms, substArms, Nat.add_assoc]
      rw [step pat body (List.mem_cons_self) k (m + patBindCount pat) v]
      rw [ih (fun pat body he => step pat body (List.mem_cons_of_mem _ he))]

/-- **The lifting law.** Substituting into a term whose indices are all above the
substitution point merely shifts them down; and the shift is exactly the one the
lift would have performed. -/
theorem subst_lifted : ∀ (k m : Nat) (w v : Expr),
    subst' (k + m) (liftUnder m (k + 1) w) v = liftUnder m k w := by
  intro k m w v
  have main : ∀ (fuel : Nat) (k m : Nat) (w v : Expr),
      nodeCount w ≤ fuel → subst' (k + m) (liftUnder m (k + 1) w) v = liftUnder m k w := by
    intro fuel
    refine Nat.strongRecOn (motive := fun fuel => ∀ (k m : Nat) (w v : Expr),
        nodeCount w ≤ fuel → subst' (k + m) (liftUnder m (k + 1) w) v = liftUnder m k w)
      fuel (fun _ ih => ?_)
    intro k m w v hnode
    cases w with
    | bvar n =>
        by_cases h1 : n < m
        · simp only [liftUnder, if_pos h1]
          have hlt : n < k + m := by omega
          simp only [subst', if_pos hlt]
        · simp only [liftUnder, if_neg h1]
          have hlt2 : ¬ (n + (k + 1) < k + m) := by omega
          have hne : ¬ (n + (k + 1) = k + m) := by omega
          simp only [subst', if_neg hlt2, if_neg hne]
          congr 1
    | fvar s =>
        simp only [liftUnder, subst']
    | lit c =>
        simp only [liftUnder, subst']
    | unop op e1 =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e1) (by omega) k m e1 v (by omega)]
    | binop op e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e1) (by omega) k m e1 v (by omega),
          ih (nodeCount e2) (by omega) k m e2 v (by omega)]
    | app fn args =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount fn) (by omega) k m fn v (by omega)]
        congr 1
        exact subst_lifted_list k m args v (fun e he => fun k' m' v' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e args he
            omega) k' m' e v' (by
            have hm := mem_nodeCountList e args he
            omega))
    | lam n body =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', Nat.add_assoc, ih (nodeCount body) (by omega) k (m + n) body v (by omega)]
    | let_ e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', Nat.add_assoc, ih (nodeCount e1) (by omega) k m e1 v (by omega),
          ih (nodeCount e2) (by omega) k (m + 1) e2 v (by omega)]
    | ifThenElse c t f =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount c) (by omega) k m c v (by omega),
          ih (nodeCount t) (by omega) k m t v (by omega),
          ih (nodeCount f) (by omega) k m f v (by omega)]
    | forLoop s e body =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', Nat.add_assoc, ih (nodeCount s) (by omega) k m s v (by omega),
          ih (nodeCount e) (by omega) k m e v (by omega)]
        congr 1
        exact subst_lifted_list k (m + 1) body v
          (fun e he => fun k' m' v' =>
            ih (nodeCount e) (by
              have hm := mem_nodeCountList e body he
              omega) k' m' e v' (by
              have hm := mem_nodeCountList e body he
              omega))
    | block es =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst']
        congr 1
        exact subst_lifted_list k m es v
          (fun e he => fun k' m' v' =>
            ih (nodeCount e) (by
              have hm := mem_nodeCountList e es he
              omega) k' m' e v' (by
              have hm := mem_nodeCountList e es he
              omega))
    | match_ scrut arms =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount scrut) (by omega) k m scrut v (by omega)]
        congr 1
        exact subst_lifted_arms k m arms v
          (fun vars body he => fun k' m' v' =>
            ih (nodeCount body) (by
              have hm := mem_nodeCountArms vars body arms he
              omega) k' m' body v' (by
              have hm := mem_nodeCountArms vars body arms he
              omega))
    | field_ e nm =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
    | pipe e f =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega),
          ih (nodeCount f) (by omega) k m f v (by omega)]
    | typeAsc e ty =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
    | some_ e =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
    | none_ =>
        simp only [liftUnder, subst']
    | ok_ e =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
    | err_ e =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
    | nullCoalesce e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e1) (by omega) k m e1 v (by omega),
          ih (nodeCount e2) (by omega) k m e2 v (by omega)]
    | tuple_ es =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst']
        congr 1
        exact subst_lifted_list k m es v
          (fun e he => fun k' m' v' =>
            ih (nodeCount e) (by
              have hm := mem_nodeCountList e es he
              omega) k' m' e v' (by
              have hm := mem_nodeCountList e es he
              omega))
    | arrayLit es =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst']
        congr 1
        exact subst_lifted_list k m es v
          (fun e he => fun k' m' v' =>
            ih (nodeCount e) (by
              have hm := mem_nodeCountList e es he
              omega) k' m' e v' (by
              have hm := mem_nodeCountList e es he
              omega))
    | arrayIndex a ix =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount a) (by omega) k m a v (by omega),
          ih (nodeCount ix) (by omega) k m ix v (by omega)]
    | refCreate e cap ty =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
    | refLoad e =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
    | refStore e w ty =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega),
          ih (nodeCount w) (by omega) k m w v (by omega)]
    | refFree e =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
    | refCast e cap =>
        simp only [nodeCount] at hnode
        simp only [liftUnder, subst', ih (nodeCount e) (by omega) k m e v (by omega)]
  exact main (nodeCount w) k m w v (Nat.le_refl _)

/-! ### The multi-argument case

The statement is

> `substAll' k vs e = seqSubst k vs e`

where `seqSubst` performs the substitutions one at a time, from the highest level
down. It is proved in `Morph/Specs/SimultaneousSubst/Lemmas.lean`
(`substAll'_eq_seqSubst`, and `substAll_eq_seqSubst` for the shipped offset-0
form), by proving the **absorption step**

> `substAll' k (v :: rest) e = subst' k (substAll' (k + 1) rest e) v`

(`substAll_cons`) and inducting on the value list. The `bvar` case of absorption
is where the work is: `substAll'` indexes its value list with a *proof-carrying*
`getElem` (`vs[n - k]` under `if h : n - k < vs.length`), so the case analysis
relates `n - k`, `j + 1` and `n - (k + 1)` through `List.getElem_cons_zero` /
`List.getElem_cons_succ` and then invokes `subst_lifted` above. -/

/-- **Sequential substitution** — the shape the multi-argument result must take.
`vs[0]` replaces the variable at level `k`, `vs[1]` the one at `k+1`, and so on;
the applications are performed from the *highest* level down, which is the order
in which each inserted value is lifted exactly once. -/
def seqSubst : Nat → List Expr → Expr → Expr
  | _k, [], e => e
  | k, v :: rest, e => subst' k (seqSubst (k + 1) rest e) v

end Morph.Specs.SimultaneousSubst
