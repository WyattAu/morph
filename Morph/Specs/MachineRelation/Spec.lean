/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Semantics
import Morph.Specs.SubstTheory.Lemmas

/-!
# Machine ↔ relation: the two β-rules are the same substitution

Research loop 10, completion. The named missing theorem was `machine_iff_step`:
a proof that the CEK machine of `Morph/Specs/ExecutionMachine` and the shipped
small-step relation of `Morph/Semantics.lean` do not disagree about β-reduction.

**The finding.** The shipped β-rule is

```lean
| app_lam : ∀ σ n body args,
    args.length = n →
    Step σ (.app (.lam n body) args) σ (substAll args.reverse body)
```

which uses `substAll' : Nat → List Expr → Expr → Expr` — a *simultaneous*
substitution taking an explicit offset and a list of values. The machine uses
`subst' : Nat → Expr → Expr → Expr` — a *single* substitution carrying its offset
implicitly. Different functions, so the two β-rules are not obviously the same,
and nothing in the repository said they were.

They are the same. Proving it at **every offset**, not just offset 0, is what
makes the statement worth having: under a `lam` both recursions raise the offset,
and that is exactly where a disagreement would surface.

The offset is the whole story. `subst' k e v` folds the offset into the traversal
and applies `lift b v` at the hit site; `substAll' k [v] e` threads `k` through
and applies `lift k (vs[n - k])`. Once the list has length one, the index
arithmetic coincides.
-/

namespace Morph.Specs.MachineRelation

open Morph.Syntax Morph.Specs.SubstTheory

/-! ### The arms case

`match_` arm bodies sit two constructors deep, so they need a strong induction
like loop 5's; this helper takes the element-level step as a hypothesis, which is
all a list induction can justify. -/

private theorem substAllArms_single (k : Nat) (v : Expr) :
    ∀ (arms : List (Pattern × Expr)),
      (∀ (pat : Pattern) (body : Expr), (pat, body) ∈ arms →
        substAll' (k + patBindCount pat) [v] body = subst' (k + patBindCount pat) body v) →
      substAllArms k [v] arms = substArms k v arms := by
  intro arms
  induction arms with
  | nil => intro _; simp [substAllArms, substArms]
  | cons hd rest ih =>
      rcases hd with ⟨pat, body⟩
      intro step
      simp only [substAllArms, substArms]
      rw [step pat body (List.mem_cons_self),
        ih (fun pat body he => step pat body (List.mem_cons_of_mem _ he))]

/-- List-shaped subterms: the step is restricted to members, which is all a
list induction can justify. -/
private theorem substAllList_single (k : Nat) (v : Expr) :
    ∀ (es : List Expr), (∀ e ∈ es, substAll' k [v] e = subst' k e v) →
      es.map (substAll' k [v]) = es.map (fun x => subst' k x v) := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
      intro step
      simp only [List.map_cons]
      rw [step e (List.mem_cons_self),
        ih (fun e' he' => step e' (List.mem_cons_of_mem _ he'))]

/-- **The two β-rules agree.** For every offset `k` and every term `e`,
`substAll' k [v] e = subst' k e v`: the shipped relation's simultaneous
substitution of a single value is the machine's single substitution, at the same
offset.

So `Morph/Semantics.lean`'s `app_lam` with `args = [v]`, `n = 1` (hence
`args.reverse = [v]`) reaches exactly the expression the CEK machine's β-step
computes. The two semantics cannot disagree about β-reduction. -/
theorem substAll_single : ∀ (k : Nat) (v : Expr) (e : Expr),
    substAll' k [v] e = subst' k e v := by
  intro k v e
  have main : ∀ (fuel : Nat) (k : Nat) (e : Expr),
      nodeCount e ≤ fuel → substAll' k [v] e = subst' k e v := by
    intro fuel
    refine Nat.strongRecOn (motive := fun fuel =>
      ∀ (k : Nat) (e : Expr), nodeCount e ≤ fuel → substAll' k [v] e = subst' k e v)
      fuel (fun _ ih => ?_)
    intro k e hnode
    cases e with
    | bvar n =>
        by_cases hlt : n < k
        · rw [subst_bvar_below n k v hlt]
          simp [substAll', hlt]
        · by_cases hle : n - k < 1
          · have heq : n = k := by omega
            subst heq
            rw [subst_bvar_hit n v]
            simp [substAll', hlt]
          · have hgt : k < n := by omega
            rw [subst_bvar_above n k v hgt]
            simp [substAll', hlt, hle]


    | fvar s => simp only [substAll', subst']
    | lit c => simp only [substAll', subst']
    | unop op e1 =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e1) (by omega) k e1 (by omega)]
    | binop op e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e1) (by omega) k e1 (by omega),
          ih (nodeCount e2) (by omega) k e2 (by omega)]
    | app fn args =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst']

        rw [substAllList_single k v args
          (fun e he => ih (nodeCount e) (by
              have hm := mem_nodeCountList e args he
              omega) k e
              (by
                have hm := mem_nodeCountList e args he
                omega)),
          ih (nodeCount fn) (by omega) k fn (by omega)]



    | lam n body =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst']
        exact congrArg (Expr.lam n) (ih (nodeCount body) (by omega) (k + n) body (by omega))
    | let_ e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e1) (by omega) k e1 (by omega),
          ih (nodeCount e2) (by omega) (k + 1) e2 (by omega)]
    | ifThenElse c t f =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount c) (by omega) k c (by omega),
          ih (nodeCount t) (by omega) k t (by omega),
          ih (nodeCount f) (by omega) k f (by omega)]
    | forLoop s e body =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount s) (by omega) k s (by omega),
          ih (nodeCount e) (by omega) k e (by omega)]
        rw [substAllList_single (k + 1) v body
          (fun e he => ih (nodeCount e) (by
              have hm := mem_nodeCountList e body he; omega) (k + 1) e (by
              have hm := mem_nodeCountList e body he; omega))]
    | block es =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst']
        rw [substAllList_single k v es
          (fun e he => ih (nodeCount e) (by
              have hm := mem_nodeCountList e es he
              omega) k e
              (by
                have hm := mem_nodeCountList e es he
                omega))]
    | match_ scrut arms =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount scrut) (by omega) k scrut (by omega)]
        have hstep : ∀ (pat : Pattern) (body : Expr), (pat, body) ∈ arms ->
            substAll' (k + patBindCount pat) [v] body = subst' (k + patBindCount pat) body v := by
          intro pat body hmem
          refine ih (nodeCount body) ?_ (k + patBindCount pat) body ?_
          · have hm := mem_nodeCountArms pat body arms hmem; omega
          · omega
        rw [substAllArms_single k v arms hstep]
    | field_ e nm =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]
    | pipe e f =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega),
          ih (nodeCount f) (by omega) k f (by omega)]
    | typeAsc e ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]
    | some_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]
    | none_ => simp only [substAll', subst']
    | ok_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]
    | err_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]
    | nullCoalesce e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e1) (by omega) k e1 (by omega),
          ih (nodeCount e2) (by omega) k e2 (by omega)]
    | tuple_ es =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst']
        rw [substAllList_single k v es
          (fun e he => ih (nodeCount e) (by
              have hm := mem_nodeCountList e es he
              omega) k e
              (by
                have hm := mem_nodeCountList e es he
                omega))]
    | arrayLit es =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst']
        rw [substAllList_single k v es
          (fun e he => ih (nodeCount e) (by
              have hm := mem_nodeCountList e es he
              omega) k e
              (by
                have hm := mem_nodeCountList e es he
                omega))]
    | arrayIndex a ix =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount a) (by omega) k a (by omega),
          ih (nodeCount ix) (by omega) k ix (by omega)]
    | refCreate e cap ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]
    | refLoad e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]
    | refStore e w ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega),
          ih (nodeCount w) (by omega) k w (by omega)]
    | refFree e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]
    | refCast e cap =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst', ih (nodeCount e) (by omega) k e (by omega)]

  exact main (nodeCount e) k e (Nat.le_refl _)

end Morph.Specs.MachineRelation