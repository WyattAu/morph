/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SimultaneousSubst.Spec

/-!
# Simultaneous = sequential, for every number of arguments

Research loop 49. `Morph/Specs/SimultaneousSubst/Spec.lean` proved the lifting
law and *shaped* the multi-argument result but left it unproved. This file
proves it:

- `substAll'_bvar_below` / `_hit` / `_above` — the three `bvar` cases of
  `substAll'`, isolated (the definition's proof-carrying `if` is awkward to
  rewrite otherwise);
- `substAll_cons` — the **absorption step**:
  `substAll' k (v :: rest) e = subst' k (substAll' (k + 1) rest e) v`;
- `substAll'_eq_seqSubst` — the multi-argument theorem:
  `substAll' k vs e = seqSubst k vs e`;
- `substAll_eq_seqSubst` — the shipped form at offset 0.

The absorption proof is a strong induction on `nodeCount`, because `match_` arm
bodies sit two constructors deep (the same shape as loops 5, 10 and 11). The
`bvar` case is the only one with arithmetic: for `n > k` it splits on whether
the next value index is in `rest`, and the "above" branch uses the fact that
`substAll'`'s fallback is `n - vs.length` (not `n - k - vs.length`).
-/

namespace Morph.Specs.SimultaneousSubst

open Morph.Syntax Morph.Specs.SubstTheory

/-! ### The three `bvar` cases -/

theorem substAll'_bvar_below (k : Nat) (vs : List Expr) (n : Nat) (h : n < k) :
    substAll' k vs (.bvar n) = .bvar n := by
  simp [substAll', h]

theorem substAll'_bvar_hit (k : Nat) (vs : List Expr) (n : Nat) (hk : k ≤ n)
    (h : n - k < vs.length) :
    substAll' k vs (.bvar n) = lift k (vs[n - k]) := by
  have hlt : ¬ n < k := by omega
  simp [substAll', hlt, h]

theorem substAll'_bvar_above (k : Nat) (vs : List Expr) (n : Nat) (hk : k ≤ n)
    (h : ¬ n - k < vs.length) :
    substAll' k vs (.bvar n) = .bvar (n - vs.length) := by
  have hlt : ¬ n < k := by omega
  simp [substAll', hlt, h]

/-! ### List and arm helpers for the absorption step -/

private theorem substAll_cons_list (k : Nat) (v : Expr) (rest : List Expr)
    (es : List Expr)
    (step : ∀ e ∈ es, ∀ (k : Nat) (v : Expr) (rest : List Expr),
      substAll' k (v :: rest) e = subst' k (substAll' (k + 1) rest e) v) :
    es.map (substAll' k (v :: rest)) =
      (es.map (substAll' (k + 1) rest)).map (fun x => subst' k x v) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons]
      rw [step e (List.mem_cons_self) k v rest,
        ih (fun e' he' => step e' (List.mem_cons_of_mem _ he'))]

private theorem substAll_cons_arms (k : Nat) (v : Expr) (rest : List Expr)
    (arms : List (Pattern × Expr))
    (step : ∀ (pat : Pattern) (body : Expr), (pat, body) ∈ arms →
      ∀ (k : Nat) (v : Expr) (rest : List Expr),
        substAll' k (v :: rest) body = subst' k (substAll' (k + 1) rest body) v) :
    substAllArms k (v :: rest) arms =
      substArms k v (substAllArms (k + 1) rest arms) := by
  induction arms with
  | nil => simp [substAllArms, substArms]
  | cons hd rest' ih =>
      rcases hd with ⟨pat, body⟩
      simp only [substAllArms, substArms]
      rw [step pat body (List.mem_cons_self) (k + patBindCount pat) v rest]
      have hk : (k + patBindCount pat) + 1 = k + 1 + patBindCount pat := by omega
      rw [hk]
      rw [ih (fun pat body he => step pat body (List.mem_cons_of_mem _ he))]

/-! ### Absorption -/

/-- **The absorption step**: substituting `v` and then `rest` simultaneously is
the same as substituting `rest` one level up and then `v` at the original
level. -/
theorem substAll_cons : ∀ (k : Nat) (v : Expr) (rest : List Expr) (e : Expr),
    substAll' k (v :: rest) e = subst' k (substAll' (k + 1) rest e) v := by
  intro k v rest e
  have main : ∀ (fuel : Nat) (k : Nat) (v : Expr) (rest : List Expr) (e : Expr),
      nodeCount e ≤ fuel →
      substAll' k (v :: rest) e = subst' k (substAll' (k + 1) rest e) v := by
    intro fuel
    refine Nat.strongRecOn (motive := fun fuel =>
      ∀ (k : Nat) (v : Expr) (rest : List Expr) (e : Expr),
        nodeCount e ≤ fuel →
        substAll' k (v :: rest) e = subst' k (substAll' (k + 1) rest e) v)
      fuel (fun _ ih => ?_)
    intro k v rest e hnode
    cases e with
    | bvar n =>
        by_cases hlt : n < k
        · rw [substAll'_bvar_below k (v :: rest) n hlt]
          rw [substAll'_bvar_below (k + 1) rest n (by omega)]
          exact (subst_bvar_below n k v hlt).symm
        · by_cases heq : n = k
          · subst heq
            rw [substAll'_bvar_hit n (v :: rest) n (Nat.le_refl n) (by simp)]
            rw [substAll'_bvar_below (n + 1) rest n (by omega)]
            rw [subst_bvar_hit n v]
            have hk0 : n - n = 0 := by omega
            simp only [hk0, List.getElem_cons_zero]
          · have hgt : k < n := by omega
            by_cases hj : n - (k + 1) < rest.length
            · have hL : n - k < (v :: rest).length := by simp; omega
              rw [substAll'_bvar_hit k (v :: rest) n (by omega) hL]
              rw [substAll'_bvar_hit (k + 1) rest n (by omega) hj]
              have hidx : n - k = (n - (k + 1)) + 1 := by omega
              have hget : (v :: rest)[n - k]'hL = rest[n - (k + 1)]'hj := by
                simp only [hidx, List.getElem_cons_succ]
              rw [hget]
              simp only [lift]
              exact (by simpa using (subst_lifted k 0 (rest[n - (k + 1)]'hj) v).symm)
            · have hL : ¬ n - k < (v :: rest).length := by simp; omega
              rw [substAll'_bvar_above k (v :: rest) n (by omega) hL]
              rw [substAll'_bvar_above (k + 1) rest n (by omega) hj]
              have hkgt : k < n - rest.length := by omega
              rw [subst_bvar_above (n - rest.length) k v hkgt]
              have hlen : (v :: rest).length = rest.length + 1 := by simp
              simp only [hlen]
              congr 1
    | fvar s => simp only [substAll', subst']
    | lit c => simp only [substAll', subst']
    | unop op e1 =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e1) (by omega) k v rest e1 (by omega)]
    | binop op e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e1) (by omega) k v rest e1 (by omega),
          ih (nodeCount e2) (by omega) k v rest e2 (by omega)]
    | app fn args =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount fn) (by omega) k v rest fn (by omega)]
        congr 1
        exact substAll_cons_list k v rest args (fun e he => fun k' v' rest' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e args he
            omega) k' v' rest' e (by
            have hm := mem_nodeCountList e args he
            omega))
    | lam n body =>
        simp only [nodeCount] at hnode
        have hk : k + 1 + n = k + n + 1 := by omega
        simp only [substAll', subst', hk,
          ih (nodeCount body) (by omega) (k + n) v rest body (by omega)]
    | let_ e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e1) (by omega) k v rest e1 (by omega),
          ih (nodeCount e2) (by omega) (k + 1) v rest e2 (by omega)]
    | ifThenElse c t f =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount c) (by omega) k v rest c (by omega),
          ih (nodeCount t) (by omega) k v rest t (by omega),
          ih (nodeCount f) (by omega) k v rest f (by omega)]
    | forLoop s e body =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount s) (by omega) k v rest s (by omega),
          ih (nodeCount e) (by omega) k v rest e (by omega)]
        congr 1
        exact substAll_cons_list (k + 1) v rest body (fun e he => fun k' v' rest' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e body he
            omega) k' v' rest' e (by
            have hm := mem_nodeCountList e body he
            omega))
    | block es =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst']
        congr 1
        exact substAll_cons_list k v rest es (fun e he => fun k' v' rest' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e es he
            omega) k' v' rest' e (by
            have hm := mem_nodeCountList e es he
            omega))
    | match_ scrut arms =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount scrut) (by omega) k v rest scrut (by omega)]
        congr 1
        exact substAll_cons_arms k v rest arms
          (fun pat body he => fun k' v' rest' =>
            ih (nodeCount body) (by
              have hm := mem_nodeCountArms pat body arms he
              omega) k' v' rest' body (by
              have hm := mem_nodeCountArms pat body arms he
              omega))
    | field_ e nm =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
    | pipe e f =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega),
          ih (nodeCount f) (by omega) k v rest f (by omega)]
    | typeAsc e ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
    | some_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
    | none_ => simp only [substAll', subst']
    | ok_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
    | err_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
    | nullCoalesce e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e1) (by omega) k v rest e1 (by omega),
          ih (nodeCount e2) (by omega) k v rest e2 (by omega)]
    | tuple_ es =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst']
        congr 1
        exact substAll_cons_list k v rest es (fun e he => fun k' v' rest' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e es he
            omega) k' v' rest' e (by
            have hm := mem_nodeCountList e es he
            omega))
    | arrayLit es =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst']
        congr 1
        exact substAll_cons_list k v rest es (fun e he => fun k' v' rest' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e es he
            omega) k' v' rest' e (by
            have hm := mem_nodeCountList e es he
            omega))
    | arrayIndex a ix =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount a) (by omega) k v rest a (by omega),
          ih (nodeCount ix) (by omega) k v rest ix (by omega)]
    | refCreate e cap ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
    | refLoad e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
    | refStore e w ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega),
          ih (nodeCount w) (by omega) k v rest w (by omega)]
    | refFree e =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
    | refCast e cap =>
        simp only [nodeCount] at hnode
        simp only [substAll', subst',
          ih (nodeCount e) (by omega) k v rest e (by omega)]
  exact main (nodeCount e) k v rest e (Nat.le_refl _)

/-! ### Empty substitution is identity -/

private theorem substAll_nil_list (k : Nat) (es : List Expr)
    (step : ∀ e ∈ es, ∀ (k : Nat), substAll' k [] e = e) :
    es.map (substAll' k []) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons]
      rw [step e (List.mem_cons_self) k,
        ih (fun e' he' => step e' (List.mem_cons_of_mem _ he'))]

private theorem substAllArms_nil (k : Nat) (arms : List (Pattern × Expr))
    (step : ∀ (pat : Pattern) (body : Expr), (pat, body) ∈ arms →
      ∀ (k : Nat), substAll' k [] body = body) :
    substAllArms k [] arms = arms := by
  induction arms with
  | nil => simp [substAllArms]
  | cons hd rest ih =>
      rcases hd with ⟨pat, body⟩
      simp only [substAllArms]
      rw [step pat body (List.mem_cons_self) (k + patBindCount pat),
        ih (fun pat body he => step pat body (List.mem_cons_of_mem _ he))]

/-- Empty simultaneous substitution leaves every term unchanged. -/
theorem substAll'_nil : ∀ (k : Nat) (e : Expr), substAll' k [] e = e := by
  intro k e
  have main : ∀ (fuel : Nat) (k : Nat) (e : Expr),
      nodeCount e ≤ fuel → substAll' k [] e = e := by
    intro fuel
    refine Nat.strongRecOn (motive := fun fuel =>
      ∀ (k : Nat) (e : Expr), nodeCount e ≤ fuel → substAll' k [] e = e)
      fuel (fun _ ih => ?_)
    intro k e hnode
    cases e with
    | bvar n =>
        by_cases hlt : n < k
        · rw [substAll'_bvar_below k [] n hlt]
        · have hle : k ≤ n := by omega
          have hlen : ¬ n - k < ([] : List Expr).length := by simp
          rw [substAll'_bvar_above k [] n hle hlen]
          simp
    | fvar s => simp only [substAll']
    | lit c => simp only [substAll']
    | unop op e1 =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e1) (by omega) k e1 (by omega)]
    | binop op e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e1) (by omega) k e1 (by omega),
          ih (nodeCount e2) (by omega) k e2 (by omega)]
    | app fn args =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount fn) (by omega) k fn (by omega)]
        congr 1
        exact substAll_nil_list k args (fun e he => fun k' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e args he
            omega) k' e (by
            have hm := mem_nodeCountList e args he
            omega))
    | lam n body =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount body) (by omega) (k + n) body (by omega)]
    | let_ e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e1) (by omega) k e1 (by omega),
          ih (nodeCount e2) (by omega) (k + 1) e2 (by omega)]
    | ifThenElse c t f =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount c) (by omega) k c (by omega),
          ih (nodeCount t) (by omega) k t (by omega),
          ih (nodeCount f) (by omega) k f (by omega)]
    | forLoop s e body =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount s) (by omega) k s (by omega),
          ih (nodeCount e) (by omega) k e (by omega)]
        congr 1
        exact substAll_nil_list (k + 1) body (fun e he => fun k' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e body he
            omega) k' e (by
            have hm := mem_nodeCountList e body he
            omega))
    | block es =>
        simp only [nodeCount] at hnode
        simp only [substAll']
        congr 1
        exact substAll_nil_list k es (fun e he => fun k' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e es he
            omega) k' e (by
            have hm := mem_nodeCountList e es he
            omega))
    | match_ scrut arms =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount scrut) (by omega) k scrut (by omega)]
        congr 1
        exact substAllArms_nil k arms
          (fun vars body he => fun k' =>
            ih (nodeCount body) (by
              have hm := mem_nodeCountArms vars body arms he
              omega) k' body (by
              have hm := mem_nodeCountArms vars body arms he
              omega))
    | field_ e nm =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
    | pipe e f =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega),
          ih (nodeCount f) (by omega) k f (by omega)]
    | typeAsc e ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
    | some_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
    | none_ => simp only [substAll']
    | ok_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
    | err_ e =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
    | nullCoalesce e1 e2 =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e1) (by omega) k e1 (by omega),
          ih (nodeCount e2) (by omega) k e2 (by omega)]
    | tuple_ es =>
        simp only [nodeCount] at hnode
        simp only [substAll']
        congr 1
        exact substAll_nil_list k es (fun e he => fun k' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e es he
            omega) k' e (by
            have hm := mem_nodeCountList e es he
            omega))
    | arrayLit es =>
        simp only [nodeCount] at hnode
        simp only [substAll']
        congr 1
        exact substAll_nil_list k es (fun e he => fun k' =>
          ih (nodeCount e) (by
            have hm := mem_nodeCountList e es he
            omega) k' e (by
            have hm := mem_nodeCountList e es he
            omega))
    | arrayIndex a ix =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount a) (by omega) k a (by omega),
          ih (nodeCount ix) (by omega) k ix (by omega)]
    | refCreate e cap ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
    | refLoad e =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
    | refStore e w ty =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega),
          ih (nodeCount w) (by omega) k w (by omega)]
    | refFree e =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
    | refCast e cap =>
        simp only [nodeCount] at hnode
        simp only [substAll', ih (nodeCount e) (by omega) k e (by omega)]
  exact main (nodeCount e) k e (Nat.le_refl _)

/-! ### The multi-argument theorem -/

/-- **Simultaneous substitution is sequential substitution** (UDF: the shipped
relation and the machine agree on every arity). -/
theorem substAll'_eq_seqSubst : ∀ (k : Nat) (vs : List Expr) (e : Expr),
    substAll' k vs e = seqSubst k vs e := by
  intro k vs
  induction vs generalizing k with
  | nil => intro e; simp only [seqSubst]; exact substAll'_nil k e
  | cons v rest ih =>
      intro e
      rw [substAll_cons, ih (k + 1) e]
      rfl

/-- The shipped `substAll` is the offset-0 sequential substitution. -/
theorem substAll_eq_seqSubst (vs : List Expr) (e : Expr) :
    substAll vs e = seqSubst 0 vs e :=
  substAll'_eq_seqSubst 0 vs e

end Morph.Specs.SimultaneousSubst
