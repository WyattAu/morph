/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.SubstTheory.Spec

/-!
# The substitution equational theory

The theorems here are the POPLmark "equational theory" obligations for Morph's
hand-written capture-avoiding substitution (`Morph.Syntax.subst'`), in the shape
Autosubst 2 would have generated them from a substitution signature.

**Scoping, not binder count.** The condition for `subst' i e v = e` is *not*
`i ≥ boundCount e`. A bare `.bvar n` introduces no binders at all, yet
substitution still needs `n < i` before it may leave the index alone. The right
judgement is the standard scoping predicate `Scoped i e` ("every de Bruijn index
occurring in `e` is below `i`"), and that is what drives `subst_above` below.
-/

namespace Morph.Specs.SubstTheory

open Morph.Syntax Morph.Specs.SubstTheory

mutual
/-- `nodeCount` over a list. -/
def nodeCountList : List Expr → Nat
  | [] => 0
  | e :: es => nodeCount e + nodeCountList es

/-- `nodeCount` over match arms. -/
def nodeCountArmsSize : List (List String × Expr) → Nat
  | [] => 0
  | (_, body) :: rest => nodeCount body + nodeCountArmsSize rest

/-- Strict structural size. Match-arm bodies sit two constructors deep, so a
plain `Expr`-structural induction cannot reach them; this measure drives a strong
induction instead. -/
def nodeCount : Expr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .lit _ => 1
  | .unop _ e => nodeCount e + 1
  | .binop _ e1 e2 => nodeCount e1 + nodeCount e2 + 1
  | .app fn args => nodeCount fn + nodeCountList args + 1
  | .lam _ e => nodeCount e + 1
  | .let_ e1 e2 => nodeCount e1 + nodeCount e2 + 1
  | .ifThenElse c t f => nodeCount c + nodeCount t + nodeCount f + 1
  | .forLoop s e body => nodeCount s + nodeCount e + nodeCountList body + 1
  | .block es => nodeCountList es + 1
  | .match_ scrut arms => nodeCount scrut + nodeCountArmsSize arms + 1
  | .field_ e _ => nodeCount e + 1
  | .pipe e f => nodeCount e + nodeCount f + 1
  | .typeAsc e _ => nodeCount e + 1
  | .some_ e => nodeCount e + 1
  | .none_ => 1
  | .ok_ e => nodeCount e + 1
  | .err_ e => nodeCount e + 1
  | .nullCoalesce e1 e2 => nodeCount e1 + nodeCount e2 + 1
  | .tuple_ es => nodeCountList es + 1
  | .arrayLit es => nodeCountList es + 1
  | .arrayIndex a ix => nodeCount a + nodeCount ix + 1
  | .refCreate e _ _ => nodeCount e + 1
  | .refLoad e => nodeCount e + 1
  | .refStore e w _ => nodeCount e + nodeCount w + 1
  | .refFree e => nodeCount e + 1
  | .refCast e _ => nodeCount e + 1
end

/-- An element of a list accounts for at most the list's total size. -/
theorem mem_nodeCountList (e : Expr) (es : List Expr) (h : e ∈ es) :
    nodeCount e ≤ nodeCountList es := by
  induction es with
  | nil => cases h
  | cons e' es ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih h) (Nat.le_add_left _ _)

/-- An arm's body accounts for at most the arms' total size. -/
theorem mem_nodeCountArms (vars : List String) (body : Expr)
    (arms : List (List String × Expr)) (h : (vars, body) ∈ arms) :
    nodeCount body ≤ nodeCountArmsSize arms := by
  induction arms with
  | nil => cases h
  | cons hd arms ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih h) (Nat.le_add_left _ _)

/-! ### The defining equations of `liftUnder` and `subst'` -/

theorem liftUnder_bvar_below (n b k : Nat) (h : n < b) :
    liftUnder b k (.bvar n) = .bvar n := by
  simp [liftUnder, h]

theorem liftUnder_bvar_above (n b k : Nat) (h : b ≤ n) :
    liftUnder b k (.bvar n) = .bvar (n + k) := by
  simp [liftUnder, Nat.not_lt.mpr h]

/-- Substitution does not touch an index strictly below the substitution
variable. -/
theorem subst_bvar_below (n i : Nat) (v : Expr) (h : n < i) :
    subst' i (.bvar n) v = .bvar n := by
  simp [subst', h]

/-- The hitting case: the index equal to the substitution variable becomes the
lifted substitute. -/
theorem subst_bvar_hit (i : Nat) (v : Expr) : subst' i (.bvar i) v = lift i v := by
  simp [subst', lift, Nat.lt_irrefl i]

/-- An index above the substitution variable is renumbered down: this is the step
that removes the hole left by the substituted variable. -/
theorem subst_bvar_above (n i : Nat) (v : Expr) (h : i < n) :
    subst' i (.bvar n) v = .bvar (n - 1) := by
  have h1 : ¬ (n < i) := by omega
  have h2 : n ≠ i := by omega
  simp [subst', h1, h2]

/-- Free variables and literals are unaffected. -/
theorem subst_fvar (s : String) (i : Nat) (v : Expr) : subst' i (.fvar s) v = .fvar s := by
  simp [subst']

theorem subst_lit (c : Morph.Core.Value) (i : Nat) (v : Expr) :
    subst' i (.lit c) v = .lit c := by
  simp [subst']

/-- The binder equations of substitution. -/
theorem subst_lam (n : Nat) (body v : Expr) (i : Nat) :
    subst' i (.lam n body) v = .lam n (subst' (i + n) body v) := by
  simp [subst']

theorem subst_let_ (e1 e2 v : Expr) (i : Nat) :
    subst' i (.let_ e1 e2) v = .let_ (subst' i e1 v) (subst' (i + 1) e2 v) := by
  simp [subst']

theorem subst_ifThenElse (c t f v : Expr) (i : Nat) :
    subst' i (.ifThenElse c t f) v = .ifThenElse (subst' i c v) (subst' i t v) (subst' i f v) := by
  simp [subst']

/-! ### Scoping

`Scoped i e`: every de Bruijn index occurring in `e` is below `i`. This is the
POPLmark / Autosubst "well-scoped at `i`" judgement, and it is what licenses
substitution at `i`. -/

mutual
/-- `Scoped` over a list. -/
def ScopedList (i : Nat) : List Expr → Prop
  | [] => True
  | e :: es => Scoped i e ∧ ScopedList i es

/-- `Scoped` over match arms; a pattern binds `vars.length` variables. -/
def ScopedArms (i : Nat) : List (List String × Expr) → Prop
  | [] => True
  | (vars, body) :: rest => Scoped (i + vars.length) body ∧ ScopedArms i rest

/-- `Scoped i e` holds when every de Bruijn index occurring in `e` is below `i`.
`bvar` is the only judgement that constrains the index; every binder raises the
scoping level by the number of variables it introduces. -/
def Scoped (i : Nat) : Expr → Prop
  | .bvar n => n < i
  | .fvar _ => True
  | .lit _ => True
  | .unop _ e => Scoped i e
  | .binop _ e1 e2 => Scoped i e1 ∧ Scoped i e2
  | .app fn args => Scoped i fn ∧ ScopedList i args
  | .lam n body => Scoped (i + n) body
  | .let_ e1 e2 => Scoped i e1 ∧ Scoped (i + 1) e2
  | .ifThenElse c t f => Scoped i c ∧ Scoped i t ∧ Scoped i f
  | .forLoop s e body => Scoped i s ∧ Scoped i e ∧ ScopedList (i + 1) body
  | .block es => ScopedList i es
  | .match_ scrut arms => Scoped i scrut ∧ ScopedArms i arms
  | .field_ e _ => Scoped i e
  | .pipe e f => Scoped i e ∧ Scoped i f
  | .typeAsc e _ => Scoped i e
  | .some_ e => Scoped i e
  | .none_ => True
  | .ok_ e => Scoped i e
  | .err_ e => Scoped i e
  | .nullCoalesce e1 e2 => Scoped i e1 ∧ Scoped i e2
  | .tuple_ es => ScopedList i es
  | .arrayLit es => ScopedList i es
  | .arrayIndex a ix => Scoped i a ∧ Scoped i ix
  | .refCreate e _ _ => Scoped i e
  | .refLoad e => Scoped i e
  | .refStore e w _ => Scoped i e ∧ Scoped i w
  | .refFree e => Scoped i e
  | .refCast e _ => Scoped i e
end

/-- List version of the no-capture law. The step is restricted to members of the
list, because that is all the induction can justify. -/
private theorem scoped_list_gen (i : Nat) (v : Expr) (es : List Expr)
    (step : ∀ e ∈ es, Scoped i e → subst' i e v = e) (hs : ScopedList i es) :
    es.map (subst' i · v) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp [ScopedList, step e (by simp) hs.1, ih (fun e he hj => step e (by simp [he]) hj) hs.2]

/-- `match_` version of the no-capture law: an arm body is substituted below its
own pattern variables. -/
private theorem scoped_arms_gen (i : Nat) (v : Expr) (arms : List (List String × Expr))
    (step : ∀ (vars : List String) (body : Expr), (vars, body) ∈ arms →
      Scoped (i + vars.length) body → subst' (i + vars.length) body v = body)
    (hs : ScopedArms i arms) : substArms i v arms = arms := by
  induction arms with
  | nil => simp [substArms]
  | cons hd rest ih =>
      rcases hd with ⟨vars, body⟩
      simp [ScopedArms, substArms, step vars body (by simp) hs.1,
        ih (fun vars body he hj => step vars body (by simp [he]) hj) hs.2]

/-! ### No capture

**The main equational-theory obligation.** -/

theorem subst_above (i : Nat) (e : Expr) (v : Expr) (hs : Scoped i e) :
    subst' i e v = e := by
  have main : ∀ (fuel : Nat) (i : Nat) (e : Expr) (v : Expr),
      nodeCount e ≤ fuel → Scoped i e → subst' i e v = e := by
    intro fuel
    refine Nat.strongRecOn (motive := fun fuel =>
      ∀ (i : Nat) (e : Expr) (v : Expr), nodeCount e ≤ fuel → Scoped i e → subst' i e v = e)
      fuel (fun fuel ih => ?_)
    intro i e v hnode hs
    cases e with
    | bvar n =>
        simp only [Scoped] at hs
        exact subst_bvar_below n i v hs
    | fvar s => exact subst_fvar s i v
    | lit c => exact subst_lit c i v
    | unop op e1 =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e1) (by omega) i e1 v (Nat.le_refl (nodeCount e1)) hs]
    | binop op e1 e2 =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e1) (by omega) i e1 v (Nat.le_refl (nodeCount e1)) hs.1,
          ih (nodeCount e2) (by omega) i e2 v (Nat.le_refl (nodeCount e2)) hs.2]
    | app fn args =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount fn) (by omega) i fn v (Nat.le_refl (nodeCount fn)) hs.1,
          scoped_list_gen i v args
            (fun e he hj => ih (nodeCountList args) (by omega) i e v
              (mem_nodeCountList e _ he) hj) hs.2]
    | lam n body =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount body) (by omega) (i + n) body v (Nat.le_refl (nodeCount body)) hs]
    | let_ e1 e2 =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e1) (by omega) i e1 v (Nat.le_refl (nodeCount e1)) hs.1,
          ih (nodeCount e2) (by omega) (i + 1) e2 v (Nat.le_refl (nodeCount e2)) hs.2]
    | ifThenElse c t f =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount c) (by omega) i c v (Nat.le_refl (nodeCount c)) hs.1,
          ih (nodeCount t) (by omega) i t v (Nat.le_refl (nodeCount t)) hs.2.1,
          ih (nodeCount f) (by omega) i f v (Nat.le_refl (nodeCount f)) hs.2.2]
    | forLoop s e body =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount s) (by omega) i s v (Nat.le_refl (nodeCount s)) hs.1,
          ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs.2.1,
          scoped_list_gen (i + 1) v body
            (fun e he hj => ih (nodeCountList body) (by omega) (i + 1) e v
              (mem_nodeCountList e _ he) hj) hs.2.2]
    | block es =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', scoped_list_gen i v es
          (fun e he hj => ih (nodeCountList es) (by omega) i e v
            (mem_nodeCountList e _ he) hj) hs]
    | match_ scrut arms =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount scrut) (by omega) i scrut v (Nat.le_refl (nodeCount scrut)) hs.1,
          scoped_arms_gen i v arms
            (fun vars body he hj => ih (nodeCountArmsSize arms) (by omega) (i + vars.length) body
              v (mem_nodeCountArms vars body _ he) hj) hs.2]
    | field_ e nm =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
    | pipe e f =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs.1,
          ih (nodeCount f) (by omega) i f v (Nat.le_refl (nodeCount f)) hs.2]
    | typeAsc e ty =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
    | some_ e =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
    | none_ => simp [subst']
    | ok_ e =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
    | err_ e =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
    | nullCoalesce e1 e2 =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e1) (by omega) i e1 v (Nat.le_refl (nodeCount e1)) hs.1,
          ih (nodeCount e2) (by omega) i e2 v (Nat.le_refl (nodeCount e2)) hs.2]
    | tuple_ es =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', scoped_list_gen i v es
          (fun e he hj => ih (nodeCountList es) (by omega) i e v
            (mem_nodeCountList e _ he) hj) hs]
    | arrayLit es =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', scoped_list_gen i v es
          (fun e he hj => ih (nodeCountList es) (by omega) i e v
            (mem_nodeCountList e _ he) hj) hs]
    | arrayIndex a ix =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount a) (by omega) i a v (Nat.le_refl (nodeCount a)) hs.1,
          ih (nodeCount ix) (by omega) i ix v (Nat.le_refl (nodeCount ix)) hs.2]
    | refCreate e cap ty =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
    | refLoad e =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
    | refStore e w ty =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs.1,
          ih (nodeCount w) (by omega) i w v (Nat.le_refl (nodeCount w)) hs.2]
    | refFree e =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
    | refCast e cap =>
        simp only [Scoped] at hs
        simp only [nodeCount] at hnode
        simp [subst', ih (nodeCount e) (by omega) i e v (Nat.le_refl (nodeCount e)) hs]
  exact main (nodeCount e) i e v (Nat.le_refl (nodeCount e)) hs

end Morph.Specs.SubstTheory
