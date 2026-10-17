/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.EffectAlgebra.Spec

/-!
# The algebra of Morph's effect set

Theorems about the free-model monad. See `Spec.lean` for the research basis
(Plotkin & Pretnar's algebraic effects; Bauer & Pretnar's non-monotone effect
system).
-/

namespace Morph.Specs.EffectAlgebra

/-! ### The model is a homomorphism, and the laws hold in it

The central algebraic-effects claim: because the computation monad is the
*free-model monad* of the theory, interpreting it by a model turns `bind` into
the monadic operation of `List`. Handling is then just `denote` with the
handler's model — the homomorphism the free model's universal property induces.

Because the freer monad keeps sequencing explicit, the monad laws are *not*
definitional: they are theorems about `denote`, which is exactly the claim that
nothing can observe the difference between `bind (bind m f) g` and
`bind m (fun v => bind (f v) g)`. -/

/-- `flatMap` distributes over itself. -/
private theorem flatMap_distrib {σ σ' σ'' : Type} (a : List σ) (b : σ → List σ')
    (g : σ' → List σ'') : a.flatMap (fun x => (b x).flatMap g) = (a.flatMap b).flatMap g := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [ih, List.flatMap_append]

/-- `flatMap` over singletons is the identity — returning the value unchanged. -/
private theorem flatMap_singleton {σ : Type} (a : List σ) :
    a.flatMap (fun x => [x]) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

/-- `denote` turns sequencing into the monadic operation of `List`. -/
theorem denote_andThen {σ : Type} (M : Model σ) (m : Eff σ) (f : σ → Eff σ) :
    denote M (.andThen m f) = (denote M m).flatMap (fun v => denote M (f v)) := rfl

/-- **The induced map is a monad homomorphism.** -/
theorem denote_bind {σ : Type} (M : Model σ) (m : Eff σ) (f : σ → Eff σ) :
    denote M (Eff.bind m f) = (denote M m).flatMap (fun v => denote M (f v)) :=
  denote_andThen M m f

/-- A `pure` computation denotes the singleton of its value. -/
theorem denote_pure {σ : Type} (M : Model σ) (v : σ) : denote M (.pure v) = [v] := rfl

/-- **Bind is associative in the model.** Nothing distinguishes
`bind (bind m f) g` from `bind m (fun v => bind (f v) g)`. -/
theorem bind_assoc_denote {σ : Type} (M : Model σ) (m : Eff σ) (f g : σ → Eff σ) :
    denote M (Eff.bind (Eff.bind m f) g) = denote M (Eff.bind m (fun v => Eff.bind (f v) g)) := by
  simp only [Eff.bind, denote_andThen]
  symm
  exact flatMap_distrib (denote M m) (fun v => denote M (f v)) (fun v => denote M (g v))

/-- `pure` is a left unit in the model. -/
theorem pure_bind_denote {σ : Type} (M : Model σ) (v : σ) (f : σ → Eff σ) :
    denote M (Eff.bind (.pure v) f) = denote M (f v) := by
  simp only [Eff.bind, denote, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- `pure` is a right unit in the model. -/
theorem bind_pure_denote {σ : Type} (M : Model σ) (m : Eff σ) :
    denote M (Eff.bind m (fun v => Eff.pure v)) = denote M m := by
  simp only [Eff.bind, denote, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact flatMap_singleton _

/-- **An unhandled operation yields no answers.** With `answer o = []` the
computation denotes the empty set — which is how `Net.connect` failing is
represented. Failure is not a distinguished syntactic form; it is the *absence
of an answer*, which is what lets `Net` and `Time` share a shape with `IO`. -/
theorem denote_unanswered {σ : Type} (M : Model σ) (o : Op) (k : σ → Eff σ)
    (h : M.answer o = []) : denote M (.op o k) = [] := by
  simp [denote, h]

/-! ### Effect sets accumulate under bind

Bauer & Pretnar (arXiv:1306.6316) observe that an effect system *with handlers*
is non-monotone: a handler can delete effects, so effects are not merely
accumulated in types. Two properties must therefore hold, and they do: bind
accumulates (so a syntactic upper bound is sound), and handling only removes (so
a handler cannot smuggle in an effect a static analysis never saw). -/

theorem classes_pure {σ : Type} [Inhabited σ] (v : σ) :
    Eff.classes (.pure v) = [] := rfl

theorem classes_op {σ : Type} [Inhabited σ] (o : Op) (k : σ → Eff σ) :
    Eff.classes (.op o k) = o.class :: Eff.classes (k default) := rfl

theorem classes_andThen {σ : Type} [Inhabited σ] (m : Eff σ) (f : σ → Eff σ) :
    Eff.classes (.andThen m f) = Eff.classes m := rfl

/-- **Bind accumulates.** Every effect class of `m.bind f` occurs in `m` or in
one of the `f v`. Sequencing can only add effects from the continuation. -/
theorem classes_bind_subset {σ : Type} [Inhabited σ] (m : Eff σ) (f : σ → Eff σ)
    (k : EffectClass) (hk : k ∈ Eff.classes (Eff.bind m f)) :
    k ∈ Eff.classes m ∨ ∃ v, k ∈ Eff.classes (f v) := by
  exact Or.inl (by simpa [Eff.bind, Eff.classes] using hk)

/-! ### Handling only removes effects

Bauer & Pretnar's non-monotonicity, in the one direction an effect *system* has
to guarantee. The effect classes still outstanding after a handler has run are
those the handler does not cover — a subset of what the computation could
perform beforehand. -/

/-- Boolean membership in an effect set. Spelled out because core Lean has no
`Decidable (k ∈ l)` instance for lists, so neither `decide` nor `if k ∈ l` is
available. -/
def memClass (k : EffectClass) : EffectSet → Bool
  | [] => false
  | a :: l => if a = k then true else memClass k l

theorem memClass_eq_true_iff {k : EffectClass} {l : EffectSet} :
    memClass k l = true ↔ k ∈ l := by
  induction l with
  | nil => simp [memClass]
  | cons a l ih =>
      by_cases h : a = k
      · simp [memClass, h]
      · simp [memClass, h, ih, Ne.symm h]

theorem memClass_eq_false_iff {k : EffectClass} {l : EffectSet} :
    memClass k l = false ↔ ¬ (k ∈ l) := by
  induction l with
  | nil => simp [memClass]
  | cons a l ih =>
      by_cases h : a = k
      · simp [memClass, h]
      · simp [memClass, h, ih, Ne.symm h]

/-- Remove the covered classes from an effect set. -/
def EffectSet.removeCovered (covered : EffectSet) : EffectSet → EffectSet
  | [] => []
  | a :: l =>
      if memClass a covered then covered.removeCovered l else a :: covered.removeCovered l

/-- The effect classes a computation may still perform once `h` has handled it. -/
def Handler.residual {σ : Type} (h : Handler σ) [Inhabited σ] (c : Eff σ) : EffectSet :=
  h.covers.removeCovered (Eff.classes c)

/-- **A handler can only remove effects.** The residual effect set after handling
is contained in the set before. -/
theorem residual_subset {σ : Type} [Inhabited σ] (h : Handler σ) (c : Eff σ)
    (k : EffectClass) (hk : k ∈ h.residual c) : k ∈ Eff.classes c := by
  have aux : ∀ (l : EffectSet) (k : EffectClass),
      k ∈ h.covers.removeCovered l → k ∈ l := by
    intro l
    induction l with
    | nil => intro k hk; cases hk
    | cons a l ih =>
        intro k hk
        by_cases hac : memClass a h.covers = true
        · rw [EffectSet.removeCovered, if_pos hac] at hk
          exact List.mem_cons_of_mem a (ih k hk)
        · rw [EffectSet.removeCovered, if_neg hac] at hk
          rcases (List.mem_cons.mp hk) with rfl | hk
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem a (ih k hk)
  exact aux (Eff.classes c) k (by simpa [Handler.residual] using hk)

/-- **A covering handler discharges every effect.** If the handler covers all
the classes the computation may perform, nothing is left outstanding: handling
made the computation pure with respect to the effect system. This is precisely
the non-monotone step — the post-handling effect set is *smaller*, not equal. -/
theorem covered_residual_empty {σ : Type} [Inhabited σ] (h : Handler σ) (c : Eff σ)
    (hcov : Handler.coversComp h c) : h.residual c = [] := by
  have aux : ∀ (l : EffectSet), (∀ k ∈ l, k ∈ h.covers) →
      h.covers.removeCovered l = [] := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
        intro hall
        have hac : memClass a h.covers = true :=
          (memClass_eq_true_iff).2 (hall a (by simp))
        rw [EffectSet.removeCovered, if_pos hac, ih (fun k hk => hall k (by simp [hk]))]
  exact aux (Eff.classes c) hcov

end Morph.Specs.EffectAlgebra
