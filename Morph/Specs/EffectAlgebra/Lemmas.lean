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
  simp only [Eff.bind, denote]
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

/-! ### Effect typing (loop 51)

Loop 6 gave the algebra but no typing. Loop 51 adds the minimal typing
judgment alongside: purity is `classes = []`, and handling preserves it.

Research: Koka (row-typed effects, Leijen 2017); OCaml 5 (one-shot
continuations, Sirektar et al.); Bauer-Pretnar non-monotone system
(arXiv:1306.6316); Affect (POPL'25, affine + effects, van Rooij et al.);
refinement types for handlers (Kawamata et al. 2024). Other languages:
Koka (rows, inferred), OCaml 5 (no effect types in the core), Unison
abilities (structural). Morph stays structural: `isPure` is `classes = []`.
-/

/-- Purity: no effect classes. -/
def Eff.isPure {σ : Type} [Inhabited σ] (c : Eff σ) : Prop :=
  Eff.classes c = []

/-- `pure` is pure. -/
theorem isPure_pure {σ : Type} [Inhabited σ] (v : σ) :
    Eff.isPure (Eff.pure v) := rfl

/-- Handling a covered computation yields no residual effects. -/
theorem handle_covered_pure {σ : Type} [Inhabited σ] (h : Handler σ) (c : Eff σ)
    (hcov : Handler.coversComp h c) : h.residual c = [] :=
  covered_residual_empty h c hcov

/-! ### Loop 62: row typing + deep handlers

Research: Koka (Leijen 2014/2017 — row-typed effects with scoped labels,
rows extended by unification); OCaml 5 multicore (deep handlers by default,
one-shot continuations — Sivaramakrishnan et al.); Hillerström & Lindley
(shallow vs deep: deep handlers are folds over the free monad, shallow handle
only the head operation); Plotkin & Pretnar (handler = model + the
homomorphism the free model's universal property induces).

Language comparison: Koka (rows inferred, handlers deep); OCaml 5 (deep
handlers, no static rows in the core language); Unison (abilities = rows
with deep handlers); Eff (deep handlers); Frank (multihandlers). Morph:
`EffectSet` is the row, `hasRow` is row containment (so row polymorphism is
weakening/extension, proved below), and `denote` is already the deep fold —
`handle_op_deep` states its fold equation, contrasted with `shallowHead`.
-/

/-- Row typing: the computation fits in row `ρ`. Row polymorphism is free:
a computation typed under `ρ` also types under any suprow (`hasRow_mono`,
`hasRow_extend`). -/
def Eff.hasRow {σ : Type} [Inhabited σ] (c : Eff σ) (ρ : EffectSet) : Prop :=
  ∀ k ∈ Eff.classes c, k ∈ ρ

/-- `pure` fits in every row. -/
theorem hasRow_pure {σ : Type} [Inhabited σ] (v : σ) (ρ : EffectSet) :
    (Eff.pure v).hasRow ρ := by
  intro k hk
  have hk' : k ∈ ([] : EffectSet) := hk
  nomatch hk'

/-- Operations fit when the head class is in the row and the continuation
(instantiated at `default` — the row must cover every answer path, and the
`default` path is one of them) fits. -/
theorem hasRow_op {σ : Type} [Inhabited σ] (o : Op) (k : σ → Eff σ)
    (ρ : EffectSet) (hhead : o.class ∈ ρ)
    (htail : (k default).hasRow ρ) : (Eff.op o k).hasRow ρ := by
  intro k' hk'
  have hd : k' = o.class ∨ k' ∈ Eff.classes (k default) :=
    List.mem_cons.mp hk'
  rcases hd with rfl | hk'
  · exact hhead
  · exact htail k' hk'

/-- Row weakening (subsumption): fitting in `ρ` implies fitting in any
suprow. This is Koka's row polymorphism, structurally. -/
theorem hasRow_mono {σ : Type} [Inhabited σ] (c : Eff σ)
    {ρ ρ' : EffectSet} (h : c.hasRow ρ)
    (hsub : ∀ k ∈ ρ, k ∈ ρ') : c.hasRow ρ' :=
  fun k hk => hsub k (h k hk)

/-- Row extension: a computation typed under `ρ` also types under `ρ` with
more effects appended. -/
theorem hasRow_extend {σ : Type} [Inhabited σ] (c : Eff σ)
    (ρ extra : EffectSet) (h : c.hasRow ρ) : c.hasRow (ρ ++ extra) :=
  fun k hk => List.mem_append.mpr (Or.inl (h k hk))

/-- Purity is the empty row. -/
theorem hasRow_nil_iff_isPure {σ : Type} [Inhabited σ] (c : Eff σ) :
    c.hasRow [] ↔ c.isPure := by
  constructor
  · intro h
    cases hc : Eff.classes c with
    | nil => exact hc
    | cons a as =>
      have hmem : a ∈ Eff.classes c := by
        rw [hc]
        exact List.mem_cons_self
      have hnil : a ∈ ([] : EffectSet) := h a hmem
      nomatch hnil
  · intro h k hk
    have hc : Eff.classes c = [] := h
    rw [hc] at hk
    exact hk

/-- Coverage is row membership: a handler covers a computation exactly when
the computation fits in the handler's row. -/
theorem hasRow_of_covers {σ : Type} [Inhabited σ] (h : Handler σ) (c : Eff σ)
    (hcov : h.coversComp c) : c.hasRow h.covers := hcov

/-! #### Deep handling is the fold; shallow handling drops continuations

`denote` recurses into continuations, so `handle` re-handles every
resumption — that is the deep-handler fold equation (Hillerström & Lindley;
OCaml 5 semantics). `shallowHead` handles only the head operation and
discards the continuation, so the two agree on `pure` and differ exactly
where depth matters. -/

/-- **The deep-handler fold equation.** Handling an operation occurrence
interprets it and re-handles every resumption under the same handler. -/
theorem handle_op_deep {σ : Type} (h : Handler σ) (o : Op) (k : σ → Eff σ) :
    handle h (.op o k) =
      (h.model.answer o).flatMap (fun v => handle h (k v)) := rfl

/-- Shallow handling: interpret the head operation only; continuations are
dropped (left for a resumption the shallow handler never performs). -/
def shallowHead {σ : Type} (M : Model σ) : Eff σ → List σ
  | .pure v => [v]
  | .op o _ => M.answer o
  | .andThen m _ => shallowHead M m

/-- Shallow and deep agree on `pure`. -/
theorem shallowHead_pure {σ : Type} (M : Model σ) (v : σ) :
    shallowHead M (.pure v) = [v] := rfl

/-- Shallow handling of an operation is just the model's answers — the
continuation is ignored. -/
theorem shallowHead_op {σ : Type} (M : Model σ) (o : Op) (k : σ → Eff σ) :
    shallowHead M (.op o k) = M.answer o := rfl

/-- A concrete model: `read` answers, everything else fails. -/
def exModel : Model String where
  answer
    | .read _ => ["v"]
    | _ => []

/-- Deep handling runs the continuation: `read` answers `"v"`, the
continuation ignores it and returns `"done"`. -/
example : handle ⟨exModel, [.io]⟩
    (.op (.read "s") (fun _ => .pure "done")) = ["done"] := rfl

/-- Shallow handling stops at the head operation: the continuation never
runs, so the answer is the raw `"v"`. This is exactly where depth matters. -/
example : shallowHead exModel
    (.op (.read "s") (fun _ => .pure "done")) = ["v"] := rfl

/-- Row example: `pure` fits in any row, e.g. `[.io]`. -/
example : (Eff.pure "x").hasRow [.io] := hasRow_pure _ _

/-! ### The named-row chain (loop 93)

The effect-system spec v2.1.0 (`spec/type/effect_system_spec.md` §2.2–2.3)
defines an effect **row** as a subset of the four classes and names four
canonical rows — IO, Net, Time, System — claiming they form a chain under row
inclusion. These definitions and lemmas are that claim, machine-checked: the
class order induces the named rows, membership in a named row is exactly the
class order, distinct named rows are distinct, and `io`/`system` are the
bottom/top classes. -/

/-- The rank of a class in the named chain `io < net < time < system`. -/
def classRank : EffectClass → Nat
  | .io => 0
  | .net => 1
  | .time => 2
  | .system => 3

/-- The class order underlying the named rows. -/
def classLE (a b : EffectClass) : Prop := classRank a ≤ classRank b

/-- Rank is injective on classes: equal ranks are equal classes. The match
compiler discharges the mismatched pairs — their rank hypotheses are
constructor-impossible. -/
theorem classRank_inj {a b : EffectClass} (h : classRank a = classRank b) : a = b := by
  match a, b, h with
  | .io, .io, _ => rfl
  | .net, .net, _ => rfl
  | .time, .time, _ => rfl
  | .system, .system, _ => rfl

/-- Reflexivity of the class order. -/
theorem classLE_refl (a : EffectClass) : classLE a a := Nat.le_refl _

/-- Transitivity of the class order. -/
theorem classLE_trans {a b c : EffectClass} (h1 : classLE a b) (h2 : classLE b c) :
    classLE a c := Nat.le_trans h1 h2

/-- Antisymmetry of the class order, via rank injectivity. -/
theorem classLE_antisym {a b : EffectClass} (h1 : classLE a b) (h2 : classLE b a) :
    a = b := classRank_inj (Nat.le_antisymm h1 h2)

/-- `io` is the least class — the IO row is below every named row. -/
theorem classLE_io_min (c : EffectClass) : classLE .io c := by
  cases c <;> simp only [classLE, classRank] <;> omega

/-- `system` is the greatest class — the System row is above every named row. -/
theorem classLE_system_max (c : EffectClass) : classLE c .system := by
  cases c <;> simp only [classLE, classRank] <;> omega

/-- The chain edges of spec §2.3: IO ⊑ Net ⊑ Time ⊑ System. -/
theorem classLE_io_net : classLE .io .net := by
  simp only [classLE, classRank]; omega

theorem classLE_net_time : classLE .net .time := by
  simp only [classLE, classRank]; omega

theorem classLE_time_system : classLE .time .system := by
  simp only [classLE, classRank]; omega

/-- The named rows of the effect-system spec: IO, Net, Time, System. Each is
the downward closure of its class in `classLE` — which is exactly why the
spec's chain holds and why row inclusion on named rows *is* the class order. -/
def namedRow : EffectClass → EffectSet
  | .io => [.io]
  | .net => [.io, .net]
  | .time => [.io, .net, .time]
  | .system => [.io, .net, .time, .system]

/-- Row membership in a named row is exactly the class order. -/
theorem mem_namedRow_iff {k c : EffectClass} : k ∈ namedRow c ↔ classLE k c := by
  cases c <;> cases k <;> simp [namedRow, classLE, classRank]

/-- The named rows separate the classes: equal named rows are equal classes
(the row view is antisymmetric, as the spec's subset-ordering claim needs). -/
theorem namedRow_inj {a b : EffectClass} (h : namedRow a = namedRow b) : a = b := by
  have h1 : classLE a b := by
    have ha : a ∈ namedRow a := by cases a <;> simp [namedRow]
    rw [h] at ha
    exact mem_namedRow_iff.mp ha
  have h2 : classLE b a := by
    have hb : b ∈ namedRow b := by cases b <;> simp [namedRow]
    rw [← h] at hb
    exact mem_namedRow_iff.mp hb
  exact classLE_antisym h1 h2

end Morph.Specs.EffectAlgebra
