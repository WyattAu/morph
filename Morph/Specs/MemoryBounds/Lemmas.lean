/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.MemoryBounds.Spec

namespace Morph.Specs.MemoryBounds

/-!
## List and heap-update facts

Proof-engineering note: every goal below is stated with `change` rather than
`dsimp`. `dsimp` zeta/iota-reduces `l₁ ++ l₂` into `l₁.head :: (l₁.tail ++ l₂)`,
which silently changes the shape of every membership goal; `change` keeps the
syntax the proof is written against while staying definitionally equal.
-/

theorem mem_cons_self' (a : Addr) (l : List Addr) : a ∈ a :: l :=
  (List.mem_cons).mpr (Or.inl rfl)

theorem appL {a : Addr} {l₁ l₂ : List Addr} (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  (List.mem_append).mpr (Or.inl h)

theorem appR {a : Addr} {l₁ l₂ : List Addr} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  (List.mem_append).mpr (Or.inr h)

theorem eraseMem {a b : Addr} {l : List Addr} (h : a ∈ l) (hab : a ≠ b) :
    a ∈ l.erase b :=
  (List.mem_erase_of_ne hab).mpr h

/-- Erasing an element from a duplicate-free list removes it. -/
theorem notMemErase {a : Addr} {l : List Addr} (hnd : l.Nodup) (h : a ∈ l) :
    a ∉ l.erase a := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
      simp only [List.nodup_cons] at hnd
      intro hmem
      by_cases hba : b = a
      · rw [← hba] at hmem
        rw [List.erase_cons_head] at hmem
        exact hnd.1 hmem
      · rw [List.erase_cons_tail (by simp [hba])] at hmem
        rcases Iff.mp (List.mem_cons) hmem with heq | hmem'
        · exact False.elim (hba heq.symm)
        · rcases Iff.mp (List.mem_cons) h with heq' | htail
          · exact False.elim (hba heq'.symm)
          · exact ih hnd.2 htail hmem'

theorem nodupErase {l : List Addr} (hnd : l.Nodup) (a : Addr) :
    (l.erase a).Nodup := by
  induction l with
  | nil => simp
  | cons b t ih =>
      simp only [List.nodup_cons] at hnd
      by_cases hba : b = a
      · rw [← hba, List.erase_cons_head]
        exact hnd.2
      · rw [List.erase_cons_tail (by simp [hba])]
        refine List.pairwise_cons.mpr ⟨?_, ih hnd.2⟩
        intro b' hb' hba
        exact hnd.1 (hba ▸ List.mem_of_mem_erase hb')

theorem hAdd_live (h : Heap) (a f x : Addr) :
    (hAdd h a f) x ≠ none ↔ h x ≠ none := by
  by_cases hxa : x = a
  · rw [hxa, hAdd, hUpd_self]
    cases hha : h a <;> simp
  · rw [hAdd, hUpd, if_neg hxa]

theorem hDel_live (h : Heap) (a x : Addr) :
    (hDel h a) x ≠ none ↔ x ≠ a ∧ h x ≠ none := by
  by_cases hxa : x = a
  · rw [hxa, hDel, hUpd_self]
    simp
  · rw [hDel, hUpd, if_neg hxa]
    simp [hxa]

/-- The one entry `store` changes. -/
theorem hAdd_self (h : Heap) (a f : Addr) :
    hAdd h a f a = match h a with
      | none => none
      | some fs => some (fs ++ [f]) := by
  rw [hAdd, hUpd_self]
  rfl

theorem hAdd_ne (h : Heap) (a f x : Addr) (hx : x ≠ a) :
    hAdd h a f x = h x := by
  rw [hAdd, hUpd_ne h a _ x hx]

theorem Reach.mono_base (h : Heap) (base base' : List Addr) (a : Addr)
    (hsub : ∀ x, x ∈ base → x ∈ base') (hr : Reach h base a) :
    Reach h base' a := by
  induction hr with
  | base_ x hx => exact .base_ x (hsub x hx)
  | edge_ x f fs hlook hfin hrec ih => exact .edge_ x f fs hlook hfin ih

/-!
## The affine `store` move

Moving the root `f` under the root `a` shrinks the base by one element (`f`)
but adds the edge `a → f`. Reachability survives because the only derivation
that leaned on `f` as a *base* element is re-anchored at `a`: `a ≠ f` and
`a ∈ roots` keep `a` in the new base, and the new edge `a → f` restores `f`
itself, with every path *out of* `f` untouched — only `a`'s field list grew,
as a prefix extension.
-/

theorem reach_store (h : Heap) (a f : Addr) (roots pending : List Addr)
    (har : a ∈ roots) (_hfr : f ∈ roots) (haf : a ≠ f)
    (ha : h a ≠ none)
    (x : Addr) (hx : Reach h (roots ++ pending) x) :
    Reach (hAdd h a f) (roots.erase f ++ pending) x := by
  induction hx with
  | base_ z hz =>
      simp only [List.mem_append] at hz
      rcases hz with hzr | hzp
      · by_cases hzf : z = f
        · have ha' : a ∈ roots.erase f := eraseMem har haf
          have hreach_a : Reach (hAdd h a f) (roots.erase f ++ pending) a :=
            .base_ a (appL ha')
          cases hha : h a with
          | none => exact False.elim ((hha ▸ ha) rfl)
          | some fs =>
              have hedg : Reach (hAdd h a f) (roots.erase f ++ pending) f :=
                .edge_ a f (fs ++ [f])
                  (by rw [hAdd_self, hha])
                  (appR (List.mem_singleton_self f))
                  hreach_a
              simpa [hzf] using hedg
        · exact .base_ z (appL (eraseMem hzr hzf))
      · exact .base_ z (appR hzp)
  | @edge_ z g fs hlook hfin _ ih =>
      by_cases hza : z = a
      · have hlook' : h a = some fs := hza ▸ hlook
        exact .edge_ a g (fs ++ [f]) (by rw [hAdd_self, hlook'])
          (appL hfin) (hza ▸ ih)
      · exact .edge_ z g fs (by rw [hAdd_ne h a f z hza, hlook]) hfin ih

/-- Allocating a *fresh* address cannot break reachability: the fresh address
has no edges in the old heap, so no derivation passes through it, and the new
root only enlarges the base. -/
theorem reach_alloc (h : Heap) (a : Addr) (v : Option (List Addr))
    (base : List Addr) (hfresh : h a = none)
    (x : Addr) (hr : Reach h base x) :
    Reach (hUpd h a v) (a :: base) x := by
  induction hr with
  | base_ y hy => exact .base_ y (List.mem_cons_of_mem _ hy)
  | @edge_ y g fs hlook hfin hrec ih =>
      refine .edge_ y g _ ?_ hfin ih
      have hya : y ≠ a := by
        intro he; subst he
        rw [hfresh] at hlook
        simp at hlook
      exact hUpd_ne h a v y hya ▸ hlook

/-- Collection deletes one entry and re-roots its children in the queue:
reachability of every other live address survives. -/
theorem reach_del (h h' : Heap) (base base' : List Addr) (a : Addr)
    (fsa : List Addr) (hfa : h a = some fsa)
    (_hnone : h' a = none)
    (hothers : ∀ y, y ≠ a → h' y = h y)
    (hbase : ∀ z, z ∈ base → z ≠ a → z ∈ base')
    (hchildren : ∀ g, g ∈ fsa → g ∈ base')
    (x : Addr) (hx : Reach h base x) (hxa : x ≠ a) :
    Reach h' base' x := by
  induction hx with
  | base_ y hy => exact .base_ y (hbase y hy hxa)
  | @edge_ y g fs hlook hfin hrec ih =>
      by_cases hya : y = a
      · subst y
        refine .base_ g ?_
        have hfs : fs = fsa := by rw [hfa] at hlook; cases hlook; rfl
        exact hchildren g (hfs.symm ▸ hfin)
      · refine .edge_ y g fs (hothers y hya ▸ hlook) hfin (ih hya)

/-!
## The invariant is preserved by every step

This is the content of SG-002: the affine discipline is not an assumption the
runtime has to re-check, it is an *invariant* every step maintains — so a
well-started program can never accumulate unreachable objects, and freeing an
object can never dangle one of its edges.
-/

theorem invariant_preserved (c c' : Config) (hstep : Step c c') :
    Invariant c → Invariant c' := by
  intro hc
  obtain ⟨⟨hp1, hp2⟩, ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩, hnd⟩ := hc
  cases hstep with
  | alloc a hfresh hnrr hnrp =>
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro x hx
        change (hUpd c.heap a (some [])) x ≠ none at hx
        change Reach (hUpd c.heap a (some [])) ((a :: c.roots) ++ c.pending) x
        by_cases hxa : x = a
        · rw [hUpd, if_pos hxa] at hx
          rw [hxa]
          exact .base_ a (appL (mem_cons_self' a c.roots))
        · rw [hUpd, if_neg hxa] at hx
          exact by simpa [List.cons_append] using
            (reach_alloc c.heap a (some []) (c.roots ++ c.pending) hfresh x
              (hp1 x hx))
      · intro r hr
        change (hUpd c.heap a (some [])) r ≠ none
        rcases Iff.mp (List.mem_cons) hr with h | hr
        · rw [h, hUpd_self]
          simp
        · rw [hUpd_ne c.heap a (some []) r (fun he => hnrr (he ▸ hr))]
          exact hp2 r hr
      · intro p hp' hmem
        change p ∈ a :: c.roots at hmem
        rcases Iff.mp (List.mem_cons) hmem with heq | hmem
        · exact hnrp (heq ▸ hp')
        · exact hq1 p hp' hmem
      · intro y g fs hy hg hmem
        change (hUpd c.heap a (some [])) y = some fs at hy
        change g ∈ a :: c.roots at hmem
        by_cases hya : y = a
        · rw [hya, hUpd_self] at hy
          cases hy
          simp at hg
        · rw [hUpd_ne c.heap a (some []) y hya] at hy
          rcases Iff.mp (List.mem_cons) hmem with heq | hmem
          · exact hq3 y g fs hy hg (heq ▸ hfresh)
          · exact hq2 y g fs hy hg hmem
      · intro y g fs hy hg
        change (hUpd c.heap a (some [])) y = some fs at hy
        change (hUpd c.heap a (some [])) g ≠ none
        by_cases hya : y = a
        · rw [hya, hUpd_self] at hy
          cases hy
          simp at hg
        · rw [hUpd_ne c.heap a (some []) y hya] at hy
          by_cases hga : g = a
          · rw [hga, hUpd_self]
            simp
          · rw [hUpd_ne c.heap a (some []) g hga]
            exact hq3 y g fs hy hg
      · intro p y fs hp' hy hg
        change (hUpd c.heap a (some [])) y = some fs at hy
        by_cases hya : y = a
        · rw [hya, hUpd_self] at hy
          cases hy
          simp at hg
        · rw [hUpd_ne c.heap a (some []) y hya] at hy
          exact hq4 p y fs hp' hy hg
      · intro p y y' fs fs' hy hpy hy' hpy'
        change (hUpd c.heap a (some [])) y = some fs at hy
        change (hUpd c.heap a (some [])) y' = some fs' at hy'
        by_cases hya : y = a
        · rw [hya, hUpd_self] at hy
          cases hy
          simp at hpy
        · rw [hUpd_ne c.heap a (some []) y hya] at hy
          by_cases hya' : y' = a
          · rw [hya', hUpd_self] at hy'
            injection hy' with hy'
            subst hy'
            simp at hpy'
          · rw [hUpd_ne c.heap a (some []) y' hya'] at hy'
            exact hq5 p y y' fs fs' hy hpy hy' hpy'
      · intro y fs hy
        change (hUpd c.heap a (some [])) y = some fs at hy
        by_cases hya : y = a
        · rw [hya, hUpd_self] at hy
          cases hy
          exact List.nodup_nil
        · rw [hUpd_ne c.heap a (some []) y hya] at hy
          exact hq6 y fs hy
      · intro y fs hy
        change (hUpd c.heap a (some [])) y = some fs at hy
        by_cases hya : y = a
        · rw [hya, hUpd_self] at hy
          cases hy
          simp
        · rw [hUpd_ne c.heap a (some []) y hya] at hy
          exact hq7 y fs hy
      · exact List.nodup_cons.mpr ⟨hnrr, hnd⟩
  | store a f har hfr haf =>
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro x hx
        change (hAdd c.heap a f) x ≠ none at hx
        change Reach (hAdd c.heap a f) ((c.roots.erase f) ++ c.pending) x
        exact reach_store c.heap a f c.roots c.pending har hfr haf
          (hp2 a har) x
          (hp1 x ((hAdd_live c.heap a f x).mp hx))
      · intro r hr
        change (hAdd c.heap a f) r ≠ none
        exact (hAdd_live c.heap a f r).mpr (hp2 r (List.mem_of_mem_erase hr))
      · intro p hp' hmem
        change p ∈ c.roots.erase f at hmem
        exact hq1 p hp' (List.mem_of_mem_erase hmem)
      · intro y g fs hy hg
        change (hAdd c.heap a f) y = some fs at hy
        by_cases heqf : g = f
        · simpa [heqf] using notMemErase hnd hfr
        · intro hmem
          have hmem' := List.mem_of_mem_erase hmem
          by_cases hya : y = a
          · rw [hya, hAdd_self] at hy
            cases hha : c.heap a with
            | none => rw [hha] at hy; simp at hy
            | some fs0 =>
                rw [hha] at hy
                cases hy
                rcases List.mem_append.mp hg with hg | hgf
                · exact hq2 a g fs0 hha hg hmem'
                · rw [List.mem_singleton] at hgf
                  exact heqf (hgf ▸ rfl)
          · rw [hAdd_ne c.heap a f y hya] at hy
            exact hq2 y g fs hy hg hmem'
      · intro y g fs hy hg
        change (hAdd c.heap a f) y = some fs at hy
        change (hAdd c.heap a f) g ≠ none
        by_cases hya : y = a
        · rw [hya, hAdd_self] at hy
          cases hha : c.heap a with
          | none => rw [hha] at hy; simp at hy
          | some fs0 =>
              rw [hha] at hy
              cases hy
              rcases List.mem_append.mp hg with hg | hgf
              · exact (hAdd_live c.heap a f g).mpr (hq3 a g fs0 hha hg)
              · rw [List.mem_singleton] at hgf
                rw [hgf]
                exact (hAdd_live c.heap a f f).mpr (hp2 f hfr)
        · rw [hAdd_ne c.heap a f y hya] at hy
          exact (hAdd_live c.heap a f g).mpr (hq3 y g fs hy hg)
      · intro p y fs hp' hy hg
        change (hAdd c.heap a f) y = some fs at hy
        by_cases hya : y = a
        · rw [hya, hAdd_self] at hy
          cases hha : c.heap a with
          | none => rw [hha] at hy; simp at hy
          | some fs0 =>
              rw [hha] at hy
              cases hy
              rcases List.mem_append.mp hg with hg | hgf
              · exact hq4 p a fs0 hp' hha hg
              · rw [List.mem_singleton] at hgf
                exact absurd (hgf ▸ hfr) (hq1 p hp')
        · rw [hAdd_ne c.heap a f y hya] at hy
          exact hq4 p y fs hp' hy hg
      · intro p y y' fs fs' hy hpy hy' hpy'
        change (hAdd c.heap a f) y = some fs at hy
        change (hAdd c.heap a f) y' = some fs' at hy'
        by_cases hya : y = a
        · rw [hya, hAdd_self] at hy
          cases hha : c.heap a with
          | none => rw [hha] at hy; simp at hy
          | some fs0 =>
              rw [hha] at hy
              cases hy
              rcases List.mem_append.mp hpy with hpy | hpy
              · by_cases hya' : y' = a
                · rw [hya, hya']
                · rw [hAdd_ne c.heap a f y' hya'] at hy'
                  exact False.elim (hya' (Eq.symm (hq5 p a y' fs0 fs' hha hpy hy' hpy')))
              · rw [List.mem_singleton] at hpy
                by_cases hya' : y' = a
                · rw [hya, hya']
                · rw [hAdd_ne c.heap a f y' hya'] at hy'
                  exact False.elim (absurd hfr (hq2 y' f fs' hy' (hpy ▸ hpy')))
        · rw [hAdd_ne c.heap a f y hya] at hy
          by_cases hya' : y' = a
          · rw [hya', hAdd_self] at hy'
            cases hha : c.heap a with
            | none => rw [hha] at hy'; simp at hy'
            | some fs0 =>
                rw [hha] at hy'
                injection hy' with hy'
                subst hy'
                rcases List.mem_append.mp hpy' with hpy' | hpy'
                · exact False.elim (hya (hq5 p y a fs fs0 hy hpy hha hpy'))
                · rw [List.mem_singleton] at hpy'
                  exact False.elim (absurd hfr (hq2 y f fs hy (hpy'.symm ▸ hpy)))
          · rw [hAdd_ne c.heap a f y' hya'] at hy'
            exact hq5 p y y' fs fs' hy hpy hy' hpy'
      · intro y fs hy
        change (hAdd c.heap a f) y = some fs at hy
        by_cases hya : y = a
        · rw [hya, hAdd_self] at hy
          cases hha : c.heap a with
          | none => rw [hha] at hy; simp at hy
          | some fs0 =>
              rw [hha] at hy
              cases hy
              refine List.nodup_append.mpr ⟨hq6 a fs0 hha, by simp, ?_⟩
              intro b hb b' hb'' heq
              have hb'f : b' = f := by simpa using hb''
              rw [hb'f] at heq
              exact absurd (heq ▸ hfr) (hq2 a b fs0 hha hb)
        · rw [hAdd_ne c.heap a f y hya] at hy
          exact hq6 y fs hy
      · intro y fs hy
        change (hAdd c.heap a f) y = some fs at hy
        by_cases hya : y = a
        · rw [hya] at hy ⊢
          rw [hAdd_self] at hy
          cases hha : c.heap a with
          | none => rw [hha] at hy; simp at hy
          | some fs0 =>
              rw [hha] at hy
              cases hy
              refine fun hmem => ?_
              rcases List.mem_append.mp hmem with hmem | hmem
              · exact (hq7 a fs0 hha) hmem
              · rw [List.mem_singleton] at hmem
                exact haf hmem
        · rw [hAdd_ne c.heap a f y hya] at hy
          exact hq7 y fs hy
      · exact nodupErase hnd f
  | dropRoot a har =>
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro x hx
        change c.heap x ≠ none at hx
        change Reach c.heap ((c.roots.erase a) ++ (c.pending ++ [a])) x
        refine Reach.mono_base c.heap (c.roots ++ c.pending)
          ((c.roots.erase a) ++ (c.pending ++ [a])) x ?_ (hp1 x hx)
        intro z hz
        rcases List.mem_append.mp hz with hzr | hzp
        · by_cases hza : z = a
          · rw [hza]
            exact appR (appR (List.mem_singleton_self a))
          · exact appL (eraseMem hzr hza)
        · exact appR (appL (hzp : z ∈ c.pending))
      · intro r hr
        change c.heap r ≠ none
        exact hp2 r (List.mem_of_mem_erase hr)
      · intro p hp' hmem
        change p ∈ c.roots.erase a at hmem
        rcases List.mem_append.mp hp' with hpp | hpp
        · exact (hq1 p hpp) (List.mem_of_mem_erase hmem)
        · have hpa : p = a := by simpa using hpp
          exact notMemErase hnd har (hpa ▸ hmem)
      · intro y g fs hy hg
        change c.heap y = some fs at hy
        by_cases heqa : g = a
        · simpa [heqa] using notMemErase hnd har
        · intro hmem
          exact (hq2 y g fs hy hg) (List.mem_of_mem_erase hmem)
      · intro y g fs hy hg
        change c.heap y = some fs at hy
        change c.heap g ≠ none
        exact hq3 y g fs hy hg
      · intro p y fs hp' hy hg
        change c.heap y = some fs at hy
        change p ∈ c.pending ++ [a] at hp'
        rcases List.mem_append.mp hp' with hpp | hpp
        · exact hq4 p y fs hpp hy hg
        · have hpa : p = a := by simpa using hpp
          by_cases hya : y = a
          · rw [hya] at hy
            exact (hpa ▸ hq7 a fs hy) (hpa ▸ hg)
          · exact absurd har (hq2 y a fs hy (hpa ▸ hg))
      · intro p y y' fs fs' hy hpy hy' hpy'
        exact hq5 p y y' fs fs' hy hpy hy' hpy'
      · intro y fs hy
        exact hq6 y fs hy
      · intro y fs hy
        exact hq7 y fs hy
      · exact nodupErase hnd a
  | collect a fs hap hnar hrel hlook =>
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro x hx
        change (hDel c.heap a) x ≠ none at hx
        change Reach (hDel c.heap a) (c.roots ++ ((c.pending.erase a) ++ fs)) x
        have hxa := (hDel_live c.heap a x).mp hx |>.1
        rw [hDel, hUpd, if_neg hxa] at hx
        refine reach_del c.heap (hDel c.heap a) (c.roots ++ c.pending)
          (c.roots ++ ((c.pending.erase a) ++ fs)) a fs hlook
          (hUpd_self c.heap a none) ?_ ?_ ?_ x (hp1 x hx) hxa
        · intro y hy
          exact hUpd_ne c.heap a none y hy
        · intro z hz hza
          change z ∈ c.roots ++ ((c.pending.erase a) ++ fs)
          rcases List.mem_append.mp hz with hzr | hzp
          · exact appL hzr
          · exact appR (appL (eraseMem hzp hza))
        · intro g hg
          exact (List.mem_append).mpr (Or.inr ((List.mem_append).mpr (Or.inr hg)))
      · intro r hr
        change (hDel c.heap a) r ≠ none
        have hra : r ≠ a := by
          intro he
          rw [he] at hr
          exact hnar hr
        rw [hDel, hUpd, if_neg hra]
        exact hp2 r hr
      · intro p hp' hmem
        rcases List.mem_append.mp hp' with hpp | hpf
        · exact hq1 p (List.mem_of_mem_erase hpp) hmem
        · exact hq2 a p fs hlook hpf hmem
      · intro y g fsx hy hg hmem
        change (hDel c.heap a) y = some fsx at hy
        change g ∈ c.roots at hmem
        by_cases hya : y = a
        · rw [hya, hDel, hUpd_self] at hy
          cases hy
        · rw [hDel, hUpd, if_neg hya] at hy
          exact hq2 y g fsx hy hg hmem
      · intro y g fsx hy hg
        change (hDel c.heap a) y = some fsx at hy
        change (hDel c.heap a) g ≠ none
        by_cases hya : y = a
        · rw [hya, hDel, hUpd_self] at hy
          cases hy
        · rw [hDel, hUpd, if_neg hya] at hy
          by_cases hga : g = a
          · rw [hga, hDel, hUpd_self]
            exact (hrel y fsx hy (hga ▸ hg)).elim
          · rw [hDel, hUpd, if_neg hga]
            exact hq3 y g fsx hy hg
      · intro p y fsx hp' hy hg
        change (hDel c.heap a) y = some fsx at hy
        rcases List.mem_append.mp hp' with hpp | hpf
        · by_cases hya : y = a
          · rw [hya, hDel, hUpd_self] at hy
            cases hy
          · rw [hDel, hUpd, if_neg hya] at hy
            exact hq4 p y fsx (List.mem_of_mem_erase hpp) hy hg
        · have hpa : p ≠ a := fun h => (hq7 a fs hlook (h ▸ hpf)).elim
          by_cases hya : y = a
          · rw [hya, hDel, hUpd_self] at hy
            cases hy
          · rw [hDel, hUpd, if_neg hya] at hy
            exact False.elim (hya (Eq.symm (hq5 p a y fs fsx hlook hpf hy hg)))
      · intro p y y' fsx fsx' hy hpy hy' hpy'
        change (hDel c.heap a) y = some fsx at hy
        change (hDel c.heap a) y' = some fsx' at hy'
        by_cases hya : y = a
        · rw [hya, hDel, hUpd_self] at hy
          cases hy
        · rw [hDel, hUpd, if_neg hya] at hy
          have hya' : y' ≠ a := by
            intro he
            rw [he, hDel, hUpd_self] at hy'
            cases hy'
          rw [hDel, hUpd, if_neg hya'] at hy'
          exact hq5 p y y' fsx fsx' hy hpy hy' hpy'
      · intro y fsx hy
        change (hDel c.heap a) y = some fsx at hy
        by_cases hya : y = a
        · rw [hya, hDel, hUpd_self] at hy
          cases hy
        · rw [hDel, hUpd, if_neg hya] at hy
          exact hq6 y fsx hy
      · intro y fsx hy
        change (hDel c.heap a) y = some fsx at hy
        by_cases hya : y = a
        · rw [hya, hDel, hUpd_self] at hy
          cases hy
        · rw [hDel, hUpd, if_neg hya] at hy
          exact hq7 y fsx hy
      · exact hnd

/-!
## SG-002 headline theorems
-/

/-- **No leaks at quiescence.** When the pending queue is empty, every live
heap address is reachable from the roots alone. This is garbage-freedom with
no escape clause: Perceus (PLDI'21 Thm 4) must exempt references that are
part of a cycle, but Morph's affine discipline rules cycles out at the type
level (`ArcAffineIntegration`), so the exemption is unnecessary. -/
theorem quiescent_no_leak (c : Config) (hp : Precise c)
    (hempty : c.pending = []) :
    ∀ a, c.heap a ≠ none → Reach c.heap c.roots a := by
  intro a ha
  have h := hp.1 a ha
  simpa [hempty] using h

/-- Growth is paid for by allocation: `alloc` bumps the counter by one;
every other step keeps it. In particular none of `store`, `dropRoot` or
`collect` can grow the heap. -/
theorem allocs_step (c c' : Config) (hstep : Step c c') :
    c'.allocs ≤ c.allocs + 1 := by
  cases hstep <;> simp <;> omega

/-- **Allocation bound (SG-002).** After any `n`-step execution the allocation
counter has advanced by at most `n`; growth is paid for by allocation and
nothing else. -/
theorem allocs_bound (n : Nat) (c₀ cₙ : Config) (hrun : Steps n c₀ cₙ) :
    cₙ.allocs ≤ c₀.allocs + n := by
  induction hrun with
  | refl => exact Nat.le_refl _
  | tail _ _ _ _ hrun' hstep ih =>
      have h1 := allocs_step _ _ hstep
      omega

/-- The invariant holds at the end of every execution: `Precise` and
`Affine` are both inductive invariants of the step relation. -/
theorem invariant_is_invariant {n : Nat} {c₀ cₙ : Config} (hrun : Steps n c₀ cₙ)
    (hp : Invariant c₀) : Invariant cₙ := by
  induction hrun with
  | refl => exact hp
  | tail _ _ _ _ hrun' hstep ih => exact invariant_preserved _ _ hstep (ih hp)

end Morph.Specs.MemoryBounds