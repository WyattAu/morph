import Morph.Specs.TypeUnification.Spec
open Morph.Specs.TypeUnification
open Morph.Specs.TypeUnification
namespace Morph.Specs.TypeUnification

example (fuel : Nat) (x y : Nat) (σ : Subst)
    (h : unifyF (fuel + 1) (.v x) (.v y) = some σ) :
    apply σ (.v x) = apply σ (.v y) := by
  rw [unifyF] at h
  split at h
  · next hxy =>
      simp only [Option.some.injEq] at h
      subst h
      rw [hxy]
  · next hne =>
      simp only [Option.some.injEq] at h
      have hσ : σ = update Subst.id x (.v y) := h.symm
      subst hσ
      show (if x = x then UTerm.v y else Subst.id x) =
        (if y = x then UTerm.v y else Subst.id y)
      rw [if_pos rfl, if_neg (fun he => hne he.symm)]

end Morph.Specs.TypeUnification
